import sys
import math
import os
import re
import hashlib
import shutil
import struct
import zlib
import lzma

done = "Error: No games found."
total = 0
count = 0

# ISO9660 directory record of the boot file: 01 0D + "SLUS_123.45" + ";1"
TITLE_RE = re.compile(rb'\x01\x0D([\x00-\xff]{4}_[\x00-\xff]{3}\.[\x00-\xff]{2});1')
CHUNK_SIZE = 1024 * 1024
OVERLAP = 20  # max pattern length - 1

IMAGE_EXTS = (".iso", ".chd")



# ---------------- Pure Python CHD v5 reader (no extraction) ----------------
# CHD v5 map compression types
COMP_NONE, COMP_SELF, COMP_PARENT = 4, 5, 6
RLE_SMALL, RLE_LARGE = 7, 8
SELF_0, SELF_1, PARENT_SELF, PARENT_0, PARENT_1 = 9, 10, 11, 12, 13

CD_FRAME = 2448      # 2352 sector + 96 subcode
CD_SECTOR = 2352


class _Bits:
    def __init__(self, data):
        self.data, self.pos, self.buf, self.cnt = data, 0, 0, 0

    def _fill(self, n):
        while self.cnt < n:
            b = self.data[self.pos] if self.pos < len(self.data) else 0
            self.pos += 1
            self.buf = (self.buf << 8) | b
            self.cnt += 8

    def peek(self, n):
        self._fill(n)
        return (self.buf >> (self.cnt - n)) & ((1 << n) - 1)

    def skip(self, n):
        self.cnt -= n
        self.buf &= (1 << self.cnt) - 1

    def read(self, n):
        if n == 0:
            return 0
        v = self.peek(n)
        self.skip(n)
        return v


def _huffman_map_decoder(bits, numcodes=16, maxbits=8):
    numbits = 4  # 4 bits per entry since maxbits >= 8
    lens = []
    while len(lens) < numcodes:
        nb = bits.read(numbits)
        if nb != 1:
            lens.append(nb)
        else:
            nb = bits.read(numbits)
            if nb == 1:
                lens.append(1)
            else:
                lens.extend([nb] * (bits.read(numbits) + 3))
    lens = lens[:numcodes]

    histo = [0] * 33
    for l in lens:
        if l <= 32:
            histo[l] += 1
    start = 0
    for l in range(32, 0, -1):
        nxt = (start + histo[l]) >> 1
        histo[l] = start
        start = nxt

    table = [None] * (1 << maxbits)
    for code, l in enumerate(lens):
        if l > 0:
            c = histo[l]
            histo[l] += 1
            shift = maxbits - l
            for i in range(c << shift, ((c + 1) << shift)):
                table[i] = (code, l)

    def decode():
        sym, l = table[bits.peek(maxbits)]
        bits.skip(l)
        return sym
    return decode


def _zstd_decompress(data):
    try:
        from compression import zstd  # Python 3.14+
        return zstd.ZstdDecompressor().decompress(data)
    except ImportError:
        import zstandard  # pip install zstandard
        return zstandard.ZstdDecompressor().decompressobj().decompress(data)


class ChdFile:
    def __init__(self, path):
        self.f = open(path, "rb")
        h = self.f.read(124)
        if h[:8] != b"MComprHD":
            raise ValueError("Non è un file CHD")
        length, version = struct.unpack(">II", h[8:16])
        if version != 5:
            raise ValueError(f"CHD v{version} non supportato (solo v5)")
        self.codecs = [h[16 + i * 4:20 + i * 4] for i in range(4)]
        self.logical, self.mapoffset, self.metaoffset = struct.unpack(">QQQ", h[32:56])
        self.hunkbytes, self.unitbytes = struct.unpack(">II", h[56:64])
        self.hunkcount = (self.logical + self.hunkbytes - 1) // self.hunkbytes
        self._entries = []          # (type, offset, length)
        self._init_map()

    def close(self):
        self.f.close()

    def __len__(self):
        return self.hunkcount

    def _init_map(self):
        f = self.f
        f.seek(self.mapoffset)
        if self.codecs[0] == b"\0\0\0\0":
            raw = f.read(self.hunkcount * 4)
            self._entries = [(COMP_NONE, struct.unpack(">I", raw[i * 4:i * 4 + 4])[0] * self.hunkbytes,
                              self.hunkbytes) for i in range(self.hunkcount)]
            self._gen = iter(())
            return
        hdr = f.read(16)
        mapbytes = struct.unpack(">I", hdr[0:4])[0]
        self._curoffs = int.from_bytes(hdr[4:10], "big")
        self._lengthbits, self._selfbits, self._parentbits = hdr[12], hdr[13], hdr[14]
        self._bits = _Bits(f.read(mapbytes))
        decode = _huffman_map_decoder(self._bits)

        types, rep, last = [], 0, 0
        for _ in range(self.hunkcount):
            if rep > 0:
                types.append(last)
                rep -= 1
                continue
            v = decode()
            if v == RLE_SMALL:
                types.append(last)
                rep = 2 + decode()
            elif v == RLE_LARGE:
                types.append(last)
                rep = 2 + 16 + (decode() << 4)
                rep += decode()
            else:
                types.append(v)
                last = v
        self._types = types
        self._last_self = 0
        self._last_parent = 0

    def _decode_upto(self, n):
        """Lazily decode the map up to and including hunk n."""
        bits = self._bits
        while len(self._entries) <= n:
            i = len(self._entries)
            t = self._types[i]
            off, ln = self._curoffs, 0
            if t <= 3:
                ln = bits.read(self._lengthbits)
                self._curoffs += ln
                bits.read(16)
            elif t == COMP_NONE:
                ln = self.hunkbytes
                self._curoffs += ln
                bits.read(16)
            elif t == COMP_SELF:
                off = bits.read(self._selfbits)
                self._last_self = off
            elif t == COMP_PARENT:
                off = bits.read(self._parentbits)
                self._last_parent = off
            elif t in (SELF_0, SELF_1):
                if t == SELF_1:
                    self._last_self += 1
                t, off = COMP_SELF, self._last_self
            else:
                t = COMP_PARENT
            self._entries.append((t, off, ln))

    def hunk(self, n):
        if n >= self.hunkcount:
            raise IndexError(n)
        if hasattr(self, "_bits"):
            self._decode_upto(n)
        t, off, ln = self._entries[n]
        if t == COMP_SELF:
            return self.hunk(off)
        if t == COMP_PARENT:
            raise NotImplementedError("CHD con parent non supportato")
        self.f.seek(off)
        data = self.f.read(ln)
        if t == COMP_NONE:
            return data
        return self._decompress(self.codecs[t], data)

    def _decompress(self, codec, data):
        hb = self.hunkbytes
        if codec == b"zlib":
            return zlib.decompressobj(-15).decompress(data, hb)
        if codec == b"lzma":
            return self._lzma(data, hb)
        if codec == b"zstd":
            return _zstd_decompress(data)
        if codec in (b"cdlz", b"cdzl", b"cdzs"):
            frames = hb // CD_FRAME
            ecc = (frames + 7) // 8
            cl = 2 if hb < 65536 else 3
            base_len = int.from_bytes(data[ecc:ecc + cl], "big")
            base = data[ecc + cl:ecc + cl + base_len]
            if codec == b"cdlz":
                sectors = self._lzma(base, frames * CD_SECTOR)
            elif codec == b"cdzl":
                sectors = zlib.decompressobj(-15).decompress(base, frames * CD_SECTOR)
            else:
                sectors = _zstd_decompress(base)
            # subcode is not needed: pad with zeros
            pad = bytes(CD_FRAME - CD_SECTOR)
            return b"".join(sectors[i * CD_SECTOR:(i + 1) * CD_SECTOR] + pad for i in range(frames))
        raise NotImplementedError(f"Codec {codec!r} non supportato")

    @staticmethod
    def _lzma(data, outlen):
        flt = [{"id": lzma.FILTER_LZMA1, "dict_size": max(4096, outlen), "lc": 3, "lp": 0, "pb": 2}]
        return lzma.LZMADecompressor(lzma.FORMAT_RAW, filters=flt).decompress(data, outlen)

    def iter_hunks(self, skip_unsupported=True):
        """Iterate over the hunks. Hunks using an unsupported codec (flac/huff)
        are replaced with zeros if skip_unsupported=True."""
        for n in range(self.hunkcount):
            try:
                yield self.hunk(n)
            except NotImplementedError:
                if not skip_unsupported:
                    raise
                yield bytes(self.hunkbytes)


def is_image(name):
    return name.lower().endswith(IMAGE_EXTS)


def iter_iso_chunks(path):
    with open(path, "rb") as f:
        while chunk := f.read(CHUNK_SIZE):
            yield chunk


def iter_chunks(path):
    if path.lower().endswith(".chd"):
        chd = ChdFile(path)
        try:
            yield from chd.iter_hunks()
        finally:
            chd.close()
    else:
        yield from iter_iso_chunks(path)


def find_title_id(path):
    tail = b""
    for chunk in iter_chunks(path):
        data = tail + chunk
        m = TITLE_RE.search(data)
        if m:
            return m.group(1).decode("utf-8", errors="ignore")
        tail = data[-OVERLAP:]
    return None


def count_iso(folder, game_path):
    global total
    for image in os.listdir(game_path + folder):
        if is_image(image):
            total += 1


def process_iso(folder, game_path, xeb_path, game_list, create_vmc):
    global total, count, done

    for image in os.listdir(game_path + folder):
        if not is_image(image):
            continue

        print(f"{math.floor((count * 100) / total)}% complete")
        print(f"Processing {image}")
        try:
            string = find_title_id(game_path + folder + "/" + image)
        except Exception as e:
            print(f"Error reading {image}: {e}")
            count += 1
            continue
        count += 1

        if not string:
            print(f"Error: Title ID not found in {image}")
            continue

        if string:
            print(f"Found title ID {string}")

            vmc = f"/VMC/{string}_0.bin"
            with open("vmc_groups.list", "r") as f:
                lines = f.readlines()

            for line in lines:
                line = line.strip()
                if line[:4] == "XEBP":
                    size = "8"
                    group = line
                elif len(line) < 5:
                    size = line[:2]
                elif line == string:
                    vmc = f"/VMC/{group}_0.bin"
                    break

            if create_vmc:
                if vmc != f"/VMC/{string}_0.bin" and not os.path.isfile(game_path + f"/VMC/{string}_0.bin"):
                    print(f"Creating VMC /VMC/{string}_0.bin (8MB)")
                    shutil.copyfile(".vmc/8.bin", game_path + f"/VMC/{string}_0.bin")
                if not os.path.isfile(game_path + vmc):
                    print(f"Creating VMC {vmc} ({size}MB)")
                    shutil.copyfile(f".vmc/{size}.bin", game_path + vmc)
                print(f"Assigned {string} to {vmc}")
            elif not os.path.isfile(game_path + vmc):
                vmc = "0000000000000000000000"

            list_name = image + ".iso" if image.lower().endswith(".chd") else image
            with open(xeb_path + game_list, "a") as output:
                output.write(f"{string} {folder}/{list_name} {vmc}\n")

    done = "Done!"


def error_message():
    print('Error: Missing argument(s).')
    print('Usage: list_builder.py <drive type>[-h -u -m -c -i -b] <path/to/games> <path/to/XEBPLUS/installation> <create VMCs>[-vmc]')
    print('')
    print('Examples:')
    print('list_builder.py -h E:\\PS2 D:\\')
    print('list_builder.py -u D:\\ D:\\ -vmc')
    print('list_builder.py -m \'/media/SD Card\' \'/media/USB Drive\'')
    print('')
    quit()


def main(arg1, arg2, arg3, arg4):
    if arg1 and arg2 and arg3:
        drive = arg1
        game_path = arg2
        xeb_path = arg3
        create_vmc = arg4 == "-vmc"
    else:
        error_message()

    print('')
    print('This program will create the list of installed PS2 games that is required by the XEB+ neutrino loader plugin.')
    print('Additonal documentation can be found at https://github.com/sync-on-luma/xebplus-neutrino-loader-plugin')

    if drive.lower() == "-h":
        game_list = 'neutrinoHDD.list'
    elif drive.lower() == "-u":
        game_list = 'neutrinoUSB.list'
    elif drive.lower() == "-m":
        game_list = 'neutrinoMX4.list'
    elif drive.lower() == "-c":
        game_list = 'neutrinoMMCE.list'
    elif drive.lower() == "-i":
        game_list = 'neutrinoILINK.list'
    elif drive.lower() == "-b":
        game_list = 'neutrinoUDPBD.list'
    else:
        print('Error: Invalid drive type')
        quit()

    if not os.path.isdir(xeb_path + '/XEBPLUS'):
        print(f'\nError: Cannot find XEBPLUS folder at {xeb_path}')
        quit()
    if not os.path.isdir(xeb_path + '/XEBPLUS/CFG/neutrinoLauncher'):
        os.mkdir(xeb_path + '/XEBPLUS/CFG/neutrinoLauncher')
    xeb_path = xeb_path + '/XEBPLUS/CFG/neutrinoLauncher/'
    print('')

    if os.path.isfile(xeb_path + game_list):
        os.remove(xeb_path + game_list)

    if create_vmc and not os.path.isfile(".vmc/8.bin"):
        print("Warning: VMC.bin not found. VMCs will not be created.")
        create_vmc = False

    if os.path.isdir(game_path + '/CD'):
        count_iso('/CD', game_path)
    else:
        print(f'CD folder not found at {game_path}')
    if os.path.isdir(game_path + '/DVD'):
        count_iso('/DVD', game_path)
    else:
        print(f'DVD folder not found at {game_path}')

    if create_vmc and not os.path.isdir(game_path + '/VMC'):
        os.mkdir(game_path + '/VMC')

    if os.path.isdir(game_path + '/DVD'):
        process_iso('/DVD', game_path, xeb_path, game_list, create_vmc)
    if os.path.isdir(game_path + '/CD'):
        process_iso('/CD', game_path, xeb_path, game_list, create_vmc)

    if os.path.isfile(xeb_path + game_list):
        with open(xeb_path + game_list, "r") as output:
            hash = hashlib.md5(output.read().encode("utf-8")).hexdigest()
        with open(xeb_path + game_list, "a") as output:
            output.write(hash)

    print(done)
    print('')


if __name__ == '__main__':
    if len(sys.argv) == 5:
        main(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4])
    elif len(sys.argv) == 4:
        main(sys.argv[1], sys.argv[2], sys.argv[3], "")
    else:
        error_message()
