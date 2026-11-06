"""Image access for the triage: symbols from the unstripped twin's .symtab, bytes from the pin's PT_LOAD file
images (the pin and its twin are one link; the twin only differs in the build-id note and the symbol/debug
sections), section and segment bounds from the ELF headers. pyelftools only."""
import bisect, hashlib, struct
from elftools.elf.elffile import ELFFile


class Img:
    def __init__(self, role, pin, twin):
        self.role = role
        self.pin_path, self.twin_path = pin, twin
        self.pin_bytes = open(pin, 'rb').read()
        self.sha_pin = hashlib.sha256(self.pin_bytes).hexdigest()[:12]
        self.sha_twin = hashlib.sha256(open(twin, 'rb').read()).hexdigest()[:12]
        with open(pin, 'rb') as fh:
            e = ELFFile(fh)
            self.machine = e['e_machine']
            self.entry = e['e_entry']
            self.loads = [(p['p_vaddr'], p['p_memsz'], p['p_offset'], p['p_filesz'], p['p_flags'])
                          for p in e.iter_segments() if p['p_type'] == 'PT_LOAD']
            self.phdrs = [(p['p_type'], p['p_vaddr'], p['p_memsz'], p['p_filesz'], p['p_flags'])
                          for p in e.iter_segments()]
        with open(twin, 'rb') as fh:
            e = ELFFile(fh)
            self.sections = {s.name: (s['sh_addr'], s['sh_size'], s['sh_type'])
                             for s in e.iter_sections() if s['sh_addr']}
            st = e.get_section_by_name('.symtab')
            syms = []
            for s in st.iter_symbols():
                t = s['st_info']['type']
                if not s.name or t in ('STT_SECTION', 'STT_FILE'):
                    continue
                syms.append((s['st_value'], s['st_size'], s.name, t, s['st_shndx'], s['st_info']['bind']))
        self.syms = sorted(syms, key=lambda s: (s[0], s[2]))
        self.vals = [s[0] for s in self.syms]
        self.byname = {}
        for s in self.syms:
            self.byname.setdefault(s[2], []).append(s)

    # --- symbols
    def at(self, a, types=('STT_OBJECT', 'STT_FUNC', 'STT_NOTYPE', 'STT_TLS', 'STT_GNU_IFUNC')):
        i = bisect.bisect_left(self.vals, a)
        out = []
        while i < len(self.syms) and self.syms[i][0] == a:
            if self.syms[i][3] in types and self.syms[i][4] not in ('SHN_UNDEF',) and not self.syms[i][2].startswith('$'):
                out.append(self.syms[i])
            i += 1
        return out

    def covering(self, a):
        """sized symbols whose [value, value + size) holds a (not ABS / TLS offsets)."""
        i = bisect.bisect_right(self.vals, a)
        out = []
        j = i - 1
        while j >= 0 and a - self.syms[j][0] < (1 << 22):
            v, sz, n, t, sh, b = self.syms[j]
            if sz and v <= a < v + sz and t in ('STT_OBJECT', 'STT_FUNC') and sh not in ('SHN_ABS', 'SHN_UNDEF'):
                out.append(self.syms[j])
            j -= 1
        return out

    def sym(self, name):
        """the unique defined symbol of that name (value, size)."""
        c = [s for s in self.byname.get(name, []) if s[4] != 'SHN_UNDEF']
        if len(c) != 1:
            raise KeyError(f'{name}: {len(c)} definitions')
        return c[0][0], c[0][1]

    def describe(self, a):
        s = self.at(a)
        if s:
            return ', '.join(sorted({x[2] for x in s}))
        c = self.covering(a)
        if c:
            v, sz, n = c[0][:3]
            return f'{n}+{a - v:#x}'
        return self.section_of(a) or 'no section'

    # --- geometry
    def section_of(self, a):
        for n, (lo, sz, t) in self.sections.items():
            if lo <= a < lo + sz:
                return n
        return None

    def sec(self, name):
        lo, sz, t = self.sections[name]
        return lo, lo + sz

    def hull(self):
        lo = min(v for v, m, *_ in self.loads) & ~0xfff
        hi = max(v + m for v, m, *_ in self.loads)
        return lo, (hi + 0xfff) & ~0xfff

    # --- bytes
    def read(self, a, n):
        out = bytearray()
        for k in range(n):
            x = a + k
            for v, m, off, fs, fl in self.loads:
                if v <= x < v + m:
                    out.append(self.pin_bytes[off + x - v] if x - v < fs else 0)
                    break
            else:
                raise ValueError(f'{x:#x} outside every PT_LOAD')
        return bytes(out)

    def u32(self, a):
        return struct.unpack('<I', self.read(a, 4))[0]

    def u64(self, a):
        return struct.unpack('<Q', self.read(a, 8))[0]

    def cstr(self, a, limit=256):
        b = self.read(a, limit)
        return b.split(b'\0', 1)[0]


def load(root):
    """the two images from a folder holding cmd.A.pin cmd.A.twin cgif.A.pin cgif.A.twin (root ends with /)."""
    ours = Img('fuzz_command.asan', root + 'cmd.A.pin', root + 'cmd.A.twin')
    donor = Img('cgif_file_fuzzer.asan', root + 'cgif.A.pin', root + 'cgif.A.twin')
    return ours, donor
