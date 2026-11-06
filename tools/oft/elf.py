"""The ELF files `oft symbols` reads: 64-bit little-endian executables (riscv64), of which it needs the section headers,
.text, the allocated sections and their bytes, and the functions and data objects of .symtab.  The standard library
only: tools/oft takes no ELF package."""
import collections
import hashlib
import struct

_HEADER = struct.Struct("<16sHHIQQQIHHHHHH")     # Elf64_Ehdr
_SECTION = struct.Struct("<IIQQQQIIQQ")          # Elf64_Shdr
_SYMBOL = struct.Struct("<IBBHQQ")               # Elf64_Sym
# the fields of an Elf64_Ehdr and of an Elf64_Shdr, in the order of the structs above
_FileHeader = collections.namedtuple("_FileHeader", "ident type machine version entry phoff shoff flags ehsize "
                                                    "phentsize phnum shentsize shnum shstrndx")
_SectionHeader = collections.namedtuple("_SectionHeader", "name type flags addr offset size link info addralign "
                                                          "entsize")
# an allocated section, as Elf.sections gives it: bytes is None for one with no file contents
Section = collections.namedtuple("Section", "name type address size bytes")
SHT_SYMTAB = 2
SHT_NOTE = 7
SHT_NOBITS = 8
SHF_WRITE = 0x1
SHF_ALLOC = 0x2
SHF_TLS = 0x400
STT_OBJECT = 1
STT_FUNC = 2
SHN_UNDEF = 0
# the kind of each symbol type a symbol fact lists (symbols.KINDS)
KINDS = {STT_FUNC: "func", STT_OBJECT: "object"}
# the binding of a symbol (Elf64_Sym st_info >> 4): STB_LOCAL, STB_GLOBAL, STB_WEAK; any other binding is "other"
BINDINGS = {0: "local", 1: "global", 2: "weak"}
# a function or data object of .symtab, as Elf.symbols gives it
Symbol = collections.namedtuple("Symbol", "name kind address size binding")


class Elf:
    """One ELF file: its sha256, and the bytes and address of its .text."""

    def __init__(self, path):
        self.path = path
        with open(path, "rb") as f:
            self.data = f.read()
        self.sha256 = hashlib.sha256(self.data).hexdigest()
        if len(self.data) < _HEADER.size or self.data[:4] != b"\x7fELF":
            raise ValueError("%s is not an ELF file" % path)
        if self.data[4:6] != b"\x02\x01":
            raise ValueError("%s is not a 64-bit little-endian ELF file" % path)
        h = _FileHeader._make(_HEADER.unpack_from(self.data))
        if h.shnum == 0 or h.shentsize != _SECTION.size or h.shoff + h.shnum * h.shentsize > len(self.data):
            raise ValueError("%s has no section headers this reader can read" % path)
        self._sections = [_SectionHeader._make(_SECTION.unpack_from(self.data, h.shoff + i * h.shentsize))
                          for i in range(h.shnum)]
        if h.shstrndx >= h.shnum:
            raise ValueError("%s has no section name table" % path)
        names = self._bytes(h.shstrndx)
        self._names = [self._string(names, s.name) for s in self._sections]
        if ".text" not in self._names:
            raise ValueError("%s has no .text" % path)
        text = self._names.index(".text")
        self.text_addr = self._sections[text].addr
        self.text = self._bytes(text)

    def _bytes(self, i):
        """The bytes of section i in the file."""
        s = self._sections[i]
        if s.type == SHT_NOBITS:
            return b""
        if s.offset + s.size > len(self.data):
            raise ValueError("%s: section %d runs past the end of the file" % (self.path, i))
        return self.data[s.offset:s.offset + s.size]

    def contents(self, address, size):
        """The bytes at [address, address + size) in the allocated section that holds them, or None when that section
        has no file contents (SHT_NOBITS: .bss); ValueError when no allocated section holds them.  A TLS section
        (.tdata, .tbss) is left out: its addresses are a template's, which overlap the sections after it."""
        for i, s in enumerate(self._sections):
            if (s.flags & SHF_ALLOC and not s.flags & SHF_TLS
                    and s.addr <= address and address + size <= s.addr + s.size):
                if s.type == SHT_NOBITS:
                    return None
                if s.offset + s.size > len(self.data):
                    raise ValueError("%s: section %d runs past the end of the file" % (self.path, i))
                start = s.offset + address - s.addr
                return self.data[start:start + size]
        raise ValueError("%s: no allocated section holds the %d bytes at 0x%x" % (self.path, size, address))

    def constant(self, address, size):
        """The bytes at [address, address + size) when an allocated section that the program cannot write holds them
        (no SHF_WRITE; not TLS; with file contents), such as a jump table in .rodata; otherwise None."""
        for i, s in enumerate(self._sections):
            if (s.flags & SHF_ALLOC and not s.flags & (SHF_WRITE | SHF_TLS) and s.type != SHT_NOBITS
                    and s.addr <= address and address + size <= s.addr + s.size):
                if s.offset + s.size > len(self.data):
                    raise ValueError("%s: section %d runs past the end of the file" % (self.path, i))
                start = s.offset + address - s.addr
                return self.data[start:start + size]
        return None

    def sections(self):
        """[Section] of every allocated section, in the order of the section headers; its bytes are None for a
        section with no file contents (SHT_NOBITS: .bss, .tbss)."""
        return [Section(self._names[i], s.type, s.addr, s.size, None if s.type == SHT_NOBITS else self._bytes(i))
                for i, s in enumerate(self._sections) if s.flags & SHF_ALLOC]

    def _string(self, table, offset):
        end = table.find(b"\0", offset)
        if offset >= len(table) or end < 0:
            raise ValueError("%s: a name at %d is outside its string table" % (self.path, offset))
        return table[offset:end].decode("utf-8")

    def symbols(self):
        """[Symbol] of every defined function ("func") and data object ("object") of .symtab, every alias under its
        own name, sorted by address, then name: each object with a size, and each function, of size 0 too (musl's
        _start), with its binding (BINDINGS).  A file without .symtab (a stripped one) is refused."""
        tables = [i for i, s in enumerate(self._sections) if s.type == SHT_SYMTAB]
        if not tables:
            raise ValueError("%s has no symbol table (.symtab): give its unstripped twin" % self.path)
        symtab = self._bytes(tables[0])
        link = self._sections[tables[0]].link
        if link >= len(self._sections):
            raise ValueError("%s: .symtab links no string table" % self.path)
        strtab = self._bytes(link)
        out = []
        for off in range(0, len(symtab) - _SYMBOL.size + 1, _SYMBOL.size):
            name, info, _other, shndx, value, size = _SYMBOL.unpack_from(symtab, off)
            kind = KINDS.get(info & 0xF)
            if kind is not None and (size > 0 or kind == "func") and shndx != SHN_UNDEF:
                out.append(Symbol(self._string(strtab, name), kind, value, size, BINDINGS.get(info >> 4, "other")))
        return sorted(out, key=lambda s: (s[2], s[0]))
