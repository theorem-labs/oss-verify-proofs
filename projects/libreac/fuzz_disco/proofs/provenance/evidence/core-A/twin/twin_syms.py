"""twin_syms.py: read an extract_twin.py text extract with the part of the pyelftools ELFFile interface the scripts of
this directory use on an unstripped twin: iter_sections(), get_section_by_name(name), and on '.symtab'
iter_symbols(). A section reads like a pyelftools section (s.name, s['sh_addr'], s['sh_size'], s['sh_type'],
s['sh_flags']); a symbol like a pyelftools symbol (s.name, s['st_value'], s['st_size'], s['st_info']['type'],
s['st_info']['bind'], s['st_shndx']). Only header facts are in the extract: section data is not.
"""


class _Entry(dict):
    def __init__(self, name, fields):
        super().__init__(fields)
        self.name = name


class _Section(_Entry):
    def __init__(self, name, fields, symbols=None):
        super().__init__(name, fields)
        self._symbols = symbols

    def iter_symbols(self):
        if self._symbols is None:
            raise AttributeError(f'section {self.name} has no symbols in the extract')
        return iter(self._symbols)


class Twin:
    def __init__(self, path):
        secs, syms = [], []
        for line in open(path):
            if line.startswith('S '):
                _, _, name, typ, addr, size, flags = line.split()
                secs.append((name if name != '-' else '', typ, int(addr, 16), int(size, 16), int(flags, 16)))
            elif line.startswith('Y '):
                _, _, val, size, typ, bind, shndx, name = line.split()
                sym = _Entry(name if name != '-' else '', {
                    'st_value': int(val, 16), 'st_size': int(size, 16),
                    'st_info': {'type': typ, 'bind': bind},
                    'st_shndx': int(shndx) if shndx.isdigit() else shndx})
                syms.append(sym)
        self._sections = [
            _Section(n, {'sh_type': t, 'sh_addr': a, 'sh_size': s, 'sh_flags': f},
                     syms if n == '.symtab' else None)
            for n, t, a, s, f in secs]

    def iter_sections(self):
        return iter(self._sections)

    def num_sections(self):
        return len(self._sections)

    def get_section_by_name(self, name):
        return next((s for s in self._sections if s.name == name), None)


def load(path):
    return Twin(path)
