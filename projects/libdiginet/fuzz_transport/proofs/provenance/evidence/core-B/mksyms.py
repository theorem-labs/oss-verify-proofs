# name addr size, from an unstripped twin's .symtab: FUNC and OBJECT symbols with size > 0, unique, sorted.
#   mksyms.py <unstripped twin> <pinned image>
# The header line names both files by sha256 only (no host path).
import sys, hashlib
from elftools.elf.elffile import ELFFile
twin, pin = sys.argv[1], sys.argv[2]
rows = set()
with open(twin, 'rb') as f:
    for s in ELFFile(f).get_section_by_name('.symtab').iter_symbols():
        if s['st_size'] > 0 and s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT') and s.name:
            rows.add((s.name, s['st_value'], s['st_size']))
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
print(f"# from the symtab of the unstripped twin sha256 {sha(twin)}; pin sha256 {sha(pin)}")
for n, a, z in sorted(rows):
    print(f"{n} {a:#x} {z}")
