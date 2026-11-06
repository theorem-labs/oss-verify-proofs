"""make.py: the fixture of test_symbols.RealLoadedTailCalls (README.md): six functions of the asan runtime in the
fuzz_ctrl asan and asan-ubsan builds of FreeREAC/libreac 3425050 and 1842185, each with what symbols.mask asks of its
build's Image (symbols.build_image) while it masks them, and __sanitizer::VSNPrintf of the 1842185 asan build with the
bytes its jump table proof reads.

    PYTHONPATH=. python3 -B oft/tests/fixtures/masker/make.py WORK_3425050 WORK_1842185 > OUT.json

where each WORK holds raw/<build>/fuzz_ctrl (the unstripped twin) and out/fuzz_ctrl/fuzz_ctrl.<build> (the stripped
binary), as tools/check's work directory does."""
import bisect
import hashlib
import json
import os
import sys

from oft import elf, symbols

NAMES = ("___interceptor_strcmp", "___interceptor_memcmp", "___interceptor_bcmp", "___interceptor_wcrtomb",
         "_ZN6__asan12PoisonShadowEmmh", "__unw_step")
VSNPRINTF = "_ZN11__sanitizer9VSNPrintfEPciPKcPv"


class Noreturn(frozenset):
    """A frozenset that records each address mask asks it about and holds."""
    def __new__(cls, items, asked):
        self = super().__new__(cls, items)
        self.asked = asked
        return self

    def __contains__(self, address):
        held = frozenset.__contains__(self, address)
        if held:
            self.asked.add(address)
        return held


def recorder(read, log):
    def ask(address, size):
        got = read(address, size)
        log["%x:%d" % (address, size)] = None if got is None else got.hex()
        return got
    return ask


def function(bare, image, sym):
    code = bare.text[sym.address - bare.text_addr:sym.address - bare.text_addr + sym.size]
    asked, constant, data = set(), {}, {}
    seen = image._replace(noreturn=Noreturn(image.noreturn, asked), constant=recorder(image.constant, constant),
                          data=recorder(image.data, data))
    masked = symbols.mask(code, sym.address, seen)
    lo, hi = sym.address, sym.address + sym.size
    k = bisect.bisect_left(image.stored, lo)
    return {"address": sym.address, "code": code.hex(), "masked_sha256": hashlib.sha256(masked).hexdigest(),
            "noreturn": sorted(asked), "constant": constant, "data": data,
            "stored": [v for v in image.stored[k:] if v < hi],
            "landing": [list(r) for r in image.landing if r[0] < hi and lo < r[1]]}


def main(work_base, work_head):
    out = {"sections": {}, "functions": {}}
    for side, work in (("3425050", work_base), ("1842185", work_head)):
        for build in ("asan", "asan-ubsan"):
            full = elf.Elf(os.path.join(work, "raw", build, "fuzz_ctrl"))
            bare = elf.Elf(os.path.join(work, "out", "fuzz_ctrl", "fuzz_ctrl." + build))
            syms = full.symbols()
            image = symbols.build_image(bare, bare.sections(), symbols.noreturn_addresses(syms),
                                        functions=[(s.address, s.size) for s in syms if s.kind == "func"])
            key = "%s/%s" % (side, build)
            out["sections"][key] = [list(s) for s in image.sections]
            by_name = {s.name: s for s in syms if s.kind == "func"}
            out["functions"][key] = {name: function(bare, image, by_name[name]) for name in NAMES}
            if key == "1842185/asan":
                sym = by_name[VSNPRINTF]
                constant, asked = {}, set()
                spans = symbols.jump_table_words(bare.text, bare.text_addr, [(sym.address, sym.size)],
                                                 recorder(bare.constant, constant), Noreturn(image.noreturn, asked))
                out["vsnprintf"] = {"address": sym.address,
                                    "code": bare.text[sym.address - bare.text_addr:
                                                      sym.address - bare.text_addr + sym.size].hex(),
                                    "constant": constant, "noreturn": sorted(asked),
                                    "spans": [list(s) for s in spans]}
    json.dump(out, sys.stdout, indent=1, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main(*sys.argv[1:])
