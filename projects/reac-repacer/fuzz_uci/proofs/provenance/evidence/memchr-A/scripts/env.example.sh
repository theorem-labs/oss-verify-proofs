# Variables read by mk_evidence_memchr.py (set each to a local path; no values are recorded here).
export UCI_A=        # fuzz_uci.asan, unstripped twin
export UCI_B=        # fuzz_uci.asan-ubsan, unstripped twin
export UCI_PIN_A=    # fuzz_uci.asan, the pinned image (projects/reac-repacer/fuzz_uci/harness.yaml)
export UCI_PIN_B=    # fuzz_uci.asan-ubsan, the pinned image
export BOX_A=        # fuzz_boxreg.asan, unstripped twin
export BOX_B=        # fuzz_boxreg.asan-ubsan, unstripped twin
export BOX_PIN_A=    # fuzz_boxreg.asan, the pinned image (projects/libreac/fuzz_boxreg/harness.yaml)
export BOX_PIN_B=    # fuzz_boxreg.asan-ubsan, the pinned image
export WT_LIB=      # the unit's proofs/reac-repacer/fuzz_uci/lib, read by memchr-local.py --check
export TOOLS=        # directory with bytecmp-7daa0e2a03d9.py and repin_check-9cbc3553c09e.py (the tools of record, commit 8cd71d3a4bb)
export PYTHONPATH=   # a pyelftools install
