# provenance/evidence/uci-b-memcpy: fuzz_uci image-B __asan_memcpy contract

The files a reader needs to check that lib/B/YE2q.v's `asan_memcpy_realizes` (carried in the image-B core, relocated from
fuzz_grant's released image B) states uci image B's `__asan_memcpy`: its build and assumptions, the byte compare of the
whole call closure against the donor image on the comparison kit 86da41d3ef68, the named measurement of every unnamed
target the kit leaves open, the use trace of every lui-built value the kit leaves open with the full address of every access it is part of, and the harness call sites on
both images. No library file is added or changed. Environment of the scripts: `KIT` the comparison kit's directory (its
SHA256SUMS checked); the two images are the unstripped twins of uci image B and fuzz_grant image B.

| file | role |
|---|---|
| MANIFEST.md | this list |
| RECORD.md | the theorem; the cb build of record (rc, wall, targets, pins, built files' sha256) and every axiom name Print Assumptions lists; the donor compare in eight steps (0-7) with its counts and measurement table; the harness call sites and why the fake-stack destination is covered |
| ambiscan-4bbd-record.out | the kit's ambiscan over this record as made on cmpkit 4bbd3a74be89: no by-name compare took the wrong copy of a duplicated name |
| twins.out | the kit's drvcmp.py twins: each unstripped twin against its stripped pin (equal outside the ELF header and the build id) |
| closure-memcpy.out | the kit's closure_strict3.py over __asan_memcpy's call closure, uci B against grant B: 785 functions, 170 EQUAL, 515 EQUAL-mod-pcrel, 100 DIFFERENT-target, with every differing target and acceptance |
| others.txt | the 100 DIFFERENT-target members, as jtcheck's function list |
| jtcheck-others.out | the kit's jtcheck.py on the 100: 10 settled; 74 lui-in-section, 74 UNMEASURED and 2 DIFF targets open; no REAL or UNPAIRED word |
| unsettled.txt | the 51 functions with an open unnamed target, as settle.py's function list |
| settle.py | the named measurement of every unnamed target jtcheck leaves open (BYTE64, WORDS(n), REL4(n) with the bound by dataflow, CSTRANY with its use check over every path of the function; rules in its docstring); exit 1 on any target not EQUAL |
| settle.out | settle.py's output: one row per target (76: BYTE64 6, REL4 3, CSTRANY 67), all EQUAL |
| control-notable.out | control: settle.py with table matching switched off, on the three jump-table targets: the use check refuses all three, exit 1 |
| luiuse.py | the use trace of every lui-in-section value (every path, stack spills, REL4 jump tables, direct callees): ADDRESS / NUMBER / NUMBER+HAND per row, on both images; rules in its docstring |
| luiuse.out | luiuse.py's output: 74 rows, 0 ADDRESS, 46 NUMBER, 28 NUMBER+HAND, X = Y on every row, each HAND use with its call chain |
| hand.tsv | the reason for each HAND use (syscall number and argument, format conversion, field, return contract) |
| handcheck.py, handcheck.out | every HAND use of luiuse.out and luiuse-luiconst.out has a reason in hand.tsv and every reason is used: 0 failures |
| luiuse_control.py, luiuse_control.out | six planted functions, each with the verdict luiuse must give; all six correct |
| basecalc.py | the full base address of every load / store / AMO / jalr that carries a lui-built value as part of its base, on both images (image addresses named by symbol + offset; run-time pointers with their origin); rules in its docstring; exit 1 on an absolute use, a differing image address, a path join or a site not measured |
| basecalc.out | basecalc.py's output: 204 base sites, 22 IMAGE EQUAL, 182 RUNTIME, nothing else |
| basecalc_control.py, basecalc_control.out | four planted functions, each with the class and full address basecalc must give; all four correct |
| luiconst_rows.py, luiconst-rows.txt | the kit's own lui-const (dataflow) acceptances in closure-memcpy.out, as rows luiuse.py / basecalc.py read (35 targets) |
| luiuse-luiconst.out, basecalc-luiconst.out | luiuse.py and basecalc.py on those rows: 0 ADDRESS; 4 base sites, all RUNTIME |
| REVIEW-86da.md | the fresh reviewer's audit of steps 4 to 7 on cmpkit 86da41d3ef68, with its verdict |
| REVIEW-4bbd.md | the fresh reviewer's audit of the earlier settlement on cmpkit 4bbd3a74be89 (superseded), with the gaps of the C-string use check it records |
| callsites.py | every direct call to a symbol's entry in one image (bytecmp's dataflow through the kit's repin_check targets); names the image by role and sha256 |
| callsites-B.out, callsites-A.out | callsites.py for __asan_memcpy on uci image B's and image A's unstripped twins: the same four harness sites (check_no_overread +0x6c / +0x7c, check_value +0x58, check_clamp +0x114) |
