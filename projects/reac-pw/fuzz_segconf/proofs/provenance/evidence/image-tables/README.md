# Image tables of reac-pw/fuzz_segconf (read from the pinned images)

The contracts of image A (lib/A/Prog/*_c.v) cite these four tables for the numbers they state about the image: call
sites and their arguments, each function's address, size, frame and runtime calls, and the ASan global descriptors.
Each table starts with a comment line naming the image it was read from and how.

| file | read from | sha256 | what it is |
|---|---|---|---|
| `callsites.asan.tsv` | fuzz_segconf.asan, pin sha256 48c5355bdacbc5ba2e0a9ff843627969cb5d2913316654369904b549fc904ef8 (names from its unstripped twin 4362701197e4...) | 704ffff206b5fe92fc9cf27eb4b8ea7e0fe03d0488babaf15d3a2b3132216a4b | every call site of the program's functions: caller, pc, callee, and the a0 / a1 constants where the code sets them |
| `program.asan.tsv` | fuzz_segconf.asan (as above) | ffd66223d752e971854442bc7947d5d6326a47369d16cf41bb263710917ef982 | per program function: address, size, instruction count, ASan report calls and kinds, shadow-index instructions, frame bytes, fake-stack class, program callees, runtime and interceptor callees, abort sites, allocation sites, leaf |
| `program.asan-ubsan.tsv` | fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3... | a820a0b8d5acdb6a10308a7ae5afd3476e3c660f540e3384b4cb484c10e7ac82 | the same per-function table for the ASan + UBSan build |
| `asan_globals.asan.tsv` | fuzz_segconf.asan (as above) | aa9a1b4e1d0b7a7f3faa789e920eb44ff4cd019c03869595a2a8dfca89e136eb | the 88 descriptors of the asan_globals section (0xa7330..0xa8930), with each object's address, size, redzone, name, module and shadow cells |

How they were made: one read-only Python script (pyelftools for the ELF sections and symbols, capstone RISCV64+C for
the disassembly of the pin's .text) run once over the pins and their unstripped twins, writing
`<table>.<image>.tsv` into an output directory: `python3 image_measure.py OUTDIR`. The script is kept byte for byte,
because its own text names the machine paths it read the binaries from, in the unit's internal record: commit
811615904648c11c8fbe72140c0acec195b30f31, path records/image-tables/image_measure.py, sha256
44639d31a95ae7d4a0d2a90c1112d343e3796fd57612a783de8730e5b515894d. (It was run under a working name; the record gives it this role name.)
