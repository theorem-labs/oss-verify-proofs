# fuzz_transport fake-stack class 5: the walked code compared with the donor's, by the comparison kit of record

**SUPERSEDED for the port2 pins** (asan e89be137db17, asan-ubsan 41113a03c82f) by BYTECMP-port2.md (cmpkit 86da41d3ef68). This file stays as the record for the old pins 29ec57e03c5d / 04463dc8ecfe.

Proves no function (kind: measurement). Supersedes BYTECMP.md (made with strictcmp 77daee258b95, a version found faulty).

Kit: cmpkit 4bbd3a74be89 (the tools registry's tools/cmpkit/4bbd3a74be89/; copy in tools/cmpkit-4bbd3a74be89/, its
SHA256SUMS checked by run.sh: 7 files OK, kit id = the first 12 hex of sha256(SHA256SUMS)). strictcmp2 16982e3ef42b is
the one compare; drvcmp 4d70e90bc1fa proves the twins.

Twins (drvcmp.py twins, out/twins-A.txt, out/twins-B.txt): each pinned image and its unstripped twin have the same
PT_LOAD layout and no differing loadable byte outside the ELF header and the build-id note: fuzz_command.asan
c0661b96b5bd / 68db792d5fa7, fuzz_command.asan-ubsan bbe55d24d096 / 658cefbe806b, fuzz_transport.asan 29ec57e03c5d /
108062932420, fuzz_transport.asan-ubsan 04463dc8ecfe / 815ecd35b970.

## Every range of the two code tables (out/class5-A.tsv, out/class5-B.tsv)

Each walked range (the n words the walk steps through) is compared, and the whole function that holds it. A range
passes when its own compare is clean or when its whole function's compare is clean (clean: EQUAL or EQUAL-mod-pcrel,
0 real, 0 unmeasured, 0 differing targets).

| donor range A / B | words | function | transport A / B | range A, B | whole function A, B |
|---|---|---|---|---|---|
| 0x3ff84 / 0x3ffd0 | 131 | __asan_stack_malloc_5 | 0x3dcfc / 0x3dd40 | EQUAL-mod-pcrel (7), same | clean, same |
| 0x67b00 / 0x67b4c | 2 | RegisterCommonFlags + 0x358 | 0x62878 / 0x628bc | EQUAL, EQUAL | 1 differing target at + 0x1218 (a .rodata region compared to the next symbol), outside the 2 walked words |
| 0x4b040 / 0x4b08c | 31 | __interceptor___tls_get_addr | 0x47658 / 0x4769c | EQUAL-mod-pcrel (5), same | clean |
| 0x9fbb8 / 0x9f714 | 9 | __tls_get_addr | 0x9de04 / 0x9da7c | EQUAL | clean |
| 0x61e40 / 0x61e8c | 8 | __asan::GetCurrentThread | 0x5cbb8 / 0x5cbfc | EQUAL | clean |
| 0x5a98c / 0x5a9d8 | 6 | __asan::AsanTSDGet | 0x55704 / 0x55748 | EQUAL-mod-pcrel (3 / 2) | clean |
| 0xa0c6c / 0xa07c8 | 7 | pthread_getspecific | 0x9eeb8 / 0x9eb30 | EQUAL | clean |
| 0x6f554 / 0x6f5a0 | 140 | __sanitizer::DTLS_on_tls_get_addr | 0x6a2cc / 0x6a310 | EQUAL-mod-pcrel (18) | clean |
| 0x40410 / 0x4045c | 28 | __asan::MemToShadow (the copy the class-5 bodies call) | 0x3dfbc / 0x3e000 | 1 unmeasured: the auipc at + 0x6c is consumed after the 28 words | clean |
| 0x40190 / 0x401dc | 45 | __asan_stack_free_5 | 0x3df08 / 0x3df4c | EQUAL-mod-pcrel (3), same | clean |

The by-name compare (strictcmp2.py cmp, strictcmp2-cmp-oldpins.out) covers the nine functions whose name has exactly one
symtab entry in each of the four twins (counted: 1 / 1 / 1 / 1 for __asan_stack_malloc_5, __asan_stack_free_5,
__interceptor___tls_get_addr, __tls_get_addr, GetCurrentThread, AsanTSDGet, pthread_getspecific,
DTLS_on_tls_get_addr, RegisterCommonFlags) and gives the same function verdicts. __asan::MemToShadow has 5 copies in
each twin, so it is not compared by name: class5cmp.py pairs the copy the class-5 bodies call by the call's target
(donor A 0x40410 / transport A 0x3dfbc, B 0x4045c / 0x3e000) and compares it by address (the table above).

## What changed from BYTECMP.md

No verdict on a walked range changed: every range passes, both images. Two whole-function rows differ from the faulty
kit's: RegisterCommonFlags now has 1 differing target at + 0x1218 (strictcmp 77daee258b95 reported 0), outside the 2
words the walk uses; and the MemToShadow range, compared alone, is cut between an auipc and its use (its whole function
is clean). The class-5 resolve lines and the alreloc check are unchanged (out/run.log: A and B PASS, controls hold,
alreloc 0 UNMAPPED, checkrep 0 wrong rows).
