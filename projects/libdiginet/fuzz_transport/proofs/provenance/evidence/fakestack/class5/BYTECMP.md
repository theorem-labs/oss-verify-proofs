# fuzz_transport fake-stack class 5: the bodies the donor's walks step through, compared with the donor's

Proves no function (kind: measurement). SUPERSEDED by BYTECMP-cmpkit.md: this record was made with strictcmp
77daee258b95, a comparison version found faulty; the kit of record (cmpkit 4bbd3a74be89) re-run is there.

Donor: plugin-hostd/fuzz_command, origin/ossv/recipes 781f46bc05cd, lib/{A,B}/Rt/RtSM5T.v (`fs_ranges`, the class-5
code table) and lib/{A,B}/Rt/RtSF5.v (`sf_ranges`), closed by RtClosed.cmd_stack_malloc5_contract_closed /
cmd_stack_free5_contract_closed and used at lib/{A,B}/Prog/CmdProgClosed.v r_sm5 / r_sf5.

Tool: strictcmp 77daee258b95 (the tools registry's tools/strictcmp/77daee258b95/strictcmp.py) with its companions
drvcmp.py fbbdb144ddfc, bytecmp-7daa0e2a03d9.py and repin_check-9cbc3553c09e.py beside it. `cmp` by name for the
uniquely named functions; its `tcmp` at the paired addresses for the two ranges whose name has several copies or that
start inside a function (pairing below).

Images (the unstripped twins of the harness.yaml pins; sha256 first 12): fuzz_command.asan 68db792d5fa7,
fuzz_command.asan-ubsan 658cefbe806b; fuzz_transport.asan 108062932420, fuzz_transport.asan-ubsan 815ecd35b970.

## Every range of the two code tables

| range (donor A / B) | words | function | transport A / B | verdict A, B (pcrel, real, unmeasured; target-differ) |
|---|---|---|---|---|
| 0x3ff84 / 0x3ffd0 | 131 | __asan_stack_malloc_5 | 0x3dcfc / 0x3dd40 | EQUAL-mod-pcrel (7, 0, 0; 0), same |
| 0x40190 / 0x401dc | 45 | __asan_stack_free_5 | 0x3df08 / 0x3df4c | EQUAL-mod-pcrel (3, 0, 0; 0), same |
| 0x4b040 / 0x4b08c | 31 | __interceptor___tls_get_addr | 0x47658 / 0x4769c | EQUAL-mod-pcrel (5, 0, 0; 0), same |
| 0x9fbb8 / 0x9f714 | 9 | __tls_get_addr | 0x9de04 / 0x9da7c | EQUAL, EQUAL |
| 0x61e40 / 0x61e8c | 8 | __asan::GetCurrentThread | 0x5cbb8 / 0x5cbfc | EQUAL, EQUAL |
| 0x5a98c / 0x5a9d8 | 6 (of 16) | __asan::AsanTSDGet | 0x55704 / 0x55748 | EQUAL-mod-pcrel (7 / 6, 0, 0; 0) |
| 0xa0c6c / 0xa07c8 | 7 | pthread_getspecific | 0x9eeb8 / 0x9eb30 | EQUAL, EQUAL |
| 0x6f554 / 0x6f5a0 | 140 (of 212) | __sanitizer::DTLS_on_tls_get_addr | 0x6a2cc / 0x6a310 | EQUAL-mod-pcrel (32, 0, 0; 0), same |
| 0x40410 / 0x4045c | 28 | __asan::MemToShadow, the copy both class-5 bodies call | 0x3dfbc / 0x3e000 | EQUAL-mod-pcrel (4, 0, 0; 0), same |
| 0x67b00 / 0x67b4c | 2 | inside __sanitizer::RegisterCommonFlags (+0x358) | +0x358 of 0x62520 / 0x62564 | whole function EQUAL-mod-pcrel (370, 0, 0; 0), same |

Pairing of the MemToShadow copy: the `jal` at word 82 of __asan_stack_malloc_5 and at word 6 of __asan_stack_free_5
targets 0x40410 (donor A) and 0x3dfbc (transport A); 0x4045c and 0x3e000 on B. The other direct callees of the
class-5 body (word 8: the __tls_get_addr trampoline; 16: FakeStack::GC; 50: GetCurrentThread; 127:
AsanThread::AsyncSignalSafeLazyInitFakeStack) name the same symbols on both sides in both images.

Fallback targets strictcmp lists (all equal on both sides): a .got cell holding 0x1 (__asan_stack_malloc_5 +0x1c); a
.rodata 16-byte datum (__asan_stack_free_5 +0x20); assert strings (AsanTSDGet, MemToShadow, DTLS_on_tls_get_addr);
a .got cell holding 0x8 (DTLS_on_tls_get_addr +0x64). Raw output beside this file: strictcmp-cmp-oldpins.out (`cmp` by name)
and strictcmp-tcmp-paired-oldpins.out (`tcmp` at the paired addresses).

Result: every body the class-5 walks step through is the donor's body with only its pc-relative fields re-pointed to
the same symbols, in both images; 0 real differences, 0 unmeasured words, 0 differing targets.
