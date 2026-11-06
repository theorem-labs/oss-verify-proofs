| file | cgif B | n | kind | fuzz_uci B | rule | fuzz_uci B source (pin/twin) | = decode B role | = grant B role | = uci A (a9) role |
|---|---|---|---|---|---|---|---|---|---|
| YE23 | 0x130 | 4 | CONST | 0x130 | atexit region size = builtin+280 - finished_atexit (asserted equal in fuzz_uci) | const | yes | yes | yes |
| YE23 | 0x303c8 | 5 | CODE | 0x2fcac | binmatch identical __do_fini+0 (delta 0x71c) | code __do_fini+0 | yes | yes | yes |
| YE23 | 0x6fa80 | 5 | CODE | 0x6e8a8 | binmatch identical __sanitizer_cov_dump+0 (delta 0x11d8) | code __sanitizer_cov_dump+0 | yes | yes | yes |
| YE23 | 0x80448 | 2 | CODE | 0x7f270 | binmatch identical oft_exit_guard+0 (delta 0x11d8) | code oft_exit_guard+0 | yes | yes (driver) | yes |
| YE23 | 0x80cc0 | 5 | CODE | 0x7fd08 | binmatch identical asan.module_dtor+0 (delta 0xfb8) | code asan.module_dtor+0 | yes | yes | yes |
| YE23 | 0x8d714 | 1 | CODE | 0x86ae0 | binmatch identical __funcs_on_exit+128 (delta 0x6c34) | code __funcs_on_exit+128 | yes | yes | yes |
| YE23 | 0x8d75c | 5 | CODE | 0x86b28 | binmatch identical __cxa_finalize+0 (delta 0x6c34) | code __cxa_finalize+0 | yes | yes | yes |
| YE23 | 0x8d824 | 6 | CODE | 0x86bf0 | binmatch identical call+0 (delta 0x6c34) | code call+0 | yes | yes | yes |
| YE23 | 0x8d85c | 1 | CODE | 0x86c28 | binmatch identical libc_exit_fini+48 (delta 0x6c34) | code __libc_exit_fini/libc_exit_fini+48 | yes | yes | yes |
| YE23 | 0x8d878 | 1 | CODE | 0x86c44 | binmatch identical exit+0 (delta 0x6c34) | code exit+0 | yes | yes | yes |
| YE23 | 0x9dc90 | 15 | DATA | 0x96bb0 | data map | data <.fini_array>+0 [.fini_array+0x0] | yes | yes | yes |
| YE23 | 0x9dc98 | 4 | DATA | 0x96bb8 | data map | data __fini+0 [.fini_array+0x8] | yes | yes | yes |
| YE23 | 0x9dca0 | 7 | DATA | 0x96bc0 | data map | data _ZL7preinit+0 [.preinit_array+0x0] | yes | yes | yes |
| YE23 | 0x9e1d8 | 12 | DATA | 0x970f8 | data map | .got slot -> code __cxa_finalize+0 | yes | yes | yes |
| YE23 | 0x9e1e0 | 5 | DATA | 0x97100 | data map | .got slot = 0, after the slot -> code __cxa_finalize+0 | yes | yes | yes |
| YE23 | 0x9e1e8 | 3 | DATA | 0x97108 | data map | .got slot -> code __cxa_finalize+0, +16 (range end) | yes | yes | yes |
| YE23 | 0x9eed8 | 11 | DATA | 0x97de0 | data map | .got slot -> data _ZL7preinit+0 | yes | yes | yes |
| YE23 | 0x9eee0 | 4 | DATA | 0x97de8 | data map | .got slot -> data <.fini_array>+0 | yes | yes | yes |
| YE23 | 0x9eee8 | 3 | DATA | 0x97df0 | data map | .got slot -> data _ZL7preinit+0, +16 (range end) | yes | yes | yes |
| YE23 | 0xa28d0 | 5 | DATA | 0x9b7c0 | data map | data __stderr_used+0 [.data+0x29a0] | yes | yes | yes |
| YE23 | 0xa28d8 | 1 | DATA | 0x9b7c8 | data map | data __stdout_FILE+0 [.data+0x29a8] | yes | yes | yes |
| YE23 | 0xa29c0 | 5 | DATA | 0x9b8b0 | data map | data __stdout_used+0 [.data+0x2a90] | yes | yes | yes |
| YE23 | 0xa29c8 | 2 | DATA | 0x9b8b8 | data map | data __stdin_FILE+0 [.data+0x2a98] | yes | yes | yes |
| YE23 | 0xa2ab0 | 5 | DATA | 0x9b9a0 | data map | data __stdin_used+0 [.data+0x2b80] | yes | yes | yes |
| YE23 | 0xa2ab8 | 1 | DATA | 0x9b9a8 | data map | data __default_stacksize+0 [.data+0x2b88] | yes | yes | yes |
| YE23 | 0xa2bc0 | 1 | DATA | 0x9ba40 | data map | data ___asan_globals_registered+0 [.bss+0x0] | yes | yes | yes |
| YE23 | 0xa2bc8 | 1 | DATA | 0x9ba48 | data map | data __do_init.__initialized+0 [.bss+0x8] | yes | yes | yes |
| YE23 | 0xa2c10 | 1 | DATA | 0x9ba90 | data map | data __do_fini.__finalized+0 [.bss+0x50] | yes | yes | yes |
| YE23 | 0xa3b30 | 1 | DATA | 0x9c9b0 | data map | data _ZN6__asanL14mu_for_globalsE+0 [.bss+0xf70] | yes | yes | yes |
| YE23 | 0xa3b38 | 1 | DATA | 0x9c9b8 | data map | data _ZN6__asanL14mu_for_globalsE+8 [.bss+0xf78] | yes | yes | yes |
| YE23 | 0x5d88d4 | 5 | DATA | 0x5d1754 | data map | data oft_in_callback+0 [.bss+0x535d14] | yes | yes (driver) | yes |
| YE23 | 0x5d88d5 | 1 | DATA | 0x5d1755 | data map | data oft_in_callback+0 [.bss+0x535d14], +1 (range end) | yes | yes (driver) | yes |
| YE23 | 0x5d9210 | 1 | DATA | 0x5d2090 | data map | data builtin_tls+200 [.bss+0x536650] | yes | yes | yes |
| YE23 | 0x5f9260 | 15 | DATA | 0x5f20e0 | data map | data finished_atexit+0 [.bss+0x5566a0] | yes | yes | yes |
| YE23 | 0x5f9264 | 4 | DATA | 0x5f20e4 | data map | data lock+0 [.bss+0x5566a4] | yes | yes | yes |
| YE23 | 0x5f9268 | 4 | DATA | 0x5f20e8 | data map | data slot+0 [.bss+0x5566a8] | yes | yes | yes |
| YE23 | 0x5f9270 | 4 | DATA | 0x5f20f0 | data map | data head+0 [.bss+0x5566b0] | yes | yes | yes |
| YE23 | 0x5f9278 | 8 | DATA | 0x5f20f8 | data map | data builtin+0 [.bss+0x5566b8] | yes | yes | yes |
| YE23 | 0x5f9280 | 4 | DATA | 0x5f2100 | data map | data builtin+8 [.bss+0x5566c0] | yes | yes | yes |
| YE23 | 0x5f9288 | 2 | DATA | 0x5f2108 | data map | data builtin+16 [.bss+0x5566c8] | yes | yes | yes |
| YE23 | 0x5f9380 | 4 | DATA | 0x5f2200 | data map | data builtin+264 [.bss+0x5567c0] | yes | yes | yes |
| YE23 | 0x5f9388 | 2 | DATA | 0x5f2208 | data map | data builtin+272 [.bss+0x5567c8] | yes | yes | yes |
| YE23 | 0x5f9390 | 7 | DATA | 0x5f2210 | data map | data builtin+280 [.bss+0x5567d0] | yes | yes | yes |
| YE23 | 0x5f9480 | 11 | DATA | 0x5f2300 | data map | data exit.exit_lock+0 [.bss+0x5568c0] | yes | yes | yes |
| YE23 | 0x5f9484 | 3 | DATA | 0x5f2304 | data map | data exit.exit_lock+4 [.bss+0x5568c4] | yes | yes | yes |
| YE23 | 0x5f94a3 | 5 | DATA | 0x5f2323 | data map | data __libc+3 [.bss+0x5568e3] | yes | yes | yes |
| YE23 | 0x5f94a4 | 1 | DATA | 0x5f2324 | data map | data __libc+4 [.bss+0x5568e4] | yes | yes | yes |
| YE23 | 0x5f9900 | 11 | DATA | 0x5f2780 | data map | data ofl_lock+0 [.bss+0x556d40] | yes | yes | yes |
| YE23 | 0x5f9908 | 4 | DATA | 0x5f2788 | data map | data ofl_head+0 [.bss+0x556d48] | yes | yes | yes |
| YE23 | 0x5f9910 | 3 | DATA | 0x5f2790 | data map | data buf+0 [.bss+0x556d50] | yes | yes | yes |
| YE23 | 0xffffffff | 8 | CONST | 0xffffffff | FILE.lock sentinel -1 (u32), read from the pin at F_STDIN+140 / F_STDERR+140 | const | yes | yes | yes |
| YE23 | 650920 | 4 | DEC | 622000 | data map (A_GOT_canary) | .got slot -> data __stack_chk_guard+0 | yes | yes | yes |
| YE23 | 665576 | 5 | DEC | 636632 | data map (F_STDERR) | data __stderr_FILE+0 [.data+0x28b8] | yes | yes | yes |
| YE23 | 665816 | 5 | DEC | 636872 | data map (F_STDOUT) | data __stdout_FILE+0 [.data+0x29a8] | yes | yes | yes |
| YE23 | 666056 | 4 | DEC | 637112 | data map (F_STDIN) | data __stdin_FILE+0 [.data+0x2a98] | yes | yes | yes |
| YE23 | 6132240 | 4 | DEC | 6103184 | data map (TFIB_TPX) | data builtin_tls+200 [.bss+0x536650] | yes | yes | yes |
| YE23 | 6263376 | 4 | DEC | 6234320 | data map (A_canary) | data __stack_chk_guard+0 [.bss+0x556690] | yes | yes | yes |
| YE23 | 6265120 | 14 | DEC | 6236064 | data map (STDOUT_BUFA) | data buf+8 [.bss+0x556d60] | yes | yes | yes |
| YD1y | 0x10000 | 2 | SEG | 0x10000 | page-rounded PT_LOAD hull point 0 | hull point 0 | yes | yes | yes |
| YD1y | 0x30000 | 1 | SEG | 0x2f000 | page-rounded PT_LOAD hull point 1 | hull point 1 | yes | yes | yes |
| YD1y | 0x9d000 | 4 | SEG | 0x96000 | page-rounded PT_LOAD hull point 2 | hull point 2 | yes | yes | yes |
| YD1y | 0x9f000 | 2 | SEG | 0x98000 | page-rounded PT_LOAD hull point 3 | hull point 3 | yes | yes | yes |
| YD1y | 0xa27a0 | 3 | DRV | 0x9b690 | data map | data oft_arg0+0 [.data+0x2870] | yes | yes (driver) | yes |
| YD1y | 0xa2ae0 | 2 | DRV | 0x9b9d0 | data map | data <asan_globals>+0 [asan_globals+0x0] | yes | yes | yes |
| YD1y | 0xa2bc8 | 2 | DRV | 0x9ba48 | data map | data __do_init.__initialized+0 [.bss+0x8] | yes | yes | yes |
| YD1y | 0xa2c10 | 2 | DRV | 0x9ba90 | data map | data __do_fini.__finalized+0 [.bss+0x50] | yes | yes | yes |
| YD1y | 0x5d88d0 | 2 | DRV | 0x5d1750 | data map | data target_run.initialized+0 [.bss+0x535d10] | yes | yes (driver) | yes |
| YD1y | 0x5d91b8 | 2 | DRV | 0x5d2038 | data map | data builtin_tls+112 [.bss+0x5365f8] | yes | yes | yes |
| YD1y | 0x5f9260 | 2 | DRV | 0x5f20e0 | data map | data finished_atexit+0 [.bss+0x5566a0] | yes | yes | yes |
| YD1y | 0x5f9480 | 2 | DRV | 0x5f2300 | data map | data exit.exit_lock+0 [.bss+0x5568c0] | yes | yes | yes |
| YD1y | 0x5fb000 | 8 | SEG | 0x5f4000 | page-rounded PT_LOAD hull point 4 | hull point 4 | yes | yes | yes |
| YD1y | 65536 | 9 | CONST | 65536 | stack window size 64 KiB (sp0 - 65536 / - 65536), image-independent | const | yes | yes | yes |
| YD1y | 4194303 | 2 | CONST | 4194303 | tid upper bound 2^22-1 (mkAF 1 4194303 0), not an address | const | yes | yes | yes |

XW2 shadow line (YE23, generated):

- cgif B:     `(0x7fffc1b8 <= a < 0x7fffc1bc) \/ (0x7fffc1c4 <= a < 0x7fffc1c8) \/ (0x7fffc1cc <= a < 0x7fffc1d0) \/ (0x8000c55c <= a < 0x8000c574).`
- fuzz_uci B: `(0x7fffc194 <= a < 0x7fffc198) \/ (0x8000b73a <= a < 0x8000b742).`

| cgif B | fuzz_uci B | rule (fuzz_uci B source) |
|---|---|---|
| 0x7fffc1b8 | 0x7fffc194 | shadow(global 0 beg 0x20ca0) |
| 0x7fffc1bc | 0x7fffc198 | shadow(global 0 beg + size_with_redzone 0x20) |
| 0x7fffc1c4 | (removed) | cgif global 1: fuzz_uci B has 1 global(s) |
| 0x7fffc1c8 | (removed) | cgif global 1 end |
| 0x7fffc1cc | (removed) | cgif global 2: fuzz_uci B has 1 global(s) |
| 0x7fffc1d0 | (removed) | cgif global 2 end |
| 0x8000c55c | 0x8000b73a | shadow(asan_globals 0x9b9d0) |
| 0x8000c574 | 0x8000b742 | shadow(asan_globals + 64 x 1) |

YE37 (x2 ranges):

| file | cgif B | kind | fuzz_uci B | source |
|---|---|---|---|---|
| YE37 | 0xafffff00000fffff | CONST | 0xafffff00000fffff | row 0x103a0 +0: image constant, uci pin at 0x103a0 = 0xafffff00000fffff |
| YE37 | 0x103a0 | ROW | 0x103a0 | data map; data <.rodata>+192 [.rodata+0xc0] |
| YE37 | 0x135d20 | PTR | 0x12eba0 | row 0x97108 +0: uci pin at 0x97108+0 = 0x12eba0; rule data map -> 0x12eba0 |
| YE37 | 0xa00d0 | PTR | 0x98fc0 | row 0x97108 +8: uci pin at 0x97108+8 = 0x98fc0; rule data map -> 0x98fc0 |
| YE37 | 0x137da8 | PTR | 0x130c28 | row 0x97108 +16: uci pin at 0x97108+16 = 0x130c28; rule data map -> 0x130c28 |
| YE37 | 0xa3a78 | PTR | 0x9c8f8 | row 0x97108 +24: uci pin at 0x97108+24 = 0x9c8f8; rule data map -> 0x9c8f8 |
| YE37 | 0xa6278 | PTR | 0x9f0f8 | row 0x97108 +32: uci pin at 0x97108+32 = 0x9f0f8; rule data map -> 0x9f0f8 |
| YE37 | 0xa6f68 | PTR | 0x9fde8 | row 0x97108 +40: uci pin at 0x97108+40 = 0x9fde8; rule data map -> 0x9fde8 |
| YE37 | 0xa6f70 | PTR | 0x9fdf0 | row 0x97108 +48: uci pin at 0x97108+48 = 0x9fdf0; rule data map -> 0x9fdf0 |
| YE37 | 0xa6f60 | PTR | 0x9fde0 | row 0x97108 +56: uci pin at 0x97108+56 = 0x9fde0; rule data map -> 0x9fde0 |
| YE37 | 0xa0098 | PTR | 0x98f88 | row 0x97108 +64: uci pin at 0x97108+64 = 0x98f88; rule data map -> 0x98f88 |
| YE37 | 0x9e1e8 | ROW | 0x97108 | data map; .got slot -> data _ZN11__sanitizer14PageSizeCachedE+0 |
| YE37 | 0xa2ae0 | PTR | 0x9b9d0 | row 0x97da0 +0: uci pin at 0x97da0+0 = 0x9b9d0; rule section asan_globals start -> 0x9b9d0 |
| YE37 | 0xa2ba0 | PTR | 0x9ba10 | row 0x97da0 +8: uci pin at 0x97da0+8 = 0x9ba10; rule section asan_globals end -> 0x9ba10 |
| YE37 | 0x9ee98 | ROW | 0x97da0 | data map; .got slot -> data <asan_globals>+0 |
| YE37 | 0x9790c | PTR | 0x9085c | row 0x98f88 +0: uci pin at 0x98f88+0 = 0x9085c; rule binmatch memset+0 -> 0x9085c |
| YE37 | 0xa0098 | ROW | 0x98f88 | data map; data _ZN14__interception11real_memsetE+0 [.data+0x168] |
| YE37 | 0xa2ae0 | GDESC | 0x20ca0 | fuzz_uci asan_globals 0x9b9d0 descriptor 0 +0 (beg), read from the pin |
| YE37 | 0xa2ae8 | GDESC | 0x8 | fuzz_uci asan_globals 0x9b9d0 descriptor 0 +8 (size), read from the pin |
| YE37 | 0xa2af0 | GDESC | 0x20 | fuzz_uci asan_globals 0x9b9d0 descriptor 0 +16 (swr), read from the pin |
| YE37 | - (not in cgif's text) | GDESC | 0x1c8af | fuzz_uci asan_globals 0x9b9d0 descriptor 0 +24 (name), read from the pin |
| YE37 | 0xa2b00 | GDESC | 0x20cc0 | fuzz_uci asan_globals 0x9b9d0 descriptor 0 +32 (mod), read from the pin |
| YE37 | 0xa2b08 | GDESC | 0x0 | fuzz_uci asan_globals 0x9b9d0 descriptor 0 +40 (dyn), read from the pin |
| YE37 | 0xa2b10 | GDESC | 0x0 | fuzz_uci asan_globals 0x9b9d0 descriptor 0 +48 (loc), read from the pin |
| YE37 | 0xa2b18 | GDESC | 0xffffffffffffffff | fuzz_uci asan_globals 0x9b9d0 descriptor 0 +56 (odr), read from the pin |
| YE37 | 0xa2ae0 | ROW | 0x9b9d0 | section asan_globals start (row size 64 x 1 = 64) |
| YE37 | 0x101010000000001 | CONST | 0x101010000000001 | row 0x9c910 +0: start-up value of a zero-fill (.bss) cell, kept (Tfib_const cell; gate below) |
| YE37 | 0xa3a90 | ROW | 0x9c910 | data map; data _ZN6__asan28asan_flags_dont_use_directlyE+24 [.bss+0xed0] |
| YE37 | 0x1000100000000 | CONST | 0x1000100000000 | row 0x9c940 +0: start-up value of a zero-fill (.bss) cell, kept (Tfib_const cell; gate below) |
| YE37 | 0xa3ac0 | ROW | 0x9c940 | data map; data _ZN6__asan28asan_flags_dont_use_directlyE+72 [.bss+0xf00] |
| YE37 | 0x1 | CONST | 0x1 | row 0x9e95c +0: start-up value of a zero-fill (.bss) cell, kept (Tfib_const cell; gate below) |
| YE37 | 0xa5adc | ROW | 0x9e95c | data map; data _ZN6__asanL17can_poison_memoryE+0 [.bss+0x2f1c] |
| YE37 | 0x7fff8000 | CONST | 0x7fff8000 | row 0x9f0f8 +0: start-up value of a zero-fill (.bss) cell, kept (Tfib_const cell; gate below) |
| YE37 | 0xa6278 | ROW | 0x9f0f8 | data map; data __asan_shadow_memory_dynamic_address+0 [.bss+0x36b8] |
| YE37 | 0x1 | CONST | 0x1 | row 0x9fdd8 +0: start-up value of a zero-fill (.bss) cell, kept (Tfib_const cell; gate below) |
| YE37 | 0xa6f58 | ROW | 0x9fdd8 | data map; data _ZN6__asanL11asan_initedE+0 [.bss+0x4398] |
| YE37 | 0x7fffffffffff | CONST | 0x7fffffffffff | row 0x9fde0 +0: start-up value of a zero-fill (.bss) cell, kept (Tfib_const cell; gate below) |
| YE37 | 0x0 | CONST | 0x0 | row 0x9fde0 +8: start-up value of a zero-fill (.bss) cell, kept (Tfib_const cell; gate below) |
| YE37 | 0x0 | CONST | 0x0 | row 0x9fde0 +16: start-up value of a zero-fill (.bss) cell, kept (Tfib_const cell; gate below) |
| YE37 | 0xa6f60 | ROW | 0x9fde0 | data map; data _ZN6__asan11kHighMemEndE+0 [.bss+0x43a0] |
| YE37 | 0x1000 | CONST | 0x1000 | row 0x12eba0 +0: start-up value of a zero-fill (.bss) cell, kept (Tfib_const cell; gate below) |
| YE37 | 0x135d20 | ROW | 0x12eba0 | data map; data _ZN11__sanitizer14PageSizeCachedE+0 [.bss+0x93160] |
| YE37 | 0xffffffffffffffff | CONST | 0xffffffffffffffff | row 0x130ca0 +0: start-up value of a zero-fill (.bss) cell, kept (Tfib_const cell; gate below) |
| YE37 | 0x137e20 | ROW | 0x130ca0 | data map; data _ZN11__sanitizer21common_flags_dont_useE+120 [.bss+0x95260] |
| YE37 | 0x7fffc1b8 | SHW | 0x7fffc194 | shadow window (shadow(beg), size_with_redzone/8 = 4) of fuzz_uci global 0, generated from the pin's asan_globals |
| YE37 | 0x7fffc1c4 | SHW | (removed) | cgif global 1 window: fuzz_uci B has 1 global(s) |
| YE37 | 0x7fffc1cc | SHW | (removed) | cgif global 2 window: fuzz_uci B has 1 global(s) |
| YE37 | 0x8000c55c | SHW | 0x8000b73a | shadow window (shadow(asan_globals), 64 x 1 / 8 = 8) of the descriptor array |
| YE37 | Hr lo | HR | 0x7fffc194 | min lo of x2_shw (decode: 0x7fffc1ac) |
| YE37 | Hr hi | HR | 0x8000b742 | max lo+n of x2_shw (decode: 0x8000bb8e) |
| YE37 | 0xa2bc0 | CELLR | 0x9ba40 | data map; data ___asan_globals_registered+0 [.bss+0x0]; value 1 kept |
| YE37 | 0xa3b30 | CELLR | 0x9c9b0 | data map; data _ZN6__asanL14mu_for_globalsE+0 [.bss+0xf70]; value 0 kept |
