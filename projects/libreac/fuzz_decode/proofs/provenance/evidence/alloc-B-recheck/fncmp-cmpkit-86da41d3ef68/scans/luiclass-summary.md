rows: {'lui-const': 35, 'lui-const NOT CERTIFIED': 23, 'lui-in-section': 74, 'lui-in-section NOT CERTIFIED': 16}

| kit row | class (the classes of its uses) | rows |
|---|---|---|
| lui-const | (c) | 5 |
| lui-const | (c)+(e) | 2 |
| lui-const | (c)+(e)+(i) | 1 |
| lui-const | (c)+(e)+(iii) | 2 |
| lui-const | (c)+(i) | 1 |
| lui-const | (e)+(ii) | 1 |
| lui-in-section | (c) | 1 |
| lui-in-section | (c)+(e) | 5 |
| lui-in-section | (c)+(e)+(i) | 1 |
| lui-in-section | (c)+(e)+(i)+(i-b)+(iv) | 1 |
| lui-in-section | (c)+(e)+(iii) | 7 |
| lui-in-section | (c)+(e)+(iii)+(iv) | 1 |
| lui-in-section | (e)+(i) | 4 |
| lui-in-section | (e)+(ii) | 5 |
| lui-in-section | (e)+(iii) | 9 |
| lui-in-section | (e)+(iv) | 1 |
| lui-in-section | (i) | 9 |
| lui-in-section | (i-b) | 2 |
| lui-in-section | (ii) | 1 |
| lui-in-section | (iii) | 9 |
| lui-in-section | (iv) | 2 |

| reason (a NOT CERTIFIED row can have several) | rows |
|---|---|
| an indirect call that may read the register (its pointer type unknown) | 31 |
| a follow-up left at the depth limit (4 levels) | 17 |
| a STORE into a field with no citation | 16 |
| a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) | 15 |
| handed back to a function with no direct caller | 11 |
| dead-at-call analysis cut (depth / recursion) | 7 |
| an argument not followed into its callee (a variadic argument) | 5 |
| luitrace verdict REVIEW (a V-derived base, or the two traces differ) | 2 |
| a syscall argument with no contract cited | 2 |
| dead-at-call analysis UNKNOWN (the cause at the end of the callee chain) | 1 |
| a V-derived base in a follow-up only one image has | 1 |

| kit row | member | word | V | unsettled uses (how many of each kind) |
|---|---|---|---|---|
| lui-in-section | 10StackStore5AllocEmPmS1_ | 0x78 | 0x100000 | dead-at-call analysis cut (depth / recursion) (6); an indirect call that may read the register (its pointer type unknown) (2); a follow-up left at the depth limit (4 levels) (1) |
| lui-in-section | 10StackStore5AllocEmPmS1_ | 0x84 | 0xfffff | dead-at-call analysis cut (depth / recursion) (6); an indirect call that may read the register (its pointer type unknown) (2); a follow-up left at the depth limit (4 levels) (1) |
| lui-in-section | 10StackStore9BlockInfo4PackENS0_11CompressionEPS0_ | 0x7c | 0x100000 | an indirect call that may read the register (its pointer type unknown) (4); handed back to a function with no direct caller (4); a STORE into a field with no citation (2); a follow-up left at the depth limit (4 levels) (1) |
| lui-in-section | 11AddrHashMapI25CommonInterceptorMetadataLm31051EE7r | 0x68 | 0xfffff | dead-at-call analysis cut (depth / recursion) (59); handed back to a function with no direct caller (24); an indirect call that may read the register (its pointer type unknown) (9); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (4); an argument not followed into its callee (a variadic argument) (2); a follow-up left at the depth limit (4 levels) (1) |
| lui-in-section | 15internal_usleepEy | 0x14 | 0xf4240 | an indirect call that may read the register (its pointer type unknown) (30); an argument not followed into its callee (a variadic argument) (5); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (2); handed back to a function with no direct caller (2); a follow-up left at the depth limit (4 levels) (1) |
| lui-in-section | 17CombinedAllocatorINS_20SizeClassAllocator32INS_4AP | 0xa8 | 0x40dc0 | an indirect call that may read the register (its pointer type unknown) (2) |
| lui-in-section | 17CombinedAllocatorINS_20SizeClassAllocator32INS_4AP | 0xac | 0x81008 | an indirect call that may read the register (its pointer type unknown) (2) |
| lui-in-section | 18LargeMmapAllocatorINS_20NoOpMapUnmapCallbackENS_32 | 0x24c | 0x40000 | an indirect call that may read the register (its pointer type unknown) (2); handed back to a function with no direct caller (2); a follow-up left at the depth limit (4 levels) (1) |
| lui-in-section | 19ReadLongProcessNameEPcm | 0x40 | 0x100000 | an indirect call that may read the register (its pointer type unknown) (2) |
| lui-in-section | 20SizeClassAllocator32INS_4AP32EE13AllocateBatchEPNS | 0x34 | 0x40040 | an indirect call that may read the register (its pointer type unknown) (94); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (58); an argument not followed into its callee (a variadic argument) (26); a STORE into a field with no citation (4); a follow-up left at the depth limit (4 levels) (1) |
| lui-in-section | 20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddre | 0xb0 | 0x40000 | a STORE into a field with no citation (2); luitrace verdict REVIEW (a V-derived base, or the two traces differ) (1) |
| lui-in-section | L22ReadNullSepFileToArrayEPKcPPPci | 0x54 | 0x100000 | an indirect call that may read the register (its pointer type unknown) (8); a STORE into a field with no citation (2) |
| lui-in-section | 9Allocator10PrintStatsEv | 0xd4 | 0xc8000 | a STORE into a field with no citation (4); an indirect call that may read the register (its pointer type unknown) (4); dead-at-call analysis cut (depth / recursion) (2) |
| lui-in-section | 14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE4find | 0x28 | 0x400008 | an argument not followed into its callee (a variadic argument) (2); a follow-up left at the depth limit (4 levels) (1) |
| lui-in-section | 14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE8GetS | 0x58 | 0xfffff | a STORE into a field with no citation (12); a follow-up left at the depth limit (4 levels) (1) |
| lui-in-section | 14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE8GetS | 0xcc | 0x3ffff | a STORE into a field with no citation (12); a follow-up left at the depth limit (4 levels) (1) |
| lui-const | 10Symbolizer11SymbolizePCEm | 0x1a0 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (38); dead-at-call analysis cut (depth / recursion) (6); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (6); a STORE into a field with no citation (4) |
| lui-const | 10Symbolizer13SymbolizeDataEmPNS_8DataInfoE | 0x1c4 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (12); a STORE into a field with no citation (6) |
| lui-const | 10Symbolizer27GetModuleNameAndOffsetForPCEmPPKcPm | 0x168 | 0xfffff | a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (182); an indirect call that may read the register (its pointer type unknown) (92); handed back to a function with no direct caller (6); a STORE into a field with no citation (6); a syscall argument with no contract cited (3); a follow-up left at the depth limit (4 levels) (1) |
| lui-const | 10Symbolizer8DemangleEPKc | 0x194 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (16); a STORE into a field with no citation (6) |
| lui-const | 11AddrHashMapI25CommonInterceptorMetadataLm31051EE7r | 0x194 | 0xfffff | handed back to a function with no direct caller (10); an indirect call that may read the register (its pointer type unknown) (9); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (2); a follow-up left at the depth limit (4 levels) (1) |
| lui-const | 11AddrHashMapI25CommonInterceptorMetadataLm31051EE7r | 0x244 | 0xfffff | dead-at-call analysis cut (depth / recursion) (119); handed back to a function with no direct caller (26); an argument not followed into its callee (a variadic argument) (2); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (2); a follow-up left at the depth limit (4 levels) (1) |
| lui-const | 14ThreadRegistry11StartThreadEjyNS_10ThreadTypeEPv | 0x1a4 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (4); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (2) |
| lui-const | 14ThreadRegistry12CreateThreadEmbjjPv | 0x21c | 0xfffff | a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (2) |
| lui-const | 17GenericScopedLockINS_5MutexEED2Ev | 0x24 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (4); a STORE into a field with no citation (2) |
| lui-const | 20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddre | 0x1b4 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (23); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (2); a follow-up left at the depth limit (4 levels) (1) |
| lui-const | 20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddre | 0x1d0 | 0xfffff | a follow-up left at the depth limit (4 levels) (1) |
| lui-const | 18AddressDescriptionC1Emmb | 0x244 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (14); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (4); a STORE into a field with no citation (2) |
| lui-const | 19ScopedInErrorReportD2Ev | 0x70 | 0xfffff | dead-at-call analysis cut (depth / recursion) (425); a V-derived base in a follow-up only one image has (116); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (100); an indirect call that may read the register (its pointer type unknown) (23); a STORE into a field with no citation (20); dead-at-call analysis UNKNOWN (the cause at the end of the callee chain) (20); handed back to a function with no direct caller (5); a follow-up left at the depth limit (4 levels) (1) |
| lui-const | 20GetGlobalsForAddressEmP13__asan_globalPji | 0x2a8 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (14); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (6); a STORE into a field with no citation (2) |
| lui-const | __asan_after_dynamic_init | 0x1d4 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (2) |
| lui-const | __asan_before_dynamic_init | 0x250 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (2) |
| lui-const | __asan_describe_address | 0x148 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (2) |
| lui-const | __asan_print_accumulated_stats | 0x178 | 0xfffff | a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (6); an indirect call that may read the register (its pointer type unknown) (6); handed back to a function with no direct caller (2); a STORE into a field with no citation (2) |
| lui-const | __asan_register_globals | 0xb2c | 0xfffff | handed back to a function with no direct caller (2); an indirect call that may read the register (its pointer type unknown) (2) |
| lui-const | __asan_set_error_report_callback | 0x130 | 0xfffff | an indirect call that may read the register (its pointer type unknown) (2) |
| lui-const | __asan_unregister_globals | 0x3fc | 0xfffff | handed back to a function with no direct caller (2); an indirect call that may read the register (its pointer type unknown) (2) |
| lui-const | __lsan_register_root_region | 0x1dc | 0xfffff | an indirect call that may read the register (its pointer type unknown) (33); a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ) (3); a follow-up left at the depth limit (4 levels) (1); luitrace verdict REVIEW (a V-derived base, or the two traces differ) (1) |
| lui-const | fcntl | 0x48 | 0x18060 | a syscall argument with no contract cited (2) |
