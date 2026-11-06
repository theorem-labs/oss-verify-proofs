# The whole tfib table of the libdiginet/fuzz_transport image-A core, read against the unstripped twin

proves no function (kind: measurement). Every `Definition tfib_(A|D|E)_<name> : Z := <numeral>.` of lib/A and
lib/Reusable (1201 cells, all in lib/A/AB1w.v and lib/A/AE3a.v; lib/Reusable has none) read against the twin
`unstripped/fuzz_transport.asan` (sha256 86efc3a80314), C++ names demangled with the C++ runtime's `__cxa_demangle`.
An _A or _D cell is read as the symbols STARTING at its value, an _E cell as the symbols ENDING there
(st_value + st_size = the value), else, for a size-0 assembly symbol, the next symbol's start.

**Result: 1201 cells = OK-EXACT 800 + OK-ALIAS 119 + OK-REGION 2 + NO-SYMBOL 114 + WRONG 160 + FALSE 6. WRONG or FALSE
cells that a file reads: 0. Removed: the 160 WRONG cells (80 _A / _E pairs) in one commit, then the 6 FALSE cells
(3 pairs) in a second.** The table is records/tfib-whole-table.tsv, one row per cell, written on the lib before both
removals, so every removed cell is in it with its reading.

**The function-label rule (FALSE, the integration owner's decision of 2026-10-31 11:55Z, with its correction of
12:07Z) removes a cell whose label is spelled as a function that is not at its value under any name or alias; an
interceptor or wrapper alias of the named function at the value (`__interceptor_trampoline_f`, `__wrap_f`,
`___interceptor_f`) is correct and stays, and the two region-bracket cells `tfib_E_start` and `tfib_E_target_run` are
OK-REGION by the bracket convention, to which the function-label test does not apply (section "The FALSE test").**

## The test for WRONG (the integration owner's decision of 2026-10-31), applied per cell

A cell is WRONG when its label NAMES a function that the twin's symbol table has at ANOTHER address (**T1**), or names
a source function the compiler inlined, so the twin has no symbol for it, other than the function at the cell's value
(**T2**) — and the label does not ALSO name the function at its value (an `X_body` or `X_CHECK_helper` cell on `X`
stays). A label that only describes code, or names a class and no function, stays NO-SYMBOL and is kept. Image B
applies the same test to lib/B (TFIB-TABLE-B.tsv, sha256 6ff7ed2cc9e2; internal record).

Of the 80 removed pairs, 60 fire T1 (120 cells) and 20 fire T2 (40 cells). Every one of the 160 carries the donor's own
value (donor pairing `same` for 160 of 160, against fuzz_grant's twin 57c26f993615): they are the released donor's
mislabels, inherited by the port, not a fault of the relocation.

## The classes

- **OK-EXACT (800)**: the cell's name is the symbol's own name in the donor's naming (namespaces dropped, `::` -> `_`,
  templates and parameters dropped; the raw name without leading `_`; the donor's `musl_` tag for libc), alone or with
  a descriptive `_...` tail. 18 of the 27 _D cells are of this class: the object at the value, a GOT slot holding its
  address, or a `REAL_<f>` cell at `__interception::real_<f>`.
- **OK-ALIAS (119 = 61 _A / _D cells and 58 _E partners)**: the symbol at the value is an alias of the named function:
  the 4-byte `__interceptor_trampoline_<f>` = `__wrap_<f>`, where the program's calls to `<f>` land (28 pairs: the 25
  cells the named-symbol addendum read, records/PAC-NAMEDIFF.md, and free, malloc, `__tls_get_addr`); the interceptor
  `__interceptor_<f>` of an `icpt_<f>` cell (28 pairs); a libc-internal name (`__libc_calloc` for calloc,
  `__malloc_alloc_meta` for alloc_meta); or a GOT slot holding the object an accessor returns (`common_flags()`,
  `__asan::flags()`), and the `__asan::flags()` object itself.
- **OK-REGION (2)**: a region bracket of the donor's convention, kept (see "The two _E region brackets" below).
- **NO-SYMBOL (114)**: a descriptive label that names NO function of the twin, or one that also names the function at
  its value: a thunk named by its donor address (`thunk_417bc` on `__interceptor_trampoline_snprintf`), a stub
  (`internal_pthread_weak_stub_ret` on `Atexit`), a label that also names the function at its value
  (`Allocator_QuarantineChunk_tail_quarantine_Put` on `Quarantine::Put`, `sigaction_libc_sigaction` on
  `__libc_sigaction`, `MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve` on `MmapFixedNoReserve`,
  `musl_sigaction_abort_area_fn_rt_sigaction_tkill` on `abort`), a label that names classes only
  (`ThreadRegistry_ThreadArgRetval_vector_growth` on `InternalMmapVectorNoCtor<ThreadContextBase*>::Realloc`,
  `SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe` on that class's `PackedCounterArray` constructor), or a data
  label (6 _D cells: `<sealed>` in .rodata, the .init_array / .fini_array starts, the environ GOT slot, the two
  AE3a.v constants 0x8080808080808080 and 0x0101010101010100). An `X_CHECK_helper` or `X_body` cell whose head IS the
  function at the value (`AsanDeactivate_activation_CHECK_helper` on `AsanDeactivate`) is OK-EXACT: the name with a
  descriptive tail. All of these are kept.
- **WRONG (160 = 80 pairs)**: by the test above; each row of the table names the function the label names, where that
  function really is, and the function at the cell's value.
- **FALSE (6 = 3 pairs)**: by the function-label test (section "The FALSE test"); each row gives the function the label
  is spelled as and the function at the cell's value.

## Reading lines

`git grep -now 'tfib_[ADE]_<word>'` over lib (every hit except the cell's own Definition): 7 cells of the 1201 are read
by another line, none of them WRONG or FALSE — `tfib_A_musl_memcpy` (281), `tfib_A_musl_memset` (87), `tfib_A_musl_memchr` (79),
`tfib_A_musl_memcmp` (18), `tfib_A_musl_strnlen` (6), all OK-EXACT on musl's own functions, and the two AE3a.v
constants `tfib_D_const_HIGHS_0x8080808080808080` and `tfib_D_const_ONES_0x0101010101010100` (11 each, NO-SYMBOL: the
bytes at the value are the constant the name states). The other 1194 cells are named nowhere else in lib.

## What was removed

The 160 WRONG cells, all with 0 readers, as 80 whole lines of lib/A/AB1w.v (each line held one _A / _E pair and
nothing else). Counts, `grep -oE 'Definition tfib_[ADE]_[A-Za-z0-9_]+'`: lib before 1201, after 1041; AB1w.v before
1199, after 1039. After the removal `git grep -nw` for each of the 160 names over lib gives 0 hits.

Groups (each label named against the function at its value):

| group | pairs |
|---|---|
| swapped with each other (T1) | asan_register_globals / asan_unregister_globals (on `__asan_(un)register_elf_globals`; the named ones are at 0x3f838 / 0x40654), AsanCheckIncompatibleRT / AsanCheckDynamicRTPrereqs, AsanThread_SetThreadStackAndTls / AsanThread_ClearShadowForThreadStackAndTLS, sanitizer_free_hook_weak_default / sanitizer_ignore_free_hook_weak_default_ret_0 |
| rotated one place (T1 / T2) | internal_strcmp / internal_strncmp / internal_strchr, QuarantineCache_MergeBatches_Transfer / QuarantineCache_DequeueBatch, StackDepotBase_find_bucket_chain_walk / StackDepotBase_lock_bucket_spin_lock |
| the named function is elsewhere in the twin (T1, the rest) | SizeClassAllocator64_ReturnToAllocator_helper, memcmp_2, vfprintf_2, icpt_vfprintf_2, DlsymAlloc_PointerIsMine_internal_allocator_From, HeapProfile_Insert_asan_memory_profile, asan_poison_stack_memory_PoisonAlignedStackMemor, asan_unpoison_stack_memory, ScopedInErrorReport_ReportError_helper, AsanInitFromRtl_ENSURE_ASAN_INITED, asan_handle_no_return_tiny_rtl_stub_2_insns, IsStackTraceSuppressed, InternalAlloc_RawInternalAlloc, InternalFree_LowLevelAllocator_free_to_freelist, internal_allocator_getter, LowLevelAllocator_InternalAlloc_bump_allocator, AllocatorMayReturnNull, IncreaseTotalMmap (on `DecreaseTotalMmap`), ReportFile_SetReportPath, FlagParser_ParseString_parse_flags, FlagParser_PrintFlagDescriptions_gate_Verbosity, LargeMmapAllocator_EnsureSortedChunks, GetNamedMappingFd_ReadProcess_openat_getdents64, internal_sigaction_syscall_wrapper_selector, MmapFixedNoAccess_3_insn_arg_shim_0x65c98, MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co, MmapFixedNoReserve, MprotectNoAccess, MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser, MmapFixedOrDie, ReserveShadowMemoryRanges_sealed_early_shadow_re, DTLS_Destroy_ForEachDVT_no_op_4_insns, sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a, ThreadContextBase_ctor_ThreadRegistry_init_helpe, GetThreadStackAndTls, GetThreadStackTopAndBottom_caller_ClearShadowFor, Atexit_internal_exit_hook_runner_12_insns_execut, asan_malloc_hook_RunMallocHooks_target_sanitizer, Unwind_GetIP_slow_unwind_helper, libc_exit_fini_array_walker_stub, fini_stub_ret (names `_fini`, which is at 0x939a8; on `__cxa_finalize`), musl_exit_helper_stub (names `exit` 0x939f8; on `_fini` = `dummy`), lock_unlock_pair_user_futex (names `__lock` 0x9dae0 / `__unlock` 0x9dd68; on `pthread_rwlock_unlock`), fprintf (on `dprintf`), syscall_cp_c_tail_sccp_9_insns, pthread_key_create_body_tsd_init |
| the named function is inlined, no symbol in the twin (T2, the rest) | Allocator_SharedInitCode, Allocator_ComputeRZLog, AsanChunkView_GetAsanChunk_ptr_helper, RoundUpTo_size_CHECK_helper_sanitizer_common_h_C, StackDepotBase_Get, FakeStack_Allocate, FakeStack_SetShadow, asan_globals_RegisterGlobal_vector_push_back, icpt_cfree_or_DlsymFree, InitializeCommonInterceptors, InitializeSignalInterceptors_or_syscall_hooks, AsanStats_Clear_ctor, OverrideCommonFlags_no_op_flag_hook_2_insns, GetPageSizeCached, InternalAllocatorLock_Unlock_or_stats_add_17_ins, InternalMmapVector_push_back, MaybeStartBackgroudThread, ubsan_MaybeCallUbsanDefaultOptions, pthread_key_atfork_tsd_table_init_11_insns |

## The FALSE test (the function-label rule), applied per cell after the WRONG removal

The integration owner's decision of 2026-10-31 11:55Z, with its correction of 12:07Z: a cell is FALSE when (1) its
label is spelled as a FUNCTION (a C / C++ function name, `Class_Method`, `ns_Func`), (2) the image has NO symbol of
that name at the cell's value under any name or alias (every symbol, local and global, demangled, so
`__sanitizer::GetPageSizeCached()` matches `GetPageSizeCached`; an interceptor or wrapper alias of f at the value,
`__interceptor_trampoline_f`, `__wrap_f` or `___interceptor_f`, is f there and the cell stays), and (3) the value starts
(_A) / ends (_E) a DIFFERENT function. Thunk labels (`thunk_<hex>`) and plain descriptions (`_helper`, `_stub_ret`,
`_3_insns`, `_or_` ...) claim no symbol and stay. The two region-bracket cells are OK-REGION by the bracket convention
(section "The two _E region brackets, kept"): read literally, (1)-(3) hold for `tfib_E_target_run` (it ends
`oft_exit_guard`) and `tfib_E_start` (it ends `_start_c`), but the function-label test does not apply to a bracket cell,
whose _E value ends the next function by that convention (the integration owner's instruction of 2026-10-31 08:40Z).

Read on the 1041 cells left after the WRONG removal (507 _A / _E pairs and 27 _D cells; a _D value is data, never a
function's start or end, so (3) cannot hold for it), all classes, not only NO-SYMBOL. tfibtable-A.py's FALSE SCREEN
lists every pair whose label is no name of a symbol at its value (alias forms included) and has no `_`-aligned part
that is one: **41 pairs**, each decided by hand:

- **FALSE, 3 pairs (6 cells), 0 reading lines, removed**: `DieOnMapFailure_sealed` (0x3510c / 0x35144) on
  `__sanitizer::SealedHangOnAllocationFailure`; `SealedTopOfMemory_check` (0x5a6c4 / 0x5a728) on
  `__asan::CheckSealedAddressSpace`; `SetSealedStartFrame_sealed_patch` (0x6077c / 0x60788) on
  `__sanitizer::SealedSetInitFrame`. Each value holds exactly one symbol, a local function of another name, and no
  interceptor or wrapper alias; none of DieOnMapFailure, SealedTopOfMemory or SetSealedStartFrame is a symbol anywhere
  in the twin. Each is the donor's label (donor pairing `same`, the same function in fuzz_grant's twin).
- **thunk labels, 19 pairs, kept**: `thunk_417bc` ... `thunk_96f9c` (each named by a donor address).
- **plain descriptions, 13 pairs, kept**: `asan_activation_flag_parse_helper_0_no`,
  `asan_linux_PlatformShadowSetup_helper_CheckForEx`, `internal_errno_mapping_helper`, `lsan_flags_init_helper`,
  `asan_suppression_kinds_getter_3_insns`, `asan_thread_tiny_getter_3_insns`, `internal_pthread_weak_stub_ret`,
  `weak_default_hook_ret` / `_2` / `_3`, `icpt_diouxXn` (the printf conversion letters, no function),
  `ThreadRegistry_ThreadArgRetval_vector_growth` (classes and "vector growth" on that vector's `Realloc`),
  `MmapFixed_named_may_die_core_MmapNamed_IncreaseT` ("the named, may-die core of MmapFixed" on `MmapFixedImpl`, with
  its callees MmapNamed and IncreaseTotalMmap).
- **labels that name the function at the value in a shortened form, 6 pairs, kept**:
  `SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe` (the `PackedCounterArray` constructor, its name cut by the 48-
  character label limit), `SetShadowRegionHugePageMode_DontDumpShadow_madvi` (`DontDumpShadow[Memory]`),
  `internal_exit_exit_group` (`internal__exit`, its double underscore written once), `icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m`
  (the bcmp entry: `__interceptor_bcmp`), `lsan_ubsan_default_options_weak_stub` (`__lsan_default_options`),
  `sanitizer_common_libcdep_static_ctor_background` (the static constructor of sanitizer_common_libcdep.cpp,
  `_GLOBAL__sub_I_sanitizer_common_libcdep.cpp`).

The OK classes pass as a check: every OK-EXACT and OK-ALIAS pair names the symbol (or its alias) at its value, and no
other _E cell than the two brackets and two thunks ends a function other than its _A partner's (`tfib_E_set_thread_area`
0x9f844 is the next symbol's start after the size-0 `__set_thread_area`; no function ends there).

Removed: the 6 FALSE cells as 3 whole lines of lib/A/AB1w.v. `git grep -nw` of the 6 names over lib: 3 lines before (the
Definitions), 0 after. Counts, `grep -oE 'Definition tfib_[ADE]_[A-Za-z0-9_]+'`: lib before 1041, after 1035; AB1w.v
before 1039, after 1033. Run on the tree of that removal, the table has the same rows less the 166 removed cells
(measured: 1035 rows, every kept cell's class unchanged, WRONG 0, FALSE 0; the screen then lists the 38 kept pairs).

## All 83 removed pairs, each with its class and the function at its value

Re-checked under the 12:07Z alias correction on the demangled symbol table (an _A value read as the symbols starting
there, an _E value as the symbols ending there): **0 of the 83 pairs holds an interceptor or wrapper alias
(`__interceptor_trampoline_f`, `__wrap_f`, `___interceptor_f`) of its label's own function f; 0 restored.** Three values
hold an alias of ANOTHER function: `memcmp_2` holds the bcmp trampoline, `vfprintf_2` the fprintf trampoline,
`icpt_vfprintf_2` the fprintf interceptor. The aliases of those labels' own functions are held by kept cells, all
OK-ALIAS: `tfib_A_memcmp` 0x42cf4 (`__interceptor_trampoline_memcmp`), `tfib_A_vfprintf` 0x42d18
(`__interceptor_trampoline_vfprintf`), `tfib_A_icpt_vfprintf` 0x46134 (`__interceptor_vfprintf`). After the removal no
_A / _E pair covers fprintf's own trampoline [0x42d20, 0x42d24) or interceptor [0x46500, 0x465d8): the pairs on them
carried other functions' labels and no line read them; 0x42d20 and 0x46500 stay only as the _E ends of the kept
vsnprintf pairs (`tfib_E_vsnprintf`, `tfib_E_icpt_vsnprintf`).

In lib/A/AB1w.v order (the line before the removals). The test is T1 / T2 (WRONG) or FALSE; "named" is the function the
label names, with where it really is in brackets; "at the value" is the function the _A value starts (and, where it
differs, the one the _E value ends; `a = b` lists aliases at one address). Every pair is the donor's label (donor pairing
`same`) and has 0 reading lines.

| line | label | class (test) | _A / _E | named [where] | at the value |
|---:|---|---|---|---|---|
| 35 | `AsanChunkView_GetAsanChunk_ptr_helper` | WRONG (T2) | 0x333d4 / 0x33518 | __asan::Allocator::GetAsanChunk [inlined: no symbol in the image] | __asan::Allocator::GetAsanChunkByAddr |
| 39 | `Allocator_SharedInitCode` | WRONG (T2) | 0x339a4 / 0x33a8c | __asan::Allocator::SharedInitCode [inlined: no symbol in the image] | __asan::Allocator::CheckOptions |
| 40 | `QuarantineCache_MergeBatches_Transfer` | WRONG (T1) | 0x33ec0 / 0x340a4 | __sanitizer::QuarantineCache::MergeBatches [0x340a4] | __sanitizer::Quarantine::Recycle |
| 41 | `QuarantineCache_DequeueBatch` | WRONG (T2) | 0x340a4 / 0x34228 | __sanitizer::QuarantineCache::DequeueBatch [inlined: no symbol in the image] | __sanitizer::QuarantineCache::MergeBatches |
| 46 | `SizeClassAllocator64_ReturnToAllocator_helper` | WRONG (T1) | 0x34af8 / 0x34b98 | __sanitizer::SizeClassAllocator64::ReturnToAllocator [0x34c9c] | __sanitizer::SizeClassAllocator64LocalCache::DrainHalfMax |
| 49 | `DieOnMapFailure_sealed` | FALSE (FALSE) | 0x3510c / 0x35144 | DieOnMapFailure [no symbol of that name in the twin, local or global] | __sanitizer::SealedHangOnAllocationFailure |
| 59 | `Allocator_ComputeRZLog` | WRONG (T2) | 0x37670 / 0x37788 | __asan::Allocator::ComputeRZLog [inlined: no symbol in the image] | __asan::RZSize2Log |
| 60 | `LargeMmapAllocator_EnsureSortedChunks` | WRONG (T1) | 0x37a90 / 0x37b8c | __sanitizer::LargeMmapAllocator::EnsureSortedChunks [0x37938] | __sanitizer::LargeMmapAllocator::ForEachChunk |
| 66 | `FakeStack_Allocate` | WRONG (T2) | 0x3d24c / 0x3d534 | __asan::FakeStack::Allocate [inlined: no symbol in the image] | __asan::FakeStack::GC |
| 72 | `FakeStack_SetShadow` | WRONG (T2) | 0x3dfc4 / 0x3e100 | __asan::FakeStack::SetShadow [inlined: no symbol in the image] | __asan::MemToShadow |
| 76 | `asan_register_globals` | WRONG (T1) | 0x40c20 / 0x40c8c | __asan_register_globals [0x3f838] | __asan_register_elf_globals |
| 77 | `asan_unregister_globals` | WRONG (T1) | 0x40c8c / 0x40cf4 | __asan_unregister_globals [0x40654] | __asan_unregister_elf_globals |
| 80 | `RoundUpTo_size_CHECK_helper_sanitizer_common_h_C` | WRONG (T2) | 0x42060 / 0x421b0 | __sanitizer::RoundUpTo [inlined: no symbol in the image] | __sanitizer::RoundUpToPowerOfTwo |
| 81 | `asan_globals_RegisterGlobal_vector_push_back` | WRONG (T2) | 0x42bcc / 0x42ce4 | __asan::RegisterGlobal / InternalMmapVector::push_back [inlined: no symbol in the image] | __sanitizer::InternalMmapVectorNoCtor::Realloc |
| 87 | `memcmp_2` | WRONG (T1) | 0x42cf8 / 0x42cfc | memcmp (its trampoline __interceptor_trampoline_memcmp) [0x42cf4 (musl memcmp 0x9d1e0)] | __interceptor_trampoline_bcmp = __wrap_bcmp |
| 97 | `vfprintf_2` | WRONG (T1) | 0x42d20 / 0x42d24 | vfprintf (its trampoline __interceptor_trampoline_vfprintf) [0x42d18 (musl vfprintf 0x99a4c)] | __interceptor_trampoline_fprintf = __wrap_fprintf |
| 133 | `icpt_vfprintf_2` | WRONG (T1) | 0x46500 / 0x465d8 | __interceptor_vfprintf [0x46134] | ___interceptor_fprintf = __interceptor_fprintf |
| 146 | `InitializeCommonInterceptors` | WRONG (T2) | 0x49574 / 0x5224c | __sanitizer::InitializeCommonInterceptors [inlined: only its static metadata_mem is a symbol] | ioctl_table_fill |
| 147 | `InitializeSignalInterceptors_or_syscall_hooks` | WRONG (T2) | 0x5224c / 0x523a8 | __sanitizer::InitializeSignalInterceptors [inlined: only its static was_called_once is a symbol] | __sanitizer::Sort |
| 159 | `AsanCheckIncompatibleRT` | WRONG (T1) | 0x53594 / 0x53598 | __asan::AsanCheckIncompatibleRT [0x53598] | __asan::AsanCheckDynamicRTPrereqs |
| 160 | `AsanCheckDynamicRTPrereqs` | WRONG (T1) | 0x53598 / 0x53700 | __asan::AsanCheckDynamicRTPrereqs [0x53594] | __asan::AsanCheckIncompatibleRT |
| 165 | `icpt_cfree_or_DlsymFree` | WRONG (T2) | 0x53a34 / 0x53b00 | cfree / the DlsymAlloc free path [no symbol in the image] | __sanitizer::DlSymAllocator::Allocate |
| 167 | `DlsymAlloc_PointerIsMine_internal_allocator_From` | WRONG (T1) | 0x53b04 / 0x53c04 | __sanitizer::internal_allocator (DlsymAlloc::PointerIsMine has no symbol) [0x5ec3c] | __sanitizer::TwoLevelMap::Create |
| 168 | `HeapProfile_Insert_asan_memory_profile` | WRONG (T1) | 0x53f2c / 0x54098 | __asan::HeapProfile::Insert [0x5429c] | __asan::HeapProfile::Print |
| 173 | `asan_poison_stack_memory_PoisonAlignedStackMemor` | WRONG (T1) | 0x54bdc / 0x54d7c | __asan_poison_stack_memory [0x553a8] | __asan_poison_memory_region |
| 174 | `asan_unpoison_stack_memory` | WRONG (T1) | 0x54d7c / 0x54efc | __asan_unpoison_stack_memory [0x55444] | __asan_unpoison_memory_region |
| 182 | `ScopedInErrorReport_ReportError_helper` | WRONG (T1) | 0x55fe8 / 0x561f4 | __asan::ScopedInErrorReport (its destructor) [0x563a8] | __asan::ReportDeadlySignal |
| 213 | `AsanInitFromRtl_ENSURE_ASAN_INITED` | WRONG (T1) | 0x5a3c0 / 0x5a460 | __asan::AsanInitFromRtl [0x5a07c] | __asan::TryAsanInitFromRtl |
| 217 | `SealedTopOfMemory_check` | FALSE (FALSE) | 0x5a6c4 / 0x5a728 | SealedTopOfMemory::check / SealedTopOfMemory [no symbol of either name in the twin, local or global] | __asan::CheckSealedAddressSpace |
| 218 | `asan_handle_no_return_tiny_rtl_stub_2_insns` | WRONG (T1) | 0x5a89c / 0x5a8a4 | __asan_handle_no_return [0x5a4c4] | __asan::OnLowLevelAllocate |
| 220 | `ReserveShadowMemoryRanges_sealed_early_shadow_re` | WRONG (T1) | 0x5ac50 / 0x5ae30 | __sanitizer::ReserveShadowMemoryRange [0x6cc4c] | __asan::SealedReserveShadow |
| 225 | `AsanStats_Clear_ctor` | WRONG (T2) | 0x5b688 / 0x5b928 | __asan::AsanStats::Clear / its constructor [inlined: no symbol in the image] | __asan::FlushToDeadThreadStats |
| 232 | `IsStackTraceSuppressed` | WRONG (T1) | 0x5c24c / 0x5c398 | __asan::IsStackTraceSuppressed [0x5c474] | __asan::IsAddrSuppressed |
| 237 | `AsanThread_SetThreadStackAndTls` | WRONG (T1) | 0x5cbe0 / 0x5cd84 | __asan::AsanThread::SetThreadStackAndTls [0x5d458] | __asan::AsanThread::ClearShadowForThreadStackAndTLS |
| 242 | `AsanThread_ClearShadowForThreadStackAndTLS` | WRONG (T1) | 0x5d458 / 0x5d564 | __asan::AsanThread::ClearShadowForThreadStackAndTLS [0x5cbe0] | __asan::AsanThread::SetThreadStackAndTls |
| 247 | `InternalAlloc_RawInternalAlloc` | WRONG (T1) | 0x5e7a8 / 0x5e9e8 | __sanitizer::InternalAlloc [0x5ed94] | __asan::GetAsanThreadContext |
| 248 | `InternalFree_LowLevelAllocator_free_to_freelist` | WRONG (T1) | 0x5ec3c / 0x5ed94 | __sanitizer::InternalFree [0x5eeb8] | __sanitizer::internal_allocator |
| 249 | `internal_allocator_getter` | WRONG (T1) | 0x5ef80 / 0x5ef8c | __sanitizer::internal_allocator [0x5ec3c] | __sanitizer::GetGlobalLowLevelAllocator |
| 250 | `LowLevelAllocator_InternalAlloc_bump_allocator` | WRONG (T1) | 0x5ef8c / 0x5f0d8 | __sanitizer::InternalAlloc [0x5ed94] | __sanitizer::LowLevelAllocator::Allocate |
| 255 | `AllocatorMayReturnNull` | WRONG (T1) | 0x5f178 / 0x5f188 | __sanitizer::AllocatorMayReturnNull [0x5f150] | __sanitizer::IsRssLimitExceeded |
| 258 | `SetSealedStartFrame_sealed_patch` | FALSE (FALSE) | 0x6077c / 0x60788 | SetSealedStartFrame [no symbol of that name in the twin, local or global] | __sanitizer::SealedSetInitFrame |
| 262 | `IncreaseTotalMmap` | WRONG (T1) | 0x60e64 / 0x60e88 | __sanitizer::IncreaseTotalMmap [0x60e20] | __sanitizer::DecreaseTotalMmap |
| 267 | `sanitizer_free_hook_weak_default` | WRONG (T1) | 0x614fc / 0x61504 | __sanitizer_free_hook [0x61504] | __sanitizer_ignore_free_hook |
| 268 | `sanitizer_ignore_free_hook_weak_default_ret_0` | WRONG (T1) | 0x61504 / 0x61508 | __sanitizer_ignore_free_hook [0x614fc] | __sanitizer_free_hook |
| 272 | `ReportFile_SetReportPath` | WRONG (T1) | 0x62094 / 0x621d8 | __sanitizer::ReportFile::SetReportPath [0x61840] | __sanitizer::CommonFlags::SetDefaults |
| 273 | `OverrideCommonFlags_no_op_flag_hook_2_insns` | WRONG (T2) | 0x621d8 / 0x621e0 | __sanitizer::OverrideCommonFlags [inlined: no symbol in the image] | __sanitizer::CommonFlags::CopyFrom |
| 274 | `FlagParser_ParseString_parse_flags` | WRONG (T1) | 0x62528 / 0x637cc | __sanitizer::FlagParser::ParseString [0x640f8] | __sanitizer::RegisterCommonFlags |
| 275 | `FlagParser_PrintFlagDescriptions_gate_Verbosity` | WRONG (T1) | 0x637cc / 0x637f0 | __sanitizer::FlagParser::PrintFlagDescriptions [0x63b84] | __sanitizer::InitializeCommonFlags |
| 289 | `internal_strcmp` | WRONG (T1) | 0x647f0 / 0x64824 | __sanitizer::internal_strcmp [0x648ac] | __sanitizer::internal_strchr |
| 292 | `internal_strncmp` | WRONG (T1) | 0x648ac / 0x648f0 | __sanitizer::internal_strncmp [0x648f0] | __sanitizer::internal_strcmp |
| 293 | `internal_strchr` | WRONG (T1) | 0x648f0 / 0x6493c | __sanitizer::internal_strchr [0x647f0] | __sanitizer::internal_strncmp |
| 333 | `GetNamedMappingFd_ReadProcess_openat_getdents64` | WRONG (T1) | 0x657e8 / 0x65be4 | __sanitizer::GetNamedMappingFd [0x672e8] | __sanitizer::ThreadLister::ListThreads |
| 335 | `GetPageSizeCached` | WRONG (T2) | 0x65e68 / 0x65e70 | __sanitizer::GetPageSizeCached (the inline caching wrapper; the value holds its callee GetPageSize) [inlined: no symbol in the image] | __sanitizer::GetPageSize |
| 339 | `internal_sigaction_syscall_wrapper_selector` | WRONG (T1) | 0x66184 / 0x661e0 | __sanitizer::internal_sigaction [0x6d03c] | __sanitizer::GetHandleSignalMode |
| 350 | `MmapFixedNoAccess_3_insn_arg_shim_0x65c98` | WRONG (T1) | 0x66c48 / 0x66c54 | __sanitizer::MmapFixedNoAccess [0x6ee58] | __sanitizer::MmapFixedOrDie |
| 352 | `MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co` | WRONG (T1) | 0x66dcc / 0x66dd8 | __sanitizer::MmapFixedSuperNoReserve [0x6ed2c] | __sanitizer::MmapFixedOrDieOnFatalError |
| 363 | `sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a` | WRONG (T1) | 0x6a2d4 / 0x6a624 | __sanitizer::GetTls [0x6d33c] | __sanitizer::DTLS_on_tls_get_addr |
| 364 | `DTLS_Destroy_ForEachDVT_no_op_4_insns` | WRONG (T1) | 0x6a624 / 0x6a634 | __sanitizer::DTLS_Destroy [0x6a0e0] | __sanitizer::DTLS_Get |
| 365 | `InternalAllocatorLock_Unlock_or_stats_add_17_ins` | WRONG (T2) | 0x6a870 / 0x6a8b4 | __sanitizer::InternalAllocatorLock / Unlock [inlined: no symbol in the image] | __sanitizer::ThreadContextBase::ThreadContextBase |
| 366 | `ThreadContextBase_ctor_ThreadRegistry_init_helpe` | WRONG (T1) | 0x6a8b4 / 0x6a914 | __sanitizer::ThreadContextBase::ThreadContextBase [0x6a870] | __sanitizer::ThreadRegistry::ThreadRegistry |
| 379 | `GetThreadStackAndTls` | WRONG (T1) | 0x6d33c / 0x6d72c | __sanitizer::GetThreadStackAndTls [0x6d72c] | __sanitizer::GetTls |
| 380 | `GetThreadStackTopAndBottom_caller_ClearShadowFor` | WRONG (T1) | 0x6d72c / 0x6d7fc | __sanitizer::GetThreadStackTopAndBottom (and AsanThread::ClearShadowForThreadStackAndTLS 0x5cbe0) [0x6d050] | __sanitizer::GetThreadStackAndTls |
| 385 | `InternalMmapVector_push_back` | WRONG (T2) | 0x6deac / 0x6dfb8 | __sanitizer::InternalMmapVector::push_back [inlined: no symbol in the image] | __sanitizer::CollectStaticTlsBlocks |
| 397 | `MmapFixedNoReserve` | WRONG (T1) | 0x6ed2c / 0x6ed8c | __sanitizer::MmapFixedNoReserve [0x6ebfc] | __sanitizer::MmapFixedSuperNoReserve |
| 399 | `MprotectNoAccess` | WRONG (T1) | 0x6ee6c / 0x6ee8c | __sanitizer::MprotectNoAccess [0x66dd8] | __sanitizer::MmapNoAccess |
| 400 | `MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser` | WRONG (T1) | 0x6ee8c / 0x6efd8 | __sanitizer::MmapFixedOrDieOnFatalError [0x66dcc] | __sanitizer::ReservedAddressRange::Map; the _E value ends __sanitizer::SealedRepairReservation |
| 401 | `MmapFixedOrDie` | WRONG (T1) | 0x6efd8 / 0x6efe8 | __sanitizer::MmapFixedOrDie [0x66c48] | __sanitizer::ReservedAddressRange::MapOrDie |
| 402 | `MaybeStartBackgroudThread` | WRONG (T2) | 0x707e0 / 0x70824 | __sanitizer::MaybeStartBackgroudThread [inlined: only its static started is a symbol] | __sanitizer::InitializeCoverage |
| 403 | `Atexit_internal_exit_hook_runner_12_insns_execut` | WRONG (T1) | 0x70824 / 0x70854 | __sanitizer::Atexit [0x6e4ec] | __sanitizer_cov_dump |
| 410 | `StackDepotBase_Get` | WRONG (T2) | 0x73528 / 0x73638 | __sanitizer::StackDepotBase::Get [inlined: no symbol in the image] | __sanitizer::StackDepotGet |
| 411 | `StackDepotBase_find_bucket_chain_walk` | WRONG (T1) | 0x73a18 / 0x73aa8 | __sanitizer::StackDepotBase::find [0x73964] | __sanitizer::StackDepotBase::lock |
| 412 | `StackDepotBase_lock_bucket_spin_lock` | WRONG (T1) | 0x73aa8 / 0x73ba8 | __sanitizer::StackDepotBase::lock [0x73a18] | __sanitizer::TwoLevelMap::Create |
| 421 | `Unwind_GetIP_slow_unwind_helper` | WRONG (T1) | 0x7a768 / 0x7a9dc | _Unwind_GetIP [0x8d160] | __sanitizer::BufferedStackTrace::UnwindSlow |
| 429 | `asan_malloc_hook_RunMallocHooks_target_sanitizer` | WRONG (T1) | 0x80784 / 0x8079c | __sanitizer::RunMallocHooks [0x61394] | __lsan::DisabledInThisThread |
| 432 | `ubsan_MaybeCallUbsanDefaultOptions` | WRONG (T2) | 0x80c4c / 0x80c64 | __ubsan MaybeCallUbsanDefaultOptions [inlined: no symbol in the image] | __ubsan::Flags::SetDefaults |
| 479 | `fini_stub_ret` | WRONG (T1) | 0x938dc / 0x938e0 | _fini [0x939a8] | __cxa_finalize |
| 481 | `libc_exit_fini_array_walker_stub` | WRONG (T1) | 0x939a4 / 0x939a8 | __libc_exit_fini [0x939ac] | call |
| 482 | `musl_exit_helper_stub` | WRONG (T1) | 0x939a8 / 0x939ac | exit [0x939f8] | _fini = dummy |
| 507 | `fprintf` | WRONG (T1) | 0x99098 / 0x990fc | fprintf (no libc fprintf in the image; its ASan aliases) [__wrap_fprintf 0x42d20, __interceptor_fprintf 0x46500] | dprintf |
| 554 | `syscall_cp_c_tail_sccp_9_insns` | WRONG (T1) | 0x9de04 / 0x9de28 | __syscall_cp_c [0x9dddc] | __tls_get_addr |
| 559 | `lock_unlock_pair_user_futex` | WRONG (T1) | 0x9f5d8 / 0x9f67c | __lock / __unlock [0x9dae0 / 0x9dd68] | __pthread_rwlock_unlock = pthread_rwlock_unlock |
| 560 | `pthread_key_create_body_tsd_init` | WRONG (T1) | 0x9f67c / 0x9f798 | __pthread_key_create [0x9f260] | __pthread_rwlock_wrlock = pthread_rwlock_wrlock; the _E value ends __pthread_rwlock_timedwrlock = pthread_rwlock_timedwrlock |
| 561 | `pthread_key_atfork_tsd_table_init_11_insns` | WRONG (T2) | 0x9f798 / 0x9f7c4 | __pthread_key_atfork [no symbol in the image] | __pthread_rwlock_trywrlock = pthread_rwlock_trywrlock |

## The two _E region brackets, kept

- `tfib_E_target_run` 0x8121c ends `oft_exit_guard` [0x811ec, 0x8121c), so the pair [0x81094, 0x8121c) covers
  `target_run` [0x81094, 0x811ec) AND `oft_exit_guard`. The checker triage records this label form as the donor's
  (records/gate-205a90-TRIAGE.md, DS-AB1W-LABEL).
- `tfib_E_start` 0x31118: `_start` (the _A cell, 0x310d0) is an assembly symbol of size 0, and 0x31118 is the END of
  `_start_c` [0x310ec, 0x31118) = the start of `__do_init`, so the pair covers `_start` and `_start_c`. **Measured
  against the donor** (fuzz_grant's twin 57c26f993615, where the cell holds 0x30824): there `_start` is at 0x307dc with
  size 0, `_start_c` is [0x307f8, 0x30824) and `__do_init` starts at 0x30824 — the donor's cell is the END of
  `_start_c` too, so our cell is the donor's quantity correctly moved (the same offset from the same symbol), not a
  changed convention. Image B's cell is the START of `_start_c` (= the end of the size-0 `_start`), a different point
  of the same pair; image B's core comes from a different donor (libreac fuzz_decode's released lib/B), so the two
  images state different donors' conventions. The value is not changed.

Both are kept with this comment by the integration owner's instruction of 2026-10-31 08:40Z (region-bracket pairs of
the documented convention stay); the function-label tests (WRONG, FALSE) do not apply to a bracket cell, and the table
says so in each one's note.

## The diff against image B (TFIB-TABLE-B.tsv, sha256 6ff7ed2cc9e2; internal record), label by label

B removed 79 pairs, this core 80. The two sets agree on 67 labels. The 13 differences, each decided by the same test:

- **12 labels B removed and this read had kept; all 12 fire the test on image A too, and are removed here**:
  AsanChunkView_GetAsanChunk_ptr_helper (T2: names `Allocator::GetAsanChunk`, inlined; on `Allocator::GetAsanChunkByAddr`),
  GetThreadStackTopAndBottom_caller_ClearShadowFor (T1: `GetThreadStackTopAndBottom` 0x6d050; on `GetThreadStackAndTls`),
  LowLevelAllocator_InternalAlloc_bump_allocator (T1: `InternalAlloc` 0x5ed94; on `LowLevelAllocator::Allocate`),
  ReserveShadowMemoryRanges_sealed_early_shadow_re (T1: `ReserveShadowMemoryRange` 0x6cc4c; on `SealedReserveShadow`),
  RoundUpTo_size_CHECK_helper_sanitizer_common_h_C (T2: `RoundUpTo`, inlined; on `RoundUpToPowerOfTwo`),
  StackDepotBase_Get (T2: `StackDepotBase::Get`, inlined; on the free function `StackDepotGet`),
  ThreadContextBase_ctor_ThreadRegistry_init_helpe (T1: `ThreadContextBase::ThreadContextBase` 0x6a870; on
  `ThreadRegistry::ThreadRegistry`), Unwind_GetIP_slow_unwind_helper (T1: `_Unwind_GetIP` 0x8d160; on
  `BufferedStackTrace::UnwindSlow`), fini_stub_ret (T1: `_fini` 0x939a8; on `__cxa_finalize`), lock_unlock_pair_user_futex
  (T1: `__lock` 0x9dae0, `__unlock` 0x9dd68; on `pthread_rwlock_unlock`), musl_exit_helper_stub (T1: `exit` 0x939f8; on
  `_fini` = `dummy`), sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a (T1: `GetTls` 0x6d33c; on
  `DTLS_on_tls_get_addr`). Each named function is in image A's own twin at the address given, and no label of the 12
  also names the function at its value.
- **1 label this read had removed and B kept, restored here**: `internal_pthread_weak_stub_ret` (on
  `__sanitizer::Atexit`). `internal_pthread` is a family prefix, not a function: the twin has
  `internal_pthread_create` 0x48668 and `internal_pthread_join` 0x48674, and the label names neither. It only
  describes a weak stub that returns, so it is NO-SYMBOL by the test and stays.
- **1 label image B does not have**: `FakeStack_SetShadow` (T2: names `FakeStack::SetShadow`, inlined; on
  `__asan::MemToShadow`). lib/B has no cell of that name, so B's set cannot contain it; it is removed here. 79 + 1 = 80.

## Re-run

    checks/tfibtable-A.py TWIN DONOR_TWIN UNIT DONOR_LIB > records/tfib-whole-table.tsv

with TWIN = the unstripped twin (86efc3a80314), DONOR_TWIN = fuzz_grant's twin (57c26f993615), UNIT = the unit's
directory in the clone, DONOR_LIB = the run of record's WORK/stage (the donor's text, renamed). The script is image B's
tfibtable-B.py (sha256 1f1eb92bf82a; internal record; the same rule and the same classes) with lib/B -> lib/A, the
two region brackets, and the hand rows added; the hand rows are checks/tfib-hand-rows.tsv, whose header states the
test. The table's first line names the lib by the sha256 of the two files that hold cells (lib/A/AB1w.v 3b4e3167677a,
lib/A/AE3a.v 9aae990f45ca: the lib before both removals), and its last column is `reading lines`. For the FALSE pass
the table was written again on that same lib (lib/A/AB1w.v put back to 3b4e3167677a for the run, then restored): it
differs from the WRONG pass's table in its first line and 8 rows only — the 6 FALSE cells (NO-SYMBOL -> FALSE, with
their note) and the notes of the two OK-REGION cells (measured, line by line). Run on the tree of the FALSE removal,
the table has the same rows less the 166 removed cells (measured: 1035 rows, every kept cell's class unchanged,
WRONG 0, FALSE 0).

## The run of record

The relocation run of record (run.sh, port_core 83f5203d2a2f) wrote these 166 cells as the donor had them; its
WORK/stage-out/A/AB1w.v therefore still holds them, and from the two removal commits the committed lib/A/AB1w.v and
that stage-out file differ in exactly these 83 lines (80 WRONG pairs, 3 FALSE pairs; before them they were byte-equal).
The checker gates read the run directory, not
the lib: gate (b)'s declaration `0x65c98` (gates/codeptr-notaddr.tsv, the hex inside
`tfib_A_MmapFixedNoAccess_3_insn_arg_shim_0x65c98`) and the gate (a) triage rows that name removed cells
(records/gate-205a90-TRIAGE.md, records/pac-namediff.tsv) are records of that run; their rows are unchanged (the gate
re-run after the scripts' comment and printed-text edits gives the same rows).
