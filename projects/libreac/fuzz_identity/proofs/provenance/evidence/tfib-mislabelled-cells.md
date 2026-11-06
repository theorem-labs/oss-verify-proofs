# tfib cells whose label names one function and holds another

These three cell pairs, inherited from the donor's table, were the first found that name one function and hold
another. The test in `label_test.py` now decides every label; `address-cell-labels.md` beside this note states it
and its result. For these three it keeps `asan_register_globals` and `asan_unregister_globals` by clause (c): the
held function calls the function the label names (image A at 0x400fc and 0x40168, image B at 0x40164 and 0x401d0).
It removes `asan_unpoison_stack_memory`: no clause holds. No `.v` file of the unit names its cells.

| cell | held | the symbol actually there | where the named function really is |
|---|---|---|---|
| `tfib_A/E_asan_register_globals` | A 0x400c8, B 0x40130 | `__asan_register_elf_globals` | `__asan_register_globals`, held by the `_impl` cell (kept) |
| `tfib_A/E_asan_unregister_globals` | A 0x40134, B 0x4019c | `__asan_unregister_elf_globals` | `__asan_unregister_globals` at A 0x3fafc, held by the `_impl` cell (kept) |
| `tfib_A/E_asan_unpoison_stack_memory` | A 0x54224, B 0x5428c | `__asan_unpoison_memory_region` | `__asan_unpoison_stack_memory` at A 0x548ec |

Donor values: the same cells hold the same functions in the donor table, so the port moved them
faithfully and the mislabel is the donor's, not this unit's.

Read from: `fuzz_identity.asan.debug` (sha256 5b0cbe573036) and `fuzz_identity.asan-ubsan.debug`, their
own `.symtab`.
