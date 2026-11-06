# Image B's listing files: how they are made

`lib/B/Prog/GrantSyms.v`, `lib/B/Prog/GrantList.v` and `lib/B/Prog/GrantAddr.v` are generated. This series
regenerated them with the generator itself, so their text is the generator's own output. Before this series,
line 2 of each file was a hand-written recipe line; the generator writes no recipe line, so line 2 is gone and
nothing else in the three files changed.

## Tools

- `mklisting.py` (sha256 f1adf8325d8a; internal record)
- `emit_rocq.py` (sha256 3b62205ad0f8; internal record)

No other script of the listing tools ran: `copy_pa.py`, `adapt_pa.py`, `adapt_kit.py` and `mkro.py` were not run,
so the walk-engine files `lib/Reusable/Pa*.v` are unchanged.

## Inputs

- The image: `fuzz_grant.asan-ubsan`, sha256 fde52226dc48 (the build `harness.yaml` pins), and its unstripped
  twin, sha256 5a5ee7c02b4e, as the symbol file.
- The listing range: 0x80a3c .. 0x86640.
- The 54 call names, in this order:
  `__asan_stack_malloc_4, __asan_set_shadow_f5, __asan_set_shadow_00, __interceptor_trampoline_malloc,
  reac_headamp_tx_init, __asan_memset, reac_headamp_tx_set, reac_headamp_tx_effective, reac_headamp_default,
  __asan_report_load1, reac_grant_alloc_fits, reac_grant_allocate, reac_grant_build_sweep,
  __interceptor_trampoline_bcmp, want_of, check_groupa, reac_ctrl_identity_poll_block,
  __interceptor_trampoline_free, reac_headamp_tx_arm_scene, reac_headamp_tx_set_resweep, reac_headamp_tx_next,
  __asan_handle_no_return, abort, __asan_report_store1, __asan_stack_malloc_2, __asan_memcpy, reac_ctrl_parse,
  reac_ctrl_headamp_record_verify, reac_ctrl_checksum_verify, __asan_init, __asan_version_mismatch_check_v8,
  __asan_register_elf_globals, __asan_unregister_elf_globals, __asan_stack_malloc_1, kind_of_link1,
  __asan_report_store4, __asan_report_store2, __asan_report_load4, __asan_stack_malloc_0, ctrl_lay_block,
  ctrl_finish, __asan_stack_malloc_6, __asan_set_shadow_f8, reac_ctrl_stamp_headamp, __asan_stack_free_6,
  reac_box_model_block, __asan_report_load8, reac_ctrl_record_cksum_stamp, reac_ctrl_block_cksum_stamp,
  build_dt1_single, name_field, dt1_head, __asan_report_load2, reac_ctrl_build_grant_sweep`

## Commands

Every value is literal. `IMAGE` is the image above and `TWIN` its unstripped twin.

    mklisting.py IMAGE TWIN 0x80a3c 0x86640 --out GEN --call <the 54 names above, comma-separated>
    emit_rocq.py GEN --dst lib/B/Prog --sub B.Prog --table-sub Reusable --extra-obj 35=a5978,36=a5980 \
      --image fuzz_grant.asan-ubsan --image-label 'image B' --img-module ''

Both exit 0. `mklisting.py` prints `slots 5889  his 68  objs 35  syms 54`; `emit_rocq.py` prints
`wrote GrantSyms.v (54 names), GrantList.v (5889 slots, 30 functions), GrantAddr.v (35 objects, 68 auipc values)`.

## Checks

1. **Output against the files it replaces.** The same commands, run first into a scratch directory, wrote three
   files equal to the previous files with line 2 removed (60, 5932 and 184 lines). The run into `lib/B/Prog`
   wrote the same bytes.
2. **Inputs.** Every input is the literal value above; no value is taken from a variable or a file other than the
   image, its twin and the call list.
3. **Emitted text.** Every comment line of the three generated files was scanned for internal names: none.
