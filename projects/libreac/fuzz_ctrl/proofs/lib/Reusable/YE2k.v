(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE2k.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_ctrl's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B (asan-ubsan) twin of A/AE2k.v in the shared sink form (a Theorem Labs lane 4d244de18f0):
   the sink's path, mode, "rwa" and trailer strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen and fclose cells are
   removed, as fuzz_ctrl.asan-ubsan holds none of them (0 hits for the strings in every PT_LOAD), so tfib_K's four string
   fields are 0 and tfib_owned is the sink's own static cells. Every value is re-measured in fuzz_ctrl.asan-ubsan (nm and
   cell contents), replacing the relocation's refused names and its moved-with-the-wrong-delta values: __libc 0x5fc8e0
   (.threaded +1, .need_locks +3; was 0x5fcb61 / 0x5fcb63), ofl_lock 0x5fcd40 / ofl_head 0x5fcd48, metadata_mem 0xa8f08
   (was 0xa9188), __stack_chk_guard 0x5fc690 (was 0x5fc910) behind the GOT word 0xa1578, __stdio_read / write / seek /
   close 0x94608 / 0x94728 / 0x94720 / 0x945dc. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x42aa4.
Definition FF_pc_wrap_fwrite : Z := 0x42abc.
Definition FF_pc_wrap_fflush : Z := 0x42af8.
Definition FF_real_strchr : Z := 0x98f2c.
Definition FF_real_fwrite : Z := 0x94fe4.
Definition FF_real_fflush : Z := 0x94a78.
Definition FF_got_strchr : Z := 0xa2600.
Definition FF_got_fwrite : Z := 0xa2630.
Definition FF_got_fflush : Z := 0xa2698.
Definition FF_meta_ptr : Z := 0xa8f00.
Definition FF_meta_mem : Z := 0xa8f08.
Definition FF_got_cflags : Z := 0xa08e0.
Definition FF_cflags : Z := 0x13b1e8.
Definition FF_got_shadow : Z := 0xa08f0.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5fcd40.
Definition A_ofl_head : Z := 0x5fcd48.
Definition A_threaded : Z := 0x5fc8e1.
Definition A_need_locks : Z := 0x5fc8e3.
Definition A_stdio_read : Z := 0x94608.
Definition A_stdio_write : Z := 0x94728.
Definition A_stdio_seek : Z := 0x94720.
Definition A_stdio_close : Z := 0x945dc.
Definition FF_got_canary : Z := 0xa1578.
Definition FF_canary : Z := 0x5fc690.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103a0.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite); (FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (FF_canary, 8)].
(* fuzz_ctrl writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0, and asink_strs is never stated for it. *)
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem
FF_got_canary FF_canary tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
