(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AE2k.v, with its module paths and addresses changed; 4 of its 42 lines of code are new or changed and 13 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x42198.
Definition FF_pc_wrap_fwrite : Z := 0x421b0.

Definition FF_pc_wrap_fflush : Z := 0x421ec.

Definition FF_real_strchr : Z := 0x94b10.
Definition FF_real_fwrite : Z := 0x90bc8.

Definition FF_real_fflush : Z := 0x9065c.

Definition FF_got_strchr : Z := 0x9e0c0.
Definition FF_got_fwrite : Z := 0x9e0f0.

Definition FF_got_fflush : Z := 0x9e158.

Definition FF_meta_ptr : Z := 0xa4800.
Definition FF_meta_mem : Z := 0xa4808.
Definition FF_got_cflags : Z := 0x9c3a0.
Definition FF_cflags : Z := 0x136ae8.
Definition FF_got_shadow : Z := 0x9c3b0.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5f8640.
Definition A_ofl_head : Z := 0x5f8648.
Definition A_threaded : Z := 0x5f81e1.
Definition A_need_locks : Z := 0x5f81e3.
Definition A_stdio_read : Z := 0x901ec.
Definition A_stdio_write : Z := 0x9030c.
Definition A_stdio_seek : Z := 0x90304.
Definition A_stdio_close : Z := 0x901c0.
Definition FF_got_canary : Z := 0x9d038.
Definition FF_canary : Z := 0x5f7f90.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103a8.
Definition FF_mask_val : Z := 0xafffff00000fffff.
(* Theorem Labs, 2026-10-29: identity writes no file, so grant's no-file sink form applies
   (ossv/recipes 48907dc7e8ca, projects/libreac/fuzz_grant/proofs/lib/A/AE2k.v:41,44-45). A_PATH / A_WB / A_RWA /
   A_TRAILER held port_core_refused_* markers - cgif's file-string addresses, for which identity has no
   counterpart - and the four string fields become 0. The owned environment cells move into tfib_owned;
   each address is confirmed BY SYMBOL in identity's own table, with the size the symbol declares:
     A_threaded    0x5f81e1  __libc @ 0x5f81e0 (size 0x68) + 0x1          1
     A_need_locks  0x5f81e3  __libc + 0x3                                 1
     A_ofl_lock    0x5f8640  ofl_lock, size 4                             4
     FF_canary     0x5f7f90  __stack_chk_guard, size 8                    8
   The four sizes match grant's (1,1,4,8) exactly: the objects are the same musl ones. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (FF_canary, 8)].
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
