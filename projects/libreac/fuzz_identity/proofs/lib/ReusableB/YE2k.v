(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/YE2k.v, with its module paths and addresses changed; 4 of its 42 lines of code are new or changed and 13 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x42200.
Definition FF_pc_wrap_fwrite : Z := 0x42218.

Definition FF_pc_wrap_fflush : Z := 0x42254.

Definition FF_real_strchr : Z := 0x94dfc.
Definition FF_real_fwrite : Z := 0x90eb4.

Definition FF_real_fflush : Z := 0x90948.

Definition FF_got_strchr : Z := 0x9e3a0.
Definition FF_got_fwrite : Z := 0x9e3d0.

Definition FF_got_fflush : Z := 0x9e438.

Definition FF_meta_ptr : Z := 0xa4b00.
Definition FF_meta_mem : Z := 0xa4b08.
Definition FF_got_cflags : Z := 0x9c680.
Definition FF_cflags : Z := 0x136de8.
Definition FF_got_shadow : Z := 0x9c690.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5f8940.
Definition A_ofl_head : Z := 0x5f8948.
Definition A_threaded : Z := 0x5f84e1.
Definition A_need_locks : Z := 0x5f84e3.
Definition A_stdio_read : Z := 0x904d8.
Definition A_stdio_write : Z := 0x905f8.
Definition A_stdio_seek : Z := 0x905f0.
Definition A_stdio_close : Z := 0x904ac.
Definition FF_got_canary : Z := 0x9d318.
Definition FF_canary : Z := 0x5f8290.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103a8.
Definition FF_mask_val : Z := 0xafffff00000fffff.
(* Theorem Labs, 2026-10-29: identity writes no file, so grant's no-file sink form applies
   (ossv/recipes 48907dc7e8ca, projects/libreac/fuzz_grant/proofs/lib/A/AE2k.v:41,44-45); this is the asan-ubsan twin
   of identity's A/AE2k.v change. A_PATH / A_WB / A_RWA / A_TRAILER held port_core's refusal markers -
   cgif's file-string addresses, for which identity has no counterpart - and the four string fields
   become 0. The owned environment cells move into tfib_owned; each address is confirmed BY SYMBOL in
   the asan-ubsan image's own table (fuzz_identity.debug .symtab), with the size the symbol declares:
     A_threaded    0x5f84e1  __libc @ 0x5f84e0 (size 0x68) + 0x1          1
     A_need_locks  0x5f84e3  __libc + 0x3                                 1
     A_ofl_lock    0x5f8940  ofl_lock, size 4                             4
     FF_canary     0x5f8290  __stack_chk_guard, size 8                    8
   The four sizes match grant's and identity asan's (1,1,4,8) exactly: the objects are the same musl ones. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (FF_canary, 8)].
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
