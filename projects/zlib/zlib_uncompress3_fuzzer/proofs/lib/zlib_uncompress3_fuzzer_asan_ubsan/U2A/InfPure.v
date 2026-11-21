(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import IDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac lia_std := lia.
Ltac icx_cbn := cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc
                     t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                     t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in *.
Ltac destr_conj H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "F" in destruct H as [H1 H]; destr_conj H1; destr_conj H
  | _ => idtac
  end.
Ltac split_conj := repeat match goal with |- _ /\ _ => split end.

Ltac mode_consts :=
  cbv [reach codes_liveP HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Ltac mode_solve Mf tac :=
  split_conj;
  first [ right; lia_std
        | intros X; exfalso; lia_std
        | intros Hf; exfalso; destruct (Mf Hf) as [Hx _]; lia_std
        | tac ].
