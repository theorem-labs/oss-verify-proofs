(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export BzParams.
From Stdlib Require Lia.

From Stdlib Require Bool List.
Module BzParamsX.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Lists.List.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Import ListNotations.

(* [comment removed for export] *)
Lemma div3_magic : forall x, 0 <= x <= 255 -> x * 171 / 512 = x / 3.
Proof.
  intros x Hx.
  assert (E : forallb (fun k => Z.eqb (Z.of_nat k * 171 / 512) (Z.of_nat k / 3)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in E. specialize (E (Z.to_nat x)).
  rewrite Z2Nat.id in E by lia. apply Z.eqb_eq, E. apply in_seq. lia.
Qed.

Section X. Context {BZP : BzParams}.
  Lemma land255_wf : Z.land (wf_clamp p_wf + -1) 255 = wf_clamp p_wf - 1.
  Proof.
    pose proof wf_clamp_rng as W. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
    rewrite Z.mod_small; [lia|]. change (2 ^ 8) with 256. lia.
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma budget_q_magic : (wf_clamp p_wf - 1) * 171 / 512 = budget_q.
  Proof. pose proof wf_clamp_rng. rewrite div3_magic by lia. reflexivity. Qed.
  Lemma budget_q_magic_land : Z.land (Z.land (wf_clamp p_wf + -1) 255 * 171) 18446744073709551615 / 512 = budget_q.
  Proof.
    pose proof wf_clamp_rng as W. rewrite land255_wf.
    change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite Z.mod_small by (change (2 ^ 64) with 18446744073709551616; lia). apply budget_q_magic.
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma hdr_digit_land : Z.land (BLOCKSIZE100K + 48) 255 = BLOCKSIZE100K + 48.
  Proof.
    pose proof p_bs_rng. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
    apply Z.mod_small. change (2 ^ 8) with 256. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma hdr_digit_land64 : Z.land (Z.land (BLOCKSIZE100K + 48) 18446744073709551615) 255 = 48 + BLOCKSIZE100K.
  Proof.
    pose proof p_bs_rng. change 18446744073709551615 with (Z.ones 64). rewrite (Z.land_ones (BLOCKSIZE100K + 48)) by lia.
    rewrite Z.mod_small by (change (2 ^ 64) with 18446744073709551616; lia). rewrite hdr_digit_land. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End X.
End BzParamsX.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac lia ::= first [ Zify.zify; xlia zchecker | bz_params_occ; Zify.zify; xlia zchecker ].
Ltac nia ::= first [ Zify.zify; xnia zchecker | bz_params_occ; Zify.zify; xnia zchecker ].

Section SelfTest. Context {BZP : BzParams}.
  (* [comment removed for export] *)
  Variable y : Z.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End SelfTest.
