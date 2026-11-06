(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 44 of its 64 lines of code are new or changed and 124 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require Import SSlot.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac slia ::= first [ exact I | lia | repeat split; try exact I; lia ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Lemma early_cond : forall u, 2 ^ 26 <= u < 2 ^ 64 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = true.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia.
  assert (H1 : 1 <= u / 2 ^ 26) by (apply Z.div_le_lower_bound; lia).
  assert (H2 : u / 2 ^ 26 < 2 ^ 38) by (apply Z.div_lt_upper_bound; lia).
  unfold bv_eqb. rewrite !unsigned_lit by lia.
  destruct (Z.eqb_spec (u / 2 ^ 26) 0); [lia | reflexivity].
Qed.

Lemma scene_early_holds : scene_early.
Proof.
  unfold scene_early.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sv lo ST LO HS MI Ha1.
  pose proof (munch_refl [(Sv - 9072, Sv)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  assert (S0 : 0 <= lo) by (destruct ST as [H _]; exact H).
  carve_frame 104%nat ST. rename FR into FRs.
  carve_frame 6%nat ST. rename FR into FRm.
  carve_frame 3005%nat ST. rename FR into FRb.
  carve_frame 3005%nat ST. rename FR into FRa.
  carve_frame 8%nat ST. rename FR into FRp.
  carve_frame 2944%nat ST. rename FR into FRl.
  do 16 zstep.
  replace (Sv + -2032 - 4096) with (Sv + -6128) by lia.
  zstep.
  zstep.
  replace (bv_unsigned (Z_to_bv 64 (Sv + -6128)) + -2048) with (Sv + -8176)
    by (rewrite unsigned_lit by lia; lia).
  zstep.
  zstep.
  zstep.
  lazymatch goal with |- context [Z.shiftr ?u 26] => if_true_by (early_cond u ltac:(lia)) end.
  do 19 zstep.
  release_frame FRl ST (Sv + -6128).
  release_frame FRp ST (Sv + -6120).
  release_frame FRa ST (Sv + -3115).
  release_frame FRb ST (Sv + -110).
  release_frame FRm ST (Sv + -104).
  release_frame FRs ST Sv.
  finish.
  all: try (f_equal; lia).
Qed.
