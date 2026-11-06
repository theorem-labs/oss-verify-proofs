(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Walk ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import AWKit AWAuto.
Open Scope Z_scope.

Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land3_mod4 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land1_mod2 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac ub_land K :=
  rewrite ?Z.land_lor_distr_l in K; rewrite ?land7_mod8, ?land3_mod4, ?land1_mod2 in K;
  repeat match goal with H : ?x mod 8 = 0 |- _ => rewrite H in K end; rewrite ?Z.lor_0_l, ?Z.lor_0_r in K;

  repeat match type of K with context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) in K by lia end.
Ltac ubr_by tac :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU; ub_land KU; [ exfalso; tac | try clear KU ].
Ltac ubr := ubr_by lia.
Ltac ub_null := step; ubr.
Ltac ub_align := zstep; step; ubr.
Ltac ub_ovf := zstep; step; ubr.

Ltac ubr2 :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU; ub_land KU; [ first [ (exfalso; lia) | fail 1 ] | ]; try clear KU.
Ltac ubr3 :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU; ub_land KU; [ | exfalso; lia ]; try clear KU.

Ltac ub_b2z :=
  repeat match goal with |- context [Z.b2z (?a <? ?b)] =>
    first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; change (Z.lxor 1 0) with 1; change (Z.lxor 0 1) with 1; change (Z.lxor 1 1) with 0; change (Z.lxor 0 0) with 0.
Ltac has_b2z_if := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => lazymatch c with context [Z.b2z] => idtac end end.
Ltac walk_ub_to p := repeat first [ (is_ms; tryif at_pc p then fail else cstep) | (has_b2z_if; ub_b2z; lit_branch_safe) | (is_if; first [ br_auto | ubr2 | ubr3 ]) ].
