(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.Riscv Require Import Decode.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import CatExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import CatSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import SeqExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Inflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvDec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvArms5.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflRod6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflCtx6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflArmLib6b.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Cl1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_ClS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ItCovIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvCov.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvTbl.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Match2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflDec6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Dist3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import Callee6i.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflMem2.
Module InflA_Lenlens1.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvDec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvArms5.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflNeed6.
Import InflA_Cl1.InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import InflA_ClS.InflA_LenlensS.
Import InflA_Cl1.InflA_Codelens3.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma order6_read : forall mem (a : Z) i e,
  rod6_clear mem -> 0 <= i < 19 -> a = A6_ORDER + 2 * i -> e = arr_get order_a i ->
  exists bs, rdn s6u_segs mem (zw a) 2 = Some bs /\ bytes_le_to_Z bs = e.
Proof.
  intros mem a i e HM Hi -> ->. pose proof (order6_cells mem HM i Hi) as Ci. unfold cell in Ci.
  pose proof (order_range i Hi) as Hr.
  eexists. split; [exact Ci|]. rewrite bytes_le_Z_to_le by lia. apply Z.mod_small. change (8 * Z.of_nat 2) with 16. lia.
Qed.
End FXG.
Ltac order_read :=
  lazymatch goal with
  | H : rod6_clear ?m |- exists bs, rdn s6u_segs ?m' (zw ?a) 2 = Some bs /\ bytes_le_to_Z bs = arr_get order_a ?i =>
      apply (order6_read m a i _ H); [lia | unfold A6_ORDER; lia | reflexivity]
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma ll1_s_alt : forall s h, 0 <= is_have s + 1 < 2 ^ 32 ->
  ll1_s s h = iset_lens (iset_have s (is_have s + 1)) (arr_set (is_lens s) (arr_get order_a (is_have s)) (wrap16 (BITSv h 3))).
Proof. intros s h H. unfold ll1_s. rewrite wrap32_id by exact H. destruct s; reflexivity. Qed.

Lemma BITSv3 : forall h, 0 <= h -> BITSv h 3 = h mod 2 ^ 3.
Proof. intros h Hh. apply BITSv_mod; lia. Qed.

Lemma lxor_m1_mod64 : forall a, 0 <= a < 2 ^ 64 -> Z.lxor a (-1) mod 2 ^ 64 = 2 ^ 64 - 1 - a.
Proof.
  intros a Ha. rewrite Z.lxor_m1_r. unfold Z.lnot. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Lemma bnd19_side : forall h, 0 <= h <= 18 -> szwrap 32 (h + -18) mod 2 ^ 64 <> 1.
Proof.
  intros h Hh. rewrite szwrap32_small by (change (2 ^ 31) with 2147483648; lia). change (2 ^ 64) with 18446744073709551616. lia.
Qed.
Lemma ne1_side : forall x, - 100 <= x <= 0 -> szwrap 32 x mod 2 ^ 64 <> 1.
Proof.
  intros x Hx. rewrite szwrap32_small by (change (2 ^ 31) with 2147483648; lia). change (2 ^ 64) with 18446744073709551616. lia.
Qed.
End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilL1 : cfg := ilSx [0x1f75c; 0x1f794; 0x1f7fc] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section L1.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition LFIXa (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 18 = zw (cv_ZP v)
    /\ getr R 1 = zw 16209 /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4.
  Lemma LFIX_LFIXa : forall R, LFIX v R -> LFIXa R.
  Proof. intros R HF. unfold LFIX in HF. destruct HF as (G2 & G27 & G13 & G8 & G11 & G1 & G3 & G4). unfold LFIXa. repeat split; assumption. Qed.
  Ltac open_fixa HF :=
    let X := fresh in pose proof HF as X; unfold LFIXa, INF_FRAME in X;
    destruct X as (G2 & G27 & G8 & G1 & G3 & G4).
  Ltac lfixa_close Hfr HR :=
    unfold LFIXa, INF_FRAME;
    repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with |- getr _ ?n = _ =>
      first [ rewrite (Hfr n eq_refl); assumption
            | let G := fresh "G" in symex_reg HR n as G; rewrite G; first [ reflexivity | assumption | apply zw_neg_mod | f_equal; lia ]
            | match goal with |- ?G => idtac "LFIXa LEFT" G end ]
    end.

  Definition L1REG (s : inflate_state) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXa R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r) /\ getr R 19 = zw (ir_bits r)
    /\ getr R 10 = zw A6_ORDER /\ getr R 11 = zw (is_ncode s) /\ getr R 12 = zw (ir_have r) /\ getr R 13 = zw (-19)
    /\ getr R 14 = zw (cv_I0 v + ir_next r) /\ getr R 15 = zw (is_have s + 1) /\ getr R 16 = zw (- is_ncode s)
    /\ getr R 17 = zw (2 * is_have s).
  Definition FREG (s : inflate_state) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXa R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r) /\ getr R 19 = zw (ir_bits r)
    /\ getr R 10 = zw A6_ORDER /\ getr R 12 = zw (ir_have r) /\ getr R 14 = zw (cv_I0 v + ir_next r) /\ getr R 17 = zw (is_have s).

  Ltac open_l1 HJ :=
    let X := fresh in pose proof HJ as X; unfold L1REG in X;
    destruct X as (HF & G9 & G22 & G18 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17); open_fixa HF.

  Definition l1pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (19, EVar 41%nat); (10, ELit 75148); (11, EVar 47%nat); (12, EVar 36%nat); (13, ELit (-19));
     (14, EAdd (EVar 43%nat) (EVar 44%nat)); (15, EAdd (EVar 46%nat) (ELit 1)); (16, ESub (ELit 0) (EVar 47%nat)); (17, EVar 45%nat)].
  Definition l1vb : list (nat * Z) := [(45%nat, 64); (46%nat, 32); (47%nat, 32)].
  Ltac l1_close Hfr HR k :=
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- LFIXa _ => lfixa_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); first [assumption | unfold A6_ORDER; assumption] end
          | k
          | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR n as G; rewrite G; first [reflexivity | unfold A6_ORDER; reflexivity | apply zw_neg_mod | f_equal; lia] end
          | match goal with |- ?G => idtac "L1 LEFT" G end ].

  Lemma ll1_go : forall s (c : icall) r R M,
    L1REG s r R -> RINV (cv_NI v) (cv_NO v) r -> 0 <= is_have s < is_ncode s -> is_ncode s <= 19 -> 3 <= ir_bits r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f75c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f794) M s6u_rom) /\ L1REG s r R1.
  Proof.
    intros s c r R M HJ RI Hh Hn Hb. open_l1 HJ. open_ictx C. open_rinv RI. unfold A6_ORDER in G10.
    arm_symexP (@nil (Z * expr)) ilL1 6%nat [true] (@nil (option expr)) l1pins l1vb v r [2 * is_have s; is_have s; is_ncode s] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f75c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTL1GO" G end.
    exists R1. split; [by_run Hms|].
    unfold L1REG. l1_close Hfr HR1 fail.
  Qed.

  Lemma ll1_pull : forall s c r R M,
    LMEM v (mkW s c r) M -> L1REG s r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    0 <= is_have s < is_ncode s -> is_ncode s <= 19 -> ir_bits r < 3 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f75c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f794) M s6u_rom) /\ L1REG s (pull1 c r) R1.
  Proof.
    intros s c r R M HM HJ RI CI Hh Hn Hb Hhv. open_l1 HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *. unfold A6_ORDER in G10.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hhv Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symexP (@nil (Z * expr)) ilL1 16%nat [false; true; true] (@nil (option expr)) l1pins l1vb v r [2 * is_have s; is_have s; is_ncode s] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f75c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTL1PULL" G end.
    exists R1. split; [by_run Hms|].
    assert (Hh32 : 0 < ir_have r < 2 ^ 32) by (clear - Hhv Rnx0 Rhv0 Rnh CI0; lia).
    symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (14%bv : reg) as Q14.
    cbn [famA] in Q22. rewrite bmod_get in Q22 by exact Hby.
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in Q22;
      [| clear - Hby; lia | clear - Rbits Hb; lia | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby); assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia].
    unfold L1REG, pull1; cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next].
    l1_close Hfr HR1 ltac:(first [ rewrite Q12; rewrite szwrap32_small by (clear - Hh32 CI0 Rnh Rnx0; lia); reflexivity
                                   | rewrite Q22; f_equal; lia
                                   | rewrite Q18; rewrite lor8_small by (clear - Rbits Hb; lia); reflexivity
                                   | rewrite Q14; f_equal; lia ]).
  Qed.

  Lemma ll1_dry : forall s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> L1REG s r R -> RINV (cv_NI v) (cv_NO v) r ->
    0 <= is_have s < is_ncode s -> is_ncode s <= 19 -> ir_bits r < 3 -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f75c) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom) /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros s c r R M HM HRC HJ RI Hh Hn Hb Hhv. open_l1 HJ. open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. unfold mapped in *. unfold A6_ORDER in G10.
    arm_symexP (@nil (Z * expr)) ilL1 12%nat [false; false] [RVal (EVar 48%nat); RVal (EVar 35%nat)] l1pins (l1vb ++ [(48%nat, 2 ^ 64)]) v r
      [2 * is_have s; is_have s; is_ncode s; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f75c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTL1DRY" G end.
    exists R1. split; [by_run Hms|].
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. rewrite Hhv.
    repeat match goal with |- _ /\ _ => split end;
      first [ assumption
            | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
            | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption | apply zw_neg_mod | f_equal; lia] end
            | match goal with |- ?G => idtac "L1DRY LEFT" G end ].
  Qed.

  Ltac open_freg HJ :=
    let X := fresh in pose proof HJ as X; unfold FREG in X;
    destruct X as (HF & G9 & G22 & G18 & G10 & G12 & G14 & G17); open_fixa HF.

  Lemma ll1_body : forall s c r1 R M,
    is_mode s = LENLENS -> LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> L1REG s r1 R -> RINV (cv_NI v) (cv_NO v) r1 ->
    0 <= is_have s < is_ncode s -> is_ncode s <= 19 -> arr_len (is_lens s) = 320 -> 3 <= ir_bits r1 ->
    let s' := ll1_s s (ir_hold r1) in let r2 := cdrop r1 3 in
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f794) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ LMEM v (mkW s' c r2) M' /\ RETC v (mkW s' c r2) M' /\ MFRAME v (ir_put r1) (ir_put r1) M M'
      /\ (if is_have s + 1 =? is_ncode s then pc' = 0x1f7fc /\ FREG s' r2 R' else pc' = 0x1f75c /\ L1REG s' r2 R').
  Proof.
    intros s c r1 R M Hmode HM HRC HJ RI Hh Hn Halen Hb. cbv zeta. open_l1 HJ. open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. unfold mapped in *.
    unfold A6_ORDER in G10.
    pose proof (cell_nlens _ _ _ Fnlens) as Fnl. clear Fnlens.
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (order_range (is_have s) ltac:(lia)) as Hor.
    pose proof (is6_have _ _ _ _ Msc) as C140.
    assert (Es' : ll1_s s (ir_hold r1) = iset_lens (iset_have s (is_have s + 1)) (arr_set (is_lens s) (arr_get order_a (is_have s)) (wrap16 (BITSv (ir_hold r1) 3))))
      by (apply ll1_s_alt; clear - Hh Hn; lia).
    assert (Hh32 : 0 <= is_have s + 1 < 2 ^ 32) by (clear - Hh Hn; lia).
    pose proof (BITSv3 (ir_hold r1) (proj1 Rhold)) as EB3.
    assert (Hb3 : 0 <= ir_hold r1 mod 2 ^ 3 < 8) by (apply Z.mod_pos_bound; lia).
    assert (POST : forall R' (pc : Z),
      (forall rg, reg_in rg [5%bv; 6%bv; 7%bv; 15%bv; 17%bv; 19%bv; 25%bv] = false -> getr R' rg = getr R rg) ->
      getr R' 19 = zw (szwrap 32 (ir_bits r1 + -3)) -> getr R' 25 = zw (ir_hold r1 / 2 ^ 3) ->
      let M' := wbytes (wbytes M (zw (cv_S v + 156)) (Z_to_le_bytes 4 (is_have s + 1)))
                       (zw (cv_S v + arr_get order_a (is_have s) * 2 ^ 1 + 168)) (Z_to_le_bytes 2 (ir_hold r1 mod 2 ^ 3)) in
      LMEM v (mkW (ll1_s s (ir_hold r1)) c (cdrop r1 3)) M' /\ RETC v (mkW (ll1_s s (ir_hold r1)) c (cdrop r1 3)) M'
      /\ MFRAME v (ir_put r1) (ir_put r1) M M' /\ LFIXa R'
      /\ getr R' 9 = zw (cv_P0 v + ir_put (cdrop r1 3)) /\ getr R' 25 = zw (ir_hold (cdrop r1 3)) /\ getr R' 19 = zw (ir_bits (cdrop r1 3))
      /\ getr R' 10 = zw A6_ORDER /\ getr R' 12 = zw (ir_have (cdrop r1 3)) /\ getr R' 14 = zw (cv_I0 v + ir_next (cdrop r1 3))).
    { intros R' pc Hfr Q18 Q22. cbv zeta.
      set (M1 := wbytes M (zw (cv_S v + 156)) (Z_to_le_bytes 4 (is_have s + 1))).
      set (s1 := iset_have s (is_have s + 1)).
      assert (HM1 : LMEM v (mkW s1 c r1) M1).
      { apply (LMEM_store_scalar v C s c r1 _ M 156 _ HM); [lia | cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_have M (cv_S v) _ s (is_have s + 1) Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM2 : LMEM v (mkW (iset_lens s1 (arr_set (is_lens s1) (arr_get order_a (is_have s)) (wrap16 (BITSv (ir_hold r1) 3)))) c r1)
                           (wbytes M1 (zw (cv_S v + 168 + 2 * arr_get order_a (is_have s))) (Z_to_le_bytes 2 (ir_hold r1 mod 2 ^ 3)))).
      { apply (LMEM_store_lens v C s1 c r1 M1 _ _ (BITSv (ir_hold r1) 3) HM1 Hput); [clear - Hor; lia | subst s1; destruct s; exact Halen | rewrite EB3; apply le2_wrap16]. }
      replace (iset_lens s1 (arr_set (is_lens s1) (arr_get order_a (is_have s)) (wrap16 (BITSv (ir_hold r1) 3)))) with (ll1_s s (ir_hold r1)) in HM2
        by (rewrite Es'; subst s1; destruct s; reflexivity).
      replace (zw (cv_S v + 168 + 2 * arr_get order_a (is_have s))) with (zw (cv_S v + arr_get order_a (is_have s) * 2 ^ 1 + 168)) in HM2 by (f_equal; lia).
      split; [apply (LMEM_regs v _ c r1 c (cdrop r1 3) _ HM2); reflexivity|].
      split.
      { apply (RETC_regs v (mkW s c r1)); [| reflexivity].
        apply (RETC_other v C); [| clear - CS Hor; lia | clear - CS Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold sep in CfS; clear - CfS CS Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
        apply (RETC_other v C); [exact HRC | clear - CS; lia | clear - CS; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold sep in CfS; clear - CfS CS; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia]. }
      split.
      { apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS Hor; lia | clear - CS Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia | right; left; clear - Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia | right; left; clear; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia]. }
      unfold LFIXa, INF_FRAME, cdrop; cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
      repeat match goal with |- _ /\ _ => split end;
        first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); first [assumption | unfold A6_ORDER; assumption] end
              | rewrite Q22; rewrite Z.shiftr_div_pow2 by lia; reflexivity
              | rewrite Q18; rewrite szwrap32_small by (clear - Rbits Hb; lia); rewrite wrap32_id by (clear - Rbits Hb; lia); f_equal; lia
              | match goal with |- ?G => idtac "L1POST LEFT" G end ]. }
    destruct (Z.eqb_spec (is_have s + 1) (is_ncode s)) as [Elast|Nlast].
    - arm_symexP (@nil (Z * expr)) ilL1 30%nat [true; true; true; false]
        [RVal (EVar 48%nat); RVal (ESub (ELit 18446744073709551447) (EVar 33%nat)); RVal (EAdd (EVar 33%nat) (ELit 168))]
        l1pins (l1vb ++ [(48%nat, 19)]) v r1 [2 * is_have s; is_have s; is_ncode s; arr_get order_a (is_have s)] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f794) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: try order_read.
      all: try (rewrite lxor_m1_mod64 by lia; lia).
      all: try (apply bnd19_side; lia).
      all: try (apply ne1_side; lia).
      all: try (unfold A6_ORDER in *; off_side).
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTL1B1" G end.
      symex_reg HR' (19%bv : reg) as Q18. symex_reg HR' (25%bv : reg) as Q22. symex_reg HR' (17%bv : reg) as Q17.
      assert (HfrW : forall rg, reg_in rg [5%bv; 6%bv; 7%bv; 15%bv; 17%bv; 19%bv; 25%bv] = false -> getr R' rg = getr R rg) by (fr_weak Hfr).
      destruct (POST R' 0 HfrW Q18 Q22) as (HM' & HRC' & MF' & HF' & P9 & P22 & P18 & P10 & P12 & P14).
      eexists R', _, 0x1f7fc. split; [by_run Hms|]. split; [exact HM'|]. split; [exact HRC'|]. split; [exact MF'|]. split; [reflexivity|].
      unfold FREG. split; [exact HF'|]. split; [exact P9|]. split; [exact P22|]. split; [exact P18|]. split; [exact P10|]. split; [exact P12|]. split; [exact P14|].
      rewrite Q17. unfold ll1_s. destruct s; cbn; rewrite wrap32_id by exact Hh32. f_equal. cbn in Elast. lia.
    - arm_symexP (@nil (Z * expr)) ilL1 30%nat [true; true; true; true]
        [RVal (EVar 48%nat); RVal (ESub (ELit 18446744073709551447) (EVar 33%nat)); RVal (EAdd (EVar 33%nat) (ELit 168))]
        l1pins (l1vb ++ [(48%nat, 19)]) v r1 [2 * is_have s; is_have s; is_ncode s; arr_get order_a (is_have s)] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f794) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: try order_read.
      all: try (rewrite lxor_m1_mod64 by lia; lia).
      all: try (apply bnd19_side; lia).
      all: try (apply ne1_side; lia).
      all: try (unfold A6_ORDER in *; off_side).
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTL1B2" G end.
      symex_reg HR' (19%bv : reg) as Q18. symex_reg HR' (25%bv : reg) as Q22. symex_reg HR' (15%bv : reg) as Q15. symex_reg HR' (17%bv : reg) as Q17.
      assert (HfrW : forall rg, reg_in rg [5%bv; 6%bv; 7%bv; 15%bv; 17%bv; 19%bv; 25%bv] = false -> getr R' rg = getr R rg) by (fr_weak Hfr).
      destruct (POST R' 0 HfrW Q18 Q22) as (HM' & HRC' & MF' & HF' & P9 & P22 & P18 & P10 & P12 & P14).
      eexists R', _, 0x1f75c. split; [by_run Hms|]. split; [exact HM'|]. split; [exact HRC'|]. split; [exact MF'|]. split; [reflexivity|].
      unfold L1REG. split; [exact HF'|]. split; [exact P9|]. split; [exact P22|]. split; [exact P18|]. split; [exact P10|].
      split; [rewrite (Hfr (11%bv : reg) eq_refl), G11; unfold ll1_s; destruct s; reflexivity|].
      split; [exact P12|]. split; [rewrite (Hfr (13%bv : reg) eq_refl); exact G13|]. split; [exact P14|].
      rewrite Q15, Q17, (Hfr (16%bv : reg) eq_refl), G16.
      unfold ll1_s; destruct s; cbn; rewrite wrap32_id by exact Hh32. cbn in Nlast, Hh32.
      repeat split; f_equal; lia.
  Qed.

  Definition l1post (w : iw) (M : word -> option byte) (res : ares unit) (R' : bvmap 5 word) (M' : word -> option byte) (pc' : Z) : Prop :=
    match res with
    | ARun _ w' => pc' = 0x1f7fc /\ is_mode (w_s w') = LENLENS /\ is_have (w_s w') = is_ncode (w_s w')
                   /\ FREG (w_s w') (w_r w') R' /\ LMEM v w' M' /\ RETC v w' M' /\ LX v w'
                   /\ pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) w'
                   /\ same_blocks (w_s w) (w_s w') /\ MFRAME v (ir_put (w_r w)) (ir_put (w_r w')) M M'
    | ALeave w' => arm_post v w M (ALeave w') R' M' pc'
    | ARet _ _ => False
    end.

  Lemma l1post_chain : forall w0 w1 M0 M1 res R' M' pc',
    same_blocks (w_s w0) (w_s w1) -> MFRAME v (ir_put (w_r w0)) (ir_put (w_r w1)) M0 M1 ->
    l1post w1 M1 res R' M' pc' -> l1post w0 M0 res R' M' pc'.
  Proof.
    intros w0 w1 M0 M1 res R' M' pc' HS HF H. destruct res as [u w'|w'|rc w']; cbn [l1post] in *; [| | exact H].
    - destruct H as (A & B & B' & G & HM & HRC & HX & HP & SB & MF).
      split; [exact A|]. split; [exact B|]. split; [exact B'|]. split; [exact G|]. split; [exact HM|]. split; [exact HRC|].
      split; [exact HX|]. split; [exact HP|]. split; [exact (same_blocks_trans _ _ _ HS SB) | exact (MFRAME_trans v _ _ _ _ _ _ HF MF)].
    - exact (arm_post_chain v w0 w1 M0 M1 _ _ _ _ HS HF H).
  Qed.

  Lemma lenlens_facts : forall s c r,
    pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> is_mode s = LENLENS ->
    4 <= is_ncode s <= 19 /\ 0 <= is_have s <= 19 /\ arr_len (is_lens s) = 320
    /\ RINV (cv_NI v) (cv_NO v) r /\ CINV (cv_NI v) (cv_NO v) c.
  Proof.
    intros s c r HP Hmode. open_pinv HP.
    destruct PS as (_ & _ & (Alens & _ & _) & _ & QL & _). destruct (QL Hmode) as (QN & QD & QC & QH & _).
    split; [exact QC|]. split; [exact QH|]. split; [exact Alens|]. split; [exact RI | exact CI].
  Qed.
  Lemma ll1_trip : forall s c r R M,
    is_mode s = LENLENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> is_have s < is_ncode s ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> L1REG s r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f75c) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ ((exists r1, NEEDBITS 3 (mkW s c r) = ARun tt (mkW s c r1)
             /\ LMEM v (mkW (ll1_s s (ir_hold r1)) c (cdrop r1 3)) M' /\ RETC v (mkW (ll1_s s (ir_hold r1)) c (cdrop r1 3)) M'
             /\ LX v (mkW (ll1_s s (ir_hold r1)) c (cdrop r1 3)) /\ pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW (ll1_s s (ir_hold r1)) c (cdrop r1 3))
             /\ is_mode (ll1_s s (ir_hold r1)) = LENLENS /\ is_have (ll1_s s (ir_hold r1)) = is_have s + 1 /\ is_ncode (ll1_s s (ir_hold r1)) = is_ncode s
             /\ same_blocks s (ll1_s s (ir_hold r1)) /\ MFRAME v (ir_put r) (ir_put (cdrop r1 3)) M M'
             /\ (if is_have s + 1 =? is_ncode s then pc' = 0x1f7fc /\ FREG (ll1_s s (ir_hold r1)) (cdrop r1 3) R'
                 else pc' = 0x1f75c /\ L1REG (ll1_s s (ir_hold r1)) (cdrop r1 3) R'))
          \/ (NEEDBITS 3 (mkW s c r) = ALeave (mkW s c r) /\ M' = M /\ pc' = pc6_leave /\ LREG_leave v (mkW s c r) R')).
  Proof.
    pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0.
    intros s c r R M Hmode HP Hlt HM HRC HX HJ.
    destruct (lenlens_facts s c r HP Hmode) as (Hnc & Hhv & Halen & RI & CI).
    pose proof RI as RI0. open_rinv RI0.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (HEAD : exists R1 res, NEEDBITS 3 (mkW s c r) = res /\
              match res with
              | ARun _ w1 => exists r1, w1 = mkW s c r1 /\ RINV (cv_NI v) (cv_NO v) r1 /\ 3 <= ir_bits r1 /\ same5 r r1
                  /\ msteps s6u_segs (mkst R (Z_to_bv 64 0x1f75c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f794) M s6u_rom) /\ L1REG s r1 R1
              | ALeave w1 => w1 = mkW s c r /\ ir_bits r < 3
                  /\ msteps s6u_segs (mkst R (Z_to_bv 64 0x1f75c) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom) /\ LREG_leave v (mkW s c r) R1
              | ARet _ _ => False
              end).
    { destruct (Z_lt_le_dec (ir_bits r) 3) as [LT|GE].
      - unfold NEEDBITS. rewrite NEEDBITS_k_S. replace (ir_bits r <? 3) with true by (symmetry; apply Z.ltb_lt; exact LT).
        destruct (Z.eqb_spec (ir_have r) 0) as [Hz|Hz].
        + destruct (ll1_dry s c r R M HM HRC HJ RI ltac:(lia) ltac:(lia) LT Hz) as (R1 & Hms1 & HL1).
          exists R1, (ALeave (mkW s c r)). split; [reflexivity|]. split; [reflexivity|]. split; [exact LT|]. split; [exact Hms1 | exact HL1].
        + destruct (pull1_RINV (cv_NI v) (cv_NO v) s c r ltac:(lia) ltac:(lia) RI CI ltac:(lia) ltac:(lia)) as [Ep HR1].
          rewrite Ep. rewrite NEEDBITS_k_done by (cbn; lia).
          destruct (ll1_pull s c r R M HM HJ RI CI ltac:(lia) ltac:(lia) LT ltac:(lia)) as (R1 & Hms1 & HJ1).
          exists R1, (ARun tt (mkW s c (pull1 c r))). split; [reflexivity|]. exists (pull1 c r).
          split; [reflexivity|]. split; [exact HR1|]. split; [cbn; lia|]. split; [repeat split; reflexivity|]. split; [exact Hms1 | exact HJ1].
      - unfold NEEDBITS. rewrite NEEDBITS_k_done by exact GE.
        destruct (ll1_go s c r R M HJ RI ltac:(lia) ltac:(lia) GE) as (R1 & Hms1 & HJ1).
        exists R1, (ARun tt (mkW s c r)). split; [reflexivity|]. exists r.
        split; [reflexivity|]. split; [exact RI|]. split; [exact GE|]. split; [repeat split; reflexivity|]. split; [exact Hms1 | exact HJ1]. }
    destruct HEAD as (R1 & res & HN & HRES). destruct res as [u w1 | w1 | rc w1]; [| | destruct HRES].
    -
      destruct u. destruct HRES as (r1 & -> & RI1 & Hb1 & S5 & Hms1 & HJ1). destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
      destruct (ll1_pinv_step (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) ltac:(lia) ltac:(lia) s c r r1 HP Hmode Hlt HN) as [HP2 _].
      assert (HM1 : LMEM v (mkW s c r1) M) by (apply (LMEM_regs v s c r c r1 M HM); first [exact Q1 | exact Q4 | exact Q2 | reflexivity]).
      assert (HRC1 : RETC v (mkW s c r1) M) by (eapply RETC_regs; [exact HRC | cbn; exact Q5]).
      pose proof (ll1_s_fields s (ir_hold r1)) as (Fm & Fn & Fh & Fl & Fsb).
      destruct (ll1_body s c r1 R1 M Hmode HM1 HRC1 HJ1 RI1 ltac:(lia) ltac:(lia) Halen Hb1) as (R2 & M2 & pc2 & Hms2 & HM2 & HRC2 & MF2 & HK).
      assert (HX2 : LX v (mkW (ll1_s s (ir_hold r1)) c (cdrop r1 3))).
      { open_lx HX. apply (LX_step0 v s c r _ c _ HX NH NB); try (destruct s; reflexivity).
        - rewrite Fm. exact Xlive.
        - unfold cdrop; cbn [ir_in irset_bits irset_hold]. exact Q3.
        - unfold cdrop; cbn [ir_ret irset_bits irset_hold]. rewrite Q5. exact Xret.
        - exact Xmsg.
        - rewrite Fm. replace (is_back (ll1_s s (ir_hold r1))) with (is_back s) by (unfold ll1_s; destruct s; reflexivity). exact Xbk. }
      exists R2, M2, pc2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      left. exists r1. split; [exact HN|]. split; [exact HM2|]. split; [exact HRC2|]. split; [exact HX2|]. split; [exact HP2|].
      split; [rewrite Fm; exact Hmode|]. split; [rewrite Fh; apply wrap32_id; lia|]. split; [exact Fn|]. split; [exact Fsb|].
      split; [rewrite <- Q1; unfold cdrop; cbn [ir_put irset_bits irset_hold]; exact MF2 | exact HK].
    -
      destruct HRES as (-> & Hb0 & Hms1 & HL1).
      exists R1, M, pc6_leave. split; [exact Hms1|]. right. split; [exact HN|]. split; [reflexivity|]. split; [reflexivity | exact HL1].
  Qed.

  Lemma ll1_loop : forall k s c r R M,
    is_mode s = LENLENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
    is_have s < is_ncode s -> is_ncode s - is_have s <= Z.of_nat (S k) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> L1REG s r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f75c) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ l1post (mkW s c r) M (lenlens_while1 (S k) (mkW s c r)) R' M' pc'.
  Proof.
    induction k as [|k IH]; intros s c r R M Hmode HP Hlt Hk HM HRC HX HJ.
    - destruct (ll1_trip s c r R M Hmode HP Hlt HM HRC HX HJ) as (R2 & M2 & pc2 & Hms & [(r1 & HN & HM2 & HRC2 & HX2 & HP2 & Fm & Fh & Fn & Fsb & MF2 & HK) | (HN & -> & -> & HL)]).
      + rewrite (ll1_step_run 0 s c r r1 Hlt HN).
        destruct (Z.eqb_spec (is_have s + 1) (is_ncode s)) as [EL|EL]; [| exfalso; cbn in Hk; lia].
        destruct HK as [-> HF2]. rewrite (ll1_done 0) by (rewrite Fn, Fh; lia).
        exists R2, M2, 0x1f7fc. split; [exact Hms|].
        cbn [l1post w_s w_r]. split; [reflexivity|]. split; [exact Fm|]. split; [rewrite Fh, Fn; exact EL|].
        split; [exact HF2|]. split; [exact HM2|]. split; [exact HRC2|]. split; [exact HX2|]. split; [exact HP2|]. split; [exact Fsb | exact MF2].
      + rewrite (ll1_step_leave 0 s c r _ Hlt HN).
        exists R2, M, pc6_leave. split; [exact Hms|].
        cbn [l1post arm_post w_r]. split; [reflexivity|]. split; [| apply MFRAME_refl].
        split; [exact HM|]. split; [exact HX|]. split; [apply same_blocks_refl | exact HL].
    - destruct (ll1_trip s c r R M Hmode HP Hlt HM HRC HX HJ) as (R2 & M2 & pc2 & Hms & [(r1 & HN & HM2 & HRC2 & HX2 & HP2 & Fm & Fh & Fn & Fsb & MF2 & HK) | (HN & -> & -> & HL)]).
      + rewrite (ll1_step_run (S k) s c r r1 Hlt HN).
        destruct (Z.eqb_spec (is_have s + 1) (is_ncode s)) as [EL|EL].
        * destruct HK as [-> HF2]. rewrite (ll1_done (S k)) by (rewrite Fn, Fh; lia).
          exists R2, M2, 0x1f7fc. split; [exact Hms|].
          cbn [l1post w_s w_r]. split; [reflexivity|]. split; [exact Fm|]. split; [rewrite Fh, Fn; exact EL|].
          split; [exact HF2|]. split; [exact HM2|]. split; [exact HRC2|]. split; [exact HX2|]. split; [exact HP2|]. split; [exact Fsb | exact MF2].
        * destruct HK as [-> HJ2].
          destruct (IH (ll1_s s (ir_hold r1)) c (cdrop r1 3) R2 M2 Fm HP2 ltac:(rewrite Fh, Fn; lia) ltac:(rewrite Fh, Fn; cbn in Hk |- *; lia) HM2 HRC2 HX2 HJ2)
            as (R' & M' & pc' & Hms3 & HPOST).
          exists R', M', pc'. split; [eapply msteps_trans; [exact Hms | exact Hms3]|].
          exact (l1post_chain (mkW s c r) (mkW (ll1_s s (ir_hold r1)) c (cdrop r1 3)) M M2 _ _ _ _ Fsb MF2 HPOST).
      + rewrite (ll1_step_leave (S k) s c r _ Hlt HN).
        exists R2, M, pc6_leave. split; [exact Hms|].
        cbn [l1post arm_post w_r]. split; [reflexivity|]. split; [| apply MFRAME_refl].
        split; [exact HM|]. split; [exact HX|]. split; [apply same_blocks_refl | exact HL].
  Qed.
End L1.
End FXG.
End InflA_Lenlens1.
Export InflA_Lenlens1.

Module InflA_Lenlens2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvDec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvArms5.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflNeed6.
Import InflA_Cl1.InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import InflA_ClS.InflA_LenlensS.
Import InflA_Cl1.InflA_Codelens3.
Import InflA_Lenlens1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition ilL2 : cfg := ilSx [0x1f818; 0x1f860] [].

Section L2.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition TREG (r : iregs) (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 18 = zw (cv_ZP v)
    /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4
    /\ LVR v r R /\ getr R 26 = zw (cv_I0 v + ir_next r).

  Lemma ll2_fill : forall k s c r R M i,
    Z.of_nat k = 19 - i -> 0 <= i <= 18 -> arr_len (is_lens s) = 320 ->
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    getr R 2 = zw (cv_sp v - 256) -> getr R 8 = zw (cv_S v) -> getr R 10 = zw A6_ORDER -> getr R 11 = zw (2 * i) -> getr R 12 = zw (A6_ORDER + 2 * i) ->
    exists R' M',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f818) M s6u_rom) (mkst R' (Z_to_bv 64 0x1f860) M' s6u_rom)
      /\ LMEM v (mkW (iset_have (iset_lens s (fillo (is_lens s) i k)) 19) c r) M'
      /\ (forall rg, reg_in rg [10; 11; 12; 13; 14; 16]%bv = false -> getr R' rg = getr R rg)
      /\ MFRAME v (ir_put r) (ir_put r) M M'
      /\ (forall w0, RETC v w0 M -> RETC v w0 M').
  Proof.
    induction k as [|k IH]; intros s c r R M i Hk Hi Halen HM Hput G2 G27 G10 G11 G12; [lia|].
    open_ictx C. open_lmem HM. open_frame Mfr. unfold mapped in *. unfold A6_ORDER in G10, G12.
    pose proof (cell_nlens _ _ _ Fnlens) as Fnl. clear Fnlens.
    pose proof (order_range i ltac:(lia)) as Hor.
    destruct (Z.eq_dec i 18) as [Elast|Nlast].
    -
      assert (K0 : k = 0%nat) by lia. subst k.
      symex s6u_segs ilL2 20%nat [true; true; false] [RVal (EVar 35%nat); RVal (ESub (ELit 18446744073709551447) (EVar 33%nat)); RVal (EAdd (EVar 33%nat) (ELit 168))]
        [(2, EVar 32%nat); (8, EVar 33%nat); (10, ELit 75148); (11, EVar 34%nat); (12, EAdd (ELit 75148) (EVar 34%nat))]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 38); (35%nat, 19)]
        NoRegions [cv_sp v - 256; cv_S v; 2 * i; arr_get order_a i] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x1f818) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: try order_read.
      all: try (rewrite lxor_m1_mod64 by lia; lia).
      all: try (unfold A6_ORDER in *; off_side).
      all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFTL2A" G end.
      set (M1 := wbytes M (zw (cv_S v + arr_get order_a i * 2 ^ 1 + 168)) (Z_to_le_bytes 2 0)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 156)) (Z_to_le_bytes 4 19)) in *.
      set (s1 := iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)).
      assert (HM1 : LMEM v (mkW s1 c r) M1).
      { subst M1 s1. replace (zw (cv_S v + arr_get order_a i * 2 ^ 1 + 168)) with (zw (cv_S v + 168 + 2 * arr_get order_a i)) by (f_equal; lia).
        replace (arr_set (is_lens s) (arr_get order_a i) 0) with (arr_set (is_lens s) (arr_get order_a i) (wrap16 0)) by reflexivity.
        apply (LMEM_store_lens v C s c r M (arr_get order_a i) 0 0 HM Hput); [clear - Hor; lia | exact Halen | reflexivity]. }
      assert (HM2 : LMEM v (mkW (iset_have s1 19) c r) M2).
      { apply (LMEM_store_scalar v C s1 c r _ M1 156 _ HM1); [lia | cbn; lia | exact Hput | | subst s1; destruct s; reflexivity | subst s1; destruct s; reflexivity | subst s1; destruct s; reflexivity | subst s1; destruct s; reflexivity].
        apply (is6_upd_have M1 (cv_S v) _ s1 19 (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      exists R', M2. split; [subst M2 M1; by_run Hms|].
      split; [subst i; cbn [fillo]; subst s1; exact HM2|].
      split; [fr_weak Hfr|].
      subst M2 M1. split.
      { apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS Hor; lia | clear - CS Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia | right; left; clear - Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia]. }
      intros w0 H0.
      apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
      apply (RETC_other v C); [exact H0 | clear - CS Hor; lia | clear - CS Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold sep in CfS; clear - CfS CS Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
    -
      symex s6u_segs ilL2 20%nat [true; true; true] [RVal (EVar 35%nat); RVal (ESub (ELit 18446744073709551447) (EVar 33%nat)); RVal (EAdd (EVar 33%nat) (ELit 168))]
        [(2, EVar 32%nat); (8, EVar 33%nat); (10, ELit 75148); (11, EVar 34%nat); (12, EAdd (ELit 75148) (EVar 34%nat))]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 38); (35%nat, 19)]
        NoRegions [cv_sp v - 256; cv_S v; 2 * i; arr_get order_a i] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x1f818) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: try order_read.
      all: try (rewrite lxor_m1_mod64 by lia; lia).
      all: try (unfold A6_ORDER in *; off_side).
      all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFTL2B" G end.
      set (M1 := wbytes M (zw (cv_S v + arr_get order_a i * 2 ^ 1 + 168)) (Z_to_le_bytes 2 0)) in *.
      set (s1 := iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)).
      assert (HM1 : LMEM v (mkW s1 c r) M1).
      { subst M1 s1. replace (zw (cv_S v + arr_get order_a i * 2 ^ 1 + 168)) with (zw (cv_S v + 168 + 2 * arr_get order_a i)) by (f_equal; lia).
        replace (arr_set (is_lens s) (arr_get order_a i) 0) with (arr_set (is_lens s) (arr_get order_a i) (wrap16 0)) by reflexivity.
        apply (LMEM_store_lens v C s c r M (arr_get order_a i) 0 0 HM Hput); [clear - Hor; lia | exact Halen | reflexivity]. }
      symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (12%bv : reg) as Q12.
      destruct (IH s1 c r R1 M1 (i + 1) ltac:(lia) ltac:(lia) ltac:(subst s1; destruct s; cbn; rewrite arr_len_set; exact Halen) HM1 Hput
                  ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2) ltac:(rewrite (Hfr1 (8%bv : reg) eq_refl); exact G27)
                  ltac:(rewrite (Hfr1 (10%bv : reg) eq_refl); unfold A6_ORDER; exact G10)
                  ltac:(rewrite Q11; f_equal; lia) ltac:(rewrite Q12; unfold A6_ORDER; f_equal; lia))
        as (R' & M' & Hms2 & HM' & Hfr' & MF' & RC').
      exists R', M'. split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms1|].
      split.
      { replace (fillo (is_lens s) i (S k)) with (fillo (is_lens s1) (i + 1) k) by (subst s1; destruct s; reflexivity).
        replace (iset_lens s (fillo (is_lens s1) (i + 1) k)) with (iset_lens s1 (fillo (is_lens s1) (i + 1) k)) by (subst s1; destruct s; reflexivity).
        exact HM'. }
      split; [intros rg Hrg; rewrite (Hfr' rg Hrg); apply Hfr1; eapply reg_in_sub; [| exact Hrg]; reflexivity|].
      subst M1. split.
      { apply (MFRAME_trans v (ir_put r) (ir_put r) (ir_put r) M (wbytes M (zw (cv_S v + arr_get order_a i * 2 ^ 1 + 168)) (Z_to_le_bytes 2 0)) M'); [| exact MF'].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS Hor; lia | clear - CS Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia | right; left; clear - Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia]. }
      intros w0 H0. apply RC'.
      apply (RETC_other v C); [exact H0 | clear - CS Hor; lia | clear - CS Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold sep in CfS; clear - CfS CS Hor; cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  Qed.

  Lemma ll2_seg : forall s c r R M,
    is_mode s = LENLENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> is_ncode s <= is_have s ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> FREG v s r R ->
    let s2 := iset_have (iset_lens s (fillo (is_lens s) (is_have s) (Z.to_nat (19 - is_have s)))) 19 in
    exists R' M',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f7fc) M s6u_rom) (mkst R' (Z_to_bv 64 0x1f860) M' s6u_rom)
      /\ LMEM v (mkW s2 c r) M' /\ RETC v (mkW s2 c r) M' /\ TREG r R' /\ MFRAME v (ir_put r) (ir_put r) M M'.
  Proof.
    intros s c r R M Hmode HP Hge HM HRC HR. cbv zeta.
    destruct (lenlens_facts v s c r HP Hmode) as (Hnc & Hhv & Halen & RI & CI).
    pose proof HR as HR0. unfold FREG, LFIXa, INF_FRAME in HR. destruct HR as ((G2 & G27 & G8 & G1 & G3 & G4) & G9 & G22 & G18 & G10 & G12 & G14 & G17). unfold A6_ORDER in G10.
    open_ictx C. pose proof HM as HM0. open_lmem HM. open_rinv RI. unfold mapped in *.
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    destruct (Z_lt_le_dec 18 (is_have s)) as [H19|H18].
    -
      arm_symexP (@nil (Z * expr)) ilL2 8%nat [true] (@nil (option expr))
        [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat);
         (10, ELit 75148); (12, EVar 36%nat); (14, EAdd (EVar 43%nat) (EVar 44%nat)); (17, EVar 45%nat)]
        [(45%nat, 32)] v r [is_have s] NoVals F0
        (mkst R (Z_to_bv 64 0x1f7fc) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFTL2S1" G end.
      assert (E19 : is_have s = 19) by lia.
      replace (iset_have (iset_lens s (fillo (is_lens s) (is_have s) (Z.to_nat (19 - is_have s)))) 19) with s
        by (rewrite E19; change (Z.to_nat (19 - 19)) with 0%nat; cbn [fillo]; rewrite <- E19; destruct s; reflexivity).
      exists R1, M. split; [by_run Hms1|]. split; [exact HM0|]. split; [exact HRC|]. split; [| apply MFRAME_refl].
      unfold TREG, LVR, INF_FRAME.
      repeat match goal with |- _ /\ _ => split end;
        first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
              | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption | f_equal; lia] end
              | match goal with |- ?G => idtac "TREG1 LEFT" G end ].
    -
      arm_symexP (@nil (Z * expr)) ilL2 12%nat [false] (@nil (option expr))
        [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat);
         (10, ELit 75148); (12, EVar 36%nat); (14, EAdd (EVar 43%nat) (EVar 44%nat)); (17, EVar 45%nat)]
        [(45%nat, 32)] v r [is_have s] NoVals F0
        (mkst R (Z_to_bv 64 0x1f7fc) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFTL2S2" G end.
      symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (12%bv : reg) as Q12.
      destruct (ll2_fill (Z.to_nat (19 - is_have s)) s c r R1 M (is_have s) ltac:(lia) ltac:(lia) Halen HM0 Hput
                  ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2) ltac:(rewrite (Hfr1 (8%bv : reg) eq_refl); exact G27)
                  ltac:(rewrite (Hfr1 (10%bv : reg) eq_refl); unfold A6_ORDER; exact G10)
                  ltac:(rewrite Q11; f_equal; lia) ltac:(rewrite Q12; unfold A6_ORDER; f_equal; lia))
        as (R' & M' & Hms2 & HM' & Hfr' & MF' & RC').
      exists R', M'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
      split; [exact HM'|]. split; [apply RC'; exact HRC|]. split; [| exact MF'].
      unfold TREG, LVR, INF_FRAME.
      repeat match goal with |- _ /\ _ => split end;
        (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr' n eq_refl) end;
         first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
               | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption | f_equal; lia] end
               | match goal with |- ?G => idtac "TREG2 LEFT" G end ]).
  Qed.
End L2.
End FXG.
End InflA_Lenlens2.
Export InflA_Lenlens2.
Module InflA_Lenlens3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InftreesCoverage.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ItCovIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvCov.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTbl.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvArms5.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Callee6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Match2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Dist3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.Callee6i.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflMem2.
Import InflA_Cl1.InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens3.
Import InflA_ClS.InflA_LenlensS.
Import InflA_Lenlens1.
Import InflA_Lenlens2.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma llt_facts_of_pinv : forall v s c r,
  is_mode s = LENLENS -> is_have s = 19 -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
  arr_len (is_lens s) = 320 /\ arr_len (is_work s) = 288 /\ arr_len (is_codes s) = 1444
  /\ (forall i, 0 <= i < 320 -> 0 <= arr_get (is_lens s) i < 65536)
  /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (is_work s) i < 65536)
  /\ (forall i, 0 <= i < 1444 -> 0 <= arr_get (is_codes s) i < 2 ^ 32)
  /\ (forall i, 0 <= i < 19 -> 0 <= arr_get (is_lens s) (0 + i) <= 7)
  /\ RINV (cv_NI v) (cv_NO v) r /\ CINV (cv_NI v) (cv_NO v) c /\ ir_ret r = 0.
Proof.
  intros v s c r Hmode H19 HP. open_pinv HP.
  destruct PS as (_ & _ & (Alens & Awork & Acodes) & _ & QLc & _). destruct (QLc Hmode) as (QN & QD & QC & QH & QL).
  pose proof SR as X. unfold SRNGq in X. do 26 (destruct X as [_ X]). destruct X as ((BL & BW & BC) & _).
  pose proof PX as XI'. unfold xinv in XI'. cbn [w_s w_c w_r] in XI'. destruct XI' as (XR & _).
  split; [exact Alens|]. split; [exact Awork|]. split; [exact Acodes|].
  split; [intros i Hi; pose proof (BL i Hi); lia|]. split; [intros i Hi; pose proof (BW i Hi); lia|]. split; [exact BC|].
  split; [intros i Hi; rewrite Z.add_0_l; destruct (order_cover i Hi) as (j & Hj & <-); apply QL; rewrite H19; exact Hj|].
  split; [exact RI|]. split; [exact CI|].
  destruct XR as [XR|XR]; [exact XR | rewrite Hmode in XR; cbv in XR; discriminate].
Qed.

Definition llB_res (flush : Z) (s1 : inflate_state) (c : icall) (r : iregs) (ret : Z) : ares unit :=
  if negb (ret =? 0) then ARun tt (mkW (iset_mode s1 BAD) (icset_msg c MSG_invalid_code_lengths_set) (irset_ret r ret))
  else arm_CODELENS ivar_ref flush (mkW (iset_mode (iset_have s1 0) CODELENS) c (irset_ret r ret)).

Definition HREGc (v : icv) (s : inflate_state) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
  LFIXc v R /\ LVARS v (mkW s c r) R.
Definition codelens_core_stmt (v : icv) : Prop :=
  forall s c r R M,
    is_mode s = CODELENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> HREGc v s c r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f8c0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_CODELENS ivar_ref (cv_flush v) (mkW s c r)) R' M' pc'.

End FXG.
Strategy expand [ll_call].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma ll_S1_alt : forall s (t : Z * arr * Z * Z * arr),
  iset_work (iset_codes (iset_next (if 136 =? 136 then iset_lenbits (iset_next (iset_lenbits (iset_distcode (iset_lencode s (CDyn 0)) (CDyn 0)) 7) 0) (it_bits t)
                                     else iset_distbits (iset_next (iset_lenbits (iset_distcode (iset_lencode s (CDyn 0)) (CDyn 0)) 7) 0) (it_bits t)) (it_table t)) (it_tbl t)) (it_work t)
  = ll_S1 s t.
Proof. intros s t. cbn [Z.eqb]. unfold ll_S1. destruct s; reflexivity. Qed.

Lemma MFRAME_itable : forall v p M M' pbo,
  ictx v -> 0 <= p -> (pbo = 136 \/ pbo = 140) -> (forall x, M x <> None -> M' x <> None) -> agree_out (ITF v pbo) M M' -> MFRAME v p p M M'.
Proof.
  intros v p M M' pbo C Hp Hpb Hg Hag. split; [lia|]. split; [exact Hg|].
  intros x N1 N2 N3 N4. apply Hag. unfold ITF, in_franges, INF_FRAME, INF_SCRATCH in *. clear - N1 N2 Hpb. lia.
Qed.

Definition ilCB : cfg := ilS.

Section SegT.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis ITABLE : itable_run6.
  Hypothesis CCORE : codelens_core_stmt v.

  Definition BREG (s : inflate_state) (c : icall) (r : iregs) (ret : Z) (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 18 = zw (cv_ZP v)
    /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4
    /\ LVARS v (mkW s c r) R /\ getr R 10 = zw ret.
  Definition bpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (19, EVar 41%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (10, EVar 45%nat)].

  Lemma llt_segB : forall s c r R M ret,
    is_mode s = LENLENS -> RINV (cv_NI v) (cv_NO v) r -> ir_ret r = 0 -> (ret = 0 \/ ret = 1 \/ ret = -1) ->
    (ret = 0 -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW (iset_mode (iset_have s 0) CODELENS) c (irset_ret r 0))) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> BREG s c r ret R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f894) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (llB_res (cv_flush v) s c r ret) R' M' pc'.
  Proof.
    intros s c r R M ret Hmode RI Hret0 Hret HPI HM HRC HX HR.
    destruct HR as (G2 & G27 & G8 & G3 & G4 & HV & G10). unfold INF_FRAME in G2.
    pose proof HV as X; unfold LVARS in X; cbn [w_r] in X; destruct X as (G24 & G9 & G22 & G18 & G25).
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. open_frame Mfr. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (Hrm : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    rewrite <- (zw_mod ret) in G10.
    unfold llB_res.
    destruct (Z.eq_dec ret 0) as [R0|R0].
    -
      subst ret. cbn [Z.eqb negb]. change (0 mod 2 ^ 64) with 0 in G10. specialize (HPI eq_refl).
      arm_symexP (@nil (Z * expr)) ilS 16%nat [true]
        [RVal (ELit 16209)]
        bpins [(45%nat, 1)] v r [0] NoVals F0
        (mkst R (Z_to_bv 64 0x1f894) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTTB1" G end.
      set (M1 := wbytes M (zw (cv_sp v - 256 + 64)) (Z_to_le_bytes 8 0)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16198)) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 156)) (Z_to_le_bytes 4 0)) in *.
      set (r' := irset_ret r 0) in *. set (sM := iset_mode s CODELENS). set (s' := iset_mode (iset_have s 0) CODELENS) in *.
      assert (Hput' : 0 <= ir_put r' <= cv_NO v) by (subst r'; exact Hput).
      assert (HM1 : LMEM v (mkW s c r') M1) by (apply (LMEM_store_fscratch v C s c r' M 64 _ (LMEM_regs v s c r c r' M HM eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) Hput'); split; [left; reflexivity | reflexivity]).
      assert (HM2 : LMEM v (mkW sM c r') M2).
      { apply (LMEM_store_scalar v C s c r' _ M1 8 _ HM1); [lia | cbn; lia | exact Hput' | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s CODELENS (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM3 : LMEM v (mkW s' c r') M3).
      { replace s' with (iset_have sM 0) by (subst s' sM; destruct s; reflexivity).
        apply (LMEM_store_scalar v C sM c r' _ M2 156 _ HM2); [lia | cbn; lia | exact Hput' | | subst sM; destruct s; reflexivity | subst sM; destruct s; reflexivity | subst sM; destruct s; reflexivity | subst sM; destruct s; reflexivity].
        apply (is6_upd_have M2 (cv_S v) _ sM 0 (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HRC3 : RETC v (mkW s' c r') M3).
      { subst M3 M2. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
        apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
        subst M1. exact (RETC_store v C s c r' M). }
      assert (HX3 : LX v (mkW s' c r')) by (apply (LX_step0 v s c r s' c r' HX NH NB); subst s' r'; try (destruct s; reflexivity); [live_mode_tac | cbn; lia | exact Xmsg | bk_side]).
      symex_reg HR1 (1%bv : reg) as Q1.
      assert (HH : HREGc v s' c r' R1).
      { unfold HREGc. split.
        - unfold LFIXc, INF_FRAME. regs_via Hfr1; first [exact Q1 | match goal with |- ?G => idtac "LFIXB LEFT" G end].
        - unfold LVARS; cbn [w_r]; subst r'; cbn. regs_via Hfr1; match goal with |- ?G => idtac "LVARSB LEFT" G end. }
      destruct (CCORE s' c r' R1 M3 ltac:(subst s'; destruct s; reflexivity) HPI HM3 HRC3 HX3 HH) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M3 M2 M1; by_run Hms1|].
      apply (arm_post_rebase v s c r c r'); [subst r'; reflexivity|].
      apply (arm_post_chain v (mkW s c r') (mkW s' c r') M M3); [subst s'; destruct s; split; [reflexivity | split; reflexivity] | | exact HPOST].
      cbn [w_r]. subst r'. cbn [ir_put irset_ret]. subst M3 M2 M1.
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
    -
      replace (negb (ret =? 0)) with true by (symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact R0).
      assert (Hrm0 : ret mod 2 ^ 64 <> 0).
      { intros E. apply R0. destruct Hret as [H|[H|H]]; subst ret; [reflexivity | discriminate E | discriminate E]. }
      arm_symexP (@nil (Z * expr)) ilCB 20%nat [false]
        [RVal (ELit 16209); RVal (EVar 35%nat)]
        bpins [(45%nat, 2 ^ 64)] v r [ret mod 2 ^ 64] NoVals F0
        (mkst R (Z_to_bv 64 0x1f894) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTTB2" G end.
      rewrite le8_mod64 in Hms1.
      set (r' := irset_ret r ret) in *. set (c' := icset_msg c MSG_invalid_code_lengths_set) in *. set (s' := iset_mode s BAD) in *.
      set (M1 := wbytes M (zw (cv_sp v - 256 + 64)) (Z_to_le_bytes 8 ret)) in *.
      set (M2 := wbytes M1 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 67148)) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      assert (Hput' : 0 <= ir_put r' <= cv_NO v) by (subst r'; exact Hput).
      assert (HM1 : LMEM v (mkW s c r') M1) by (apply (LMEM_store_fscratch v C s c r' M 64 _ (LMEM_regs v s c r c r' M HM eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) Hput'); split; [left; reflexivity | reflexivity]).
      assert (HM2 : LMEM v (mkW s c' r') M2) by (exact (LMEM_store_msg v C s c r' M1 MSG_invalid_code_lengths_set HM1 Hput')).
      assert (HM3 : LMEM v (mkW s' c' r') M3).
      { apply (LMEM_store_scalar v C s c' r' _ M2 8 _ HM2); [lia | cbn; lia | exact Hput' | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M2 (cv_S v) _ s BAD (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HRC3 : RETC v (mkW s' c' r') M3).
      { subst M3 M2. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
        apply (RETC_other v C); [| clear - CZP; lia | clear - CZP; cbn; lia | unfold sep in CfZ; clear - CfZ CZP; cbn; lia].
        exact (RETC_store v C s c r' M). }
      pose proof (icset_msg_facts c MSG_invalid_code_lengths_set) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      assert (HX3 : LX v (mkW s' c' r')).
      { apply (LX_step0 v s c r s' c' r' HX NH NB); subst s' c' r'; try reflexivity; [live_mode_tac | cbn; clear - Hret; lia | rewrite K11; unfold MSG_invalid_code_lengths_set; lia | bk_side]. }
      arm_disp C HM3 Hfr1 R2 Hms2 G26' Hfr2.
      exists R2, M3, (arm6_pc (is_mode s')). split.
      { eapply msteps_trans; [| exact Hms2]. subst M3 M2 M1. by_run Hms1. }
      replace (is_mode s') with BAD by (subst s'; destruct s; reflexivity).
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s'; apply same_blocks_mode |]].
      + split; [exact HM3|]. split; [exact HRC3|]. split; [exact HX3|].
        unfold LREG_arm. split; [lfix_close2 Hfr2 Hfr1 HR1 | split; [| intros _; exact G26']].
        unfold LVARS; cbn [w_r]. subst r'. cbn.
        repeat match goal with |- _ /\ _ => split end;
          first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr2 n eq_refl), (Hfr1 n eq_refl); assumption end
                | match goal with |- ?G => idtac "LVARS2 LEFT" G end ].
      + cbn [w_r]. subst r'. cbn [ir_put irset_ret]. subst M3 M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
  Qed.

  Definition tpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (19, EVar 41%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat))].

  Lemma llt_segA : forall s c r R M,
    is_mode s = LENLENS -> is_have s = 19 -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> TREG v r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f860) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (ll_after (cv_flush v) s c r) R' M' pc'.
  Proof.
    intros s c r R M Hmode H19 HP HM HRC HX HR.
    destruct (llt_facts_of_pinv v s c r Hmode H19 HP) as (Alens & Awork & Acodes & Blens & Bwork & Bcodes & L7 & RI & CI & Hret0).
    destruct HR as (G2 & G27 & G8 & G3 & G4 & HV & G25). unfold INF_FRAME in G2. pose proof HV as HV0. unfold LVR in HV. destruct HV as (G24 & G9 & G22 & G18).
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr.
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    arm_symexP (@nil (Z * expr)) ilS 20%nat (@nil bool)
      [RVal (EAdd (EVar 33%nat) (ELit 1384)); RVal (EAdd (EVar 33%nat) (ELit 168)); RVal (EAdd (EVar 33%nat) (ELit 160)); RVal (EAdd (EVar 33%nat) (ELit 136)); RVal (EAdd (EVar 33%nat) (ELit 808))]
      tpins (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x1f860) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTTA" G end.
    replace (Z_to_le_bytes 8 (cv_S v + 1384)) with (Z_to_le_bytes 8 (codeptr_addr 75438 77486 (cv_S v) (CDyn 0))) in Hms1 by (cbn [codeptr_addr]; f_equal; lia).
    (* zlib 1.4: lencode = distcode = next (sd a1,120(s0); sd a1,128(s0)), then lenbits, then next *)
    set (sA := iset_lencode s (CDyn 0)). set (sA2 := iset_distcode sA (CDyn 0)). set (sB := iset_lenbits sA2 7). set (sC := iset_next sB 0).
    set (M1 := wbytes M (zw (cv_S v + 120)) (Z_to_le_bytes 8 (codeptr_addr 75438 77486 (cv_S v) (CDyn 0)))) in *.
    set (M1b := wbytes M1 (zw (cv_S v + 128)) (Z_to_le_bytes 8 (codeptr_addr 75438 77486 (cv_S v) (CDyn 0)))) in *.
    set (M2 := wbytes M1b (zw (cv_S v + 136)) (Z_to_le_bytes 4 7)) in *.
    set (M3 := wbytes M2 (zw (cv_S v + 160)) (Z_to_le_bytes 8 (codeptr_addr 75438 77486 (cv_S v) (CDyn 0)))) in *.
    assert (HM1 : LMEM v (mkW sA c r) M1).
    { apply (LMEM_store_scalar v C s c r _ M 120 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      exact (is6_upd_lencode M (cv_S v) _ s (CDyn 0) Msc ltac:(clear - CS; lia) ltac:(clear - CS; unfold is6_SIZE; lia)). }
    assert (HM1b : LMEM v (mkW sA2 c r) M1b).
    { apply (LMEM_store_scalar v C sA c r _ M1 128 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      exact (is6_upd_distcode M1 (cv_S v) _ sA (CDyn 0) (lm_sc _ _ _ HM1) ltac:(clear - CS; lia) ltac:(clear - CS; unfold is6_SIZE; lia)). }
    assert (HM2 : LMEM v (mkW sB c r) M2).
    { apply (LMEM_store_scalar v C sA2 c r _ M1b 136 _ HM1b); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_lenbits M1b (cv_S v) _ sA2 7 (lm_sc _ _ _ HM1b)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM3 : LMEM v (mkW sC c r) M3).
    { apply (LMEM_store_scalar v C sB c r _ M2 160 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      replace (codeptr_addr 75438 77486 (cv_S v) (CDyn 0)) with (cv_S v + 1384 + 4 * 0) by (cbn [codeptr_addr]; lia).
      apply (is6_upd_next M2 (cv_S v) _ sB 0 (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    pose proof HM3 as HM3'. clear Mrod Msc Mlens Mwork Mcodes Mwin Minp Mout Mzs Mfr Moutc Mleftc Mmap_f Mmap_Z Mmap_S Mmap_P Mmap_W.
    clear Fsv Fflush Flens Fnlens Fm16224 Fjtab Fbad Fin Fsane Ffl5 Fnext Fwork Fcodes Flenb Fdistb.
    open_lmem HM3'. unfold mapped in *.
    pose proof (is6_next _ _ _ _ Msc) as C144. pose proof (is6_lenbits _ _ _ _ Msc) as C120. cbn [w_s] in C144, C120.
    replace (is_next sC) with 0 in C144 by (subst sC sB sA2 sA; destruct s; reflexivity).
    replace (is_lenbits sC) with 7 in C120 by (subst sC sB sA2 sA; destruct s; reflexivity).
    replace (is_lens sC) with (is_lens s) in Mlens by (subst sC sB sA2 sA; destruct s; reflexivity).
    replace (is_work sC) with (is_work s) in Mwork by (subst sC sB sA2 sA; destruct s; reflexivity).
    replace (is_codes sC) with (is_codes s) in Mcodes by (subst sC sB sA2 sA; destruct s; reflexivity).
    symex_reg HR1 (10%bv : reg) as Q10. symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (13%bv : reg) as Q13.
    symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (1%bv : reg) as Q1.
    destruct (ITABLE M3 R1 CODES (cv_S v) 0 19 0 7 (cv_S v + 136) (cv_sp v - 256) (zw 0x1f894) (is_lens s) (is_codes s) (is_work s)
                Q10 ltac:(rewrite Q11; f_equal; lia) Q12 Q13 Q14 Q15 ltac:(rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2) Q1
                ltac:(apply ret_ok_lit; [lia | reflexivity]) ltac:(left; reflexivity)
                ltac:(clear - CS; lia) ltac:(clear - CS; lia) ltac:(clear - CS; lia) CoS
                ltac:(unfold ITFR6, IMG6_TOP in *; clear - Csp; lia) ltac:(clear - Csp; lia) ltac:(clear - Csp47; lia)
                ltac:(clear - Csp; replace (cv_sp v - 256) with (cv_sp v + (-16) * 16) by lia; rewrite Z.mod_add by lia; destruct Csp as (_ & _ & E); exact E)
                ltac:(unfold ITFR6; clear - CSb; lia))
      as (R3 & M4 & HmsT & T10 & Tret & T2 & Tfr & Tlens & Tcodes & Twork & Tnext & Tbits & TLt & TLw & TRt & TRw & Tsh & Tg & Tag).
    { intros x Hx. apply Mmap_f. unfold ITFR6 in Hx. clear - Hx. lia. }
    { exact Mmap_S. }
    { exact Mrod. }
    { exact Alens. } { exact Acodes. } { exact Awork. }
    { exact Mlens. } { exact Mcodes. } { exact Mwork. }
    { replace (cv_S v + 1384 + 4 * 0) with (codeptr_addr 75438 77486 (cv_S v) (CDyn 0)) by (cbn [codeptr_addr]; lia). exact C144. } { exact C120. }
    { exact Blens. } { exact Bcodes. } { exact Bwork. }
    { lia. } { lia. } { lia. }
    { intros i Hi. pose proof (L7 i Hi). lia. }
    { intros _. split; [lia|]. split; [reflexivity|]. intros i Hi. pose proof (L7 i Hi). lia. }
    { intros X; discriminate X. }
    { lia. } { lia. } { cbn [it_room]; lia. }
    change (inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s)) with (ll_call s) in *.
    assert (Et0 : exists t, t = ll_call s) by (exists (ll_call s); reflexivity).
    destruct Et0 as [t Et]. rewrite <- Et in *.
    assert (IT : inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) = (it_ret t, it_tbl t, it_table t, it_bits t, it_work t))
      by (exact (eq_trans (eq_sym Et) (it_eta t))).
    pose proof (LMEM_itable v C sC c r M3 M4 136 (it_table t) (it_bits t) (it_tbl t) (it_work t) HM3 Hput ltac:(left; reflexivity)
                  (ITF_agree v 136 M3 M4 Tag) Tg Tcodes Twork Tnext Tbits) as HM4.
    subst sC sB sA2 sA. rewrite (ll_S1_alt s t) in HM4.
    assert (HRC4 : RETC v (mkW (ll_S1 s t) c r) M4).
    { apply (RETC_itable v C (mkW s c r) 136 M3 M4); [subst M3 M2 M1b M1; retc_tower C HRC | left; reflexivity | exact (ITF_agree v 136 M3 M4 Tag)]. }
    assert (HX4 : LX v (mkW (ll_S1 s t) c r)).
    { apply (LX_step0 v s c r _ c r HX NH NB); unfold ll_S1; try (destruct s; reflexivity); [destruct s; cbn; cbn in Xlive; exact Xlive | exact Xret | exact Xmsg | destruct s; cbn; cbn in Xbk; bk_side]. }
    assert (HB4 : BREG (ll_S1 s t) c r (it_ret t) R3).
    { unfold BREG, INF_FRAME, LVARS. cbn [w_r].
      repeat match goal with |- _ /\ _ => split end;
        first [ exact T2 | exact T10
              | lazymatch goal with |- getr _ ?n = _ => rewrite (Tfr n eq_refl), (Hfr1 n eq_refl); assumption end
              | match goal with |- ?G => idtac "BREGT LEFT" G end ]. }
    assert (HPI : it_ret t = 0 -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW (iset_mode (iset_have (ll_S1 s t) 0) CODELENS) c (irset_ret r 0))).
    { intros R0. unfold ll_S1.
      exact (lenlens_codelens_pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) s c r
               (it_ret t) (it_tbl t) (it_table t) (it_bits t) (it_work t) HP Hmode H19 IT R0). }
    destruct (llt_segB (ll_S1 s t) c r R3 M4 (it_ret t) ltac:(unfold ll_S1; destruct s; exact Hmode) RI0 Hret0 Tret
                HPI HM4 HRC4 HX4 HB4)
      as (R' & M' & pc' & Hms3 & HPOST).
    exists R', M', pc'. split.
    { apply (msteps_trans _ _ (mkst R1 (Z_to_bv 64 0x21cb4) M3 s6u_rom)); [subst M3 M2 M1b M1; by_run Hms1 | eapply msteps_trans; [exact HmsT | exact Hms3]]. }
    unfold ll_after. cbv zeta. rewrite <- Et. fold (llB_res (cv_flush v) (ll_S1 s t) c r (it_ret t)).
    apply (arm_post_chain v (mkW s c r) (mkW (ll_S1 s t) c r) M M4); [unfold ll_S1; destruct s; split; [reflexivity | split; reflexivity] | | exact HPOST].
    cbn [w_r]. apply (MFRAME_trans v (ir_put r) (ir_put r) (ir_put r) M M3 M4); [| exact (MFRAME_itable v (ir_put r) M3 M4 136 C (proj1 Hput) ltac:(left; reflexivity) Tg (ITF_agree v 136 M3 M4 Tag))].
    subst M3 M2 M1b M1. do 4 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
    apply MFRAME_refl.
  Qed.
End SegT.
End FXG.
End InflA_Lenlens3.
Export InflA_Lenlens3.
Module InflA_Table1.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvDec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvArms5.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflNeed6.
Import InflA_Cl1.InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import InflA_ClS.InflA_LenlensS.
Import InflA_Lenlens1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.



Definition EREGt (v : icv) (s : inflate_state) (r : iregs) (R : bvmap 5 word) : Prop :=
  LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r) /\ getr R 19 = zw (ir_bits r)
  /\ getr R 14 = zw (cv_I0 v + ir_next r) /\ getr R 12 = zw (ir_have r) /\ getr R 17 = zw (is_have s).
Definition lenlens_core_stmt (v : icv) : Prop :=
  forall s c r R M,
    is_mode s = LENLENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> EREGt v s r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f728) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_LENLENS ivar_ref (cv_flush v) (mkW s c r)) R' M' pc'.

Definition ilTB : cfg := ilSx [0x1f36c; 0x1f6d0; 0x1f728] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section ArmTABLE.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition JS (h0 n0 b0 : Z) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 13 = zw (cv_ZP v) /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r)
    /\ getr R 12 = zw (ir_have r) /\ getr R 5 = zw (cv_I0 v + ir_next r) /\ getr R 15 = zw (cv_I0 v + ir_next r)
    /\ getr R 11 = zw (ir_bits r) /\ getr R 17 = zw (ir_bits r)
    /\ getr R 23 = zw h0 /\ getr R 26 = zw (cv_I0 v + n0) /\ getr R 19 = zw b0
    /\ ir_have r + ir_next r = h0 + n0 /\ ir_bits r = b0 + 8 * (ir_next r - n0) /\ 0 <= h0 < 2 ^ 31 /\ 0 <= b0 /\ 0 <= n0.
  Definition JE (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 13 = zw (cv_ZP v) /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r)
    /\ getr R 14 = zw (cv_I0 v + ir_next r) /\ getr R 12 = zw (ir_have r) /\ getr R 11 = zw (ir_bits r).

  Ltac open_fixc HF :=
    let X := fresh in pose proof HF as X; unfold LFIXc, INF_FRAME in X;
    destruct X as (G2 & G27 & G8 & G1 & G3 & G4).
  Ltac lfixc_close Hfr HR :=
    unfold LFIXc, INF_FRAME;
    repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with |- getr _ ?n = _ =>
      first [ rewrite (Hfr n eq_refl); assumption
            | let G := fresh "G" in symex_reg HR n as G; rewrite G; first [ reflexivity | assumption | apply zw_neg_mod | f_equal; lia ]
            | match goal with |- ?G => idtac "LFIXc LEFT" G end ]
    end.
  Ltac open_js HJ :=
    let X := fresh in pose proof HJ as X; unfold JS in X;
    destruct X as (HF & G13 & G9 & G22 & G12 & G5 & G15 & G11 & G17 & G24 & G25 & G18 & E1 & E2 & Hh0 & Hb0 & Hn00); open_fixc HF.

  Definition js_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (13, EVar 34%nat); (18, EVar 34%nat); (1, ELit 16209);
     (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat);
     (12, EVar 36%nat); (5, EAdd (EVar 43%nat) (EVar 44%nat)); (15, EAdd (EVar 43%nat) (EVar 44%nat)); (11, EVar 41%nat); (17, EVar 41%nat);
     (23, EVar 45%nat); (26, EAdd (EVar 43%nat) (EVar 46%nat)); (19, EVar 47%nat)].

  Ltac js_close HR Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00 :=
    let Q12 := fresh in let Q22 := fresh in let Q5 := fresh in let Q15 := fresh in let Q11 := fresh in let Q17 := fresh in let Q14 := fresh in
    symex_reg HR (12%bv : reg) as Q12; symex_reg HR (25%bv : reg) as Q22; symex_reg HR (5%bv : reg) as Q5; symex_reg HR (15%bv : reg) as Q15;
    symex_reg HR (11%bv : reg) as Q11; symex_reg HR (17%bv : reg) as Q17; symex_reg HR (14%bv : reg) as Q14;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in Q22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold JS, JE, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- LFIXc _ _ => lfixc_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q12; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q22; f_equal; lia
          | rewrite Q5; f_equal; lia
          | rewrite Q15; f_equal; lia
          | rewrite Q11; f_equal; lia
          | rewrite Q17; f_equal; lia
          | rewrite Q14; f_equal; lia
          | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR n as G; rewrite G; first [reflexivity | assumption | f_equal; lia] end
          | clear - E1 E2 Hh0 Hb0 Hn00; lia
          | match goal with |- ?G => idtac "JS LEFT" G end ].

  Lemma table_step_H : forall h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> JS h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < 14 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f36c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f36c) M s6u_rom)
               /\ JS h0 n0 b0 c (pull1 c r) R1.
  Proof.
    intros h0 n0 b0 s c r R M HM HJ RI CI Hb Hh. open_js HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP js_pins ilTB 24%nat [true; true; true] (@nil (option expr)) (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)] v r [h0; n0; b0] NoVals
      (famA c s)
      (mkst R (Z_to_bv 64 0x1f36c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTTH" G end.
    exists R1. split; [by_run Hms|].
    js_close HR1 Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00.
  Qed.

  Lemma table_step_E : forall h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> JS h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 14 -> 14 <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f36c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f6d0) M s6u_rom)
               /\ JE c (pull1 c r) R1.
  Proof.
    intros h0 n0 b0 s c r R M HM HJ RI CI Hb Hb8 Hh. open_js HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP js_pins ilTB 24%nat [true; true; false] (@nil (option expr)) (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)] v r [h0; n0; b0] NoVals
      (famA c s)
      (mkst R (Z_to_bv 64 0x1f36c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTTE" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    js_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00.
  Qed.

  Lemma table_dry : forall h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> JS h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 14 -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f36c) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros h0 n0 b0 s c r R M HM HRC HJ RI CI Hb Hh. open_js HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP js_pins ilTB 14%nat [false] [RVal (EVar 48%nat); RVal (EVar 35%nat)] (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64); (48%nat, 2 ^ 64)] v r
      [h0; n0; b0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f36c) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTTD" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as Q26. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (23%bv : reg) as Q24.
    symex_reg HR1 (11%bv : reg) as Q11.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. repeat match goal with |- _ /\ _ => split end;
      first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
            | rewrite Q26; apply zw_neg_mod
            | rewrite Q11; reflexivity
            | rewrite Q24; f_equal; clear - Hh; lia
            | rewrite Q18; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - E1 E2 Hh Hh0; lia
            | rewrite Q25; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - E1 E2 Hh Hh0; lia
            | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.
End ArmTABLE.
End FXG.
End InflA_Table1.
Export InflA_Table1.
Module InflA_Table2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvDec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvArms5.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflNeed6.
Import InflA_Cl1.InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import InflA_ClS.InflA_LenlensS.
Import InflA_Lenlens1.
Import InflA_Table1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma cdrop14_eq : forall r, 14 <= ir_bits r < 64 -> 0 <= ir_hold r ->
  cdrop (cdrop (cdrop r 5) 5) 4
  = mkIR (ir_next r) (ir_have r) (ir_put r) (ir_left r) (ir_hold r / 2 ^ 14) (ir_bits r - 14) (ir_in r) (ir_out r) (ir_ret r).
Proof.
  intros r Hb Hh. unfold cdrop. destruct r as [nx hv pt lf ho bi i o rt]; cbv beta iota delta [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret irset_bits irset_hold] in *.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite !Zdiv_Zdiv by lia. change (2 ^ 5 * 2 ^ 5 * 2 ^ 4) with (2 ^ 14).
  rewrite (wrap32_id (bi - 5)) by lia. rewrite (wrap32_id (bi - 5 - 5)) by lia. rewrite (wrap32_id (bi - 5 - 5 - 4)) by lia.
  f_equal. lia.
Qed.

Lemma mod_div_field : forall h a b, 0 <= h -> 0 <= a -> 0 <= b -> h mod 2 ^ (a + b) / 2 ^ a = (h / 2 ^ a) mod 2 ^ b.
Proof.
  intros h a b Hh Ha Hb. apply Z.bits_inj'. intros n Hn.
  rewrite Z.div_pow2_bits by lia.
  destruct (Z_lt_le_dec n b).
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Section Body.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis LCORE : lenlens_core_stmt v.

  Ltac open_je HJ :=
    let X := fresh in pose proof HJ as X; unfold JE, LFIXc, INF_FRAME in X;
    destruct X as ((G2 & G27 & G8 & G1 & G3 & G4) & G13 & G9 & G22 & G14 & G12 & G11).
  Definition je_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (13, EVar 34%nat); (18, EVar 34%nat); (1, ELit 16209);
     (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat);
     (14, EAdd (EVar 43%nat) (EVar 44%nat)); (12, EVar 36%nat); (11, EVar 41%nat)].

  Lemma table_body : forall s c r r1 R M,
    is_mode s = TABLE -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
    NEEDBITS 14 (mkW s c r) = ARun tt (mkW s c r1) ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> JE v c r1 R ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c -> 14 <= ir_bits r1 ->
    let s3 := tb_s s (ir_hold r1) in
    let r4 := cdrop (cdrop (cdrop r1 5) 5) 4 in
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f6d0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r1) M
           (if (286 <? is_nlen s3) || (30 <? is_ndist s3)
            then ARun tt (mkW (iset_mode s3 BAD) (icset_msg c MSG_too_many_length_or_distance_symbols) r4)
            else arm_LENLENS ivar_ref (cv_flush v) (mkW (iset_mode (iset_have s3 0) LENLENS) c r4)) R' M' pc'.
  Proof.
    intros s c r r1 R M Hmode HP HN HM HRC HX HJ RI CI Hb14. cbv zeta. open_je HJ.
    open_ictx C. pose proof HM as HM0. open_lmem HM. open_frame Mfr. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (tb_s_fields s (ir_hold r1)) as (Fnl & Fnd & Fnc & Fm & Fh & Fsb).
    set (s3 := tb_s s (ir_hold r1)) in *.
    pose proof (cdrop14_eq r1 ltac:(clear - Hb14 Rbits; lia) (proj1 Rhold)) as Er4.
    set (r4 := cdrop (cdrop (cdrop r1 5) 5) 4) in *.
    set (nl := BITSv (ir_hold r1) 5) in *. set (nd := BITSv (Z.shiftr (ir_hold r1) 5) 5) in *. set (nc := BITSv (Z.shiftr (Z.shiftr (ir_hold r1) 5) 5) 4) in *.
    assert (Hnl : 0 <= nl < 32) by (subst nl; apply BITSv_bound; lia).
    assert (Hnd : 0 <= nd < 32) by (subst nd; apply BITSv_bound; lia).
    assert (Hnc : 0 <= nc < 16) by (subst nc; apply BITSv_bound; lia).
    assert (E1 : ir_hold r1 mod 2 ^ 5 = nl) by (subst nl; symmetry; apply BITSv_mod; lia).
    assert (E2 : ir_hold r1 mod 2 ^ 10 / 2 ^ 5 = nd).
    { subst nd. change (2 ^ 10) with (2 ^ (5 + 5)). rewrite mod_div_field by lia. rewrite Z.shiftr_div_pow2 by lia. symmetry. apply BITSv_mod; [apply Z.div_pos; lia | lia]. }
    assert (E3 : ir_hold r1 mod 2 ^ 14 / 2 ^ 10 = nc).
    { subst nc. change (2 ^ 14) with (2 ^ (10 + 4)). rewrite mod_div_field by lia. rewrite !Z.shiftr_div_pow2 by lia. rewrite Zdiv_Zdiv by lia.
      change (2 ^ 5 * 2 ^ 5) with (2 ^ 10). symmetry. apply BITSv_mod; [apply Z.div_pos; lia | lia]. }
    set (sA := iset_ncode s (nc + 4)). set (sB := iset_nlen sA (nl + 257)).
    set (M1 := wbytes M (zw (cv_S v + 144)) (Z_to_le_bytes 4 (nc + 4))).
    set (M2 := wbytes M1 (zw (cv_S v + 148)) (Z_to_le_bytes 4 (nl + 257))).
    set (M3 := wbytes M2 (zw (cv_S v + 152)) (Z_to_le_bytes 4 (nd + 1))).
    assert (HM1 : LMEM v (mkW sA c r1) M1).
    { apply (LMEM_store_scalar v C s c r1 _ M 144 _ HM0); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_ncode M (cv_S v) _ s (nc + 4) Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM2 : LMEM v (mkW sB c r1) M2).
    { apply (LMEM_store_scalar v C sA c r1 _ M1 148 _ HM1); [lia | cbn; lia | exact Hput | | subst sA; destruct s; reflexivity | subst sA; destruct s; reflexivity | subst sA; destruct s; reflexivity | subst sA; destruct s; reflexivity].
      apply (is6_upd_nlen M1 (cv_S v) _ sA (nl + 257) (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM3 : LMEM v (mkW s3 c r1) M3).
    { replace s3 with (iset_ndist sB (nd + 1)) by (subst s3 sB sA; unfold tb_s; destruct s; reflexivity).
      apply (LMEM_store_scalar v C sB c r1 _ M2 152 _ HM2); [lia | cbn; lia | exact Hput | | subst sB sA; destruct s; reflexivity | subst sB sA; destruct s; reflexivity | subst sB sA; destruct s; reflexivity | subst sB sA; destruct s; reflexivity].
      apply (is6_upd_ndist M2 (cv_S v) _ sB (nd + 1) (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (MF3 : MFRAME v (ir_put r1) (ir_put r1) M M3).
    { subst M3 M2 M1. do 3 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
      apply MFRAME_refl. }
    assert (BADPOST : forall R1 (HR1 : Prop),
      (forall rg, reg_in rg [5%bv; 6%bv; 7%bv; 10%bv; 11%bv; 14%bv; 15%bv; 16%bv; 17%bv; 19%bv; 25%bv; 23%bv; 26%bv] = false -> getr R1 rg = getr R rg) ->
      getr R1 25 = zw (ir_hold r1 / 2 ^ 14) -> getr R1 19 = zw (szwrap 32 (ir_bits r1 + -14)) -> getr R1 26 = zw (cv_I0 v + ir_next r1) -> getr R1 23 = zw (ir_have r1) ->
      getr R1 11 = zw (cv_flush v) -> getr R1 2 = zw (cv_sp v - 256) -> getr R1 8 = zw (cv_S v) ->
      let M' := wbytes (wbytes M3 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66585)) (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209) in
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f6d0) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_disp) M' s6u_rom) ->
      exists R' M'' pc', msteps s6u_segs (mkst R (Z_to_bv 64 0x1f6d0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M'' s6u_rom)
        /\ arm_post v (mkW s c r1) M (ARun tt (mkW (iset_mode s3 BAD) (icset_msg c MSG_too_many_length_or_distance_symbols) r4)) R' M'' pc').
    { intros R1 _ Hfr Q22 Q18 Q25 Q24 Q11 Q2 Q27. cbv zeta. intros Hms1.
      set (c' := icset_msg c MSG_too_many_length_or_distance_symbols). set (s' := iset_mode s3 BAD).
      set (M4 := wbytes M3 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66585)) in *.
      assert (HM4 : LMEM v (mkW s3 c' r1) M4) by (exact (LMEM_store_msg v C s3 c r1 M3 MSG_too_many_length_or_distance_symbols HM3 Hput)).
      assert (HM5 : LMEM v (mkW s' c' r4) (wbytes M4 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209))).
      { apply (LMEM_regs v s' c' r1 c' r4); try reflexivity; try (rewrite Er4; reflexivity).
        apply (LMEM_store_scalar v C s3 c' r1 _ M4 8 _ HM4); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M4 (cv_S v) _ s3 BAD (lm_sc _ _ _ HM4)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_too_many_length_or_distance_symbols) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      arm_disp C HM5 Hfr R2 Hms2 G26' Hfr2.
      exists R2, (wbytes M4 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)), (arm6_pc (is_mode s')). split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      replace (is_mode s') with BAD by (subst s' s3; unfold tb_s; destruct s; reflexivity).
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s' s3; apply (same_blocks_trans _ _ _ Fsb); apply same_blocks_mode |]].
      - split; [exact HM5|]. split.
        { apply (RETC_regs v (mkW s c r1)); [| rewrite Er4; reflexivity]. subst M4 M3 M2 M1. retc_tower C HRC. }
        split.
        { apply (LX_step0 v s c r1 s' c' r4 HX NH NB); subst s' c'; rewrite ?Er4; cbn [ir_in ir_ret];
            first [ subst s3; unfold tb_s; destruct s; reflexivity | exact Xret | exact Xmsg
                  | rewrite K11; unfold MSG_too_many_length_or_distance_symbols; clear; lia
                  | subst s3; unfold tb_s; destruct s; live_mode_tac
                  | bk_side ]. }
        unfold LREG_arm. split; [| split; [| intros _; exact G26']].
        { unfold LFIX, INF_FRAME. repeat match goal with |- _ /\ _ => split end;
            (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr2 n eq_refl) end;
             first [ assumption | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
                   | match goal with |- ?G => idtac "LFIXB LEFT" G end ]). }
        unfold LVARS; cbn [w_r]. rewrite Er4; cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next].
        repeat match goal with |- _ /\ _ => split end;
          (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr2 n eq_refl) end;
           first [ assumption | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
                 | rewrite Q18; rewrite szwrap32_small by (clear - Hb14 Rbits; lia); f_equal; lia
                 | match goal with |- ?G => idtac "LVARSB LEFT" G end ]).
      - cbn [w_r]. subst M4 M3 M2 M1.
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [exact MF3 | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]. }
    rewrite Fnl, Fnd.
    destruct (Z.ltb_spec 286 (nl + 257)) as [B1|B1]; [| destruct (Z.ltb_spec 30 (nd + 1)) as [B2|B2]]; cbn [orb].
    -
      assert (Hc1 : 29 < ir_hold r1 mod 2 ^ 5) by (rewrite E1; lia).
      arm_symexP je_pins ilTB 40%nat [true] [RVal (EVar 35%nat)] (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals F0
        (mkst R (Z_to_bv 64 0x1f6d0) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTTB_A" G end.
      rewrite E1, E2, E3 in Hms.
      symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (23%bv : reg) as Q24.
      symex_reg HR1 (11%bv : reg) as Q11.
      apply (BADPOST R1 True ltac:(fr_weak Hfr) Q22 Q18 Q25 Q24 Q11 ltac:(rewrite (Hfr (2%bv : reg) eq_refl); exact G2) ltac:(rewrite (Hfr (8%bv : reg) eq_refl); exact G27)).
      subst M3 M2 M1; by_run Hms.
    -
      assert (Hc1 : ~ 29 < ir_hold r1 mod 2 ^ 5) by (rewrite E1; lia).
      assert (Hc2 : 30 <= ir_hold r1 mod 2 ^ 10 / 2 ^ 5) by (rewrite E2; lia).
      arm_symexP je_pins ilTB 40%nat [false; true] [RVal (EVar 35%nat)] (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals F0
        (mkst R (Z_to_bv 64 0x1f6d0) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTTB_B" G end.
      rewrite E1, E2, E3 in Hms.
      symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (23%bv : reg) as Q24.
      symex_reg HR1 (11%bv : reg) as Q11.
      apply (BADPOST R1 True ltac:(fr_weak Hfr) Q22 Q18 Q25 Q24 Q11 ltac:(rewrite (Hfr (2%bv : reg) eq_refl); exact G2) ltac:(rewrite (Hfr (8%bv : reg) eq_refl); exact G27)).
      subst M3 M2 M1; by_run Hms.
    -
      assert (Hc1 : ~ 29 < ir_hold r1 mod 2 ^ 5) by (rewrite E1; lia).
      assert (Hc2 : ~ 30 <= ir_hold r1 mod 2 ^ 10 / 2 ^ 5) by (rewrite E2; lia).
      arm_symexP je_pins ilTB 30%nat [false; false] [RVal (EVar 35%nat)] (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals F0
        (mkst R (Z_to_bv 64 0x1f6d0) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTTB_C" G end.
      rewrite E1, E2, E3 in Hms.
      set (s4 := iset_mode (iset_have s3 0) LENLENS) in *.
      set (M4 := wbytes M3 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16197)).
      set (M5 := wbytes M4 (zw (cv_S v + 156)) (Z_to_le_bytes 4 0)).
      assert (HM4 : LMEM v (mkW (iset_mode s3 LENLENS) c r1) M4).
      { apply (LMEM_store_scalar v C s3 c r1 _ M3 8 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M3 (cv_S v) _ s3 LENLENS (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM5 : LMEM v (mkW s4 c r4) M5).
      { apply (LMEM_regs v s4 c r1 c r4); try reflexivity; try (rewrite Er4; reflexivity).
        replace s4 with (iset_have (iset_mode s3 LENLENS) 0) by (subst s4 s3; unfold tb_s; destruct s; reflexivity).
        apply (LMEM_store_scalar v C _ c r1 _ M4 156 _ HM4); [lia | cbn; lia | exact Hput | | subst s3; destruct s; reflexivity | subst s3; destruct s; reflexivity | subst s3; destruct s; reflexivity | subst s3; destruct s; reflexivity].
        apply (is6_upd_have M4 (cv_S v) _ _ 0 (lm_sc _ _ _ HM4)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HRC5 : RETC v (mkW s4 c r4) M5).
      { apply (RETC_regs v (mkW s c r1)); [| rewrite Er4; reflexivity]. subst M5 M4 M3 M2 M1. retc_tower C HRC. }
      assert (HX5 : LX v (mkW s4 c r4)).
      { apply (LX_step0 v s c r1 s4 c r4 HX NH NB); subst s4; rewrite ?Er4; cbn [ir_in ir_ret];
          first [ subst s3; unfold tb_s; destruct s; reflexivity | exact Xret | exact Xmsg
                | subst s3; unfold tb_s; destruct s; live_mode_tac | bk_side ]. }
      assert (HP5 : pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s4 c r4)).
      { subst s4 s3 r4. apply (table_lenlens_pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) s c r r1 HP Hmode HN).
        rewrite Fnl, Fnd. apply Bool.orb_false_intro; apply Z.ltb_ge; lia. }
      symex_reg HR' (25%bv : reg) as Q22. symex_reg HR' (19%bv : reg) as Q18. symex_reg HR' (17%bv : reg) as Q17.
      assert (HE : EREGt v s4 r4 R').
      { unfold EREGt, LFIXc, INF_FRAME. rewrite Er4; cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next].
        repeat match goal with |- _ /\ _ => split end;
          first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
                | exact Q22
                | rewrite Q18; rewrite szwrap32_small by (clear - Hb14 Rbits; lia); f_equal; lia
                | rewrite Q17; subst s4 s3; unfold tb_s; destruct s; reflexivity
                | match goal with |- ?G => idtac "EREG LEFT" G end ]. }
      destruct (LCORE s4 c r4 R' M5 ltac:(subst s4; destruct s3; reflexivity) HP5 HM5 HRC5 HX5 HE)
        as (R'' & M'' & pc'' & Hms2 & HPOST).
      exists R'', M'', pc''. split; [eapply msteps_trans; [| exact Hms2]; subst M5 M4 M3 M2 M1; by_run Hms|].
      apply (arm_post_rebase v s c r1 c r4); [rewrite Er4; reflexivity|].
      apply (arm_post_chain v (mkW s c r4) (mkW s4 c r4) M M5); [| | exact HPOST].
      { subst s4 s3. apply (same_blocks_trans _ _ _ Fsb). unfold tb_s; destruct s; split; [reflexivity | split; reflexivity]. }
      cbn [w_r]. rewrite Er4; cbn [ir_put]. subst M5 M4.
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [exact MF3 | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.
End Body.

Section ArmT.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis LCORE : lenlens_core_stmt v.

  Lemma table_A : forall s c r R M,
    LFIX v R -> LVARS v (mkW s c r) R -> RINV (cv_NI v) (cv_NO v) r ->
    exists R1,
      if 14 <=? ir_bits r
      then msteps s6u_segs (mkst R (Z_to_bv 64 0x1f350) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f6d0) M s6u_rom) /\ JE v c r R1
      else msteps s6u_segs (mkst R (Z_to_bv 64 0x1f350) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f36c) M s6u_rom) /\ JS v (ir_have r) (ir_next r) (ir_bits r) c r R1.
  Proof.
    intros s c r R M HF HV RI. cbv zeta.
    open_ictx C. open_fix HF. open_vars HV. open_rinv RI.
    destruct (Z.leb_spec 14 (ir_bits r)) as [GE|LT].
    - arm_symex ilTB 8%nat [true] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f350) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTTA1" G end.
      exists R1. split; [by_run Hms|].
      unfold JE, LFIXc, INF_FRAME; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
      repeat match goal with |- _ /\ _ => split end;
        first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
              | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption | f_equal; lia] end
              | match goal with |- ?G => idtac "JE_A LEFT" G end ].
    - arm_symex ilTB 10%nat [false] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f350) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTTA2" G end.
      exists R1. split; [by_run Hms|].
      unfold JS, LFIXc, INF_FRAME; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
      repeat match goal with |- _ /\ _ => split end;
        first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
              | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption | f_equal; lia] end
              | clear - Rhv0 Rnh Rnx0 Rbits CI0; lia
              | match goal with |- ?G => idtac "JS_A LEFT" G end ].
  Qed.

  Theorem arm_TABLE_sim0 : forall w R M,
    is_mode (w_s w) = TABLE -> ENTRY v w R M -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) w ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 (arm6_pc TABLE)) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v w M (dispatch ivar_ref (cv_flush v) w) R' M' pc'.
  Proof.
    intros w R M Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) TABLE) with (arm_TABLE ivar_ref (cv_flush v)).
    destruct HE as (HM & HRC & HX & (HF & HV & G26)).
    arm_begin C HM HRC HX HF HV HP.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    destruct (table_A s c r R M HF HV RI) as (R1 & HA).
    change (arm6_pc TABLE) with 0x1f350.
    destruct (Z.leb_spec 14 (ir_bits r)) as [GE|LT].
    -
      destruct HA as (Hms1 & HJE).
      assert (HN : NEEDBITS 14 (mkW s c r) = ARun tt (mkW s c r)) by (unfold NEEDBITS; apply NEEDBITS_k_done; cbn; exact GE).
      rewrite (arm_TABLE_run (cv_flush v) s c r r HN).
      destruct (table_body v C LCORE s c r r R1 M Hmode HP HN HM HRC HX HJE RI CI GE) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
    -
      destruct HA as (Hms1 & HJS).
      pose proof (need_loop v 14 0x1f36c 0x1f6d0 (JS v (ir_have r) (ir_next r) (ir_bits r)) (JE v) C ltac:(lia)
                    (table_step_H v C _ _ _) (table_step_E v C _ _ _) (table_dry v C _ _ _)
                    8%nat s c r R1 M HM HRC HJS RI CI LT ltac:(cbn; clear - LT Rbits; lia)) as NL.
      change (NEEDBITS_k 8 14) with (NEEDBITS 14) in NL.
      destruct (NEEDBITS 14 (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:HN; [| | destruct NL].
      + destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        rewrite (arm_TABLE_run (cv_flush v) s c r r1 HN).
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side]).
        destruct (table_body v C LCORE s c r r1 R2 M Hmode HP HN HM1 HRC1 HX1 HJE RI1 CI ltac:(clear - Hb1; lia)) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      + destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
        rewrite (arm_TABLE_leave (cv_flush v) s c r _ HN).
        exists R2, M, pc6_leave. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
        split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
        apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
  Qed.
End ArmT.

Section ArmT2.
  Hypothesis LCORE : forall v, ictx v -> lenlens_core_stmt v.
  Theorem arm_TABLE_sim : arm_stmt TABLE.
  Proof. intros v w R M C Hmode HE HP. exact (arm_TABLE_sim0 v C (LCORE v C) w R M Hmode HE HP). Qed.
End ArmT2.
End FXG.
End InflA_Table2.
Export InflA_Table2.
Module InflA_Lenlens4.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvArms5.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Callee6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Match2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Dist3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.Callee6i.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflMem2.
Import InflA_Cl1.InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Cl1.InflA_Codelens3.
Import InflA_Lenlens1.
Import InflA_Lenlens2.
Import InflA_Lenlens3.
Import InflA_Table1.
Import InflA_ClS.InflA_LenlensS.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilL4 : cfg := ilSx [0x1f75c; 0x1f728; 0x1f7fc] [].

Section Core.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis ITABLE : itable_run6.
  Hypothesis CCORE : codelens_core_stmt v.

  Lemma lenlens_tail : forall s c r R M,
    is_mode s = LENLENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> is_ncode s <= is_have s ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> FREG v s r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f7fc) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M
           (ll_after (cv_flush v) (iset_have (iset_lens s (fillo (is_lens s) (is_have s) (Z.to_nat (19 - is_have s)))) 19) c r) R' M' pc'.
  Proof.
    intros s c r R M Hmode HP Hge HM HRC HX HR.
    destruct (lenlens_facts v s c r HP Hmode) as (Hnc & Hhv & Halen & RI & CI).
    pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    destruct (ll2_seg v C s c r R M Hmode HP Hge HM HRC HR) as (R2 & M2 & Hms2 & HM2 & HRC2 & HT2 & MF2).
    set (s2 := iset_have (iset_lens s (fillo (is_lens s) (is_have s) (Z.to_nat (19 - is_have s)))) 19) in *.
    pose proof (ll2_pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) ltac:(lia) ltac:(lia) s c r HP Hmode ltac:(lia)) as HP2. change (iset_have _ 19) with s2 in HP2.
    assert (Em : is_mode s2 = LENLENS) by (subst s2; destruct s; exact Hmode).
    assert (HX2 : LX v (mkW s2 c r)).
    { open_lx HX. apply (LX_step0 v s c r s2 c r HX NH NB); subst s2; try (destruct s; reflexivity); [rewrite Em, <- Hmode; exact Xlive | exact Xret | exact Xmsg | rewrite Em; destruct s; cbn; cbn in Xbk; rewrite <- Hmode; exact Xbk]. }
    destruct (llt_segA v C ITABLE CCORE s2 c r R2 M2 Em ltac:(subst s2; destruct s; reflexivity) HP2 HM2 HRC2 HX2 HT2) as (R' & M' & pc' & Hms3 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [exact Hms2 | exact Hms3]|].
    apply (arm_post_chain v (mkW s c r) (mkW s2 c r) M M2); [subst s2; destruct s; split; [reflexivity | split; reflexivity] | exact MF2 | exact HPOST].
  Qed.

  Lemma lenlens_core : forall s c r R M,
    is_mode s = LENLENS -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> EREGt v s r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f728) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_LENLENS ivar_ref (cv_flush v) (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HP HM HRC HX HR.
    destruct (lenlens_facts v s c r HP Hmode) as (Hnc & Hhv & Halen & RI & CI).
    pose proof HR as X; unfold EREGt, LFIXc, INF_FRAME in X; destruct X as ((G2 & G27 & G8 & G1 & G3 & G4) & G9 & G22 & G18 & G14 & G12 & G17).
    open_ictx C. pose proof HM as HM0. open_lmem HM. pose proof RI as RI0. open_rinv RI. unfold mapped in *.
    pose proof (is6_ncode _ _ _ _ Msc) as C128.
    destruct (Z_lt_le_dec (is_have s) (is_ncode s)) as [Hlt|Hge].
    -
      arm_symexP (@nil (Z * expr)) ilL4 16%nat [false; false] [RVal (EVar 46%nat)]
        [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat);
         (14, EAdd (EVar 43%nat) (EVar 44%nat)); (12, EVar 36%nat); (17, EVar 45%nat)]
        [(45%nat, 32); (46%nat, 32)] v r [is_have s; is_ncode s] NoVals F0
        (mkst R (Z_to_bv 64 0x1f728) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTE1" G end.
      assert (HL1 : L1REG v s r R1).
      { unfold L1REG, InflA_Lenlens1.LFIXa, INF_FRAME.
        repeat match goal with |- _ /\ _ => split end;
          first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR1 n as G; rewrite G;
                    first [ reflexivity | unfold A6_ORDER; reflexivity | apply zw_neg_mod | f_equal; lia
                          | rewrite ?Z.mod_small by (clear - Hhv; lia); rewrite ?szwrap32_small by (clear - Hnc Hhv; lia); first [reflexivity | apply zw_neg_mod | f_equal; clear - Hhv Hnc; lia] ] end
                | match goal with |- ?G => idtac "L1REG LEFT" G end ]. }
      destruct (ll1_loop v C 18 s c r R1 M Hmode HP Hlt ltac:(clear - Hnc Hhv Hlt; cbn; lia) HM0 HRC HX HL1) as (R2 & M2 & pc2 & Hms2 & HL).
      destruct (lenlens_while1 19 (mkW s c r)) as [u w1 | w1 | rc w1] eqn:E1.
      + destruct u. destruct w1 as [s1 c1 r1]. cbn [l1post w_s w_r w_c] in HL.
        destruct HL as (-> & Hm1 & Hhn & HF1 & HM1 & HRC1 & HX1 & HP1 & SB1 & MF1).
        destruct (lenlens_facts v s1 c1 r1 HP1 Hm1) as (Hnc1 & Hhv1 & _).
        destruct (lenlens_tail s1 c1 r1 R2 M2 Hm1 HP1 ltac:(rewrite Hhn; apply Z.le_refl) HM1 HRC1 HX1 HF1) as (R' & M' & pc' & Hms3 & HPOST).
        rewrite (arm_LENLENS_run (cv_flush v) (mkW s c r) (mkW s1 c1 r1) _ c1 r1 E1 (ll2_fill 19 s1 c1 r1 ltac:(clear - Hhv1; lia) ltac:(clear - Hhv1; cbn; lia))).
        exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
        exact (arm_post_chain v (mkW s c r) (mkW s1 c1 r1) M M2 _ _ _ _ SB1 MF1 HPOST).
      + cbn [l1post] in HL. rewrite (arm_LENLENS_leave (cv_flush v) _ _ E1).
        exists R2, M2, pc2. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HL].
      + cbn [l1post] in HL. destruct HL.
    -
      arm_symexP (@nil (Z * expr)) ilL4 8%nat [true] [RVal (EVar 46%nat)]
        [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat);
         (14, EAdd (EVar 43%nat) (EVar 44%nat)); (12, EVar 36%nat); (17, EVar 45%nat)]
        [(45%nat, 32); (46%nat, 32)] v r [is_have s; is_ncode s] NoVals F0
        (mkst R (Z_to_bv 64 0x1f728) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTE2" G end.
      assert (HF1 : FREG v s r R1).
      { unfold FREG, InflA_Lenlens1.LFIXa, INF_FRAME.
        repeat match goal with |- _ /\ _ => split end;
          first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR1 n as G; rewrite G; first [reflexivity | unfold A6_ORDER; reflexivity | f_equal; lia] end
                | match goal with |- ?G => idtac "FREG LEFT" G end ]. }
      destruct (lenlens_tail s c r R1 M Hmode HP Hge HM0 HRC HX HF1) as (R' & M' & pc' & Hms2 & HPOST).
      rewrite (arm_LENLENS_run (cv_flush v) (mkW s c r) (mkW s c r) _ c r (ll1_done 19 s c r Hge) (ll2_fill 19 s c r ltac:(clear - Hhv; lia) ltac:(clear - Hhv; cbn; lia))).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  Qed.

  Theorem arm_LENLENS_sim0 : forall w R M,
    is_mode (w_s w) = LENLENS -> ENTRY v w R M -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) w ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 (arm6_pc LENLENS)) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v w M (dispatch ivar_ref (cv_flush v) w) R' M' pc'.
  Proof.
    intros w R M Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) LENLENS) with (arm_LENLENS ivar_ref (cv_flush v)).
    change (arm6_pc LENLENS) with 0x1f1b8.
    destruct (lenlens_facts v s c r HP Hmode) as (Hnc & Hhv & Halen & RI & CI).
    destruct HE as (HM & HRC & HX & HR). destruct HR as (HF & HV & _). pose proof HF as HF0. open_fix HF. pose proof HV as HV0. open_vars HV.
    open_ictx C. pose proof HM as HM0. open_lmem HM. pose proof RI as RI0. open_rinv RI.
    unfold mapped in *.
    pose proof (is6_have _ _ _ _ Msc) as C140.
    arm_symex ilL4 8%nat (@nil bool) [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 32)] v r
      [is_have s] NoVals F0
      (mkst R (Z_to_bv 64 0x1f1b8) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTLA1" G end.
    assert (HE1 : EREGt v s r R1).
    { unfold EREGt, LFIXc, INF_FRAME.
      repeat match goal with |- _ /\ _ => split end;
        first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
              | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption | f_equal; lia] end
              | match goal with |- ?G => idtac "EREG1 LEFT" G end ]. }
    destruct (lenlens_core s c r R1 M Hmode HP HM0 HRC HX HE1) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  Qed.
End Core.

Section Arm.
  Hypothesis ITABLE : itable_run6.
  Hypothesis CCORE : forall v, ictx v -> codelens_core_stmt v.
  Theorem arm_LENLENS_sim : arm_stmt LENLENS.
  Proof. intros v w R M C Hmode HE HP. exact (arm_LENLENS_sim0 v C ITABLE (CCORE v C) w R M Hmode HE HP). Qed.
  Theorem lenlens_core_ok : forall v, ictx v -> lenlens_core_stmt v.
  Proof. intros v C. unfold lenlens_core_stmt. exact (lenlens_core v C ITABLE (CCORE v C)). Qed.
End Arm.
End FXG.
End InflA_Lenlens4.
Export InflA_Lenlens4.

