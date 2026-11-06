(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
Definition STRLEN_WORDS : list (Z * Z) :=
  [(0, 0x00000593); (4, 0x00b50633); (8, 0x00064603); (12, 0x00158593); (16, 0xfe061ae3);
   (20, 0xfff58513); (24, 0x00008067)]%Z.

Lemma D_0  : decode_any (Z_to_bv 32 0x00000593) = Some (OpImm ALU_ADD 11 0 0, 4%Z). Proof. wdec. Qed.
Lemma D_4  : decode_any (Z_to_bv 32 0x00b50633) = Some (Op ALU_ADD 12 10 11, 4%Z). Proof. wdec. Qed.
Lemma D_8  : decode_any (Z_to_bv 32 0x00064603) = Some (Load SZ1 false 12 12 0, 4%Z). Proof. wdec. Qed.
Lemma D_12 : decode_any (Z_to_bv 32 0x00158593) = Some (OpImm ALU_ADD 11 11 1, 4%Z). Proof. wdec. Qed.
Lemma D_16 : decode_any (Z_to_bv 32 0xfe061ae3) = Some (Branch BC_NE 12 0 8180, 4%Z). Proof. wdec. Qed.
Lemma D_20 : decode_any (Z_to_bv 32 0xfff58513) = Some (OpImm ALU_ADD 10 11 4095, 4%Z). Proof. wdec. Qed.
Lemma D_24 : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr 0 1 0, 4%Z). Proof. wdec. Qed.

Section Strlen.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable b : Z.
Hypothesis HW : words_ok segs b STRLEN_WORDS = true.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get segs b STRLEN_WORDS); [exact HW | inw | lia].

Lemma F_0  : fetch_word segs (pcw b 0)  = Some (Z_to_bv 32 0x00000593). Proof. fw. Qed.
Lemma F_4  : fetch_word segs (pcw b 4)  = Some (Z_to_bv 32 0x00b50633). Proof. fw. Qed.
Lemma F_8  : fetch_word segs (pcw b 8)  = Some (Z_to_bv 32 0x00064603). Proof. fw. Qed.
Lemma F_12 : fetch_word segs (pcw b 12) = Some (Z_to_bv 32 0x00158593). Proof. fw. Qed.
Lemma F_16 : fetch_word segs (pcw b 16) = Some (Z_to_bv 32 0xfe061ae3). Proof. fw. Qed.
Lemma F_20 : fetch_word segs (pcw b 20) = Some (Z_to_bv 32 0xfff58513). Proof. fw. Qed.
Lemma F_24 : fetch_word segs (pcw b 24) = Some (Z_to_bv 32 0x00008067). Proof. fw. Qed.

Section Loop.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Variable ms0 : machine_state.
Variable K : TSet.
Variables (s : word) (bs : list byte).
Hypothesis Hstr : cstr segs (ms_mem ms0) s bs.
Hypothesis Hnw : (bv_unsigned s + Z.of_nat (length bs) + 1 <= 2 ^ 64)%Z.
Hypothesis Hnl : no_lazy model (bv_unsigned s) (bv_unsigned s + Z.of_nat (length bs) + 1).
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis HK : forall ms', FR [10; 11; 12] ms0 ms' -> ms_pc_val ms' = rg ms0 1 ->
  rg ms' 10 = Z_to_bv 64 (Z.of_nat (length bs)) -> rg ms' 11 = Z_to_bv 64 (Z.of_nat (S (length bs))) ->
  rg ms' 12 = w0 -> realizes_cfg segs cfg (mkCfg ms' model) K.

Lemma strlen_loop : forall d k ms, (k + d = length bs)%nat ->
  ms_pc_val ms = pcw b 4 -> FR [10; 11; 12] ms0 ms -> rg ms 10 = s -> rg ms 11 = Z_to_bv 64 (Z.of_nat k) ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  induction d as [|d IH]; intros k ms Hkd Hpc HF H10 H11.
  all: pose proof HF as (Hsvc & _ & _ & _ & _ & Hmem & _).
  all: pose proof (rdn_nth segs (ms_mem ms0) _ _ _ k (proj1 Hstr) ltac:(lia)) as Hrd.
  all: assert (Hu : bv_unsigned (s + Z_to_bv 64 (Z.of_nat k)) = (bv_unsigned s + Z.of_nat k)%Z)
         by (apply u_add_small; lia).
  all: wst wacc_Op F_4 D_4.
  all: rgn; rewrite H10, H11, alu_add.
  all: eapply rzc_acc;
        [ assumption | reflexivity
        | eapply wacc_Load; [ fetch_tac F_8 | reflexivity | exact D_8 | ] | | ].
  all: try (rewrite rg_setx_same by reflexivity; rewrite add_sext0; cbn [ms_mem setx]; rewrite Hmem; exact Hrd).
  all: try (apply acc_ok_one; rewrite rg_setx_same by reflexivity; rewrite add_sext0; cbn [msz_n]; rewrite Hu;
            [ lia | apply (no_lazy_sub model _ _ _ _ Hnl); lia ]).
  all: pcn; rewrite lbu_val.
  all: wst wacc_OpImm F_12 D_12.
  all: rgn; rewrite H11, alu_add, zw_succ.
  all: wst wacc_Branch F_16 D_16.
  all: rgn; rewrite branch_ne_byte.
  - (* [comment removed for export] *)
    assert (Hk : k = length bs) by lia. subst k.
    rewrite nth_app_last. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. cbn [Z.eqb negb]. pcn.
    wst wacc_OpImm F_20 D_20.
    rgn. rewrite alu_add, zw_pred.
    eapply rzc_acc;
      [ assumption | reflexivity | eapply wacc_Jalr; [ fetch_tac F_24 | reflexivity | exact D_24 ] | apply acc_ok_nil | ].
    rgn. rewrite pc_setx.
    assert (Hr1 : rg ms 1 = rg ms0 1) by (pose proof HF as (_ & _ & _ & _ & _ & _ & HR); apply HR; cbn; intuition discriminate).
    rewrite Hr1, ret_even by exact Hra.
    apply HK.
    + frs HF.
    + reflexivity.
    + rgn. reflexivity.
    + rgn. reflexivity.
    + rgn. reflexivity.
  - (* [comment removed for export] *)
    rewrite nth_app_l by lia.
    pose proof (nul_free_nth bs k (proj2 Hstr) ltac:(lia)) as Hnz.
    rewrite (proj2 (Z.eqb_neq _ 0%Z) Hnz). cbn [negb]. pcn.
    apply (IH (S k)); [lia | reflexivity | | | ].
    + frs HF.
    + rgn. exact H10.
    + rgn. reflexivity.
Qed.
End Loop.

(* [comment removed for export] *)
Theorem strlen_sum : forall (ms : machine_state) (model : Model) (K : TSet) (s : word) (bs : list byte),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw b 0 -> m_halted model = None ->
  rg ms 10 = s -> cstr segs (ms_mem ms) s bs ->
  (bv_unsigned s + Z.of_nat (length bs) + 1 <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned s) (bv_unsigned s + Z.of_nat (length bs) + 1) ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms', FR [10; 11; 12] ms ms' -> ms_pc_val ms' = rg ms 1 ->
     rg ms' 10 = Z_to_bv 64 (Z.of_nat (length bs)) -> rg ms' 11 = Z_to_bv 64 (Z.of_nat (S (length bs))) ->
     rg ms' 12 = w0 -> realizes_cfg segs cfg (mkCfg ms' model) K) ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros ms model K s bs Hsvc Hpc Hh H10 Hstr Hnw Hnl Hra HK.
  wst wacc_OpImm F_0 D_0.
  rgn. rewrite alu_add.
  apply (strlen_loop model Hh ms K s bs Hstr Hnw Hnl Hra HK (length bs) 0); [lia | reflexivity | | | ].
  - apply FR_setx; [apply FR_refl; exact Hsvc | right; cbn; tauto | reflexivity | reflexivity].
  - rgn. exact H10.
  - rgn. rewrite add_sext0. reflexivity.
Qed.

End Strlen.
