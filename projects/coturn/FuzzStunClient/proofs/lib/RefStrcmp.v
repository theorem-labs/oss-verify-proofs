(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefMemcpyBase RefStrLib Ref_code_235f0_2427c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition strcmp_clob : list reg := [10; 11; 12; 13]%list.

Section SC.
  Variables (mem rom : word -> option byte) (l r : word) (K : nat) (la lb : list byte).
  Hypothesis Hla : rdn SEGS mem l (S K) = Some la.
  Hypothesis Hlb : rdn SEGS mem r (S K) = Some lb.
  Hypothesis HK : bv_unsigned (nth K lb B0) = 0%Z.
  Hypothesis Hlw : (bv_unsigned l + Z.of_nat K < 2 ^ 64)%Z.
  Hypothesis Hrw : (bv_unsigned r + Z.of_nat K < 2 ^ 64)%Z.

  #[local] Notation LA i := (nth i la B0).
  #[local] Notation LB i := (nth i lb B0).

  (* [comment removed for export] *)
  Ltac mlbu F D H j :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?v_addi_0; first [apply (rdn_nth1 SEGS _ _ _ _ j H); lia | apply (rdn_nth1_0 SEGS _ _ _ _ H); lia] ]
      | step_simpl]; vnorm.
  Ltac condb := rwH; unfold c_ltu, c_eq, bv_ltu, bv_eqb, LBv; imm_norm; unorm;
    first [ apply Z.eqb_eq | apply Z.eqb_neq ]; first [lia | apply byte_neq_u; assumption | assumption].

  (* [comment removed for export] *)
  Lemma sc_loop : forall (m : nat) regs (ret : word) (i : nat),
    (m = K - i)%nat -> (1 <= i <= K)%nat ->
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = at_ l (Z.of_nat i) -> getr regs 11 = at_ r (Z.of_nat i) ->
    (forall j, (j < i)%nat -> LA j = LB j /\ bv_unsigned (LA j) <> 0%Z) ->
    exists regs' (k : nat),
      msteps SEGS (mkst regs (0x23b54 : word) mem rom) (mkst regs' ret mem rom)
      /\ regs_agree (fun x => In x strcmp_clob) regs regs'
      /\ (k <= K)%nat
      /\ (forall j, (j < k)%nat -> LA j = LB j /\ bv_unsigned (LA j) <> 0%Z)
      /\ (bv_unsigned (LA k) = 0%Z \/ LA k <> LB k)
      /\ getr regs' 10 = v_sub (LBv (LA k)) (LBv (LB k)).
  Proof.
    induction m as [m IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs ret i Hm Hi Hret H1 H10 H11 Hpre.
    pose proof (u64_range l). pose proof (u64_range r).
    pose proof (u8_range (LA i)) as U1. pose proof (u8_range (LB i)) as U2.
    destruct (Z.eq_dec (bv_unsigned (LA i)) 0) as [Hz|Hnz].
    { (* [comment removed for export] *)
      eexists _, i. split; [|split; [|split; [lia|split; [exact Hpre|split; [left; exact Hz|]]]]].
      - mlbu F_23b54 D_23b54 Hla i.                  (* [comment removed for export] *)
        mlbu F_23b58 D_23b58 Hlb i.                  (* [comment removed for export] *)
        stepb_tk F_23b5c D_23b5c ltac:(condb).       (* [comment removed for export] *)
        stepn F_23b6c D_23b6c.                       (* [comment removed for export] *)
        stepret F_23b70 D_23b70 ret ltac:(rwH; reflexivity). apply mst_refl.
      - unfold strcmp_clob. solve_regs_agree.
      - gres. reflexivity. }
    destruct (base.decide (LA i = LB i)) as [Heq|Hne].
    2:{ (* [comment removed for export] *)
      eexists _, i. split; [|split; [|split; [lia|split; [exact Hpre|split; [right; exact Hne|]]]]].
      - mlbu F_23b54 D_23b54 Hla i.
        mlbu F_23b58 D_23b58 Hlb i.
        stepb_ft F_23b5c D_23b5c ltac:(condb).       (* [comment removed for export] *)
        stepn F_23b60 D_23b60.                       (* [comment removed for export] *)
        stepn F_23b64 D_23b64.                       (* [comment removed for export] *)
        stepb_ft F_23b68 D_23b68 ltac:(condb).       (* [comment removed for export] *)
        stepn F_23b6c D_23b6c.                       (* [comment removed for export] *)
        stepret F_23b70 D_23b70 ret ltac:(rwH; reflexivity). apply mst_refl.
      - unfold strcmp_clob. solve_regs_agree.
      - gres. reflexivity. }
    (* [comment removed for export] *)
    assert (HiK : (i < K)%nat).
    { destruct (Nat.eq_dec i K) as [->|]; [|lia]. exfalso. apply Hnz. rewrite Heq. exact HK. }
    eapply (runs_trans_k SEGS _ (fun r1 => mkst r1 (0x23b54 : word) mem rom)
             (fun r1 => getr r1 1 = ret /\ getr r1 10 = at_ l (Z.of_nat (S i)) /\ getr r1 11 = at_ r (Z.of_nat (S i))
                        /\ regs_agree (fun x => In x strcmp_clob) regs r1)
             (fun r1 => mkst r1 ret mem rom)).
    - eexists. split.
      + mlbu F_23b54 D_23b54 Hla i.
        mlbu F_23b58 D_23b58 Hlb i.
        stepb_ft F_23b5c D_23b5c ltac:(condb).       (* [comment removed for export] *)
        stepn F_23b60 D_23b60.                       (* [comment removed for export] *)
        stepn F_23b64 D_23b64.                       (* [comment removed for export] *)
        stepb_tk F_23b68 D_23b68 ltac:(rwH; rewrite Heq; unfold c_eq; apply bv_eqb_refl).  (* [comment removed for export] *)
        apply mst_refl.
      + cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia). unfold strcmp_clob. solve_regs_agree.
    - cbv beta. intros r1 (R1 & R10 & R11 & AG1).
      destruct (IH (K - S i)%nat ltac:(lia) r1 ret (S i) eq_refl ltac:(lia) Hret R1 R10 R11) as (r2 & k & RUN & AG & REST).
      { intros j Hj. destruct (Nat.eq_dec j i) as [->|]; [split; [exact Heq|exact Hnz] | apply Hpre; lia]. }
      exists r2, k. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact REST]].
  Qed.

  Theorem ref_strcmp : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = l -> getr regs 11 = r ->
    exists regs' (i : nat),
      msteps SEGS (mkst regs (0x23b3c : word) mem rom) (mkst regs' ret mem rom)
      /\ regs_agree (fun x => In x strcmp_clob) regs regs'
      /\ (i <= K)%nat
      /\ (forall j, (j < i)%nat -> LA j = LB j /\ bv_unsigned (LA j) <> 0%Z)
      /\ (bv_unsigned (LA i) = 0%Z \/ LA i <> LB i)
      /\ getr regs' 10 = v_sub (LBv (LA i)) (LBv (LB i)).
  Proof.
    intros regs ret Hret H1 H10 H11.
    pose proof (u64_range l). pose proof (u64_range r).
    pose proof (u8_range (LA 0)) as U1. pose proof (u8_range (LB 0)) as U2.
    assert (H10' : getr regs 10 = at_ l (Z.of_nat 0)) by (rewrite at_0; exact H10).
    assert (H11' : getr regs 11 = at_ r (Z.of_nat 0)) by (rewrite at_0; exact H11).
    clear H10 H11.
    destruct (Z.eq_dec (bv_unsigned (LA 0)) 0) as [Hz|Hnz].
    { eexists _, 0%nat. split; [|split; [|split; [lia|split; [intros j Hj; lia|split; [left; exact Hz|]]]]].
      - mlbu F_23b3c D_23b3c Hla 0%nat.              (* [comment removed for export] *)
        mlbu F_23b40 D_23b40 Hlb 0%nat.              (* [comment removed for export] *)
        stepb_tk F_23b44 D_23b44 ltac:(condb).       (* [comment removed for export] *)
        stepn F_23b6c D_23b6c.
        stepret F_23b70 D_23b70 ret ltac:(rwH; reflexivity). apply mst_refl.
      - unfold strcmp_clob. solve_regs_agree.
      - gres. reflexivity. }
    destruct (base.decide (LA 0 = LB 0)) as [Heq|Hne].
    2:{ eexists _, 0%nat. split; [|split; [|split; [lia|split; [intros j Hj; lia|split; [right; exact Hne|]]]]].
      - mlbu F_23b3c D_23b3c Hla 0%nat.
        mlbu F_23b40 D_23b40 Hlb 0%nat.
        stepb_ft F_23b44 D_23b44 ltac:(condb).       (* [comment removed for export] *)
        stepb_tk F_23b48 D_23b48 ltac:(condb).       (* [comment removed for export] *)
        stepn F_23b6c D_23b6c.
        stepret F_23b70 D_23b70 ret ltac:(rwH; reflexivity). apply mst_refl.
      - unfold strcmp_clob. solve_regs_agree.
      - gres. reflexivity. }
    assert (HiK : (0 < K)%nat).
    { destruct (Nat.eq_dec K 0) as [E|]; [|lia]. exfalso. apply Hnz. rewrite Heq. rewrite <- E at 1. exact HK. }
    eapply (runs_trans_k SEGS _ (fun r1 => mkst r1 (0x23b54 : word) mem rom)
             (fun r1 => getr r1 1 = ret /\ getr r1 10 = at_ l (Z.of_nat 1) /\ getr r1 11 = at_ r (Z.of_nat 1)
                        /\ regs_agree (fun x => In x strcmp_clob) regs r1)
             (fun r1 => mkst r1 ret mem rom)).
    - eexists. split.
      + mlbu F_23b3c D_23b3c Hla 0%nat.
        mlbu F_23b40 D_23b40 Hlb 0%nat.
        stepb_ft F_23b44 D_23b44 ltac:(condb).       (* [comment removed for export] *)
        stepb_ft F_23b48 D_23b48 ltac:(rwH; rewrite Heq; unfold c_eq; apply bv_eqb_refl).  (* [comment removed for export] *)
        stepn F_23b4c D_23b4c.                       (* [comment removed for export] *)
        stepn F_23b50 D_23b50.                       (* [comment removed for export] *)
        apply mst_refl.
      + cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia). unfold strcmp_clob. solve_regs_agree.
    - cbv beta. intros r1 (R1 & R10 & R11 & AG1).
      destruct (sc_loop (K - 1)%nat r1 ret 1%nat ltac:(lia) ltac:(lia) Hret R1 R10 R11) as (r2 & k & RUN & AG & REST).
      { intros j Hj. replace j with 0%nat by lia. split; [exact Heq|exact Hnz]. }
      exists r2, k. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact REST]].
  Qed.
End SC.
