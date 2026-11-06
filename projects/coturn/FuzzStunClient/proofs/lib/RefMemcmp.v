(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefMemcpyBase RefStrLib Ref_code_225f0_235f0 Ref_code_235f0_2427c.
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

Definition memcmp_clob : list reg := [10; 11; 12; 13; 14]%list.

Section MC.
  Variables (mem rom : word -> option byte) (l r : word) (n : nat) (la lb : list byte).
  Hypothesis Hla : rdn SEGS mem l n = Some la.
  Hypothesis Hlb : rdn SEGS mem r n = Some lb.
  Hypothesis Hn : (Z.of_nat n < 2 ^ 64)%Z.
  Hypothesis Hlw : (bv_unsigned l + Z.of_nat n < 2 ^ 64)%Z.
  Hypothesis Hrw : (bv_unsigned r + Z.of_nat n < 2 ^ 64)%Z.

  #[local] Notation LA i := (nth i la B0).
  #[local] Notation LB i := (nth i lb B0).

  Definition mc_post (regs' : bvmap 5 word) (i : nat) : Prop :=
    (i <= n)%nat /\ (forall j, (j < i)%nat -> LA j = LB j)
    /\ ((i = n /\ getr regs' 10 = Z_to_bv 64 0)
        \/ ((i < n)%nat /\ LA i <> LB i /\ getr regs' 10 = v_sub (LBv (LA i)) (LBv (LB i)))).

  Ltac mlbu F D H j :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?v_addi_0;
            first [apply (rdn_nth1 SEGS _ _ _ _ j H); lia | apply (rdn_nth1_0 SEGS _ _ _ _ H); lia] ]
      | step_simpl]; vnorm.
  Ltac condb := rwH; unfold c_ltu, c_eq, bv_ltu, bv_eqb, LBv; imm_norm; unorm;
    first [ apply Z.eqb_eq | apply Z.eqb_neq ]; first [lia | apply byte_neq_u; assumption | assumption].

  (* [comment removed for export] *)
  Lemma mc_loop : forall (m : nat) regs (ret : word) (i : nat),
    (m = n - i)%nat -> (i < n)%nat ->
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = at_ l (Z.of_nat i) -> getr regs 11 = at_ r (Z.of_nat i) ->
    getr regs 12 = Z_to_bv 64 (Z.of_nat n - Z.of_nat i) ->
    (forall j, (j < i)%nat -> LA j = LB j) ->
    exists regs' (k : nat),
      msteps SEGS (mkst regs (0x23614 : word) mem rom) (mkst regs' ret mem rom)
      /\ regs_agree (fun x => In x memcmp_clob) regs regs' /\ mc_post regs' k.
  Proof.
    induction m as [m IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs ret i Hm Hi Hret H1 H10 H11 H12 Hpre.
    pose proof (u64_range l). pose proof (u64_range r).
    pose proof (u8_range (LA i)) as U1. pose proof (u8_range (LB i)) as U2.
    destruct (byte_eq_dec (LA i) (LB i)) as [Heq|Hne].
    2:{ (* [comment removed for export] *)
      eexists _, i. split; [|split].
      - mlbu F_23614 D_23614 Hla i.                  (* [comment removed for export] *)
        mlbu F_23618 D_23618 Hlb i.                  (* [comment removed for export] *)
        stepb_tk F_2361c D_2361c ltac:(condb).       (* [comment removed for export] *)
        stepn F_23638 D_23638.                       (* [comment removed for export] *)
        stepret F_2363c D_2363c ret ltac:(rwH; reflexivity). apply mst_refl.
      - unfold memcmp_clob. solve_regs_agree.
      - split; [lia|]. split; [exact Hpre|]. right. split; [lia|]. split; [exact Hne|]. gres. reflexivity. }
    destruct (Nat.eq_dec (S i) n) as [Hlast|Hmore].
    { (* [comment removed for export] *)
      eexists _, n. split; [|split].
      - mlbu F_23614 D_23614 Hla i.
        mlbu F_23618 D_23618 Hlb i.
        stepb_ft F_2361c D_2361c ltac:(rwH; rewrite Heq; unfold c_eq; apply bv_eqb_refl).  (* [comment removed for export] *)
        sv F_23620 D_23620 (Z_to_bv 64 (Z.of_nat n - Z.of_nat (S i))).   (* [comment removed for export] *)
        stepn F_23624 D_23624.                       (* [comment removed for export] *)
        stepn F_23628 D_23628.                       (* [comment removed for export] *)
        stepb_ft F_2362c D_2362c ltac:(cond_lia).     (* [comment removed for export] *)
        stepn F_23630 D_23630.                       (* [comment removed for export] *)
        stepret F_23634 D_23634 ret ltac:(rwH; reflexivity). apply mst_refl.
      - unfold memcmp_clob. solve_regs_agree.
      - split; [lia|]. split.
        + intros j Hj. destruct (Nat.eq_dec j i) as [->|]; [exact Heq | apply Hpre; lia].
        + left. split; [reflexivity|]. gres. reflexivity. }
    eapply (runs_trans_k SEGS _ (fun r1 => mkst r1 (0x23614 : word) mem rom)
             (fun r1 => getr r1 1 = ret /\ getr r1 10 = at_ l (Z.of_nat (S i)) /\ getr r1 11 = at_ r (Z.of_nat (S i))
                        /\ getr r1 12 = Z_to_bv 64 (Z.of_nat n - Z.of_nat (S i))
                        /\ regs_agree (fun x => In x memcmp_clob) regs r1)
             (fun r1 => mkst r1 ret mem rom)).
    - eexists. split.
      + mlbu F_23614 D_23614 Hla i.
        mlbu F_23618 D_23618 Hlb i.
        stepb_ft F_2361c D_2361c ltac:(rwH; rewrite Heq; unfold c_eq; apply bv_eqb_refl).
        sv F_23620 D_23620 (Z_to_bv 64 (Z.of_nat n - Z.of_nat (S i))).
        stepn F_23624 D_23624.
        stepn F_23628 D_23628.
        stepb_tk F_2362c D_2362c ltac:(cond_lia).     (* [comment removed for export] *)
        apply mst_refl.
      + cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia).
        unfold memcmp_clob. solve_regs_agree.
    - cbv beta. intros r1 (R1 & R10 & R11 & R12 & AG1).
      destruct (IH (n - S i)%nat ltac:(lia) r1 ret (S i) eq_refl ltac:(lia) Hret R1 R10 R11 R12) as (r2 & k & RUN & AG & POST).
      { intros j Hj. destruct (Nat.eq_dec j i) as [->|]; [exact Heq | apply Hpre; lia]. }
      exists r2, k. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact POST]].
  Qed.

  Theorem ref_memcmp : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = l -> getr regs 11 = r -> getr regs 12 = Z_to_bv 64 (Z.of_nat n) ->
    exists regs' (i : nat),
      msteps SEGS (mkst regs (0x23610 : word) mem rom) (mkst regs' ret mem rom)
      /\ regs_agree (fun x => In x memcmp_clob) regs regs' /\ mc_post regs' i.
  Proof.
    intros regs ret Hret H1 H10 H11 H12.
    destruct (Nat.eq_dec n 0) as [Hz|Hnz].
    { eexists _, 0%nat. split; [|split].
      - stepb_tk F_23610 D_23610 ltac:(cond_lia).     (* [comment removed for export] *)
        stepn F_23630 D_23630.                        (* [comment removed for export] *)
        stepret F_23634 D_23634 ret ltac:(rwH; reflexivity). apply mst_refl.
      - unfold memcmp_clob. solve_regs_agree.
      - split; [lia|]. split; [intros j Hj; lia|]. left. split; [lia|]. gres. reflexivity. }
    eapply (runs_trans_k SEGS _ (fun r1 => mkst r1 (0x23614 : word) mem rom)
             (fun r1 => getr r1 1 = ret /\ getr r1 10 = at_ l (Z.of_nat 0) /\ getr r1 11 = at_ r (Z.of_nat 0)
                        /\ getr r1 12 = Z_to_bv 64 (Z.of_nat n - Z.of_nat 0)
                        /\ regs_agree (fun x => In x memcmp_clob) regs r1)
             (fun r1 => mkst r1 ret mem rom)).
    - eexists. split.
      + stepb_ft F_23610 D_23610 ltac:(cond_lia).     (* [comment removed for export] *)
        apply mst_refl.
      + cbv beta. rewrite !at_0, Z.sub_0_r. repeat split; try assumption; apply regs_agree_refl.
    - cbv beta. intros r1 (R1 & R10 & R11 & R12 & AG1).
      destruct (mc_loop n r1 ret 0%nat ltac:(lia) ltac:(lia) Hret R1 R10 R11 R12 ltac:(intros j Hj; lia))
        as (r2 & k & RUN & AG & POST).
      exists r2, k. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact POST]].
  Qed.

  Theorem ref_bcmp : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = l -> getr regs 11 = r -> getr regs 12 = Z_to_bv 64 (Z.of_nat n) ->
    exists regs' (i : nat),
      msteps SEGS (mkst regs (0x23540 : word) mem rom) (mkst regs' ret mem rom)
      /\ regs_agree (fun x => In x memcmp_clob) regs regs' /\ mc_post regs' i.
  Proof.
    intros regs ret Hret H1 H10 H11 H12.
    destruct (ref_memcmp regs ret Hret H1 H10 H11 H12) as (r2 & k & RUN & REST).
    exists r2, k. split; [|exact REST].
    stepn F_23540 D_23540.                            (* [comment removed for export] *)
    exact RUN.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_post_zero_iff : forall regs' i, mc_post regs' i ->
    (getr regs' 10 = Z_to_bv 64 0 <-> la = lb).
  Proof.
    intros regs' i (Hi & Hpre & Hres).
    pose proof (rdn_length _ _ _ _ _ Hla) as L1. pose proof (rdn_length _ _ _ _ _ Hlb) as L2.
    destruct Hres as [(-> & R0) | (Hlt & Hne & Rs)].
    - split; [intros _|intros _; exact R0].
      apply (nth_ext la lb B0 B0); [lia|]. intros j Hj. apply Hpre. lia.
    - split.
      + intros R0. exfalso. rewrite Rs in R0. apply Hne.
        pose proof (u8_range (LA i)). pose proof (u8_range (LB i)).
        apply bv_eq. unfold v_sub, LBv in R0.
        apply (f_equal bv_unsigned) in R0. rewrite !Z_to_bv_unsigned in R0.
        change (bv_wrap 64 0) with 0%Z in R0. unfold bv_wrap in R0.
        change (bv_modulus 64) with (2^64)%Z in R0.
        rewrite (Z.mod_small (bv_unsigned (LA i)) (2^64)) in R0 by lia.
        rewrite (Z.mod_small (bv_unsigned (LB i)) (2^64)) in R0 by lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        assert (E : ((bv_unsigned (LA i) - bv_unsigned (LB i)) mod 2 ^ 64 = 0)%Z) by exact R0.
        lia.
      + intros ->. exfalso. apply Hne. reflexivity.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End MC.
