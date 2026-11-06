(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.

Lemma v_addi_lit : forall a k, 0 <= a < 2 ^ 64 -> v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold v_addi. rewrite u_lit by lia. reflexivity. Qed.

Lemma v_add_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b Ha Hb. unfold v_add. rewrite !u_lit by lia. reflexivity. Qed.

Lemma btgt_lit : forall a k, 0 <= a < 2 ^ 64 -> btgt (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold btgt. apply v_addi_lit. exact Ha. Qed.

(* [comment removed for export] *)
Ltac rif :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?u else ?v] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let c := eval vm_compute in (bv_eqb a b) in
              lazymatch c with
              | true => change (if bv_eqb a b then u else v) with u
              | false => change (if bv_eqb a b then u else v) with v
              end
          end
      end
  end.

Ltac pc_is v :=
  lazymatch goal with
  | |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
  end.

Lemma signed12_0 : bv_signed (0 : bv 12) = 0. Proof. reflexivity. Qed.
Lemma signed12_1 : bv_signed (1 : bv 12) = 1. Proof. reflexivity. Qed.
Lemma signed12_m1 : bv_signed (4095 : bv 12) = -1. Proof. reflexivity. Qed.
Lemma signed13_m12 : bv_signed (8180 : bv 13) = -12. Proof. reflexivity. Qed.

Section IStrlen.
  Context {fx : FPState}.   (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable x : Z.
  Variables w0 w1 w2 w3 w4 w5 w6 : bv 32.
  Hypothesis Hx : 0 <= x /\ x + 28 < 2 ^ 64.
  Hypothesis F0 : fetch_word SEGS (Z_to_bv 64 x) = Some w0.
  Hypothesis F1 : fetch_word SEGS (Z_to_bv 64 (x + 4)) = Some w1.
  Hypothesis F2 : fetch_word SEGS (Z_to_bv 64 (x + 8)) = Some w2.
  Hypothesis F3 : fetch_word SEGS (Z_to_bv 64 (x + 12)) = Some w3.
  Hypothesis F4 : fetch_word SEGS (Z_to_bv 64 (x + 16)) = Some w4.
  Hypothesis F5 : fetch_word SEGS (Z_to_bv 64 (x + 20)) = Some w5.
  Hypothesis F6 : fetch_word SEGS (Z_to_bv 64 (x + 24)) = Some w6.
  Hypothesis E0 : is_ecall w0 = false.
  Hypothesis E1 : is_ecall w1 = false.
  Hypothesis E2 : is_ecall w2 = false.
  Hypothesis E3 : is_ecall w3 = false.
  Hypothesis E4 : is_ecall w4 = false.
  Hypothesis E5 : is_ecall w5 = false.
  Hypothesis E6 : is_ecall w6 = false.
  Hypothesis D0 : decode_any w0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
  Hypothesis D1 : decode_any w1 = Some (Op ALU_ADD 12 10 11, 4%Z).
  Hypothesis D2 : decode_any w2 = Some (Load SZ1 false 12 12 0, 4%Z).
  Hypothesis D3 : decode_any w3 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis D4 : decode_any w4 = Some (Branch BC_NE 12 0 8180, 4%Z).
  Hypothesis D5 : decode_any w5 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
  Hypothesis D6 : decode_any w6 = Some (Jalr 0 1 0, 4%Z).

  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Variable s : Z.
  Variable L : nat.
  Variable byte : nat -> byte.
  Hypothesis Hs : 0 <= s /\ s + Z.of_nat L + 1 < 2 ^ 64.
  Hypothesis Rd : forall j, (j <= L)%nat -> rdn SEGS M (Z_to_bv 64 (s + Z.of_nat j)) 1 = Some [byte j].
  Hypothesis Bnz : forall j, (j < L)%nat -> bv_unsigned (byte j) <> 0.
  Hypothesis Bz : bv_unsigned (byte L) = 0.

  Definition istrlen_post (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 10 = Z_to_bv 64 (Z.of_nat L)
    /\ getr regs' 11 = Z_to_bv 64 (Z.of_nat L + 1)
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ regs_agree (fun r => r = 10%bv \/ r = 11%bv \/ r = 12%bv) regs regs'.

  (* [comment removed for export] *)
  #[using="w1 w2 w3 w4 w5 w6 Hx F1 F2 F3 F4 F5 F6 E1 E2 E3 E4 E5 E6 D1 D2 D3 D4 D5 D6 byte Hs Rd Bnz Bz"] Lemma istrlen_loop : forall n j regs (ret : word),
    (j + n = L)%nat ->
    getr regs 10 = Z_to_bv 64 s ->
    getr regs 11 = Z_to_bv 64 (Z.of_nat j) ->
    ret_ok ret -> getr regs 1 = ret ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (x + 4)) M rom) (mkst regs' ret M rom)
      /\ istrlen_post regs regs'.
  Proof. LiaFast.lf_pins (fun (w1 w2 w3 w4 w5 w6 Hx F1 F2 F3 F4 F5 F6 E1 E2 E3 E4 E5 E6 D1 D2 D3 D4 D5 D6 byte Hs Rd Bnz Bz : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros j regs ret Hjn H10 H11 Hret H1.
    - assert (j = L) by lia. subst j.
      eexists. split.
      + eapply mst_step; [reflexivity| |].
        { eapply (step_add SEGS regs _ M rom w1 12 10 11 F1 E1 D1). }
        rif. rewrite H10, H11, v_add_lit, v_addi_lit by lia. pc_is (x + 8).
        eapply mst_step; [reflexivity| |].
        { eapply (step_lbu SEGS _ _ M rom w2 12 12 0 (byte L) F2 E2 D2).
          rewrite getr_same by reg_neq_tac. rewrite signed12_0, v_addi_lit, Z.add_0_r by lia. apply Rd. lia. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 12). rewrite Bz.
        eapply mst_step; [reflexivity| |].
        { eapply (step_addi SEGS _ _ M rom w3 11 11 1 F3 E3 D3). }
        rif. rewrite signed12_1, v_addi_lit by lia. pc_is (x + 16).
        rewrite !getr_other by reg_neq_tac. rewrite H11, v_addi_lit by lia.
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_ft SEGS _ _ M rom w4 12 0 8180 F4 E4 D4).
          rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac. rewrite getr_zero. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 20).
        eapply mst_step; [reflexivity| |].
        { eapply (step_addi SEGS _ _ M rom w5 10 11 4095 F5 E5 D5). }
        rif. rewrite signed12_m1, v_addi_lit by lia. pc_is (x + 24).
        rewrite getr_same by reg_neq_tac. rewrite v_addi_lit by lia.
        eapply mst_step; [reflexivity| |].
        { eapply (step_jalr_x0 SEGS _ _ M rom w6 1 0 ret F6 E6 D6).
          rewrite !getr_other by reg_neq_tac. exact H1. }
        rewrite signed12_0. unfold ret_ok in Hret. rewrite Hret. apply mst_refl.
      + split; [|split; [|split]].
        * rewrite getr_same by reg_neq_tac. apply f_equal. lia.
        * rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac. reflexivity.
        * rewrite !getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac. reflexivity.
        * intros r Hr. rewrite !getr_other; [reflexivity| | | |]; intros ->; apply Hr; auto.
    - assert (Hj : (j < L)%nat) by lia.
      destruct (IH (S j) (regupd (regupd (regupd regs 12 (Z_to_bv 64 (s + Z.of_nat j))) 12 (Z_to_bv 64 (bv_unsigned (byte j))))
                             11 (Z_to_bv 64 (Z.of_nat (S j)))) ret ltac:(lia))
        as [regs' [Hms Hpost]].
      { rewrite !getr_other by reg_neq_tac. exact H10. }
      { rewrite getr_same by reg_neq_tac. reflexivity. }
      { exact Hret. }
      { rewrite !getr_other by reg_neq_tac. exact H1. }
      exists regs'. split.
      + eapply mst_step; [reflexivity| |].
        { eapply (step_add SEGS regs _ M rom w1 12 10 11 F1 E1 D1). }
        rif. rewrite H10, H11, v_add_lit, v_addi_lit by lia. pc_is (x + 8).
        eapply mst_step; [reflexivity| |].
        { eapply (step_lbu SEGS _ _ M rom w2 12 12 0 (byte j) F2 E2 D2).
          rewrite getr_same by reg_neq_tac. rewrite signed12_0, v_addi_lit, Z.add_0_r by lia. apply Rd. lia. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 12).
        eapply mst_step; [reflexivity| |].
        { eapply (step_addi SEGS _ _ M rom w3 11 11 1 F3 E3 D3). }
        rif. rewrite signed12_1, v_addi_lit by lia. pc_is (x + 16).
        rewrite !getr_other by reg_neq_tac. rewrite H11, v_addi_lit by lia.
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_tk SEGS _ _ M rom w4 12 0 8180 F4 E4 D4).
          rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac. rewrite getr_zero.
          apply c_eq_0_false. rewrite u_lit; [apply Bnz; exact Hj|]. pose proof (u8_range (byte j)). lia. }
        rewrite signed13_m12, btgt_lit by lia. pc_is (x + 4).
        replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
        exact Hms.
      + destruct Hpost as (P10 & P11 & P12 & Pag). split; [exact P10|]. split; [exact P11|]. split; [exact P12|].
        intros r Hr. rewrite (Pag r Hr). rewrite !getr_other; [reflexivity| | |]; intros ->; apply Hr; auto.
  Qed.

  #[using="w0 w1 w2 w3 w4 w5 w6 Hx F0 F1 F2 F3 F4 F5 F6 E0 E1 E2 E3 E4 E5 E6 D0 D1 D2 D3 D4 D5 D6 byte Hs Rd Bnz Bz"] Theorem istrlen_run : forall regs (ret : word),
    getr regs 10 = Z_to_bv 64 s ->
    ret_ok ret -> getr regs 1 = ret ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' ret M rom)
      /\ istrlen_post regs regs'.
  Proof. LiaFast.lf_pins (fun (w0 w1 w2 w3 w4 w5 w6 Hx F0 F1 F2 F3 F4 F5 F6 E0 E1 E2 E3 E4 E5 E6 D0 D1 D2 D3 D4 D5 D6 byte Hs Rd Bnz Bz : LiaFast.U) => LiaFast.u0).
    intros regs ret H10 Hret H1.
    destruct (istrlen_loop L 0 (regupd regs 11 (Z_to_bv 64 0)) ret ltac:(lia)) as [regs' [Hms Hpost]].
    { rewrite getr_other by reg_neq_tac. exact H10. }
    { rewrite getr_same by reg_neq_tac. reflexivity. }
    { exact Hret. }
    { rewrite getr_other by reg_neq_tac. exact H1. }
    exists regs'. split.
    - eapply mst_step; [reflexivity| |].
      { eapply (step_addi SEGS regs _ M rom w0 11 0 0 F0 E0 D0). }
      rif. rewrite getr_zero, signed12_0, v_addi_lit by lia. rewrite v_addi_lit by lia. pc_is (x + 4).
      exact Hms.
    - destruct Hpost as (P10 & P11 & P12 & Pag). split; [exact P10|]. split; [exact P11|]. split; [exact P12|].
      intros r Hr. rewrite (Pag r Hr). rewrite getr_other; [reflexivity|]. intros ->; apply Hr; auto.
  Qed.
End IStrlen.
(* [comment removed for export] *)
