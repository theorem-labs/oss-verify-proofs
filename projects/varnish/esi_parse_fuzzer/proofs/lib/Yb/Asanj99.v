(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk StepTac ShapeAlg SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.RefL1zx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import AsanPlan Asanqlm.

Module Asangat.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.

Lemma v_addi_lit : forall a k, 0 <= a < 2 ^ 64 -> v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold v_addi. rewrite u_lit by lia. reflexivity. Qed.

Lemma btgt_lit : forall a k, 0 <= a < 2 ^ 64 -> btgt (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold btgt. apply v_addi_lit. exact Ha. Qed.

Lemma c_eq_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)

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

(* [comment removed for export] *)
Ltac pc_is v :=
  lazymatch goal with
  | |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
  end.

(* [comment removed for export] *)
Lemma signed12_0 : bv_signed (0 : bv 12) = 0. Proof. reflexivity. Qed.
Lemma signed12_1 : bv_signed (1 : bv 12) = 1. Proof. reflexivity. Qed.
Lemma signed12_8 : bv_signed (8 : bv 12) = 8. Proof. reflexivity. Qed.
Lemma signed12_m1 : bv_signed (4095 : bv 12) = -1. Proof. reflexivity. Qed.
Lemma signed13_m8 : bv_signed (8184 : bv 13) = -8. Proof. reflexivity. Qed.
Lemma signed13_m12 : bv_signed (8180 : bv 13) = -12. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EnvLoop.
  Variable SEGS : list Segment.
  Variable x : Z.
  Variables w1 w2 w3 : bv 32.
  Hypothesis Hx : 0 <= x /\ x + 12 < 2 ^ 64.
  Hypothesis F1 : fetch_word SEGS (Z_to_bv 64 x) = Some w1.
  Hypothesis F2 : fetch_word SEGS (Z_to_bv 64 (x + 4)) = Some w2.
  Hypothesis F3 : fetch_word SEGS (Z_to_bv 64 (x + 8)) = Some w3.
  Hypothesis E1 : is_ecall w1 = false.
  Hypothesis E2 : is_ecall w2 = false.
  Hypothesis E3 : is_ecall w3 = false.
  Hypothesis D1 : decode_any w1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis D2 : decode_any w2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis D3 : decode_any w3 = Some (Branch BC_NE 10 0 8184, 4%Z).

  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Variable e : Z.
  Variable envc : nat.
  Variable ptr : nat -> word.
  Hypothesis He : 0 <= e /\ e + 8 * Z.of_nat envc + 16 < 2 ^ 64.
  Hypothesis Rk : forall k, (k < envc)%nat ->
    rdn SEGS M (Z_to_bv 64 (e + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (ptr k))
    /\ bv_unsigned (ptr k) <> 0.
  Hypothesis Rn : rdn SEGS M (Z_to_bv 64 (e + 8 * Z.of_nat envc)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Definition env_post (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 9 = Z_to_bv 64 (e + 8 * Z.of_nat envc + 8)
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ regs_agree (fun r => r = 9%bv \/ r = 10%bv) regs regs'.

  Lemma env_loop : forall n k regs,
    (k + n = envc)%nat ->
    getr regs 9 = Z_to_bv 64 (e + 8 * Z.of_nat k) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 12)) M rom)
      /\ env_post regs regs'.
  Proof.
    induction n as [|n IH]; intros k regs Hkn H9.
    - (* [comment removed for export] *)
      assert (k = envc) by lia. subst k.
      eexists. split.
      + eapply mst_step; [reflexivity| |].
        { eapply (step_ld SEGS regs _ M rom w1 10 9 0 _ (Z_to_bv 64 0) F1 E1 D1).
          - rewrite H9, signed12_0, v_addi_lit by lia. rewrite Z.add_0_r. exact Rn.
          - apply bytes_le_to_Z_8. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        eapply mst_step; [reflexivity| |].
        { eapply (step_addi SEGS _ _ M rom w2 9 9 8 F2 E2 D2). }
        rif. rewrite v_addi_lit by lia. pc_is (x + 8). rewrite signed12_8.
        rewrite getr_other by reg_neq_tac. rewrite H9, v_addi_lit by lia.
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_ft SEGS _ _ M rom w3 10 0 8184 F3 E3 D3).
          rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
          rewrite getr_zero. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 12). apply mst_refl.
      + split; [|split].
        * rewrite getr_same by reg_neq_tac. reflexivity.
        * rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac. reflexivity.
        * intros r Hr. rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
    - assert (Hk : (k < envc)%nat) by lia.
      destruct (Rk k Hk) as [Rd Hnz].
      destruct (IH (S k) (regupd (regupd regs 10 (ptr k)) 9 (Z_to_bv 64 (e + 8 * Z.of_nat (S k)))) ltac:(lia)) as [regs' [Hms Hpost]].
      { rewrite getr_same by reg_neq_tac. reflexivity. }
      exists regs'. split.
      + eapply mst_step; [reflexivity| |].
        { eapply (step_ld SEGS regs _ M rom w1 10 9 0 _ (ptr k) F1 E1 D1).
          - rewrite H9, signed12_0, v_addi_lit by lia. rewrite Z.add_0_r. exact Rd.
          - apply bytes_le_to_Z_8. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        eapply mst_step; [reflexivity| |].
        { eapply (step_addi SEGS _ _ M rom w2 9 9 8 F2 E2 D2). }
        rif. rewrite v_addi_lit by lia. pc_is (x + 8). rewrite signed12_8.
        rewrite getr_other by reg_neq_tac. rewrite H9, v_addi_lit by lia.
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_tk SEGS _ _ M rom w3 10 0 8184 F3 E3 D3).
          rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
          rewrite getr_zero. apply c_eq_0_false. exact Hnz. }
        rewrite signed13_m8, btgt_lit by lia. pc_is x.
        replace (e + 8 * Z.of_nat k + 8) with (e + 8 * Z.of_nat (S k)) by lia.
        exact Hms.
      + destruct Hpost as (P9 & P10 & Pag). split; [exact P9|]. split; [exact P10|].
        intros r Hr. rewrite (Pag r Hr). rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
  Qed.
End EnvLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PnLoop.
  Variable SEGS : list Segment.
  Variable x : Z.            (* [comment removed for export] *)
  Variables w0 w1 w2 w3 w4 : bv 32.
  Hypothesis Hx : 8 <= x /\ x + 12 < 2 ^ 64.
  Hypothesis F0 : fetch_word SEGS (Z_to_bv 64 (x - 8)) = Some w0.
  Hypothesis F1 : fetch_word SEGS (Z_to_bv 64 (x - 4)) = Some w1.
  Hypothesis F2 : fetch_word SEGS (Z_to_bv 64 x) = Some w2.
  Hypothesis F3 : fetch_word SEGS (Z_to_bv 64 (x + 4)) = Some w3.
  Hypothesis F4 : fetch_word SEGS (Z_to_bv 64 (x + 8)) = Some w4.
  Hypothesis E0 : is_ecall w0 = false.
  Hypothesis E1 : is_ecall w1 = false.
  Hypothesis E2 : is_ecall w2 = false.
  Hypothesis E3 : is_ecall w3 = false.
  Hypothesis E4 : is_ecall w4 = false.
  Hypothesis D0 : decode_any w0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis D1 : decode_any w1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis D2 : decode_any w2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis D3 : decode_any w3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis D4 : decode_any w4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  Variable M0 : word -> option byte.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Variable p pn : Z.
  Variable s : list byte.
  Hypothesis Hp : 0 <= p /\ p + 8 <= 2 ^ 64.
  Hypothesis Hpn : 0 <= pn /\ pn + Z.of_nat (length s) + 2 < 2 ^ 64.
  Hypothesis Hapart : p + 8 <= pn \/ pn + Z.of_nat (length s) + 1 <= p.
  Hypothesis Hnz : ~ In (Z_to_bv 8 0) s.
  Hypothesis Hrd : forall j, (j <= length s)%nat ->
    rdn SEGS M0 (Z_to_bv 64 (pn + Z.of_nat j)) 1 = Some [byte_at s j].
  Hypothesis Hst : store_ok SEGS M0 (Z_to_bv 64 p) 8 = true.

  (* [comment removed for export] *)
  Definition cellrel (M : word -> option byte) : Prop :=
    (forall a : word, bv_unsigned a < p \/ p + 8 <= bv_unsigned a -> M a = M0 a) /\ mem_grows M0 M.

  Lemma cellrel_refl : cellrel M0.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Lemma cellrel_wbytes : forall M (v : word), cellrel M -> cellrel (wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 v)).
  Proof.
    intros M v [H1 H2]. split.
    - intros a Ha. rewrite <- (H1 a Ha).
      destruct Ha as [Ha|Ha].
      + apply wbytes_below; rewrite ?length_N_to_le_bytes, u_lit by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
      + apply wbytes_above. rewrite length_N_to_le_bytes, u_lit by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - eapply mem_grows_trans; [exact H2 | apply wbytes_grows].
  Qed.

  Lemma cellrel_rd : forall M j, cellrel M -> (j <= length s)%nat ->
    rdn SEGS M (Z_to_bv 64 (pn + Z.of_nat j)) 1 = Some [byte_at s j].
  Proof.
    intros M j [H1 _] Hj. rewrite <- (Hrd j Hj). apply rdn_ext.
    - rewrite u_lit by lia. change (Z.of_nat 1) with 1. lia.
    - intros y Hy. rewrite u_lit in Hy by lia. change (Z.of_nat 1) with 1 in Hy. apply H1. lia.
  Qed.

  Lemma cellrel_st : forall M, cellrel M -> store_ok SEGS M (Z_to_bv 64 p) 8 = true.
  Proof. intros M [_ H2]. eapply store_ok_mono; [exact H2 | exact Hst]. Qed.

  Definition pn_post (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 11 = Z_to_bv 64 (pn + Z.of_nat (length s) + 1)
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ regs_agree (fun r => r = 11%bv \/ r = 13%bv) regs regs'.

  Lemma byte_u : forall b : byte, 0 <= bv_unsigned b < 256.
  Proof. intros b. pose proof (u8_range b). lia. Qed.

  Lemma pn_loop : forall l2 j regs M,
    skipn j s = l2 -> (j <= length s)%nat ->
    getr regs 10 = Z_to_bv 64 p ->
    getr regs 11 = Z_to_bv 64 (pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    cellrel M ->
    exists regs' M',
      msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 12)) M' rom)
      /\ pn_post regs regs' /\ cellrel M'.
  Proof.
    induction l2 as [|b l2 IH]; intros j regs M Hskip Hj H10 H11 H12 HM.
    - (* [comment removed for export] *)
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      subst j.
      exists (regupd regs 13 (Z_to_bv 64 (bv_unsigned (byte_at s (length s))))), M. split; [|split; [|exact HM]].
      + eapply mst_step; [reflexivity| |].
        { eapply (step_lbu SEGS regs _ M rom w2 13 11 4095 (byte_at s (length s)) F2 E2 D2).
          rewrite H11, signed12_m1, v_addi_lit by lia.
          replace (pn + Z.of_nat (length s) + 1 + -1) with (pn + Z.of_nat (length s)) by lia.
          apply cellrel_rd; [exact HM | lia]. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        rewrite byte_at_len. change (bv_unsigned (Z_to_bv 8 0)) with 0.
        eapply mst_step; [reflexivity| |].
        { eapply (step_beq_ft SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
          rewrite getr_same by reg_neq_tac. rewrite getr_other by reg_neq_tac.
          rewrite H12. rewrite c_eq_lit by lia. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 8).
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_ft SEGS _ _ M rom w4 13 0 8180 F4 E4 D4).
          rewrite getr_same by reg_neq_tac. rewrite getr_zero. rewrite c_eq_lit by lia. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 12). apply mst_refl.
      + split; [|split].
        * rewrite getr_other by reg_neq_tac. exact H11.
        * rewrite getr_same by reg_neq_tac. rewrite byte_at_len. reflexivity.
        * intros r Hr. rewrite getr_other; [reflexivity|]. intros ->. apply Hr. auto.
    - assert (Hjlt : (j < length s)%nat).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      assert (Hb : byte_at s j = b).
      { unfold byte_at. rewrite app_nth1 by lia. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
      assert (Hbnz : bv_unsigned b <> 0).
      { intros Hb0. apply Hnz. rewrite <- Hb in Hb0. rewrite nth_lt_byte_at in Hb0 by lia.
        replace (Z_to_bv 8 0) with (nth j s (Z_to_bv 8 0)); [apply nth_In; lia|].
        apply bv_eq. rewrite Hb0. reflexivity. }
      assert (Hskip' : skipn (S j) s = l2).
      { replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, Hskip. reflexivity. }
      pose proof (byte_u b) as Hbu.
      (* [comment removed for export] *)
      set (regs1 := regupd regs 13 (Z_to_bv 64 (bv_unsigned b))).
      assert (S1 : RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 x) M rom) = MachineOk (mkst regs1 (Z_to_bv 64 (x + 4)) M rom)).
      { erewrite (step_lbu SEGS regs _ M rom w2 13 11 4095 b F2 E2 D2).
        - rif. rewrite v_addi_lit by lia. reflexivity.
        - rewrite H11, signed12_m1, v_addi_lit by lia.
          replace (pn + Z.of_nat j + 1 + -1) with (pn + Z.of_nat j) by lia. rewrite <- Hb.
          apply cellrel_rd; [exact HM | lia]. }
      assert (G13 : getr regs1 13 = Z_to_bv 64 (bv_unsigned b)) by (unfold regs1; rewrite getr_same by reg_neq_tac; reflexivity).
      assert (G10 : getr regs1 10 = Z_to_bv 64 p) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H10).
      assert (G11 : getr regs1 11 = Z_to_bv 64 (pn + Z.of_nat j + 1)) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H11).
      assert (G12 : getr regs1 12 = Z_to_bv 64 47) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H12).
      destruct (Z.eqb (bv_unsigned b) 47) eqn:Eb.
      + (* [comment removed for export] *)
        set (M1 := wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 (pn + Z.of_nat j + 1)))).
        set (regs2 := regupd regs1 11 (Z_to_bv 64 (pn + Z.of_nat (S j) + 1))).
        assert (HM1 : cellrel M1) by (unfold M1; apply cellrel_wbytes; exact HM).
        destruct (IH (S j) regs2 M1 Hskip' ltac:(lia)) as (regs' & M' & Hms & Hpost & HM').
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G10. }
        { unfold regs2. rewrite getr_same by reg_neq_tac. reflexivity. }
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G12. }
        { exact HM1. }
        exists regs', M'. split; [|split; [|exact HM']].
        * eapply mst_step; [reflexivity | exact S1 |].
          eapply mst_step; [reflexivity| |].
          { eapply (step_beq_tk SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
            rewrite G13, G12. rewrite c_eq_lit by lia. exact Eb. }
          rewrite signed13_m12, btgt_lit by lia. pc_is (x - 8).
          eapply mst_step; [reflexivity| |].
          { eapply (step_sd_at SEGS regs1 _ M rom w0 10 11 0 (Z_to_bv 64 p) _ F0 E0 D0).
            - rewrite G10, signed12_0, v_addi_lit by lia. f_equal. lia.
            - exact G11.
            - apply cellrel_st. exact HM. }
          fold M1. rewrite v_addi_lit by lia. pc_is (x - 4).
          eapply mst_step; [reflexivity| |].
          { eapply (step_addi SEGS regs1 _ M1 rom w1 11 11 1 F1 E1 D1). }
          rif. rewrite G11, signed12_1, !v_addi_lit by lia. pc_is x.
          replace (pn + Z.of_nat j + 1 + 1) with (pn + Z.of_nat (S j) + 1) by lia.
          exact Hms.
        * destruct Hpost as (P11 & P13 & Pag). split; [exact P11|]. split; [exact P13|].
          intros r Hr. rewrite (Pag r Hr). unfold regs2, regs1.
          rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
      + (* [comment removed for export] *)
        set (regs2 := regupd regs1 11 (Z_to_bv 64 (pn + Z.of_nat (S j) + 1))).
        destruct (IH (S j) regs2 M Hskip' ltac:(lia)) as (regs' & M' & Hms & Hpost & HM').
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G10. }
        { unfold regs2. rewrite getr_same by reg_neq_tac. reflexivity. }
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G12. }
        { exact HM. }
        exists regs', M'. split; [|split; [|exact HM']].
        * eapply mst_step; [reflexivity | exact S1 |].
          eapply mst_step; [reflexivity| |].
          { eapply (step_beq_ft SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
            rewrite G13, G12. rewrite c_eq_lit by lia. exact Eb. }
          rewrite v_addi_lit by lia. pc_is (x + 8).
          eapply mst_step; [reflexivity| |].
          { eapply (step_bne_tk SEGS _ _ M rom w4 13 0 8180 F4 E4 D4).
            rewrite G13, getr_zero. apply c_eq_0_false. rewrite u_lit by lia. exact Hbnz. }
          rewrite signed13_m12, btgt_lit by lia. pc_is (x - 4).
          eapply mst_step; [reflexivity| |].
          { eapply (step_addi SEGS regs1 _ M rom w1 11 11 1 F1 E1 D1). }
          rif. rewrite G11, signed12_1, !v_addi_lit by lia. pc_is x.
          replace (pn + Z.of_nat j + 1 + 1) with (pn + Z.of_nat (S j) + 1) by lia.
          exact Hms.
        * destruct Hpost as (P11 & P13 & Pag). split; [exact P11|]. split; [exact P13|].
          intros r Hr. rewrite (Pag r Hr). unfold regs2, regs1.
          rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
  Qed.
End PnLoop.
End Asangat.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99.Asangat.

Module Asanfjy.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk StepTac ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.RefL1zx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import AsanPlan Asanqlm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

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

(* [comment removed for export] *)
Ltac pc_is v :=
  lazymatch goal with
  | |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma len_eqb_sound : forall SEGS E M k n m,
  know_ok SEGS E M k -> len_eqb k n m = true -> edenot E n = edenot E m.
Proof.
  intros SEGS E M k n m HK H. unfold len_eqb in H. apply orb_prop in H as [H|H].
  - apply expr_eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as A2.
    cbn [xt_den] in A1, A2. apply bv_eq. lia.
Qed.

(* [comment removed for export] *)
Lemma kwritable_sound : forall segs E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable allkn k b off n = true -> 0 <= n ->
  store_ok segs M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
  intros segs E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable] in H.
  destruct K; try exact (IH Hrest H).
  lazymatch type of HKK with kentry_ok _ _ _ (KWr ?a ?n) => destruct a as [wb wk]; rename n into wn end.
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
  { intros A B. split; [|lia].
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
  lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hc0.
    pose proof (xlo_sound segs E M allkn wn wl Hall Hx) as Hwl. unfold elenZ in *. apply CORE; lia.
  - lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
    apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
    apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
    destruct (xinside_sound segs E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
    unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u64_lit in I2 by lia.
    unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kimg_cut_sound : forall segs E M k a n,
  know_ok segs E M k -> know_ok segs E M (kimg_cut k a n).
Proof.
  intros segs E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
  lazymatch goal with |- Forall _ (if _ then [KImg ?a ?b] else _) => rename a into lo; rename b into hi end.
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
  apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
  cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Hnone).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
  - destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.

(* [comment removed for export] *)
Lemma reg_lit5 : forall n, (n < 32)%nat -> bv_unsigned (Z_to_bv 5 (Z.of_nat n)) = Z.of_nat n.
Proof.
  intros n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia.
Qed.

Lemma regs_ok_post2 : forall E sr R R' n1 (r1 : bv 5) e1 n2 (r2 : bv 5) e2,
  regs_ok E sr R -> (0 < n1 < 32)%nat -> (0 < n2 < 32)%nat -> n1 <> n2 ->
  bv_unsigned r1 = Z.of_nat n1 -> bv_unsigned r2 = Z.of_nat n2 ->
  getr R' r1 = edenot E e1 -> getr R' r2 = edenot E e2 ->
  (forall r, r <> r1 -> r <> r2 -> getr R' r = getr R r) ->
  regs_ok E (sr_upd (sr_upd sr n1 e1) n2 e2) R'.
Proof.
  intros E sr R R' n1 r1 e1 n2 r2 e2 HR Hn1 Hn2 Hne U1 U2 G1 G2 Gr.
  assert (E1 : r1 = Z_to_bv 5 (Z.of_nat n1)) by (apply bv_eq; rewrite reg_lit5 by lia; exact U1).
  assert (E2 : r2 = Z_to_bv 5 (Z.of_nat n2)) by (apply bv_eq; rewrite reg_lit5 by lia; exact U2).
  pose proof (regs_ok_set_n E _ _ n2 e2 (edenot E e2) (regs_ok_set_n E sr R n1 e1 (edenot E e1) HR Hn1 eq_refl) Hn2 eq_refl) as K.
  rewrite <- E1, <- E2 in K.
  assert (Z1 : r1 <> 0%bv) by (intros H0; apply (f_equal bv_unsigned) in H0; rewrite U1 in H0; change (bv_unsigned (0%bv : bv 5)) with 0 in H0; lia).
  assert (Z2 : r2 <> 0%bv) by (intros H0; apply (f_equal bv_unsigned) in H0; rewrite U2 in H0; change (bv_unsigned (0%bv : bv 5)) with 0 in H0; lia).
  assert (Z12 : r1 <> r2) by (intros H0; apply (f_equal bv_unsigned) in H0; lia).
  intros r. rewrite <- (K r).
  destruct (bv_eqb r r2) eqn:Q2.
  { unfold bv_eqb in Q2. apply Z.eqb_eq in Q2. apply bv_eq in Q2. subst r. rewrite getr_same by exact Z2. exact G2. }
  assert (N2 : r <> r2) by (intros ->; rewrite bv_eqb_refl in Q2; discriminate).
  rewrite (getr_other _ r2 _ r N2).
  destruct (bv_eqb r r1) eqn:Q1.
  { unfold bv_eqb in Q1. apply Z.eqb_eq in Q1. apply bv_eq in Q1. subst r. rewrite getr_same by exact Z1. exact G1. }
  assert (N1 : r <> r1) by (intros ->; rewrite bv_eqb_refl in Q1; discriminate).
  rewrite (getr_other _ r1 _ r N1). apply Gr; assumption.
Qed.

(* [comment removed for export] *)
Fixpoint nb_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ a c | EAluw _ a c | EMd _ a c | EMdw _ a c => nb_lt b a && nb_lt b c
  | EExt _ _ _ a => nb_lt b a
  | EBlob _ _ _ _ => false
  end.

Lemma edenot_ev_agree : forall b E E' e,
  nb_lt b e = true -> (forall n, (n < b)%nat -> ev E n = ev E' n) -> edenot E e = edenot E' e.
Proof.
  intros b E E' e. induction e; cbn [nb_lt edenot]; intros H Hag; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1 Hag), (IHe2 H2 Hag); reflexivity).
  - apply Hag. apply Nat.ltb_lt. exact H.
  - rewrite (IHe H Hag). reflexivity.
  - discriminate.
Qed.

(* [comment removed for export] *)
Lemma fetch_lit : forall segs z (w : word) x,
  bv_unsigned w = z -> fetch_word segs w = Some x -> fetch_word segs (Z_to_bv 64 z) = Some x.
Proof.
  intros segs z w x Hw Hf. replace (Z_to_bv 64 z) with w; [exact Hf|].
  apply bv_eq. rewrite Z_to_bv_unsigned, <- Hw. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma with_ss_idem : forall cs s1 s2, with_ss (with_ss cs s1) s2 = with_ss cs s2.
Proof. reflexivity. Qed.
Lemma a_ss_with_ss : forall cs s, a_ss (with_ss cs s) = s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_base_le' : forall a : word, bv_unsigned (page_base a) <= bv_unsigned a
                                       /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
                                       /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)

Lemma A_wf_allowA' : forall A E cs, A_wf (allowA A E cs).
Proof.
  intros A E cs. unfold A_wf, allowA. apply Forall_forall. intros iv Hin.
  apply in_flat_map in Hin as [p [_ Hin]]. unfold allow1 in Hin.
  pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
  destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; unfold page_size.
  - pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))). unfold uE in *.
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
  - pose proof (pagedown_le (sh_lo A E p)). pose proof (pageup_ge (sh_hi A E p)). unfold sh_lo, sh_hi, uE in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Section NodesD.
  (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition Hv (E : env) (cs : acs) (model : Model) : word -> bool := fun a => negb (vis A E cs model a).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma Hv_high : forall E cs model (a : word), alloc_top (m_vmmaps model) <= bv_unsigned a -> Hv E cs model a = false.
  Proof.
    intros E cs model a Ha. unfold Hv, vis. apply negb_false_iff.
    replace (alloc_top (m_vmmaps model) <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Ha).
    rewrite orb_true_r. reflexivity.
  Qed.

  (* [comment removed for export] *)

  Lemma lazy_cover_vis : forall E cs R FULL model,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> lazy_cover (Hv E cs model) (m_vm_lazy model) (allowA A E cs).
  Proof.
    intros E cs R FULL model HC w Hlz Hh. unfold Hv in Hh.
    apply negb_false_iff in Hh. unfold vis in Hh. rename Hh into Hv0.
    (* [comment removed for export] *)
    pose proof Hlz as Hlz0. unfold page_in_ranges in Hlz0. apply existsb_exists in Hlz0 as [iv [Hiniv Hbiv]].
    apply andb_prop in Hbiv as [Hbi1 Hbi2]. apply Z.leb_le in Hbi1. apply Z.leb_le in Hbi2.
    pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC) iv Hiniv) as [L1 L2].
    pose proof (page_base_le' w) as (P1 & P2 & P3). unfold page_size in *.
    pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (H0 & H1 & H2 & H3).
    apply orb_prop in Hv0 as [Hv0|Hv0].
    - exfalso. apply orb_prop in Hv0 as [Hv0|Hv0].
      + unfold in_hull in Hv0. apply andb_prop in Hv0 as [Hv1 Hv2]. apply Z.leb_le in Hv1. apply Z.ltb_lt in Hv2.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        destruct L1 as [L1|L1]; lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      + apply Z.leb_le in Hv0. lia.
    - apply andb_prop in Hv0 as [_ Hv0]. rewrite Hlz in Hv0. cbn [negb orb] in Hv0.
      unfold page_allowedb, allowA. apply existsb_exists. unfold page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      unfold in_allow in Hv0. apply orb_prop in Hv0 as [Hv0|Hv0].
      + unfold in_vis in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
        apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
        exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
        * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. left. reflexivity.
        * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      + unfold in_sh in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
        apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
        exists (pagedown (sh_lo A E p), pageup (sh_hi A E p)). split.
        * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. right. left. reflexivity.
        * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma H_off_segments_vis : forall E cs model, H_off_segments SEGS (Hv E cs model).
  Proof.
    intros E cs model a Hh. unfold Hv in Hh. apply negb_true_iff in Hh. unfold vis in Hh.
    apply orb_false_iff in Hh as [Hh _]. apply orb_false_iff in Hh as [Hh _].
    apply SEGS_in_hull. exact Hh.
  Qed.

  (* [comment removed for export] *)
  Lemma mrestrict_Hv_high : forall E cs model FULL (a : word),
    alloc_top (m_vmmaps model) <= bv_unsigned a -> mrestrict (Hv E cs model) FULL a = FULL a.
  Proof. intros. unfold mrestrict. rewrite Hv_high by assumption. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma Mr_grows_Hv : forall E cs model FULL,
    mem_grows (Mr A argH E cs model FULL) (mrestrict (Hv E cs model) FULL).
  Proof.
    intros E cs model FULL a. unfold Mr, mrestrict, hid, Hv.
    destruct (argH E a), (vis A E cs model a); cbn; auto.
  Qed.

  Lemma munrestrict_mrestrict : forall (H : word -> bool) FULL, munrestrict H FULL (mrestrict H FULL) = FULL.
  Proof.
    intros H FULL. apply functional_extensionality. intros a. unfold munrestrict, mrestrict. destruct (H a); reflexivity.
  Qed.

End NodesD.
End Asanfjy.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99.Asanfjy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l.

Module Asanfrq.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec StoreOk ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import AsanPlan Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import AP. Import APS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Lemma bytes_le_to_Z_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by lia. exact IH.
Qed.

Section Sound2.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
Lemma kread_bytes_sound : forall E M k n b off zs,
  know_ok SEGS E M k ->
  kread_bytes SEGS n k b off = Some zs ->
  0 <= estart E (SA b off) -> estart E (SA b off) + Z.of_nat n <= 2 ^ 64 ->
  exists bs, length bs = n /\ map bv_unsigned bs = zs
             /\ forall j, (j < n)%nat -> rdn SEGS M (Z_to_bv 64 (estart E (SA b off) + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros E M k n. induction n as [|n IH]; intros b off zs HK Hr Hlo Hhi.
  - cbn in Hr. injection Hr as <-. exists []. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity. intros j Hj. lia.
  - cbn [kread_bytes] in Hr.
    destruct (kreadZ SEGS k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes SEGS n k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate]. injection Hr as <-.
    unfold kreadZ in Hz.
    pose proof (know_lookup_sound SEGS E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as KL.
    destruct (know_lookup SEGS k b off 1 false [] []) as [v scs nx| |]; try discriminate.
    destruct v as [zl| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection Hz as <-.
    assert (Hfl : flat E (SA b off) (Z.of_nat 1)) by (unfold flat; change (Z.of_nat 1) with 1; rewrite Nat2Z.inj_succ in Hhi; lia).
    destruct (KL ltac:(constructor) Hfl) as [bs1 (R1 & L1 & V1)].
    destruct bs1 as [|b0 [|? ?]]; try (cbn in L1; lia).
    destruct (IH b (off + 1) rest HK Hrest) as [bs (Lb & Mb & Rb)].
    { unfold estart in *; cbn [a_base a_off] in *. lia. }
    { unfold estart in *; cbn [a_base a_off] in *. rewrite Nat2Z.inj_succ in Hhi. lia. }
    exists (b0 :: bs). split; [cbn; lia|]. split.
    + cbn [map]. rewrite Mb. f_equal.
      cbn [edenot] in V1. apply (f_equal bv_unsigned) in V1. rewrite !u_lit64 in V1.
      unfold extz in V1. cbn [bytes_le_to_Z] in V1. rewrite Z.shiftl_0_l, Z.lor_0_r in V1.
      pose proof (u8_range b0). unfold two64 in *. rewrite Z.mod_small in V1 by lia. exact V1.
    + intros j Hj. destruct j as [|j].
      * cbn [nth]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite <- R1. reflexivity.
      * cbn [nth]. rewrite <- (Rb j) by lia. f_equal. f_equal. unfold estart; cbn [a_base a_off]. rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_bytes1 : forall M n (a : word) bs,
  length bs = n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < n)%nat -> rdn SEGS M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
  rdn SEGS M a n = Some bs.
Proof.
  intros M n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
  - destruct bs; [reflexivity | cbn in Hlen; lia].
  - destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen.
    pose proof (Hpt 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [nth] in H0.
    destruct n as [|n'].
    + destruct bs'; [exact H0 | cbn in Hlen; lia].
    + apply rdn_cons1; [exact H0|].
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      apply IH; [lia | rewrite Hu1; lia |].
      intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
      exact (Hpt (S j) ltac:(lia)).
Qed.

Theorem node_join_sound : join_stmt SEGS A nx0 LIMIT SINV argH FS0.
Proof.
  intros b off n cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_join in Hn.
  destruct (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool eqn:Ht; [|discriminate].
  apply andb_prop in Ht as [Ht Hfx]. apply andb_prop in Ht as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
  destruct (kread_bytes SEGS n (kn cs) b off) as [zs|] eqn:Hr; [|discriminate].
  apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit (Z.of_nat n)) HK Hfx) as (F1 & F2 & F3).
  rewrite edenot_lit, u64_lit in F2, F3 by lia.
  destruct (kread_bytes_sound E _ (kn cs) n b off zs HK Hr F1 F2) as [bs (Lb & Mb & Rb)].
  apply (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))); [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH FS0); [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok]. split; [exact H8|]. split; [unfold flat; lia|].
  rewrite (rdn_of_bytes1 _ n (adenot E (SA b off)) bs Lb).
  - f_equal. cbn [edenot]. unfold word_to_le_bytes. rewrite <- Mb, zbytes_map.
    pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
    assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply Z_to_le_bytes_to_Z.
  - rewrite (flat_u E _ (Z.of_nat n)); [lia | unfold flat; lia].
  - intros j Hj. rewrite (flat_u E _ (Z.of_nat n)) by (unfold flat; lia). exact (Rb j Hj).
Qed.
End Sound2.
End Asanfrq.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section NodesD.
  (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Hypothesis NX0_ok : APS.nx0_ok nx0.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[local] Notation Hv := (Asanfjy.Hv A).
  #[local] Notation lazy_cover_vis := (Asanfjy.lazy_cover_vis SEGS A LIMIT SINV argH FS0 HULL_ok).
  #[local] Notation H_off_segments_vis := (Asanfjy.H_off_segments_vis SEGS A SEGS_in_hull).
  #[local] Notation mrestrict_Hv_high := (Asanfjy.mrestrict_Hv_high A).
  #[local] Notation Mr_grows_Hv := (Asanfjy.Mr_grows_Hv A argH).

  (* [comment removed for export] *)
  Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
  Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
  Hypothesis Fe1 : fetch_word SEGS (Z_to_bv 64 (x_envscan A)) = Some we1.
  Hypothesis Fe2 : fetch_word SEGS (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
  Hypothesis Fe3 : fetch_word SEGS (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
  Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
  Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
  Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
  Hypothesis Fp0 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
  Hypothesis Fp1 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
  Hypothesis Fp2 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A)) = Some wp2.
  Hypothesis Fp3 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
  Hypothesis Fp4 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
  Hypothesis Ep : is_ecall wp0 = false /\ is_ecall wp1 = false /\ is_ecall wp2 = false /\ is_ecall wp3 = false /\ is_ecall wp4 = false.
  Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  (* [comment removed for export] *)
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable uid : word.                  (* [comment removed for export] *)
  Variable hw : word.                   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hsp_lo : sp_window_lo <= bv_unsigned sp.
  Hypothesis Hsp_hi : bv_unsigned sp <= sp_window_hi.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  Let bsb := build_stack_bytes ph sp argv envp uid hw rdraw.
  (* [comment removed for export] *)
  Let EA := usp + 8 * argc + 16.
  Let STR0 := usp + 8 * argc + 8 * envc + 184.   (* [comment removed for export] *)

  Hypothesis SINV_vals : forall E M, SINV E M ->
    uE E e_envp = EA /\ ev E V_ENVC = Z_to_bv 64 envc /\ uE E e_str0 = STR0.
  (* [comment removed for export] *)
  Hypothesis SINV_sp : forall E M, SINV E M -> uE E e_sp0 = usp.
  Hypothesis SINV_envp : forall E M (a : word), SINV E M ->
    EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem ph sp argv envp uid hw rdraw a.
  Hypothesis SINV_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M a = wrap_mem ph sp argv envp uid hw rdraw a.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma len_s0 : Z.of_nat (length s0) <= 131071.
  Proof. unfold s0. apply (valid_argv_str_len argv 0 Hva). destruct Hva as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. unfold sp_window_lo in Hsp_lo. lia. Qed.
  Lemma usp_hi : usp <= 0x800000000000.
  Proof. unfold usp. unfold sp_window_hi in Hsp_hi. lia. Qed.
  Lemma bsb_nw : usp + Z.of_nat (length bsb) < 2 ^ 64.
  Proof. unfold usp, bsb. apply lay_bsb_nw; assumption. Qed.

  Lemma STR0_eq : cat_argv_ptr sp argv envp 0 = Z_to_bv 64 STR0.
  Proof.
    pose proof len_av. pose proof len_ev. pose proof usp_hi.
    rewrite (cat_argv_ptr_offset sp argv envp 0) by (destruct Hva as [Hl _]; lia).
    unfold cat_string_base. rewrite nat_to_word_add_merge, word_add_nat.
    lazymatch goal with |- Z_to_bv 64 ?a = Z_to_bv 64 ?b => replace a with b; [reflexivity|] end.
    change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat.
    unfold cat_struct_size, auxv_size, STR0, usp, argc, envc. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_envp_k : forall M k, (k < length envp)%nat ->
    (forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem ph sp argv envp uid hw rdraw a) ->
    rdn SEGS M (Z_to_bv 64 (EA + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (cat_envp_ptr sp argv envp k)).
  Proof.
    intros M k Hk HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi.
    assert (Hk' : Z.of_nat k < envc) by (unfold envc; lia).
    rewrite (rdn_ext SEGS 8 M (wrap_mem ph sp argv envp uid hw rdraw)).
    - rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold EA in *; lia | rewrite u64_lit; unfold EA in *; [change (Z.of_nat 8) with 8|]; lia].
      rewrite <- n_to_le_8_spec.
      rewrite <- (read_envp_ptr_k SEGS ph sp rdraw argv envp uid hw Hva Hve Hsp_hi k Hk).
      f_equal. rewrite word_add_nat. f_equal. unfold envp_off, EA, argc, usp. lia.
    - rewrite u64_lit; unfold EA in *; [change (Z.of_nat 8) with 8|]; lia.
    - intros a Ha. rewrite u64_lit in Ha by (unfold EA in *; lia). change (Z.of_nat 8) with 8 in Ha. apply HM. lia.
  Qed.

  Lemma rd_envp_null : forall M,
    (forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem ph sp argv envp uid hw rdraw a) ->
    rdn SEGS M (Z_to_bv 64 (EA + 8 * Z.of_nat (length envp))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof.
    intros M HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi.
    rewrite (rdn_ext SEGS 8 M (wrap_mem ph sp argv envp uid hw rdraw)).
    - rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold EA, envc in *; lia | rewrite u64_lit; unfold EA, envc in *; [change (Z.of_nat 8) with 8|]; lia].
      rewrite <- n_to_le_8_spec.
      rewrite <- (read_envp_null SEGS ph sp rdraw argv envp uid hw Hva Hve Hsp_hi).
      f_equal. rewrite word_add_nat. f_equal. unfold envp_off, EA, argc, usp. lia.
    - rewrite u64_lit; unfold EA, envc in *; [change (Z.of_nat 8) with 8|]; lia.
    - intros a Ha. rewrite u64_lit in Ha by (unfold EA, envc in *; lia). change (Z.of_nat 8) with 8 in Ha. apply HM. unfold envc. lia.
  Qed.

  Lemma rd_str0_j : forall M j, (j <= length s0)%nat ->
    (forall a : word, STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M a = wrap_mem ph sp argv envp uid hw rdraw a) ->
    rdn SEGS M (Z_to_bv 64 (STR0 + Z.of_nat j)) 1 = Some [byte_at s0 j].
  Proof.
    intros M j Hj HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi. pose proof len_s0.
    rewrite (rdn_ext SEGS 1 M (wrap_mem ph sp argv envp uid hw rdraw)).
    - rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold STR0 in *; lia | rewrite u64_lit; unfold STR0 in *; [change (Z.of_nat 1) with 1|]; lia].
      unfold byte_at, s0.
      rewrite <- (read_argv_byte_k ph SEGS sp argv envp 0 j uid hw rdraw ltac:(destruct Hva as [Hl _]; lia) Hj bsb_nw).
      f_equal. rewrite STR0_eq, word_add_nat, u64_lit by (unfold STR0 in *; lia). reflexivity.
    - rewrite u64_lit; unfold STR0 in *; [change (Z.of_nat 1) with 1|]; lia.
    - intros a Ha. rewrite u64_lit in Ha by (unfold STR0 in *; lia). change (Z.of_nat 1) with 1 in Ha. apply HM. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem x_sound_envscan : x_stmt SEGS A nx0 LIMIT SINV argH FS0 XEnvScan.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_envscan in Hn.
    destruct (Z.eqb (pc cs) (x_envscan A) && len_eqb (kn cs) (reg cs 9) e_envp)%bool eqn:Hc; [|discriminate].
    injection Hn as <-. apply andb_prop in Hc as [Hpc Heq]. apply Z.eqb_eq in Hpc.
    pose proof len_av as Lav. pose proof len_ev as Lev. pose proof usp_lo as U1. pose proof usp_hi as U2.
    destruct Xenv as (X1 & X2 & X3). destruct Ee as (Ee1 & Ee2 & Ee3).
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    destruct (SINV_vals E FULL HS) as (V1 & V2 & V3).
    assert (HAT : alloc_top (m_vmmaps model) + 8388608 = usp) by (rewrite <- (SINV_sp E FULL HS); exact (co_top _ _ _ _ _ _ _ _ _ _ _ HC)).
    pose proof (len_eqb_sound SEGS E _ (kn cs) (reg cs 9) e_envp (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Heq) as H9e.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as H9.
    replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) in H9 by (apply bv_eq; reflexivity). rewrite H9e in H9.
    assert (H9' : getr R 9%bv = Z_to_bv 64 (EA + 8 * Z.of_nat 0)).
    { rewrite H9. apply bv_eq. rewrite u64_lit by (unfold EA; lia). unfold uE in V1. rewrite V1. lia. }
    (* [comment removed for export] *)
    set (H2 := Hv E cs model).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    assert (HM : forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> mrestrict H2 FULL a = wrap_mem ph sp argv envp uid hw rdraw a).
    { intros a Ha. unfold H2. rewrite mrestrict_Hv_high by (unfold EA in *; lia). eapply SINV_envp; [exact HS | exact Ha]. }
    destruct (env_loop SEGS (x_envscan A) we1 we2 we3 ltac:(lia) Fe1 Fe2 Fe3 Ee1 Ee2 Ee3 De1 De2 De3
                (mrestrict H2 FULL) (seg_rom SEGS) EA (length envp) (cat_envp_ptr sp argv envp)
                ltac:(unfold EA, envc in *; lia)
                ltac:(intros k Kk; split; [apply rd_envp_k; [exact Kk | exact HM] | apply (cat_envp_ptr_nz ph sp rdraw argv envp uid hw Hva Hve Hsp_lo Hsp_hi k Kk)])
                (rd_envp_null _ HM) (length envp) 0%nat R ltac:(lia) H9') as [R' [Hms Hpost]].
    unfold cfg_of. fold ms.
    assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (mrestrict H2 FULL) (seg_rom SEGS))).
    { unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
    apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (mrestrict H2 FULL) (seg_rom SEGS)))
      with (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
    rewrite munrestrict_mrestrict.
    specialize (Hk E R' FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold cfg_of, pc in Hk. cbn [set_pc set_reg with_ss a_ss mk_ss s_pc] in Hk. rewrite X3 in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
    (* [comment removed for export] *)
    unfold set_pc, set_reg. rewrite !a_ss_with_ss, !with_ss_idem. cbn [s_regs s_know s_next].
    eapply cs_ok_frame; [exact SINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
    cbn [s_regs]. destruct Hpost as (P9 & P10 & Pag).
    eapply (regs_ok_post2 E _ R R' 9 9%bv _ 10 10%bv); [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | lia | lia | reflexivity | reflexivity | | |].
    - rewrite P9. unfold eadd, escale. rewrite !mkAlu_denot, mkMd_denot, !edenot_lit. fold (reg cs 9). rewrite H9e.
      apply bv_eq. rewrite !u_add64, u_mul64, !u64_lit by lia. cbn [edenot]. rewrite V2, u64_lit by lia. unfold uE in V1. rewrite V1.
      rewrite (Z.mod_small (8 * envc)) by lia. rewrite (Z.mod_small (8 * envc + 8)) by lia.
      rewrite Z.mod_small by (unfold EA; lia). unfold envc. lia.
    - rewrite P10. rewrite edenot_lit. reflexivity.
    - intros r N1 N2. apply (Pag r). intros [H|H]; [exact (N1 H) | exact (N2 H)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem x_sound_pnscan : x_stmt SEGS A nx0 LIMIT SINV argH FS0 XPnScan.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_pnscan in Hn.
    destruct (reg_lit cs 10) as [p|] eqn:Hp10; [|discriminate].
    destruct (reg_lit cs 12) as [c|] eqn:Hp12; [|discriminate].
    destruct c as [|pc|pc]; try discriminate.
    do 6 (destruct pc as [pc|pc|]; try discriminate).
    lazymatch type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [|discriminate] end.
    injection Hn as <-.
    apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Hlo].
    apply andb_prop in Hc as [Hc Hwr]. apply andb_prop in Hc as [Hpc Heq].
    apply Z.eqb_eq in Hpc. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
    pose proof len_av as Lav. pose proof len_ev as Lev. pose proof usp_lo as U1. pose proof usp_hi as U2. pose proof len_s0 as Ls0.
    destruct Xpn as (X1 & X2 & X3). destruct Ep as (Ep0 & Ep1 & Ep2 & Ep3 & Ep4).
    pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    destruct (SINV_vals E FULL HS) as (V1 & V2 & V3).
    assert (HAT : alloc_top (m_vmmaps model) + 8388608 = usp) by (rewrite <- (SINV_sp E FULL HS); exact (co_top _ _ _ _ _ _ _ _ _ _ _ HC)).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    (* [comment removed for export] *)
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 p HC ltac:(lia) Hp10) as [H10 Hpr].
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 12 _ HC ltac:(lia) Hp12) as [H12 _].
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in H12 by (apply bv_eq; reflexivity).
    pose proof (len_eqb_sound SEGS E _ (kn cs) (reg cs 11) (eaddz e_str0 1) HK Heq) as H11e.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as H11.
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in H11 by (apply bv_eq; reflexivity). rewrite H11e in H11.
    assert (H11' : getr R 11%bv = Z_to_bv 64 (STR0 + Z.of_nat 0 + 1)).
    { rewrite H11. unfold eaddz. rewrite mkAlu_denot, edenot_lit. apply bv_eq. rewrite u_add64, !u64_lit by (unfold STR0; lia).
      unfold uE in V3. rewrite V3. rewrite Z.mod_small by (unfold STR0; lia). lia. }
    (* [comment removed for export] *)
    destruct (kwritable_sound SEGS E _ (kn cs) (kn cs) (ELit 0) p 8 HK HK Hwr ltac:(lia)) as (HKW & _ & _).
    unfold estart in HKW. cbn [a_base a_off] in HKW. rewrite edenot_lit, u64_lit in HKW by lia. rewrite Z.add_0_l in HKW.
    change (Z.to_nat 8) with 8%nat in HKW.
    (* [comment removed for export] *)
    set (H2 := Hv E cs model).
    set (M0 := mrestrict H2 FULL).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    assert (Hst0 : store_ok SEGS M0 (Z_to_bv 64 p) 8 = true).
    { eapply store_ok_mono; [apply Mr_grows_Hv | exact HKW]. }
    assert (HM : forall a : word, STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M0 a = wrap_mem ph sp argv envp uid hw rdraw a).
    { intros a Ha. unfold M0, H2. rewrite mrestrict_Hv_high by (unfold STR0 in *; lia). eapply SINV_str0; [exact HS | exact Ha]. }
    destruct (pn_loop SEGS (x_pnscan A) wp0 wp1 wp2 wp3 wp4 ltac:(lia) Fp0 Fp1 Fp2 Fp3 Fp4 Ep0 Ep1 Ep2 Ep3 Ep4 Dp0 Dp1 Dp2 Dp3 Dp4
                M0 (seg_rom SEGS) p STR0 s0
                ltac:(unfold KHI in *; lia) ltac:(unfold STR0; lia) ltac:(left; unfold STR0, KHI in *; lia)
                (valid_argv_str_nz argv 0 Hva ltac:(destruct Hva as [Hl _]; lia))
                (fun j Hj => rd_str0_j M0 j Hj HM) Hst0
                s0 0%nat R M0 eq_refl ltac:(lia) H10 H11' H12 (cellrel_refl M0 p)) as (R' & M' & Hms & Hpost & HM').
    unfold cfg_of. fold ms.
    assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) M' (seg_rom SEGS))).
    { unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
    apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) M' (seg_rom SEGS)))
      with (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) (munrestrict H2 FULL M') (seg_rom SEGS)).
    set (FULL' := munrestrict H2 FULL M').
    assert (HF : forall a : word, bv_unsigned a < p \/ p + 8 <= bv_unsigned a -> FULL' a = FULL a).
    { intros a Ha. unfold FULL', munrestrict. destruct (H2 a) eqn:H2a; [reflexivity|].
      destruct HM' as [HM1 _]. rewrite (HM1 a Ha). unfold M0, mrestrict. rewrite H2a. reflexivity. }
    (* [comment removed for export] *)
    set (v := nxt cs). set (E' := ext1 E v (getr R' 11%bv)).
    assert (Hag : env_agree v E E') by apply ext1_agree.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    pose proof (cs_ok_agree SEGS A nx0 LIMIT NX0_ok SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
    pose proof (hid_agree A nx0 argH argH_agree v E E' cs model Hag Fle Fallow) as Hhid.
    specialize (Hk E' R' FULL' model' (conj (env_agree_le nx0 v E E' Hag Fle) Hag)).
    unfold cfg_of, pc in Hk. cbn [a_ss with_ss mk_ss s_pc] in Hk. rewrite X3 in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
    (* [comment removed for export] *)
    eapply cs_ok_frame; [exact SINV_frame | exact HC' | exact Hsame | | | reflexivity | |].
    - rewrite (allowA_agree A v E E' cs Hag Fallow). exact Hinv'.
    - cbn [s_regs]. destruct Hpost as (P11 & P13 & Pag).
      eapply (regs_ok_post2 E' _ R R' 11 11%bv _ 13 13%bv); [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') | lia | lia | lia | reflexivity | reflexivity | | |].
      + cbn [edenot]. unfold E'. rewrite ext1_at. reflexivity.
      + rewrite P13, edenot_lit. reflexivity.
      + intros r N1 N2. apply (Pag r). intros [H|H]; [exact (N1 H) | exact (N2 H)].
    - cbn [s_know]. unfold Mr. rewrite Hhid.
      apply (know_ok_havoc SEGS E' (mrestrict (hid A argH E cs model) FULL)).
      + apply kimg_cut_sound. pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC') as HK'. unfold Mr in HK'. rewrite Hhid in HK'. exact HK'.
      + intros x Hx. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite !u64_lit in Hx by lia.
        unfold mrestrict. rewrite HF by lia. reflexivity.
      + intros x Hx. unfold mrestrict in *. destruct (hid A argH E cs model x) eqn:Hh; [exact Hx|].
        unfold FULL', munrestrict. unfold hid in Hh. apply orb_false_iff in Hh as [_ Hvx].
        unfold H2 at 1. unfold Hv. rewrite Hvx. cbn [negb].
        destruct HM' as [_ HM2]. apply HM2. unfold M0, mrestrict, H2, Hv. rewrite Hvx. cbn [negb]. exact Hx.
    - intros a Ha. rewrite Hhid in Ha. unfold hid in Ha. apply orb_prop in Ha as [Ha|Ha].
      + apply HF. right. pose proof (argH_high E a Ha). unfold CEIL, KHI in *. lia.
      + unfold FULL', munrestrict. unfold H2 at 1. unfold Hv. rewrite Ha. reflexivity.
  Qed.

End NodesD.

Lemma some_inj_acs : forall a b : acs, Some a = Some b -> a = b.
Proof. intros a b H. exact (f_equal (fun o => match o with Some x => x | None => a end) H). Qed.

Section LayoutSound.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.

  (* [comment removed for export] *)
  Lemma e_argv1w_ge2 : forall E, 2 <= bv_unsigned (ev E V_ARGC) -> edenot E e_argv1w = edenot E e_str1.
  Proof.
    intros E H. unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit by lia.
    replace (1 <? bv_unsigned (ev E V_ARGC)) with true by (symmetry; apply Z.ltb_lt; lia).
    pose proof (u64_range (edenot E e_str1)). rewrite Z.mul_1_l. apply Z.mod_small. lia.
  Qed.

  Lemma e_argv1w_le1 : forall E, bv_unsigned (ev E V_ARGC) <= 1 -> edenot E e_argv1w = edenot E (ELit 0).
  Proof.
    intros E H. unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, !u64_lit by lia.
    replace (1 <? bv_unsigned (ev E V_ARGC)) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  Qed.

  Lemma kw_argv1_respell : forall E M v v',
    kentry_ok SEGS E M (kw_argv1 v) -> edenot E v' = edenot E v -> kentry_ok SEGS E M (kw_argv1 v').
  Proof. intros E M v v' HK Hv. unfold kw_argv1 in *. cbn [kentry_ok] in *. rewrite Hv. exact HK. Qed.

  Theorem x_sound_layout : x_stmt SEGS A nx0 LIMIT SINV argH FS0 XLayout.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_layout in Hn.
    destruct (existsb (kentry_eqb (kw_argv1 e_argv1w)) (kn cs)) eqn:Hex; [|discriminate]. cbn [negb] in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    (* [comment removed for export] *)
    apply existsb_exists in Hex as [K0 [Hin Heqb]]. apply kentry_eqb_eq in Heqb. subst K0.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HK0.
    assert (HK' : know_ok SEGS E (Mr A argH E cs model FULL)
                    (List.filter (fun K => negb (kentry_eqb (kw_argv1 e_argv1w) K)) (kn cs)))
      by (apply know_ok_filter; exact HK).
    assert (FIN : forall v, edenot E v = edenot E e_argv1w ->
                  cs' = set_kn cs (kw_argv1 v :: List.filter (fun K => negb (kentry_eqb (kw_argv1 e_argv1w) K)) (kn cs)) ->
                  srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T).
    { intros v Hv ->. specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
      rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
      apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK'].
      eapply kw_argv1_respell; [exact HK0 | exact Hv]. }
    (* [comment removed for export] *)
    destruct args as [|[z| | | | | | |] [|e2 l2]]; try discriminate; destruct z as [|pz|pz]; try discriminate;
      try (destruct pz; try discriminate).
    - (* [comment removed for export] *)
      destruct (xhi (kn cs) (EVar V_ARGC)) as [hi|] eqn:Hhi; [|discriminate].
      destruct (Z.leb hi 1) eqn:Hle; [|discriminate]. apply Z.leb_le in Hle. apply some_inj_acs in Hn.
      pose proof (xhi_sound SEGS E _ (kn cs) (EVar V_ARGC) hi HK Hhi) as B. cbn [edenot] in B.
      apply (FIN (ELit 0)); [|symmetry; exact Hn]. symmetry. apply e_argv1w_le1. lia.
    - (* [comment removed for export] *)
      destruct (xlo (kn cs) (EVar V_ARGC)) as [lo|] eqn:Hlo; [|discriminate].
      destruct (Z.leb 2 lo) eqn:Hle; [|discriminate]. apply Z.leb_le in Hle. apply some_inj_acs in Hn.
      pose proof (xlo_sound SEGS E _ (kn cs) (EVar V_ARGC) lo HK Hlo) as B. cbn [edenot] in B.
      apply (FIN e_str1); [|symmetry; exact Hn]. symmetry. apply e_argv1w_ge2. lia.
  Qed.
End LayoutSound.

