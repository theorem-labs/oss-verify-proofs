(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib As0StepLib PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4MemcmpTab.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub; imm_norm; unorm; first [reflexivity | f_equal; lia].

#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
(* [comment removed for export] *)
#[local] Ltac mlbus F D z HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | maddr z; exact HYP] | step_simpl; vnorm].

Lemma rdn_cons_inv : forall (M : word -> option byte) (a : word) (k : nat) (b : byte) (r : list byte),
  rdn ASEGS M a (S k) = Some (b :: r) -> rdn ASEGS M a 1%nat = Some [b] /\ rdn ASEGS M (a + 1)%bv k = Some r.
Proof.
  intros M a k b r H. cbn [rdn] in H |- *.
  destruct (match M a with Some b0 => Some b0 | None => seg_rom ASEGS a end) as [b0|] eqn:Eb; [|discriminate].
  destruct (rdn ASEGS M (a + 1)%bv k) as [rest|] eqn:Er; [|discriminate].
  injection H as -> ->. split; reflexivity.
Qed.
Lemma word_succ_Z : forall z, (0 <= z)%Z -> (z + 1 < 2 ^ 64)%Z -> (Z_to_bv 64 z + 1)%bv = Z_to_bv 64 (z + 1).
Proof.
  intros z H0 H1. apply bv_eq. rewrite bv_add_unsigned. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  change (bv_unsigned (1 : bv 64)) with 1%Z. rewrite (Z.mod_small z) by lia. reflexivity.
Qed.
Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 8)%Z with 256%Z in H. exact H. Qed.

Section MMC.
  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.

  (* [comment removed for export] *)
  Lemma musl_memcmp_loop : forall (b1 b2 : list byte) (a1 a2 : Z) regs,
    b1 <> [] -> length b2 = length b1 ->
    rdn ASEGS M (Z_to_bv 64 a1) (length b1) = Some b1 -> rdn ASEGS M (Z_to_bv 64 a2) (length b2) = Some b2 ->
    (0 <= a1)%Z -> (a1 + Z.of_nat (length b1) < 2 ^ 64)%Z -> (0 <= a2)%Z -> (a2 + Z.of_nat (length b1) < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 a1 -> getr regs 11 = Z_to_bv 64 a2 -> getr regs 12 = Z_to_bv 64 (Z.of_nat (length b1)) -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x152a74 : word) M rom) (mkst regs' ra M rom)
      /\ getr regs' 10 = Z_to_bv 64 (memcmp_val b1 b2) /\ keeps_cs regs regs'.
  Proof.
    induction b1 as [|x r1 IH]; intros b2 a1 a2 regs NE LEN R1 R2 A1 A1h A2 A2h H10 H11 H12 H1; [congruence|].
    destruct b2 as [|y r2]; [discriminate LEN|]. cbn [length] in *.
    destruct (rdn_cons_inv _ _ _ _ _ R1) as (X1 & X1r). destruct (rdn_cons_inv _ _ _ _ _ R2) as (Y1 & Y1r).
    pose proof (byte_range x) as Bx. pose proof (byte_range y) as By.
    rewrite Nat2Z.inj_succ in *.
    cbn [memcmp_val]. destruct (Z.eqb (bv_unsigned x) (bv_unsigned y)) eqn:EQ.
    - apply Z.eqb_eq in EQ.
      destruct r1 as [|x' r1'].
      + (* [comment removed for export] *)
        destruct r2; [|discriminate LEN]. cbn [memcmp_val].
        eexists. split.
        * mlbus Fx_152a30 Dx_152a30 a1 X1.                                     (* [comment removed for export] *)
          mlbus Fx_152a34 Dx_152a34 a2 Y1.                                     (* [comment removed for export] *)
          stepb_ft Fx_152a38 Dx_152a38 ltac:(cond).                                        (* [comment removed for export] *)
          stepiv Fx_152a3c Dx_152a3c (Z_to_bv 64 0) ltac:(wval).                           (* [comment removed for export] *)
          stepn Fx_152a40 Dx_152a40.                                                       (* [comment removed for export] *)
          stepn Fx_152a44 Dx_152a44.                                                       (* [comment removed for export] *)
          stepb_ft Fx_152a48 Dx_152a48 ltac:(cond).                                        (* [comment removed for export] *)
          stepn Fx_152a4c Dx_152a4c.                                                       (* [comment removed for export] *)
          stepret Fx_152a50 Dx_152a50 ra ltac:(rwH; reflexivity).
          apply mst_refl.
        * split; [gres; reflexivity | solve_keeps_cs].
      + (* [comment removed for export] *)
        assert (KP : (0 < Z.of_nat (length (x' :: r1')))%Z) by (cbn [length]; lia).
        eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x152a74 : word) M rom)
                 (fun rg => getr rg 10 = Z_to_bv 64 (a1 + 1) /\ getr rg 11 = Z_to_bv 64 (a2 + 1) /\ getr rg 12 = Z_to_bv 64 (Z.of_nat (length (x' :: r1'))) /\ getr rg 1 = ra /\ keeps_cs regs rg)).
        * eexists. split.
          -- mlbus Fx_152a30 Dx_152a30 a1 X1.
             mlbus Fx_152a34 Dx_152a34 a2 Y1.
             stepb_ft Fx_152a38 Dx_152a38 ltac:(cond).
             stepiv Fx_152a3c Dx_152a3c (Z_to_bv 64 (Z.of_nat (length (x' :: r1')))) ltac:(wval).
             stepiv Fx_152a40 Dx_152a40 (Z_to_bv 64 (a1 + 1)) ltac:(wval).
             stepiv Fx_152a44 Dx_152a44 (Z_to_bv 64 (a2 + 1)) ltac:(wval).
             stepb_tk Fx_152a48 Dx_152a48 ltac:(cond).                                     (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps_cs.
        * cbv beta. intros rg (Q10 & Q11 & Q12 & Q1 & K1).
          rewrite word_succ_Z in X1r, Y1r by lia.
          destruct (IH r2 (a1 + 1)%Z (a2 + 1)%Z rg ltac:(discriminate) ltac:(cbn [length] in *; lia) X1r
                      ltac:(replace (length r2) with (length (x' :: r1')) in Y1r by (cbn [length] in *; lia); replace (length r2) with (length (x' :: r1')) by (cbn [length] in *; lia); exact Y1r)
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Q10 Q11 Q12 Q1) as (r' & RUN & V10 & K2).
          exists r'. split; [exact RUN | split; [exact V10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      apply Z.eqb_neq in EQ.
      eexists. split.
      + mlbus Fx_152a30 Dx_152a30 a1 X1.
        mlbus Fx_152a34 Dx_152a34 a2 Y1.
        stepb_tk Fx_152a38 Dx_152a38 ltac:(cond).                                          (* [comment removed for export] *)
        stepiv Fx_152a54 Dx_152a54 (Z_to_bv 64 (bv_unsigned x - bv_unsigned y))
          ltac:(gres; rwH; unfold v_sub; unorm; reflexivity).               (* [comment removed for export] *)
        stepret Fx_152a58 Dx_152a58 ra ltac:(rwH; reflexivity).
        apply mst_refl.
      + split; [gres; reflexivity | solve_keeps_cs].
  Qed.

  (* [comment removed for export] *)
  Theorem musl_memcmp_run : forall (b1 b2 : list byte) (p q n : Z) regs,
    rdn ASEGS M (Z_to_bv 64 p) (Z.to_nat n) = Some b1 -> rdn ASEGS M (Z_to_bv 64 q) (Z.to_nat n) = Some b2 ->
    (0 <= n)%Z -> (0 <= p)%Z -> (p + n < 2 ^ 64)%Z -> (0 <= q)%Z -> (q + n < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 q -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x152a70 : word) M rom) (mkst regs' ra M rom)
      /\ getr regs' 10 = Z_to_bv 64 (memcmp_val b1 b2) /\ keeps_cs regs regs'.
  Proof.
    intros b1 b2 p q n regs R1 R2 Hn Hp Hpn Hq Hqn H10 H11 H12 H1.
    pose proof (rdn_length _ _ _ _ _ R1) as L1. pose proof (rdn_length _ _ _ _ _ R2) as L2.
    destruct (Z.eq_dec n 0) as [Hz|Hz].
    - subst n. cbn in L1, L2. destruct b1; [|discriminate L1]. cbn [memcmp_val].
      eexists. split.
      + stepb_tk Fx_152a2c Dx_152a2c ltac:(cond).                                          (* [comment removed for export] *)
        stepn Fx_152a4c Dx_152a4c.
        stepret Fx_152a50 Dx_152a50 ra ltac:(rwH; reflexivity).
        apply mst_refl.
      + split; [gres; reflexivity | solve_keeps_cs].
    - assert (NE : b1 <> []) by (intros ->; cbn in L1; lia).
      assert (LN : Z.of_nat (length b1) = n) by (rewrite L1, Z2Nat.id by lia; reflexivity).
      eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x152a74 : word) M rom) (fun rg => rg = regs)).
      + eexists. split; [|reflexivity].
        stepb_ft Fx_152a2c Dx_152a2c ltac:(cond).
        apply mst_refl.
      + cbv beta. intros rg ->.
        rewrite <- L1 in R1. rewrite <- L2 in R2.
        apply (musl_memcmp_loop b1 b2 p q regs NE ltac:(congruence) R1 R2 Hp ltac:(lia) Hq ltac:(lia) H10 H11 ltac:(rewrite LN; exact H12) H1).
  Qed.
End MMC.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
