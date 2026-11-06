(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import PropExec CatExec CatSim SeqExec AgentLib AsanStartLoops.

Unset Lia Cache.
Unset Nia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W0 : bv 32 := 0x00155593.
Lemma D0 : decode_any W0 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z). Proof. vm_refl. Qed.
Lemma E0 : is_ecall W0 = false. Proof. reflexivity. Qed.

Definition W1 : bv 32 := 0x55555637.
Lemma D1 : decode_any W1 = Some (Lui 12 349525, 4%Z). Proof. vm_refl. Qed.
Lemma E1 : is_ecall W1 = false. Proof. reflexivity. Qed.

Definition W2 : bv 32 := 0x333336b7.
Lemma D2 : decode_any W2 = Some (Lui 13 209715, 4%Z). Proof. vm_refl. Qed.
Lemma E2 : is_ecall W2 = false. Proof. reflexivity. Qed.

Definition W3 : bv 32 := 0x0f0f1737.
Lemma D3 : decode_any W3 = Some (Lui 14 61681, 4%Z). Proof. vm_refl. Qed.
Lemma E3 : is_ecall W3 = false. Proof. reflexivity. Qed.

Definition W4 : bv 32 := 0x010107b7.
Lemma D4 : decode_any W4 = Some (Lui 15 4112, 4%Z). Proof. vm_refl. Qed.
Lemma E4 : is_ecall W4 = false. Proof. reflexivity. Qed.

Definition W5 : bv 32 := 0x00b56533.
Lemma D5 : decode_any W5 = Some (Op ALU_OR 10 10 11, 4%Z). Proof. vm_refl. Qed.
Lemma E5 : is_ecall W5 = false. Proof. reflexivity. Qed.

Definition W6 : bv 32 := 0x5556059b.
Lemma D6 : decode_any W6 = Some (OpImm32 11 12 1365, 4%Z). Proof. vm_refl. Qed.
Lemma E6 : is_ecall W6 = false. Proof. reflexivity. Qed.

Definition W7 : bv 32 := 0x3336861b.
Lemma D7 : decode_any W7 = Some (OpImm32 12 13 819, 4%Z). Proof. vm_refl. Qed.
Lemma E7 : is_ecall W7 = false. Proof. reflexivity. Qed.

Definition W8 : bv 32 := 0xf0f7069b.
Lemma D8 : decode_any W8 = Some (OpImm32 13 14 3855, 4%Z). Proof. vm_refl. Qed.
Lemma E8 : is_ecall W8 = false. Proof. reflexivity. Qed.

Definition W9 : bv 32 := 0x1017871b.
Lemma D9 : decode_any W9 = Some (OpImm32 14 15 257, 4%Z). Proof. vm_refl. Qed.
Lemma E9 : is_ecall W9 = false. Proof. reflexivity. Qed.

Definition W10 : bv 32 := 0x00255793.
Lemma D10 : decode_any W10 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z). Proof. vm_refl. Qed.
Lemma E10 : is_ecall W10 = false. Proof. reflexivity. Qed.

Definition W11 : bv 32 := 0x00f56533.
Lemma D11 : decode_any W11 = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
Lemma E11 : is_ecall W11 = false. Proof. reflexivity. Qed.

Definition W12 : bv 32 := 0x02059793.
Lemma D12 : decode_any W12 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z). Proof. vm_refl. Qed.
Lemma E12 : is_ecall W12 = false. Proof. reflexivity. Qed.

Definition W13 : bv 32 := 0x00f585b3.
Lemma D13 : decode_any W13 = Some (Op ALU_ADD 11 11 15, 4%Z). Proof. vm_refl. Qed.
Lemma E13 : is_ecall W13 = false. Proof. reflexivity. Qed.

Definition W14 : bv 32 := 0x02061793.
Lemma D14 : decode_any W14 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z). Proof. vm_refl. Qed.
Lemma E14 : is_ecall W14 = false. Proof. reflexivity. Qed.

Definition W15 : bv 32 := 0x00f60633.
Lemma D15 : decode_any W15 = Some (Op ALU_ADD 12 12 15, 4%Z). Proof. vm_refl. Qed.
Lemma E15 : is_ecall W15 = false. Proof. reflexivity. Qed.

Definition W16 : bv 32 := 0x02069793.
Lemma D16 : decode_any W16 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z). Proof. vm_refl. Qed.
Lemma E16 : is_ecall W16 = false. Proof. reflexivity. Qed.

Definition W17 : bv 32 := 0x00f686b3.
Lemma D17 : decode_any W17 = Some (Op ALU_ADD 13 13 15, 4%Z). Proof. vm_refl. Qed.
Lemma E17 : is_ecall W17 = false. Proof. reflexivity. Qed.

Definition W18 : bv 32 := 0x02071793.
Lemma D18 : decode_any W18 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z). Proof. vm_refl. Qed.
Lemma E18 : is_ecall W18 = false. Proof. reflexivity. Qed.

Definition W19 : bv 32 := 0x00f70733.
Lemma D19 : decode_any W19 = Some (Op ALU_ADD 14 14 15, 4%Z). Proof. vm_refl. Qed.
Lemma E19 : is_ecall W19 = false. Proof. reflexivity. Qed.

Definition W20 : bv 32 := 0x00455793.
Lemma D20 : decode_any W20 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z). Proof. vm_refl. Qed.
Lemma E20 : is_ecall W20 = false. Proof. reflexivity. Qed.

Definition W21 : bv 32 := 0x00f56533.
Lemma D21 : decode_any W21 = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
Lemma E21 : is_ecall W21 = false. Proof. reflexivity. Qed.

Definition W22 : bv 32 := 0x00855793.
Lemma D22 : decode_any W22 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z). Proof. vm_refl. Qed.
Lemma E22 : is_ecall W22 = false. Proof. reflexivity. Qed.

Definition W23 : bv 32 := 0x00f56533.
Lemma D23 : decode_any W23 = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
Lemma E23 : is_ecall W23 = false. Proof. reflexivity. Qed.

Definition W24 : bv 32 := 0x01055793.
Lemma D24 : decode_any W24 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z). Proof. vm_refl. Qed.
Lemma E24 : is_ecall W24 = false. Proof. reflexivity. Qed.

Definition W25 : bv 32 := 0x00f56533.
Lemma D25 : decode_any W25 = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
Lemma E25 : is_ecall W25 = false. Proof. reflexivity. Qed.

Definition W26 : bv 32 := 0x02055793.
Lemma D26 : decode_any W26 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z). Proof. vm_refl. Qed.
Lemma E26 : is_ecall W26 = false. Proof. reflexivity. Qed.

Definition W27 : bv 32 := 0x00f56533.
Lemma D27 : decode_any W27 = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
Lemma E27 : is_ecall W27 = false. Proof. reflexivity. Qed.

Definition W28 : bv 32 := 0xfff54513.
Lemma D28 : decode_any W28 = Some (OpImm ALU_XOR 10 10 4095, 4%Z). Proof. vm_refl. Qed.
Lemma E28 : is_ecall W28 = false. Proof. reflexivity. Qed.

Definition W29 : bv 32 := 0x00155793.
Lemma D29 : decode_any W29 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z). Proof. vm_refl. Qed.
Lemma E29 : is_ecall W29 = false. Proof. reflexivity. Qed.

Definition W30 : bv 32 := 0x00b7f5b3.
Lemma D30 : decode_any W30 = Some (Op ALU_AND 11 15 11, 4%Z). Proof. vm_refl. Qed.
Lemma E30 : is_ecall W30 = false. Proof. reflexivity. Qed.

Definition W31 : bv 32 := 0x40b50533.
Lemma D31 : decode_any W31 = Some (Op ALU_SUB 10 10 11, 4%Z). Proof. vm_refl. Qed.
Lemma E31 : is_ecall W31 = false. Proof. reflexivity. Qed.

Definition W32 : bv 32 := 0x00c575b3.
Lemma D32 : decode_any W32 = Some (Op ALU_AND 11 10 12, 4%Z). Proof. vm_refl. Qed.
Lemma E32 : is_ecall W32 = false. Proof. reflexivity. Qed.

Definition W33 : bv 32 := 0x00255513.
Lemma D33 : decode_any W33 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z). Proof. vm_refl. Qed.
Lemma E33 : is_ecall W33 = false. Proof. reflexivity. Qed.

Definition W34 : bv 32 := 0x00c57533.
Lemma D34 : decode_any W34 = Some (Op ALU_AND 10 10 12, 4%Z). Proof. vm_refl. Qed.
Lemma E34 : is_ecall W34 = false. Proof. reflexivity. Qed.

Definition W35 : bv 32 := 0x00a58533.
Lemma D35 : decode_any W35 = Some (Op ALU_ADD 10 11 10, 4%Z). Proof. vm_refl. Qed.
Lemma E35 : is_ecall W35 = false. Proof. reflexivity. Qed.

Definition W36 : bv 32 := 0x00455593.
Lemma D36 : decode_any W36 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z). Proof. vm_refl. Qed.
Lemma E36 : is_ecall W36 = false. Proof. reflexivity. Qed.

Definition W37 : bv 32 := 0x00b50533.
Lemma D37 : decode_any W37 = Some (Op ALU_ADD 10 10 11, 4%Z). Proof. vm_refl. Qed.
Lemma E37 : is_ecall W37 = false. Proof. reflexivity. Qed.

Definition W38 : bv 32 := 0x00d57533.
Lemma D38 : decode_any W38 = Some (Op ALU_AND 10 10 13, 4%Z). Proof. vm_refl. Qed.
Lemma E38 : is_ecall W38 = false. Proof. reflexivity. Qed.

Definition W39 : bv 32 := 0x02e50533.
Lemma D39 : decode_any W39 = Some (Mul M_MUL 10 10 14, 4%Z). Proof. vm_refl. Qed.
Lemma E39 : is_ecall W39 = false. Proof. reflexivity. Qed.

Definition W40 : bv 32 := 0x03855513.
Lemma D40 : decode_any W40 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z). Proof. vm_refl. Qed.
Lemma E40 : is_ecall W40 = false. Proof. reflexivity. Qed.

Definition W41 : bv 32 := 0x40a0053b.
Lemma D41 : decode_any W41 = Some (Op32 ALU_SUB 10 0 10, 4%Z). Proof. vm_refl. Qed.
Lemma E41 : is_ecall W41 = false. Proof. reflexivity. Qed.

Definition W42 : bv 32 := 0xfff00593.
Lemma D42 : decode_any W42 = Some (OpImm ALU_ADD 11 0 4095, 4%Z). Proof. vm_refl. Qed.
Lemma E42 : is_ecall W42 = false. Proof. reflexivity. Qed.

Definition W43 : bv 32 := 0x00a59533.
Lemma D43 : decode_any W43 = Some (Op ALU_SLL 10 11 10, 4%Z). Proof. vm_refl. Qed.
Lemma E43 : is_ecall W43 = false. Proof. reflexivity. Qed.

Definition W44 : bv 32 := 0xfff54513.
Lemma D44 : decode_any W44 = Some (OpImm ALU_XOR 10 10 4095, 4%Z). Proof. vm_refl. Qed.
Lemma E44 : is_ecall W44 = false. Proof. reflexivity. Qed.
Definition MAXVA_WORDS : list (bv 32) := [W0; W1; W2; W3; W4; W5; W6; W7; W8; W9; W10; W11; W12; W13; W14; W15; W16; W17; W18; W19; W20; W21; W22; W23; W24; W25; W26; W27; W28; W29; W30; W31; W32; W33; W34; W35; W36; W37; W38; W39; W40; W41; W42; W43; W44].

Lemma step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_and_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_and (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_sll_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLL rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_sll (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_sll segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_subw_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_subw (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.

Definition topfull (k : Z) (v : Z) : Prop :=
  0 <= v /\ (forall i, 47 - k <= i <= 46 -> Z.testbit v i = true) /\ (forall i, 47 <= i -> Z.testbit v i = false).

Lemma topfull_init : forall x, 2 ^ 46 <= x < 2 ^ 47 -> topfull 1 x.
Proof.
  intros x Hx. split; [lia|]. split.
  - intros i Hi. assert (i = 46) by lia. subst i. apply Z.testbit_true; [lia|].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    replace (x / 2 ^ 46) with 1 by nia. reflexivity.
  - intros i Hi. apply Z.testbit_false; [lia|].
    assert (Hp : 2 ^ 47 <= 2 ^ i) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.div_small by lia. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma topfull_step : forall k j v, 1 <= j <= k -> topfull k v -> topfull (Z.min (k + j) 47) (Z.lor v (Z.shiftr v j)).
Proof.
  intros k j v Hj (H0 & H1 & H2). split; [|split].
  - apply Z.lor_nonneg. split; [exact H0 | apply Z.shiftr_nonneg; exact H0].
  - intros i Hi. rewrite Z.lor_spec. destruct (Z_le_dec (47 - k) i) as [Hle|Hgt].
    + rewrite (H1 i) by lia. reflexivity.
    + rewrite Z.shiftr_spec by lia. rewrite (H1 (i + j)) by lia. apply orb_true_r.
  - intros i Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite (H2 i), (H2 (i + j)) by lia. reflexivity.
Qed.

Lemma topfull_all : forall v, topfull 47 v -> v = 2 ^ 47 - 1.
Proof.
  intros v (H0 & H1 & H2). apply Z.bits_inj'. intros i Hi.
  change (2 ^ 47 - 1) with (Z.ones 47).
  destruct (Z_lt_dec i 47) as [Hlt|Hge].
  - rewrite Z.ones_spec_low by lia. apply H1. lia.
  - rewrite Z.ones_spec_high by lia. apply H2. lia.
Qed.

Lemma u_orsrl : forall (a : word) (j : Z), 0 <= j ->
  bv_unsigned (v_or a (v_srli a j)) = Z.lor (bv_unsigned a) (Z.shiftr (bv_unsigned a) j).
Proof.
  intros a j Hj. pose proof (u64_range a) as Ra.
  assert (Hs : 0 <= Z.shiftr (bv_unsigned a) j < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj) as Hp.
    split; [apply Z.div_pos; lia|]. apply Z.le_lt_trans with (bv_unsigned a); [|lia].
    apply Z.div_le_upper_bound; [lia|]. nia. }
  unfold v_or, v_srli. rewrite (u64_lit (Z.shiftr (bv_unsigned a) j)) by lia.
  apply u64_lit. apply Z_lor_range; lia.
Qed.

Lemma smear47 : forall x : word, 2 ^ 46 <= bv_unsigned x < 2 ^ 47 ->
  (v_or (v_or (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) (v_srli (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) 16)) (v_srli (v_or (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) (v_srli (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) 16)) 32)) = Z_to_bv 64 0x7fffffffffff.
Proof.
  intros x Hx.
  set (s1 := v_or x (v_srli x 1)). set (s2 := v_or s1 (v_srli s1 2)). set (s3 := v_or s2 (v_srli s2 4)).
  set (s4 := v_or s3 (v_srli s3 8)). set (s5 := v_or s4 (v_srli s4 16)).
  pose proof (topfull_init _ Hx) as T0.
  pose proof (topfull_step 1 1 _ ltac:(lia) T0) as T1. rewrite <- (u_orsrl x 1) in T1 by lia. fold s1 in T1. change (Z.min (1 + 1) 47) with 2 in T1.
  pose proof (topfull_step 2 2 _ ltac:(lia) T1) as T2. rewrite <- (u_orsrl s1 2) in T2 by lia. fold s2 in T2. change (Z.min (2 + 2) 47) with 4 in T2.
  pose proof (topfull_step 4 4 _ ltac:(lia) T2) as T3. rewrite <- (u_orsrl s2 4) in T3 by lia. fold s3 in T3. change (Z.min (4 + 4) 47) with 8 in T3.
  pose proof (topfull_step 8 8 _ ltac:(lia) T3) as T4. rewrite <- (u_orsrl s3 8) in T4 by lia. fold s4 in T4. change (Z.min (8 + 8) 47) with 16 in T4.
  pose proof (topfull_step 16 16 _ ltac:(lia) T4) as T5. rewrite <- (u_orsrl s4 16) in T5 by lia. fold s5 in T5. change (Z.min (16 + 16) 47) with 32 in T5.
  pose proof (topfull_step 32 32 _ ltac:(lia) T5) as T6. rewrite <- (u_orsrl s5 32) in T6 by lia. change (Z.min (32 + 32) 47) with 47 in T6.
  apply topfull_all in T6. apply bv_eq. rewrite T6. reflexivity.
Qed.

Local Ltac greg := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ]; rewrite ?getr_zero.
Local Ltac wlit := greg; first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].

Section Block.
  Variable SEGS : list Segment.
  Variable x : Z.
  Hypothesis Hx : 0 <= x /\ x + 180 < 2 ^ 64.
  Hypothesis CODE : forall i, (i < 45)%nat -> fetch_word SEGS (Z_to_bv 64 (x + 4 * Z.of_nat i)) = Some (nth i MAXVA_WORDS W0).

  Definition maxva_post (regs regs' : bvmap 5 word) : Prop :=

    getr regs' 10 = Z_to_bv 64 0x7fffffffffff /\ getr regs' 11 = Z_to_bv 64 0xffffffffffffffff /\ getr regs' 12 = Z_to_bv 64 0x3333333333333333 /\ getr regs' 13 = Z_to_bv 64 0xf0f0f0f0f0f0f0f /\ getr regs' 14 = Z_to_bv 64 0x101010101010101 /\ getr regs' 15 = Z_to_bv 64 0x7fffc00000000000
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).

  #[using="Hx CODE"] Lemma maxva_block : forall regs M rom,
    2 ^ 46 <= bv_unsigned (getr regs 10) < 2 ^ 47 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 180)) M rom)
      /\ maxva_post regs regs'.
  Proof.
    intros regs M rom Hx10.
    assert (C0 : fetch_word SEGS (Z_to_bv 64 x) = Some W0).
    { replace x with (x + 4 * Z.of_nat 0) at 1 by lia. exact (CODE 0%nat ltac:(lia)). }
    eexists. split.
    -

      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W0 11 10 (1 : bv 6) (v_srli (getr regs 10%bv) 1) C0 E0 D0 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 1).

      eapply mst_step; [reflexivity | eapply (step_lui_at SEGS _ _ M rom W1 12 (349525 : bv 20) (Z_to_bv 64 0x55555000) (CODE 1%nat ltac:(lia)) E1 D1 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 2).

      eapply mst_step; [reflexivity | eapply (step_lui_at SEGS _ _ M rom W2 13 (209715 : bv 20) (Z_to_bv 64 0x33333000) (CODE 2%nat ltac:(lia)) E2 D2 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 3).

      eapply mst_step; [reflexivity | eapply (step_lui_at SEGS _ _ M rom W3 14 (61681 : bv 20) (Z_to_bv 64 0xf0f1000) (CODE 3%nat ltac:(lia)) E3 D3 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 4).

      eapply mst_step; [reflexivity | eapply (step_lui_at SEGS _ _ M rom W4 15 (4112 : bv 20) (Z_to_bv 64 0x1010000) (CODE 4%nat ltac:(lia)) E4 D4 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 5).

      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W5 10 10 11 (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (CODE 5%nat ltac:(lia)) E5 D5 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 6).

      eapply mst_step; [reflexivity | eapply (step_addiw_at SEGS _ _ M rom W6 11 12 (1365 : bv 12) (Z_to_bv 64 0x55555555) (CODE 6%nat ltac:(lia)) E6 D6 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 7).

      eapply mst_step; [reflexivity | eapply (step_addiw_at SEGS _ _ M rom W7 12 13 (819 : bv 12) (Z_to_bv 64 0x33333333) (CODE 7%nat ltac:(lia)) E7 D7 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 8).

      eapply mst_step; [reflexivity | eapply (step_addiw_at SEGS _ _ M rom W8 13 14 (3855 : bv 12) (Z_to_bv 64 0xf0f0f0f) (CODE 8%nat ltac:(lia)) E8 D8 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 9).

      eapply mst_step; [reflexivity | eapply (step_addiw_at SEGS _ _ M rom W9 14 15 (257 : bv 12) (Z_to_bv 64 0x1010101) (CODE 9%nat ltac:(lia)) E9 D9 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 10).

      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W10 15 10 (2 : bv 6) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2) (CODE 10%nat ltac:(lia)) E10 D10 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 11).

      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W11 10 10 15 (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (CODE 11%nat ltac:(lia)) E11 D11 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 12).

      eapply mst_step; [reflexivity | eapply (step_slli_at SEGS _ _ M rom W12 15 11 (32 : bv 6) (Z_to_bv 64 0x5555555500000000) (CODE 12%nat ltac:(lia)) E12 D12 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 13).

      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W13 11 11 15 (Z_to_bv 64 0x5555555555555555) (CODE 13%nat ltac:(lia)) E13 D13 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 14).

      eapply mst_step; [reflexivity | eapply (step_slli_at SEGS _ _ M rom W14 15 12 (32 : bv 6) (Z_to_bv 64 0x3333333300000000) (CODE 14%nat ltac:(lia)) E14 D14 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 15).

      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W15 12 12 15 (Z_to_bv 64 0x3333333333333333) (CODE 15%nat ltac:(lia)) E15 D15 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 16).

      eapply mst_step; [reflexivity | eapply (step_slli_at SEGS _ _ M rom W16 15 13 (32 : bv 6) (Z_to_bv 64 0xf0f0f0f00000000) (CODE 16%nat ltac:(lia)) E16 D16 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 17).

      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W17 13 13 15 (Z_to_bv 64 0xf0f0f0f0f0f0f0f) (CODE 17%nat ltac:(lia)) E17 D17 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 18).

      eapply mst_step; [reflexivity | eapply (step_slli_at SEGS _ _ M rom W18 15 14 (32 : bv 6) (Z_to_bv 64 0x101010100000000) (CODE 18%nat ltac:(lia)) E18 D18 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 19).

      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W19 14 14 15 (Z_to_bv 64 0x101010101010101) (CODE 19%nat ltac:(lia)) E19 D19 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 20).

      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W20 15 10 (4 : bv 6) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4) (CODE 20%nat ltac:(lia)) E20 D20 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 21).

      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W21 10 10 15 (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (CODE 21%nat ltac:(lia)) E21 D21 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 22).

      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W22 15 10 (8 : bv 6) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8) (CODE 22%nat ltac:(lia)) E22 D22 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 23).

      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W23 10 10 15 (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) (CODE 23%nat ltac:(lia)) E23 D23 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 24).

      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W24 15 10 (16 : bv 6) (v_srli (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) 16) (CODE 24%nat ltac:(lia)) E24 D24 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 25).

      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W25 10 10 15 (v_or (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) (v_srli (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) 16)) (CODE 25%nat ltac:(lia)) E25 D25 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 26).

      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W26 15 10 (32 : bv 6) (v_srli (v_or (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) (v_srli (v_or (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) (v_srli (v_or (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) (v_srli (v_or (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) (v_srli (v_or (getr regs 10%bv) (v_srli (getr regs 10%bv) 1)) 2)) 4)) 8)) 16)) 32) (CODE 26%nat ltac:(lia)) E26 D26 eq_refl); greg; reflexivity |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 27).

      eapply mst_step; [reflexivity | eapply (step_or_at SEGS _ _ M rom W27 10 10 15 (Z_to_bv 64 0x7fffffffffff) (CODE 27%nat ltac:(lia)) E27 D27 eq_refl); greg; exact (smear47 _ Hx10) |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 28).

      eapply mst_step; [reflexivity | eapply (step_xori_at SEGS _ _ M rom W28 10 10 (4095 : bv 12) (Z_to_bv 64 0xffff800000000000) (CODE 28%nat ltac:(lia)) E28 D28 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 29).

      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W29 15 10 (1 : bv 6) (Z_to_bv 64 0x7fffc00000000000) (CODE 29%nat ltac:(lia)) E29 D29 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 30).

      eapply mst_step; [reflexivity | eapply (step_and_at SEGS _ _ M rom W30 11 15 11 (Z_to_bv 64 0x5555400000000000) (CODE 30%nat ltac:(lia)) E30 D30 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 31).

      eapply mst_step; [reflexivity | eapply (step_sub_at SEGS _ _ M rom W31 10 10 11 (Z_to_bv 64 0xaaaa400000000000) (CODE 31%nat ltac:(lia)) E31 D31 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 32).

      eapply mst_step; [reflexivity | eapply (step_and_at SEGS _ _ M rom W32 11 10 12 (Z_to_bv 64 0x2222000000000000) (CODE 32%nat ltac:(lia)) E32 D32 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 33).

      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W33 10 10 (2 : bv 6) (Z_to_bv 64 0x2aaa900000000000) (CODE 33%nat ltac:(lia)) E33 D33 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 34).

      eapply mst_step; [reflexivity | eapply (step_and_at SEGS _ _ M rom W34 10 10 12 (Z_to_bv 64 0x2222100000000000) (CODE 34%nat ltac:(lia)) E34 D34 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 35).

      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W35 10 11 10 (Z_to_bv 64 0x4444100000000000) (CODE 35%nat ltac:(lia)) E35 D35 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 36).

      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W36 11 10 (4 : bv 6) (Z_to_bv 64 0x444410000000000) (CODE 36%nat ltac:(lia)) E36 D36 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 37).

      eapply mst_step; [reflexivity | eapply (step_add_at SEGS _ _ M rom W37 10 10 11 (Z_to_bv 64 0x4888510000000000) (CODE 37%nat ltac:(lia)) E37 D37 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 38).

      eapply mst_step; [reflexivity | eapply (step_and_at SEGS _ _ M rom W38 10 10 13 (Z_to_bv 64 0x808010000000000) (CODE 38%nat ltac:(lia)) E38 D38 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 39).

      eapply mst_step; [reflexivity | eapply (step_mul_at SEGS _ _ M rom W39 10 10 14 (Z_to_bv 64 0x1109010000000000) (CODE 39%nat ltac:(lia)) E39 D39 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 40).

      eapply mst_step; [reflexivity | eapply (step_srli_at SEGS _ _ M rom W40 10 10 (56 : bv 6) (Z_to_bv 64 0x11) (CODE 40%nat ltac:(lia)) E40 D40 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 41).

      eapply mst_step; [reflexivity | eapply (step_subw_at SEGS _ _ M rom W41 10 0 10 (Z_to_bv 64 0xffffffffffffffef) (CODE 41%nat ltac:(lia)) E41 D41 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 42).

      eapply mst_step; [reflexivity | eapply (step_addi_at SEGS _ _ M rom W42 11 0 (4095 : bv 12) (Z_to_bv 64 0xffffffffffffffff) (CODE 42%nat ltac:(lia)) E42 D42 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 43).

      eapply mst_step; [reflexivity | eapply (step_sll_at SEGS _ _ M rom W43 10 11 10 (Z_to_bv 64 0xffff800000000000) (CODE 43%nat ltac:(lia)) E43 D43 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 44).

      eapply mst_step; [reflexivity | eapply (step_xori_at SEGS _ _ M rom W44 10 10 (4095 : bv 12) (Z_to_bv 64 0x7fffffffffff) (CODE 44%nat ltac:(lia)) E44 D44 eq_refl); wlit |].
      rewrite v_addi_lit by lia. pc_is (x + 4 * Z.of_nat 45).
      pc_is (x + 180). apply mst_refl.
    - unfold maxva_post. greg. repeat split; try reflexivity.
      intros r N10 N11 N12 N13 N14 N15. repeat (rewrite getr_other by assumption). reflexivity.
  Qed.
End Block.
