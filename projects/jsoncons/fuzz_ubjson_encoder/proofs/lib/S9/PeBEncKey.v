(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PmModelFactsA PmStep PeStepAB0 PmParKit PeBSrcKit PeBParKit LibIfaceAB PmBUar PeBSrcRead1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrame PeCFrameA PeCValSpecA PeEncKit PeBCReset1 PeBEncKitC PeBEncKeyP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_ad440_ad444 Eb0_code_ad4bc_ad4cc Eb0_code_ad4f4_ad4fc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENCK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).
Abbreviation SBL := 2147450880.

Definition CSK : list nat := [3; 4; 23; 24; 25; 26; 27]%nat.

Definition CSI : list nat := [2; 8; 20; 21; 22; 3; 4; 23; 24; 25; 26; 27]%nat.

Lemma gstep fx R R' M (pc pc2 : Z) (pcw : word) (W : bv 32) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W ->
  RiscvSemantics.step RSEGS (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) = MachineOk (mkst R' pcw M (seg_rom RSEGS)) ->
  pcw = Z_to_bv 64 pc2 ->
  msteps RSEGS (mst fx R pc M) (mst fx R' pc2 M).
Proof. intros HF HS HP. eapply mst_step; [reflexivity| | apply mst_refl]. rewrite HS, HP. reflexivity. Qed.
Lemma addi_lit pc k : 0 <= pc < 2 ^ 64 -> 0 <= pc + k < 2 ^ 64 -> v_addi (Z_to_bv 64 pc) k = Z_to_bv 64 (pc + k).
Proof. intros. unfold v_addi. rewrite L5.unsigned_lit by Lia.lia. reflexivity. Qed.
Lemma reg_index_neq (i j : nat) : (i < 32)%nat -> (j < 32)%nat -> i <> j -> (reg i) <> (reg j).
Proof.
  intros Hi Hj Hne E. apply Hne. apply (f_equal (@bv_unsigned 5)) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 5) with 32 in E. rewrite !Z.mod_small in E by Lia.lia. Lia.lia.
Qed.
Lemma land7 c : 0 <= c -> Z.land c 7 = c mod 8.
Proof. intros Hc. change 7 with (Z.ones 3). rewrite Z.land_ones by Lia.lia. reflexivity. Qed.

Lemma chk1 fx R M cur k :
  getr R (reg 9) = Z_to_bv 64 cur -> getr R (reg 20) = Z_to_bv 64 SBL -> 0 <= cur < 2 ^ 47 ->
  rdn RSEGS M (Z_to_bv 64 (cur / 8 + SBL)) 1%nat = Some [Z_to_bv 8 k] ->
  (k = 0 \/ (1 <= k <= 7 /\ cur mod 8 < k)) ->
  exists R', msteps RSEGS (mst fx R 0xad50c M) (mst fx R' 0xad51c M)
    /\ (forall j, j <> 11%nat -> j <> 12%nat -> (j < 32)%nat -> getr R' (reg j) = getr R (reg j)).
Proof.
  intros A8 A20 Hc RD Hk.
  assert (N11 : (reg 11) <> 0%bv) by (intros X; discriminate X). assert (N12 : (reg 12) <> 0%bv) by (intros X; discriminate X).
  set (R1 := regupd R (reg 11) (v_srli (getr R (reg 9)) (bv_unsigned (3%bv : bv 6)))).
  set (R2 := regupd R1 (reg 11) (v_add (getr R1 (reg 11)) (getr R1 (reg 20)))).
  set (R3 := regupd R2 (reg 11) (v_lb (Z_to_bv 8 k))).
  assert (E1 : getr R1 (reg 11) = Z_to_bv 64 (cur / 8)).
  { unfold R1. rewrite (getr_same _ _ _ N11), A8. change (bv_unsigned (3%bv : bv 6)) with 3. unfold v_srli. rewrite Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by Lia.lia. rewrite Z.shiftr_div_pow2 by Lia.lia. reflexivity. }
  assert (E1o : forall j, j <> 11%nat -> (j < 32)%nat -> getr R1 (reg j) = getr R (reg j)) by (intros j Hj Hl; unfold R1; apply getr_other; apply reg_index_neq; Lia.lia).
  assert (E2 : getr R2 (reg 11) = Z_to_bv 64 (cur / 8 + SBL)).
  { unfold R2. rewrite (getr_same _ _ _ N11), E1, (E1o 20%nat) by Lia.lia. rewrite A20. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite !Z.mod_small by Lia.lia. reflexivity. }
  assert (E2o : forall j, j <> 11%nat -> (j < 32)%nat -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj Hl; unfold R2; apply getr_other; apply reg_index_neq; Lia.lia).
  assert (E3 : getr R3 (reg 11) = Z_to_bv 64 k).
  { unfold R3. rewrite (getr_same _ _ _ N11). unfold v_lb. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap. change (bv_modulus 8) with 256. change (bv_half_modulus 8) with 128.
    rewrite (Z.mod_small k) by Lia.lia. rewrite (Z.mod_small (k + 128)) by Lia.lia. rewrite !Z.mod_small by Lia.lia. Lia.lia. }
  assert (E3o : forall j, j <> 11%nat -> (j < 32)%nat -> getr R3 (reg j) = getr R2 (reg j)) by (intros j Hj Hl; unfold R3; apply getr_other; apply reg_index_neq; Lia.lia).
  assert (MS3 : msteps RSEGS (mst fx R 0xad50c M) (mst fx R3 0xad518 M)).
  { eapply msteps_trans.
    { eapply (gstep fx R R1 M 0xad50c 0xad510 _ W_ad4bc F_ad4bc); [rewrite (step_srli RSEGS R (Z_to_bv 64 0xad50c) M (seg_rom RSEGS) W_ad4bc _ _ _ F_ad4bc eq_refl D_ad4bc); reflexivity| apply addi_lit; Lia.lia]. }
    eapply msteps_trans.
    { eapply (gstep fx R1 R2 M 0xad510 0xad514 _ W_ad4c0 F_ad4c0); [rewrite (step_add RSEGS R1 (Z_to_bv 64 0xad510) M (seg_rom RSEGS) W_ad4c0 _ _ _ F_ad4c0 eq_refl D_ad4c0); reflexivity| apply addi_lit; Lia.lia]. }
    eapply (gstep fx R2 R3 M 0xad514 0xad518 _ W_ad4c4 F_ad4c4).
    { rewrite (step_lb RSEGS R2 (Z_to_bv 64 0xad514) M (seg_rom RSEGS) W_ad4c4 _ _ _ (Z_to_bv 8 k) F_ad4c4 eq_refl D_ad4c4); [reflexivity|].
      rewrite L5K.rl11, E2. change (bv_signed (0%bv : bv 12)) with 0. rewrite addi_lit by Lia.lia. rewrite Z.add_0_r. exact RD. }
    apply addi_lit; Lia.lia. }
  destruct Hk as [K0|(K17 & KM)].
  - exists R3. split.
    + eapply msteps_trans; [exact MS3|]. eapply (gstep fx R3 R3 M 0xad518 0xad51c _ W_ad4c8 F_ad4c8).
      { rewrite (step_bne_ft RSEGS R3 (Z_to_bv 64 0xad518) M (seg_rom RSEGS) W_ad4c8 _ _ _ F_ad4c8 eq_refl D_ad4c8); [reflexivity|].
        rewrite L5K.rl11, E3, K0. unfold getr. cbn [bv_eqb Z.eqb]. apply c_eq_refl. }
      apply addi_lit; Lia.lia.
    + intros j H11 H12 Hl. rewrite (E3o j), (E2o j), (E1o j) by Lia.lia. reflexivity.
  - set (R4 := regupd R3 (reg 12) (v_andi (getr R3 (reg 9)) (bv_signed (7%bv : bv 12)))).
    assert (E4 : getr R4 (reg 12) = Z_to_bv 64 (cur mod 8)).
    { unfold R4. rewrite (getr_same _ _ _ N12), (E3o 9%nat), (E2o 9%nat), (E1o 9%nat) by Lia.lia. rewrite A8. change (bv_signed (7%bv : bv 12)) with 7.
      unfold v_andi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite (Z.mod_small cur) by Lia.lia. rewrite (Z.mod_small 7) by Lia.lia. rewrite land7 by Lia.lia. rewrite !Z.mod_small by Lia.lia. reflexivity. }
    assert (E4o : forall j, j <> 12%nat -> (j < 32)%nat -> getr R4 (reg j) = getr R3 (reg j)) by (intros j Hj Hl; unfold R4; apply getr_other; apply reg_index_neq; Lia.lia).
    exists R4. split.
    + eapply msteps_trans; [exact MS3|]. eapply msteps_trans.
      { eapply (gstep fx R3 R3 M 0xad518 0xad544 _ W_ad4c8 F_ad4c8).
        - rewrite (step_bne_tk RSEGS R3 (Z_to_bv 64 0xad518) M (seg_rom RSEGS) W_ad4c8 _ _ _ F_ad4c8 eq_refl D_ad4c8); [reflexivity|].
          rewrite L5K.rl11, E3. replace (getr R3 (0%bv : bv 5)) with (Z_to_bv 64 0) by reflexivity. apply c_eq_neq. rewrite !L5.unsigned_lit by (clear - K17; Lia.lia). clear - K17. Lia.lia.
        - unfold btgt. vm_compute. reflexivity. }
      eapply msteps_trans.
      { eapply (gstep fx R3 R4 M 0xad544 0xad548 _ W_ad4f4 F_ad4f4); [rewrite (step_andi RSEGS R3 (Z_to_bv 64 0xad544) M (seg_rom RSEGS) W_ad4f4 _ _ _ F_ad4f4 eq_refl D_ad4f4); reflexivity| apply addi_lit; Lia.lia]. }
      eapply (gstep fx R4 R4 M 0xad548 0xad51c _ W_ad4f8 F_ad4f8).
      * rewrite (step_blt_tk RSEGS R4 (Z_to_bv 64 0xad548) M (seg_rom RSEGS) W_ad4f8 _ _ _ F_ad4f8 eq_refl D_ad4f8); [reflexivity|].
        rewrite L5K.rl12, L5K.rl11, E4, (E4o 11%nat) by Lia.lia. rewrite E3. unfold c_lts, bv_lts. unfold bv_signed. rewrite !Z_to_bv_unsigned.
        unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
        rewrite (Z.mod_small (cur mod 8)) by Lia.lia. rewrite (Z.mod_small k) by Lia.lia. rewrite !Z.mod_small by Lia.lia. apply Z.ltb_lt. Lia.lia.
      * unfold btgt. vm_compute. reflexivity.
    + intros j H11 H12 Hl. rewrite (E4o j), (E3o j), (E2o j), (E1o j) by Lia.lia. reflexivity.
Qed.

Definition inregsA (R : bvmap 5 word) (sp ov sv ec : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 80) /\ getr R (reg 8) = Z_to_bv 64 ov /\ getr R (reg 9) = Z_to_bv 64 sv /\ getr R (reg 18) = Z_to_bv 64 (sv + 8) /\ getr R (reg 19) = Z_to_bv 64 ec
  /\ getr R (reg 20) = Z_to_bv 64 SBL /\ getr R (reg 21) = Z_to_bv 64 (sv / 8 + SBL) /\ getr R (reg 22) = Z_to_bv 64 ((sv + 8) / 8 + SBL).

Definition inregsL (R : bvmap 5 word) (sp ov : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 80) /\ getr R (reg 8) = Z_to_bv 64 (ov + 8) /\ getr R (reg 21) = Z_to_bv 64 ((ov + 8) / 8 + SBL) /\ getr R (reg 20) = Z_to_bv 64 SBL
  /\ getr R (reg 22) = Z_to_bv 64 18446744073709551615.
Definition fstat (M : word -> option byte) (sp : Z) : Prop :=
  L5.img_clear M 1273856 1306624 /\ L5.u64_at RSEGS M 1335544 SBL /\ L5.u32_at RSEGS M 1335552 1 /\ 140735332487248 <= sp <= 140737488355328 /\ sp mod 16 = 0
  /\ L5.writable RSEGS M (sp - 80) 80.

Definition fov (M : word -> option byte) (sp ov osk : Z) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ ((sp - 80) + 80 <= ov \/ ov + 56 <= (sp - 80))
  /\ L5.u64_at RSEGS M (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0.

Definition fsv (M : word -> option byte) (sp sv dptr n : Z) : Prop :=
  4096 <= sv <= 140737488355312 /\ sv mod 8 = 0 /\ (2147446784 + 17592186048512 <= sv \/ sv + 16 <= 2147446784)
  /\ L5KA.zeros_at M (sv / 8 + SBL) 2 /\ L5KA.zeros_at M ((sv + 8) / 8 + SBL) 1 /\ (sv + 16 <= (sp - 80) \/ (sp - 80) + 80 <= sv)
  /\ L5.u64_at RSEGS M sv dptr /\ L5.u64_at RSEGS M (sv + 8) n /\ 0 <= dptr <= 140737488355328 /\ 0 <= n <= 67108864.

Definition fcells (R0 : bvmap 5 word) (r : Z) (M : word -> option byte) (sp : Z) : Prop :=
  L5.u64_at RSEGS M (sp - 8) r /\ L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8))) /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9)))
  /\ L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18))) /\ L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (sp - 64) (bv_unsigned (getr R0 (reg 22))).

Definition runA : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk sv ec dptr n r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= sv < 2 ^ 64 -> 0 <= ec < 2 ^ 64 -> 0 <= dptr < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 ov -> getr R (reg 11) = Z_to_bv 64 sv -> getr R (reg 13) = Z_to_bv 64 ec -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
    fstat M sp -> fov M sp ov osk -> fsv M sp sv dptr n ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad3e8 M) (mst fx' R' 0xb4350 M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 0xad454 /\ inregsA R' sp ov sv ec /\ getr R' (reg 10) = Z_to_bv 64 dptr /\ getr R' (reg 11) = Z_to_bv 64 n
      /\ fcells R r M' sp.

Definition runB : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk sv ec dptr n : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= sv < 2 ^ 64 -> 0 <= ec < 2 ^ 64 -> 0 <= dptr < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    inregsA R sp ov sv ec -> getr R (reg 11) = Z_to_bv 64 0 -> fstat M sp -> fov M sp ov osk -> fsv M sp sv dptr n ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad454 M) (mst fx' R' 0xafe84 M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)) /\ getr R' (reg 9) = getr R (reg 9) /\ getr R' (reg 18) = getr R (reg 18) /\ getr R' (reg 19) = getr R (reg 19)
      /\ getr R' (reg 1) = Z_to_bv 64 0xad4a8 /\ getr R' (reg 10) = Z_to_bv 64 ov /\ getr R' (reg 11) = Z_to_bv 64 n.

Definition runC0 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov osk sv ec dptr r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= sv < 2 ^ 64 -> 0 <= ec < 2 ^ 64 -> 0 <= dptr < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    inregsA R sp ov sv ec -> fstat M sp -> fov M sp ov osk -> fsv M sp sv dptr 0 -> fcells R0 r M sp -> L5.ra_ok r ->
    getr R0 (reg 2) = Z_to_bv 64 sp -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad4a8 M) (mst fx' R' r M')
      /\ regs_preserved R0 R'.

Definition runC1 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk sv ec dptr n : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= sv < 2 ^ 64 -> 0 <= ec < 2 ^ 64 -> 0 <= dptr < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    inregsA R sp ov sv ec -> fstat M sp -> fov M sp ov osk -> fsv M sp sv dptr n -> 1 <= n -> 1 <= dptr <= 140737488355326 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad4a8 M) (mst fx' R' 0xad50c M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ inregsL R' sp ov /\ getr R' (reg 9) = Z_to_bv 64 dptr /\ getr R' (reg 19) = Z_to_bv 64 dptr /\ getr R' (reg 18) = Z_to_bv 64 n /\ getr R' (reg 10) = Z_to_bv 64 osk.

Definition runD : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk cur cnt b : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= cur < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
    inregsL R sp ov -> getr R (reg 9) = Z_to_bv 64 cur -> getr R (reg 19) = Z_to_bv 64 cur -> getr R (reg 18) = Z_to_bv 64 cnt -> getr R (reg 10) = Z_to_bv 64 osk ->
    fstat M sp -> fov M sp ov osk -> 1 <= cur <= 140737488355326 -> 1 <= cnt <= 67108864 -> L5.u8_at RSEGS M cur b -> 0 <= b <= 255 ->
    (cur + 1 <= sp - 80 \/ (sp - 80) + 80 <= cur) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 65 <= i < sp - 65 + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad51c M) (mst fx' R' 0xb120c M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)) /\ getr R' (reg 9) = getr R (reg 9) /\ getr R' (reg 18) = getr R (reg 18) /\ getr R' (reg 19) = getr R (reg 19)
      /\ getr R' (reg 1) = Z_to_bv 64 0xad52c /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp - 65)
      /\ L5.u8_at RSEGS M' (sp - 65) b.

Definition runM0 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov cur r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= cur < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    inregsL R sp ov -> getr R (reg 9) = Z_to_bv 64 cur -> getr R (reg 19) = Z_to_bv 64 cur -> getr R (reg 18) = Z_to_bv 64 1 ->
    fstat M sp -> 1 <= cur <= 140737488355326 -> fcells R0 r M sp -> L5.ra_ok r ->
    getr R0 (reg 2) = Z_to_bv 64 sp -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad52c M) (mst fx' R' r M')
      /\ regs_preserved R0 R'.

Definition runM1 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk cur cnt : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= cur < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 ->
    inregsL R sp ov -> getr R (reg 9) = Z_to_bv 64 cur -> getr R (reg 19) = Z_to_bv 64 cur -> getr R (reg 18) = Z_to_bv 64 cnt ->
    fstat M sp -> fov M sp ov osk -> 1 <= cur <= 140737488355326 -> 2 <= cnt <= 67108864 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad52c M) (mst fx' R' 0xad50c M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 9) = Z_to_bv 64 (cur + 1) /\ getr R' (reg 19) = Z_to_bv 64 (cur + 1) /\ getr R' (reg 18) = Z_to_bv 64 (cnt - 1) /\ getr R' (reg 10) = Z_to_bv 64 osk.

Local Ltac kept_tac KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Local Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEBENCKP.aligned; assumption | lia]).
Local Ltac wid G := let H := fresh in pose proof (bv_unsigned_in_range 64 G) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Local Ltac junk R i := let G := fresh "J" in assert (G : getr R (reg i) = Z_to_bv 64 (bv_unsigned (getr R (reg i)))) by (symmetry; apply PMPK.word_id); wid (getr R (reg i)).

Lemma u_runA : runA.
Proof.
  unfold runA. intros fx R M sp ov osk sv ec dptr n r H1 H2 H3 H4 H5 H6 H7 G2 G10 G11 G13 G1 RA (K0 & K1 & K2 & K3 & K4 & K5) FOV FSV.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9). destruct FSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  assert (HO : bv_unsigned (getr R (reg 10)) = ov) by (rewrite G10; apply L5.unsigned_lit; exact H2).
  assert (HS : bv_unsigned (getr R (reg 11)) = sv) by (rewrite G11; apply L5.unsigned_lit; exact H4).
  assert (HE : bv_unsigned (getr R (reg 13)) = ec) by (rewrite G13; apply L5.unsigned_lit; exact H5).
  assert (Hr : bv_unsigned (getr R (reg 1)) = r) by (rewrite G1; apply L5.unsigned_lit; destruct RA as [Hr1 Hr2]; clear - Hr1; lia).
  pose proof (PEBENCKP.bqKA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => dptr | 34%nat => n | 41%nat => osk | _ => 0 end)) as P. cbn beta iota in P. rewrite !HO, !HS in P.
  feedP P. rewrite Hr in P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & _ & T18 & T19 & T20 & T21 & T22 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [exact T1|]. split.
  { split; [exact T2|]. split; [rewrite T8; exact G10|]. split; [rewrite T9; exact G11|]. split; [exact T18|]. split; [rewrite T19; exact G13|]. split; [exact T20|]. split; [exact T21| exact T22]. }
  split; [exact T10|]. split; [exact T11|].
  split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32|]. split; [exact S40|]. split; [exact S48|]. split; [exact S56| exact S64].
Qed.

Lemma u_runB : runB.
Proof.
  unfold runB. intros fx R M sp ov osk sv ec dptr n H1 H2 H3 H4 H5 H6 H7 (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22) G11 (K0 & K1 & K2 & K3 & K4 & K5) FOV FSV.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9). destruct FSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  junk R 10%nat. junk R 12%nat. junk R 13%nat.
  pose proof (PEBENCKP.bqKB_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => sv | 13%nat => ec | 33%nat => dptr | 34%nat => n | 41%nat => osk
      | 55%nat => bv_unsigned (getr R (reg 10)) | 57%nat => bv_unsigned (getr R (reg 13)) | 58%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P. cbn beta iota in P.
  feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T10 & T11).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [apply KS1; inl|]. split; [apply KS1; inl|]. split; [apply KS1; inl|]. split; [exact T1|]. split; [exact T10| exact T11].
Qed.

Lemma regs_end (R R0 R3 : bvmap 5 word) (sp : Z) (KS : list nat) :
  (forall j, In j CSK -> In j KS) -> (forall x, In x KS -> getr R3 (reg x) = getr R (reg x)) -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
  getr R0 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 2) = Z_to_bv 64 sp ->
  getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R3 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  getr R3 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) -> regs_preserved R0 R3.
Proof.
  intros SUB KS3 QCS Rsp T2 T8 T9 T18 T19 T20 T21 T22. apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
  repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8; apply PMPK.word_id | rewrite T9; apply PMPK.word_id | rewrite T18; apply PMPK.word_id
                                          | rewrite T19; apply PMPK.word_id | rewrite T20; apply PMPK.word_id | rewrite T21; apply PMPK.word_id | rewrite T22; apply PMPK.word_id
                                          | rewrite (KS3 _) by (apply SUB; inl); apply QCS; inl ] |]). destruct Hj.
Qed.

Lemma u_runC0 : runC0.
Proof.
  unfold runC0. intros fx R R0 M sp ov osk sv ec dptr r H1 H2 H3 H4 H5 H6 H7 (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22) (K0 & K1 & K2 & K3 & K4 & K5) FOV FSV
    (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64) RA R0sp QCS.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9). destruct FSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  junk R 10%nat. junk R 11%nat. junk R 12%nat. junk R 13%nat.
  wid (getr R0 (reg 8)). wid (getr R0 (reg 9)). wid (getr R0 (reg 18)). wid (getr R0 (reg 19)). wid (getr R0 (reg 20)). wid (getr R0 (reg 21)). wid (getr R0 (reg 22)).
  assert (P : exists (fx' : FPState) R' M', mem_grows M M' /\ (forall a : word, M' a = M a) /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad4a8 M) (mst fx' R' 0xad490 M') /\ (forall x, In x PEBENCKP.KS_bqKC0z -> getr R' (reg x) = getr R (reg x))
      /\ getr R' (reg 1) = Z_to_bv 64 r /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) /\ getr R' (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9)))
      /\ getr R' (reg 10) = Z_to_bv 64 1 /\ getr R' (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) /\ getr R' (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19)))
      /\ getr R' (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) /\ getr R' (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) /\ getr R' (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22)))).
  { destruct (Z.eq_dec dptr 0) as [DZ|DP].
    - assert (DZR : 0 <= dptr <= 0) by (clear - DZ; lia).
  pose proof (PEBENCKP.bqKC0z_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => sv | 13%nat => ec | 33%nat => dptr | 41%nat => osk | 44%nat => r
      | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19))
      | 49%nat => bv_unsigned (getr R0 (reg 20)) | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22))
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 13)) | 58%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & FRW1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & T18 & T19 & T20 & T21 & T22).
  exists fx1, R1, M1. repeat (split; [assumption|]). exact T22.
    - assert (DPR : 1 <= dptr <= 140737488355328) by (clear - DP H6 V9; lia).
  pose proof (PEBENCKP.bqKC0p_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => sv | 13%nat => ec | 33%nat => dptr | 41%nat => osk | 44%nat => r
      | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19))
      | 49%nat => bv_unsigned (getr R0 (reg 20)) | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22))
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 13)) | 58%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & FRW1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & T18 & T19 & T20 & T21 & T22).
  exists fx1, R1, M1. repeat (split; [assumption|]). exact T22. }
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T18 & T19 & T20 & T21 & T22).
  pose proof RA as (Hr1 & Hr2).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xad490 W_ad440 r F_ad440 eq_refl D_ad440 T1 ltac:(lia) Hr2) as MSR.
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
  apply (regs_end R R0 R1 sp PEBENCKP.KS_bqKC0z); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS1| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22].
Qed.

Lemma u_runC1 : runC1.
Proof.
  unfold runC1. intros fx R M sp ov osk sv ec dptr n H1 H2 H3 H4 H5 H6 H7 (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22) (K0 & K1 & K2 & K3 & K4 & K5) FOV FSV N1 D1.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9). destruct FSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  junk R 10%nat. junk R 11%nat. junk R 12%nat. junk R 13%nat.
  assert (V9' : 1 <= dptr <= 140737488355326) by exact D1. assert (V10' : 1 <= n <= 67108864) by (clear - N1 V10; lia). clear V9 V10.
  pose proof (PEBENCKP.bqKC1_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => sv | 13%nat => ec | 33%nat => dptr | 34%nat => n | 41%nat => osk
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 13)) | 58%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T8 & T9 & T10 & _ & T18 & T19 & T21 & T22).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [split; [rewrite (KS1 2%nat) by inl; exact G2|]; split; [exact T8|]; split; [exact T21|]; split; [rewrite (KS1 20%nat) by inl; exact G20| exact T22]|].
  split; [exact T9|]. split; [exact T19|]. split; [exact T18| exact T10].
Qed.

Lemma u_runD : runD.
Proof.
  unfold runD. intros fx R M sp ov osk cur cnt b H1 H2 H3 H4 H5 H6 (G2 & G8 & G21 & G20 & G22) G9 G19 G18 G10 (K0 & K1 & K2 & K3 & K4 & K5) FOV C1 N1 U8 B8 CD.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
  junk R 11%nat. junk R 12%nat. junk R 13%nat.
  assert (Q38 : 0 <= (ov + 8) / 8 + SBL < 2 ^ 64) by (clear - O1; Lia.lia). assert (Q38' : 2147451393 <= (ov + 8) / 8 + SBL <= 19791209299968) by (clear - O1; Lia.lia).
  pose proof (PEBENCKP.bqKD_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 36%nat => cur | 37%nat => cnt | 38%nat => (ov + 8) / 8 + SBL | 40%nat => b | 41%nat => osk
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 13)) | 58%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T11 & C65).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [apply KS1; inl|]. split; [apply KS1; inl|]. split; [apply KS1; inl|]. split; [exact T1|]. split; [rewrite (KS1 10%nat) by inl; exact G10|]. split; [exact T11| exact C65].
Qed.

Lemma u_runM0 : runM0.
Proof.
  unfold runM0. intros fx R R0 M sp ov cur r H1 H2 H3 H4 (G2 & G8 & G21 & G20 & G22) G9 G19 G18 (K0 & K1 & K2 & K3 & K4 & K5) C1 (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64) RA R0sp QCS.
  junk R 10%nat. junk R 11%nat. junk R 12%nat. junk R 13%nat.
  wid (getr R0 (reg 8)). wid (getr R0 (reg 9)). wid (getr R0 (reg 18)). wid (getr R0 (reg 19)). wid (getr R0 (reg 20)). wid (getr R0 (reg 21)). wid (getr R0 (reg 22)).
  assert (Q38 : 0 <= (ov + 8) / 8 + SBL < 2 ^ 64) by (clear - H2; Lia.lia).
  pose proof (PEBENCKP.bqKM0_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 36%nat => cur | 38%nat => (ov + 8) / 8 + SBL | 44%nat => r
      | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19))
      | 49%nat => bv_unsigned (getr R0 (reg 20)) | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22))
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 13)) | 58%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T18 & T19 & T20 & T21 & T22).
  pose proof RA as (Hr1 & Hr2).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xad490 W_ad440 r F_ad440 eq_refl D_ad440 T1 ltac:(lia) Hr2) as MSR.
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
  apply (regs_end R R0 R1 sp PEBENCKP.KS_bqKM0); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS1| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22].
Qed.

Lemma u_runM1 : runM1.
Proof.
  unfold runM1. intros fx R M sp ov osk cur cnt H1 H2 Ho H3 H4 (G2 & G8 & G21 & G20 & G22) G9 G19 G18 (K0 & K1 & K2 & K3 & K4 & K5) FOV C1 N2.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
  junk R 10%nat. junk R 11%nat. junk R 12%nat. junk R 13%nat.
  assert (Q38 : 0 <= (ov + 8) / 8 + SBL < 2 ^ 64) by (clear - H2; Lia.lia). assert (Q38' : 2147451393 <= (ov + 8) / 8 + SBL <= 19791209299968) by (clear - O1; Lia.lia).
  pose proof (PEBENCKP.bqKM1_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 36%nat => cur | 37%nat => cnt | 38%nat => (ov + 8) / 8 + SBL | 41%nat => osk
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 13)) | 58%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T9 & T10 & _ & T18 & T19).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [exact T9|]. split; [exact T19|]. split; [exact T18| exact T10].
Qed.

Lemma u8_at_of_defined (M : word -> option byte) a : 0 <= a < 2 ^ 64 -> M (Z_to_bv 64 a) <> None -> exists b, 0 <= b <= 255 /\ L5.u8_at RSEGS M a b.
Proof.
  intros Ha D. destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [|exfalso; exact (D eq_refl)].
  exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb. split; [lia|].
  unfold L5.u8_at. cbn [rdn]. rewrite E. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMB.ly_as0 L C LY.

Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Hypothesis PUTL : PECSB.put_length_spec L ar HI P.
Hypothesis VAL : PECVSA.validate_fun_spec RSEGS AD L ar HI (pe_validate_enc EE).

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (dptr sv : Z) (l : list Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z).
Variables (xstk : list pstate) (xpos : Z) (xmore xdone xhalt : bool) (xdepth : Z) (xec : bool) (xestk : list eitem) (xedepth xlo xhi : Z) (xbad : bool).
Variables (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Let X : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad.
Let XS (a : Z) : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + a) (xhi + a) xbad.
Let n : Z := Z.of_nat (length l).
Let NB : Z := pl_size n + n.
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 4.
Hypothesis FRM : PMSPA.ffroomA 4 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 sv.
Hypothesis A13 : getr R (reg 13) = Z_to_bv 64 (PMSPA.o_ec AD fb).
Hypothesis SV8 : sv mod 8 = 0.
Hypothesis SVF : sv + 16 <= fb \/ fb + 2048 <= sv.
Hypothesis AOSV : PMSPA.aobjA FF sv 16.
Hypothesis ACSV : PMSPA.accA M sv 16.
Hypothesis U0 : L5.u64_at RSEGS M sv dptr.
Hypothesis U8 : L5.u64_at RSEGS M (sv + 8) n.
Hypothesis BYT : L5.bytes_at RSEGS M dptr l.
Hypothesis BOK : bytes_ok l.
Hypothesis N26 : n < 2 ^ 26.
Hypothesis DEF : L5.defined M dptr n.
Hypothesis ACC : PMSPA.accA M dptr n.
Hypothesis LOC : (exists B m, In (B, m) (PM.parser_own s) /\ B <= dptr /\ dptr + n <= B + m)
                 \/ (PMSPA.o_tb AD fb + 1 <= dptr /\ dptr + n <= PMSPA.o_tb AD fb + 24) \/ (dptr = 0 /\ l = [])
                 \/ (PMSPA.aobjA FF dptr n /\ (dptr + n <= fb \/ fb + 2048 <= dptr)).
Hypothesis UV : utf8_valid l = true.
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_enc p X.
Hypothesis HBN : PESKA.spa_hb P (xhi + NB).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (XS NB) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Definition FC (Mx : word -> option byte) : Prop := fcells R r Mx sp.
Let LB : list (Z * Z) := PEC.owned s en k ++ LBX.
Let LBc0 : list (Z * Z) := PM.parser_own s ++ LBX.
Let Ws : list L5.range := [(PESK.o_sink EE fb, 24)].
Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH;
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl3 in Rgp; rewrite L5K.rl4 in Rtp.
Local Ltac frame_facts :=
  pose proof FOK as ((rs & Hfb) & Fal);
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & _);
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6); cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6; change (ff_bytes 5) with 2048 in F1, F2, F3, F4, F5, F6;
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP; unfold FS_BYTES in F1, F2, F3, F4, F5, F6, FSAPP, FSCEIL, FSIMG.

Lemma FC_frame M1 M2 : (forall a, sp - 80 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros AG (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64). entry_facts.
  assert (SV : forall a0 w, sp - 80 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; clear - Hi H1 H2; lia| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC, fcells. repeat (split; [apply SV; [clear; lia| clear; lia| assumption]|]). apply SV; [clear; lia| clear; lia| assumption].
Qed.

Lemma FC_but M1 M2 lo hi : hi <= sp - 64 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros Hhi AG (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64). entry_facts.
  assert (SV : forall a0 w, sp - 64 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; [clear - Hi H1 H2 SLO SHI SPT; lia| clear - Hi H1 Hhi; lia]| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC, fcells. repeat (split; [apply SV; [clear; lia| clear; lia| assumption]|]). apply SV; [clear; lia| clear; lia| assumption].
Qed.
Lemma HFR : 80 = 32 \/ 80 = 64 \/ 80 = 80 \/ 80 = 96. Proof. right; right; left; reflexivity. Qed.
Lemma CSK3 : In 3%nat CSK. Proof. inl. Qed.
Lemma CSK4 : In 4%nat CSK. Proof. inl. Qed.
Lemma CSKall j : In j CSK -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.
Lemma CSIall j : In j CSI -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.
Lemma PLS : 2 <= pl_size n <= 9. Proof. unfold pl_size. repeat destruct (_ <=? _); lia. Qed.
Lemma N0 : 0 <= n. Proof. unfold n. clear. lia. Qed.

Abbreviation INV := (PEBEKC.inv L ar HI P M model LBX FF LK Aw cr sp fb xlo xhi s en k FC).
Abbreviation csk := (PEBEKC.csk CSK R).

Lemma csk_after R1 R2 : csk R1 -> regs_preserved R1 R2 -> csk R2.
Proof. intros QCS RP j Hj. rewrite (L5SAR.cs_of_preserved R1 R2 j RP (CSKall j Hj)). exact (QCS j Hj). Qed.
Lemma csk_kept R1 R2 : csk R1 -> (forall j, In j CSK -> getr R2 (reg j) = getr R1 (reg j)) -> csk R2.
Proof. intros QCS KS j Hj. rewrite (KS j Hj). exact (QCS j Hj). Qed.
Lemma csk_keptI R1 R2 : csk R1 -> (forall j, In j CSI -> getr R2 (reg j) = getr R1 (reg j)) -> csk R2.
Proof. intros QCS KS j Hj. rewrite (KS j) by (revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl). exact (QCS j Hj). Qed.
Lemma inregsL_after R1 R2 : inregsL R1 sp (PMSPA.o_v AD fb) -> regs_preserved R1 R2 -> inregsL R2 sp (PMSPA.o_v AD fb).
Proof.
  intros (G2 & G8 & G21 & G20 & G22) RP.
  split; [rewrite (L5SAR.cs_of_preserved R1 R2 2 RP) by inl; exact G2|]. split; [rewrite (L5SAR.cs_of_preserved R1 R2 8 RP) by inl; exact G8|].
  split; [rewrite (L5SAR.cs_of_preserved R1 R2 21 RP) by inl; exact G21|]. split; [rewrite (L5SAR.cs_of_preserved R1 R2 20 RP) by inl; exact G20| rewrite (L5SAR.cs_of_preserved R1 R2 22 RP) by inl; exact G22].
Qed.
Lemma inregsL_kept R1 R2 : inregsL R1 sp (PMSPA.o_v AD fb) -> (forall j, In j CSI -> getr R2 (reg j) = getr R1 (reg j)) -> inregsL R2 sp (PMSPA.o_v AD fb).
Proof.
  intros (G2 & G8 & G21 & G20 & G22) KS.
  split; [rewrite (KS 2%nat) by inl; exact G2|]. split; [rewrite (KS 8%nat) by inl; exact G8|]. split; [rewrite (KS 21%nat) by inl; exact G21|].
  split; [rewrite (KS 20%nat) by inl; exact G20| rewrite (KS 22%nat) by inl; exact G22].
Qed.

Lemma txt_facts : 0 <= dptr /\ dptr + n <= 2 ^ 47 /\ (n = 0 \/ 0 < dptr)
  /\ (n = 0 \/ (ar_fs ar <= dptr /\ dptr + n <= ar_fs ar + FS_BYTES) \/ (exists q m, In (q, m) (PM.parser_own s) /\ q <= dptr /\ dptr + n <= q + m)).
Proof.
  entry_facts. frame_facts.
  destruct LOC as [(B & m & Hin & X1 & X2)|[(X1 & X2)|[(X1 & X2)|(X1 & X2)]]].
  - assert (HinLB : In (B, m) LB) by (unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hin).
    pose proof (WB _ HinLB) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
    split; [clear - X1 Q0; Lia.lia|]. split; [clear - X2 Q4 SLO SHI SPT; Lia.lia|]. split; [right; clear - X1 Q0; Lia.lia|]. right; right. exists B, m. split; [exact Hin| split; [exact X1| exact X2]].
  - unfold PMSPA.o_tb, PMSPA.o_p in X1, X2. cbn [pa_off_p PeCLayoutB.CADDR_B] in X1, X2.
    split; [clear - X1 F1 FSAPP; Lia.lia|]. split; [clear - X2 F2 FSCEIL SLO SHI SPT; Lia.lia|]. split; [right; clear - X1 F1 FSAPP; Lia.lia|]. right; left. unfold FS_BYTES. clear - X1 X2 F1 F2; Lia.lia.
  - unfold n. rewrite X1, X2. cbn. split; [Lia.lia|]. split; [Lia.lia|]. split; [left; reflexivity|]. left; reflexivity.
  - pose proof X1 as (f & Hf & Y1 & Y2). pose proof (WF f Hf) as (W1 & W2 & _). unfold FS_BYTES in W1, W2.
    split; [clear - Y1 W1 FSAPP; Lia.lia|]. split; [clear - Y2 W2 FSCEIL SLO SHI SPT; Lia.lia|]. split; [right; clear - Y1 W1 FSAPP; Lia.lia|]. right; left. unfold FS_BYTES. clear - Y1 Y2 W1 W2; Lia.lia.
Qed.

Lemma step_ro a (fxq : FPState) Rq Mq mdq LKq Awq crq kq (pcq pc' : Z) (fx3 : FPState) R3 M3v :
  INV Mq mdq LKq Awq crq kq a ->
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 pc' M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) ->
  (forall md3, INV Mq md3 LKq Awq crq kq a -> srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx3) R3 pc' Mq md3) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INVq MS3 MG3 FRZ3 KX3. pose proof INVq as (FCq & _ & _ & _ & AMq & _ & _ & HHq & _).
  unfold PMSPA.cfg. apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq fxq fx3 Rq pcq R3 pc' M3v K HHq AMq MS3 MG3 FRZ3).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree Mq M3 AG3) as EM. subst M3.
  apply KX3. apply (PEBEKC.inv_frame L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq Mq mdq md3 LKq Awq crq kq a sp sp INVq);
    [clear; lia| clear; lia| intros w D; exact D| intros i _ _; reflexivity| exact FCq| exact HH3| exact AM3| exact MRT3].
Qed.

Lemma inv_callee0 Mq mdq LKq Awq crq kq a M2 md2 scr :
  INV Mq mdq LKq Awq crq kq a -> 0 <= scr <= 16384 ->
  L5CA.ahpres L ar (PEC.owned s en kq ++ LBX) FF (sp - 80) scr [] Mq M2 ->
  ri_inv HI (PEC.owned s en kq ++ LBX) FF LKq crq Awq M2 (vml_of md2) -> L5CA.amodel_ok Awq md2 -> model_rt mdq md2 ->
  INV M2 md2 LKq Awq crq kq a.
Proof.
  intros INVq Hscr HP2 HH2 AM2 MRT2. entry_facts. frame_facts.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  set (LBq := PEC.owned s en kq ++ LBX) in *.
  assert (XINCq : incl LBc0 LBq) by (unfold LBc0, LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINCq : incl (PEC.enc_own en) LBq) by (unfold LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (KINCq : incl (PESK.sink_own kq) LBq) by (unfold LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHq) as BRBq.
  pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq) as FRBq.
  set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  assert (Eov : ov = fb + 496) by reflexivity. assert (Eosk : osk = fb + 432) by reflexivity.
  assert (FRAME12 : forall a0, sp - 80 <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT; lia| intros Y; clear - Ha0 Y; lia].
    - intros r0 []. }
  assert (EK12 : L5SAR.ek L ar LBq FF sp 20480 [] Mq M2).
  { apply (L5SAR.ek_callee L ar LBq [] FF [] sp 20480 (sp - 80) scr [] [] Mq M2 HP2); [clear - Hscr; lia| clear - Hscr; lia| intros a0 _ O; exact O]. }
  assert (DK12 : L5SAR.dk L ar LBq FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar LBq [] FF [] sp 20480 (sp - 80) scr [] Mq M2 HP2); clear - Hscr; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKB.astk_after_ahpres L ar LBq FF Mq M2 sp 20480 (sp - 80) scr [] ASTKq HP2); [clear - Hscr; lia| clear - Hscr; lia| clear - Hscr; lia| exact STOP]. }
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKB.stksh_keepA L ar LBq FF sp 20480 [] Mq M2 EK12 PMKB.wapp_nil (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact SZq].
    apply (PEBEKC.SPd8 sp SP32). reflexivity. }
  unfold PEBEKC.inv. split; [exact (FC_frame Mq M2 FRAME12 FCq)|]. split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|]. split; [exact ILKq|]. split; [exact IAWq|].
  split; [exact HH2|].
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LBq FF sp 20480 [] Mq M2 EK12 PMKB.wapp_nil FRBq BRBq ov fb en (PEBEKC.AOF FF fb FOK ov 56 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact EINCq| | exact EAq].
    - intros i _ r0 [].
    - intros _ i _ r0 []. }
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LBq FF sp 20480 [] Mq M2 EK12 PMKB.wapp_nil FRBq BRBq P osk kq (PEBEKC.AOF FF fb FOK osk 24 ltac:(clear - Eosk; lia) ltac:(clear - Eosk; lia))); [| exact KINCq| | exact SKAq].
    - intros i _ r0 [].
    - intros _ i _ r0 []. }
  split; [exact CLq|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (L5SAR.ek_W L ar LBc0 FF sp 20480 Ws [] Mq M2 (PMKB.ek_sublb L ar LBq LBc0 FF sp 20480 [] Mq M2 XINCq EK12) ltac:(intros a0 O r0 [])))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKB.dk_sublb L ar LBq LBc0 FF sp 20480 Mq M2 XINCq DK12))|].
  exact CKq.
Qed.

Lemma txt_keep Mq : L5SAR.ek L ar LBc0 FF sp 20480 Ws M Mq -> L5.defined Mq dptr n /\ PMSPA.accA Mq dptr n /\ L5.bytes_at RSEGS Mq dptr l.
Proof.
  intros EK. entry_facts. frame_facts.
  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (BRB0 : forall b, In b LBc0 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRB; apply INC0; exact Hb).
  pose proof (PEBEKC.ws_wapp L ar C HI HIok R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK) as WAPP.
  set (osk := PESK.o_sink EE fb) in *. assert (Eosk : osk = fb + 432) by reflexivity.
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply (PEBEKC.AOF FF fb FOK); clear - Eosk; lia).
  destruct LOC as [(B & m & Hin & X1 & X2)|[(X1 & X2)|[(X1 & X2)|(X1 & X2)]]].
  - assert (Hin0 : In (B, m) LBc0) by (unfold LBc0; apply in_or_app; left; exact Hin).
    assert (HinLB : In (B, m) LB) by (apply INC0; exact Hin0).
    assert (OW : forall i, B <= i < B + m -> L5.outside Ws i).
    { intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk.
      destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ B m osk 24 HH HinLB AOSK) as [Y|Y]; clear - Hi Y; lia. }
    destruct (PMKB.agA_blk L ar LBc0 FF sp 20480 Ws M Mq EK WAPP BRB0 B m Hin0 OW) as [AG SH].
    pose proof (BRB0 _ Hin0) as [B0 B47]. cbn [fst snd] in B0, B47.
    split; [apply (L5C.defined_agree M Mq dptr n); [intros i Hi; apply AG; clear - Hi X1 X2; lia| exact DEF]|].
    split; [apply (PMFA.accA_agree M Mq dptr n); [intros x Hx; apply SH; clear - Hx X1 X2; lia| exact ACC]|].
    apply (L5C.bytes_at_agree RSEGS M Mq dptr l); [intros i Hi; apply AG; fold n in Hi; clear - Hi X1 X2; lia| clear - X1 B0; lia| fold n; clear - X2 B47; lia| exact BYT].
  - unfold PMSPA.o_tb, PMSPA.o_p in X1, X2. cbn [pa_off_p PeCLayoutB.CADDR_B] in X1, X2.
    assert (AOT : PMSPA.aobjA FF dptr n) by (apply (PEBEKC.AOF FF fb FOK); clear - X1 X2; pose proof N0; lia).
    assert (OW : forall i, dptr <= i < dptr + n -> L5.outside Ws i) by (intros i Hi r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; fold osk; clear - Hi X1 X2 Eosk; lia).
    destruct (PMKB.agA_obj L ar LBc0 FF sp 20480 Ws M Mq EK WAPP FRB dptr n AOT OW) as [AG SH].
    split; [apply (L5C.defined_agree M Mq dptr n); [exact AG| exact DEF]|].
    split; [apply (PMFA.accA_agree M Mq dptr n); [exact SH| exact ACC]|].
    apply (L5C.bytes_at_agree RSEGS M Mq dptr l); [exact AG| clear - X1 F1 FSAPP; Lia.lia| fold n; clear - X2 F2 FSCEIL SLO SHI SPT; Lia.lia| exact BYT].
  - unfold n. rewrite X1, X2. cbn. split; [intros i Hi; exfalso; clear - Hi; Lia.lia|]. split; [intros x Hx; exfalso; clear - Hx; Lia.lia|]. intros i Hi. cbn in Hi. exfalso. clear - Hi. Lia.lia.
  - pose proof X1 as (f & Hf & Y1 & Y2). pose proof (WF f Hf) as (W1 & W2 & _). unfold FS_BYTES in W1, W2.
    assert (OW : forall i, dptr <= i < dptr + n -> L5.outside Ws i) by (intros i Hi r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; fold osk; clear - Hi X2 Eosk; lia).
    destruct (PMKB.agA_obj L ar LBc0 FF sp 20480 Ws M Mq EK WAPP FRB dptr n X1 OW) as [AG SH].
    split; [apply (L5C.defined_agree M Mq dptr n); [exact AG| exact DEF]|].
    split; [apply (PMFA.accA_agree M Mq dptr n); [exact SH| exact ACC]|].
    apply (L5C.bytes_at_agree RSEGS M Mq dptr l); [exact AG| clear - Y1 W1 FSAPP; Lia.lia| fold n; clear - Y2 W2 FSCEIL SLO SHI SPT; Lia.lia| exact BYT].
Qed.

Lemma SP16' : (sp - 80) mod 16 = 0.
Proof. pose proof (PEBEKC.A16' sp SP32) as A. replace (sp - 80) with (sp + (-5) * 16) by (clear; Lia.lia). rewrite Z_mod_plus_full. exact A. Qed.

Lemma val_call (fxq : FPState) Rq Mq mdq LKq Awq crq :
  INV Mq mdq LKq Awq crq k 0 ->
  getr Rq (reg 1) = Z_to_bv 64 0xad454 -> getr Rq (reg 2) = Z_to_bv 64 (sp - 80) -> getr Rq (reg 10) = Z_to_bv 64 dptr -> getr Rq (reg 11) = Z_to_bv 64 n -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2, INV M2 md2 LKq Awq crq k 0 -> regs_preserved Rq R2 -> getr R2 (reg 11) = Z_to_bv 64 0 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xad454 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xb4350 Mq mdq) K.
Proof.
  intros INVq Q1 Q2 Q10 Q11 QCS KX. entry_facts. frame_facts.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  destruct (txt_keep Mq EKq) as (DEFq & ACCq & BYTq).
  destruct txt_facts as (D0 & D47 & DNZ & DLOC).
  destruct (PEBEKC.keepf L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS Mq EKq)
    as (_ & _ & _ & BASEq & _).
  assert (ASTKv : L5CA.astk ar Mq (sp - 80) 12288).
  { apply (L5SAR.astk_sub ar Mq Mq sp 20480 80 12288 ASTKq); [intros w D; exact D| clear; lia| clear; lia| clear; lia| exact SP16']. }
  pose proof VAL as VX. unfold PECVSA.validate_fun_spec in VX. cbn [pe_validate_enc EE PeCLayoutB.EADDR_B] in VX.
  unfold PMSPA.cfg.
  apply (VX fxq Rq Mq mdq K LB FF LKq Awq crq dptr n (sp - 80) 0xad454 l HHq AMq K0); clear VX.
  { split; [rewrite L5K.rl1; exact Q1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3, (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4, (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split; [exact ASTKv|].
    apply (PMKB.shadow_zero_sub Mq (sp - 20480) 2560); [apply (PEBEKC.SPd8 sp SP32); reflexivity| | clear; lia| clear; lia| clear; lia| exact SZq].
    replace (sp - 80 - 12288) with (sp - 12368) by (clear; lia). apply (PEBEKC.SPd8 sp SP32). reflexivity. }
  { apply (PEBEKC.ffroomA_mono 4 0 FF LK LKq FRM ILKq NDFq). clear; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { split; [exact N0| exact N26]. }
  { exact D0. } { exact DNZ. } { exact D47. } { exact DEFq. } { exact ACCq. }
  { intros a Ha. apply (PMBSR1.vis_scan L ar C HI LY HIok _ FF LKq crq Awq Mq mdq dptr n HHq); [| exact Ha].
    destruct DLOC as [Y|[Y|(q & m & Hin & Y1 & Y2)]]; [left; exact Y| right; left; exact Y| right; right; exists q, m].
    split; [apply in_or_app; left; unfold PEC.owned; apply in_or_app; left; exact Hin| split; [exact Y1| exact Y2]]. }
  { change (PMSPA.pm_scr 0) with 12288.
    destruct LOC as [(B & m & Hin & X1 & X2)|[(X1 & X2)|[(X1 & X2)|(X1 & X2)]]].
    - right. right. assert (HinLB : In (B, m) LB) by (unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hin).
      pose proof (WB _ HinLB) as ((_ & _ & _ & _ & Xc & _) & _). cbn [fst snd] in Xc. clear - X2 Xc SLO. lia.
    - right. right. unfold PMSPA.o_tb, PMSPA.o_p in X2. cbn [pa_off_p PeCLayoutB.CADDR_B] in X2. clear - X2 F2 FSCEIL SLO. lia.
    - left. unfold n. rewrite X2. reflexivity.
    - right. right. pose proof X1 as (f & Hf & Y1 & Y2). pose proof (WF f Hf) as (W1 & W2 & _). unfold FS_BYTES in W2. clear - Y2 W2 FSCEIL SLO. lia. }
  { exact BASEq. }
  { exact BYTq. } { reflexivity. } { exact BOK. }
  intros fx8 R8 M8 md8 v RP8 FBT8 MG8 MRT8 AM8 HH8 V11 Hv HV.
  assert (AH8 : L5CA.ahpres L ar LB FF (sp - 80) 12288 [] Mq M8).
  { apply (PMBUAR.ahpres_of_frame_but L ar C HI LY HIok LB FF LKq crq Awq Mq M8 (vml_of mdq) (sp - 80) 12288 HHq);
      [clear - SPT; lia| clear - SLO; lia| clear; lia| exact FBT8| exact MG8|].
    pose proof ASTKv as (_ & _ & _ & _ & X' & _). exact X'. }
  apply (KX fx8 R8 M8 md8).
  - exact (inv_callee0 Mq mdq LKq Awq crq k 0 M8 md8 12288 INVq ltac:(clear; lia) AH8 HH8 AM8 MRT8).
  - exact RP8.
  - rewrite <- L5K.rl11, V11. f_equal. apply (proj2 HV). exact UV.
Qed.

Lemma pl_call (fxq : FPState) Rq Mq mdq LKq Awq crq :
  INV Mq mdq LKq Awq crq k 0 ->
  getr Rq (reg 1) = Z_to_bv 64 0xad4a8 -> getr Rq (reg 2) = Z_to_bv 64 (sp - 80) -> getr Rq (reg 10) = Z_to_bv 64 (PMSPA.o_v AD fb) -> getr Rq (reg 11) = Z_to_bv 64 n -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, INV M2 md2 LK2 Aw2 cr2 k2 (pl_size n) -> regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xad4a8 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xafe84 Mq mdq) K.
Proof.
  intros INVq Q1 Q2 Q10 Q11 QCS KX. entry_facts. frame_facts.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  pose proof PLS as HPL. pose proof N0 as HN0.
  pose proof (PEBEKC.inv_cpre L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
                HH ENT FOK FC CPRE INCS Mq mdq LKq Awq crq k 0 xlo xhi INVq ltac:(clear; lia) ltac:(clear; lia)) as CPq.
  pose proof PUTL as PX. unfold PECSB.put_length_spec, PECSPA.put_length_spec in PX. cbn [pe_put_length EE PeCLayoutB.EADDR_B] in PX.
  unfold PMSPA.cfg.
  apply (PX PMODE fxq Rq Mq mdq K LBX FF LKq Awq crq (sp - 80) 0xad4a8 fb cat n p X s str sm en k e HHq AMq K0); clear PX.
  { split; [rewrite L5K.rl1; exact Q1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3, (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4, (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 3) with 18432. change (18432 / 8) with 2304. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 80 18432 ASTKq); [intros w D; exact D| clear; lia| clear; lia| clear; lia| exact SP16'].
    - apply (PMKB.shadow_zero_sub Mq (sp - 20480) 2560); [apply (PEBEKC.SPd8 sp SP32); reflexivity| | clear; lia| clear; lia| clear; lia| exact SZq].
      replace (sp - 80 - 18432) with (sp - 18512) by (clear; lia). apply (PEBEKC.SPd8 sp SP32). reflexivity. }
  { apply (PEBEKC.ffroomA_mono 4 3 FF LK LKq FRM ILKq NDFq). clear; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  { exact FOK. }
  { exact SP16'. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { unfold INT64_MAX. clear - HN0 N26; lia. }
  { exact CPq. }
  { exact INCS. }
  { exact POK. }
  { exact MP. }
  { cbn [s_hi X]. apply (PESKA.spao_hb_mono L P PO (xhi + NB)); [exact HBN| unfold NB; clear - HN0; Lia.lia]. }
  { unfold PMSP.credit_le, PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CRED, CKq |- *. cbn [fst snd] in CRED, CKq |- *. clear - CRED CKq. lia. }
  intros fx2 R2 M2 md2 LK2 Aw2 k2 cr2 RP2 CP2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 3) with 18432 in HP2.
  set (LBY := PM.parser_own s ++ PEC.enc_own en ++ LBX) in *.
  set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  assert (Eov : ov = fb + 496) by reflexivity. assert (Eosk : osk = fb + 432) by reflexivity.
  assert (XINCq : incl LBc0 LBY) by (unfold LBc0, LBY; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside Ws a0).
  { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Ha0 Eosk F2 FSCEIL SLO; lia. }
  assert (FRAME12 : forall a0, sp - 80 <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT; lia| intros Y; clear - Ha0 Y; lia].
    - apply OWs. clear - Ha0; lia. }
  assert (EK12 : L5SAR.ek L ar LBY FF sp 20480 Ws Mq M2).
  { apply (L5SAR.ek_callee L ar LBY [] FF [] sp 20480 (sp - 80) 18432 Ws Ws Mq M2 HP2); [clear; lia| clear; lia| intros a0 _ O; exact O]. }
  assert (DK12 : L5SAR.dk L ar LBY FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar LBY [] FF [] sp 20480 (sp - 80) 18432 Ws Mq M2 HP2); clear; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKB.astk_after_ahpres L ar LBY FF Mq M2 sp 20480 (sp - 80) 18432 Ws ASTKq HP2); [clear; lia| clear; lia| clear; lia| exact STOP]. }
  pose proof (PEBEKC.ws_wapp L ar C HI HIok R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK) as WAPP.
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKB.stksh_keepA L ar LBY FF sp 20480 Ws Mq M2 EK12 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply (PEBEKC.SPd8 sp SP32); reflexivity| clear; lia| exact SZq]. }
  pose proof CP2 as (_ & _ & EA2 & _ & SKA2 & _ & _ & _ & _ & CL2 & _).
  unfold PMSPA.o_v, PESK.o_sink in EA2, SKA2. fold ov in EA2. fold osk in SKA2.
  destruct CL2 as (_ & _ & _ & _ & _ & _ & _ & Lz2 & _). cbn [s_lo s_hi w_out X] in Lz2.
  apply (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2); [| exact RP2].
  unfold PEBEKC.inv. split; [exact (FC_frame Mq M2 FRAME12 FCq)|]. split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|].
  split; [intros x Hx; apply ILKq; apply ILK2; exact Hx|]. split; [intros x Hx; apply IAW2; apply IAWq; exact Hx|].
  split; [exact HH2|].
  split; [exact EA2|]. split; [exact SKA2|].
  split; [clear - Lz2; lia|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (PMKB.ek_sublb L ar LBY LBc0 FF sp 20480 Ws Mq M2 XINCq EK12))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKB.dk_sublb L ar LBY LBc0 FF sp 20480 Mq M2 XINCq DK12))|].
  unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq, CK2 |- *. cbn [fst snd] in CKq, CK2 |- *. clear - CKq CK2. lia.
Qed.

Lemma fin (fxq : FPState) Rq Mq mdq LKq Awq crq kq pcq (fx3 : FPState) R3 M3v :
  INV Mq mdq LKq Awq crq kq NB ->
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 r M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) -> regs_preserved R R3 ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INVq MS3 MG3 FRZ3 RP3. entry_facts.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq fxq fx3 Rq pcq R3 r M3v K HHq AMq MS3 MG3 FRZ3).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree Mq M3 AG3) as EM. subst M3.
  apply (KONT fx3 R3 Mq md3 LKq Awq en kq e crq).
  - exact RP3.
  - exact (PEBEKC.inv_cpre L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
             HH ENT FOK FC CPRE INCS Mq mdq LKq Awq crq kq NB _ _ INVq eq_refl eq_refl).
  - intros E1; exact E1.
  - change (PMSPA.pm_scr 4) with 20480. apply (L5SAR.ahpres_of L ar LBc0 FF sp 20480 _ M Mq); [| exact SDEFq| exact DKq].
    apply (L5SAR.ek_W L ar LBc0 FF sp 20480 _ Ws M Mq EKq). exact (PEBEKC.ws_wenc fb).
  - exact CKq.
  - exact (L5LZ.model_rt_trans model mdq md3 MRTq MRT3).
  - exact ILKq.
  - exact IAWq.
  - exact AM3.
  - exact HH3.
Qed.

Lemma dloc_of kq : (n = 0 \/ (ar_fs ar <= dptr /\ dptr + n <= ar_fs ar + FS_BYTES) \/ (exists q m, In (q, m) (PM.parser_own s) /\ q <= dptr /\ dptr + n <= q + m)) ->
  (n = 0 \/ (ar_fs ar <= dptr /\ dptr + n <= ar_fs ar + FS_BYTES) \/ (exists q m, In (q, m) (PEC.owned s en kq ++ LBX) /\ q <= dptr /\ dptr + n <= q + m)).
Proof.
  intros [Y|[Y|(q & m & Hin & Y1 & Y2)]]; [left; exact Y| right; left; exact Y| right; right; exists q, m].
  split; [apply in_or_app; left; unfold PEC.owned; apply in_or_app; left; exact Hin| split; [exact Y1| exact Y2]].
Qed.

Lemma pbk (m : nat) : forall (j : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq,
  Z.of_nat m = n - j -> 0 <= j < n ->
  INV Mq mdq LKq Awq crq kq (pl_size n + j) ->
  inregsL Rq sp (PMSPA.o_v AD fb) -> getr Rq (reg 9) = Z_to_bv 64 (dptr + j) -> getr Rq (reg 19) = Z_to_bv 64 (dptr + j) -> getr Rq (reg 18) = Z_to_bv 64 (n - j) -> csk Rq ->
  getr Rq (reg 10) = Z_to_bv 64 (PESK.o_sink EE fb) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xad50c Mq mdq) K.
Proof.
  induction m as [|m IH]; intros j fxq Rq Mq mdq LKq Awq crq kq Hm Hj INVq IRq G8 G21 G18 QCS G10q; [exfalso; clear - Hm Hj; lia|].
  entry_facts. frame_facts. pose proof PLS as HPL.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  pose proof (PEBEKC.vis_facts L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq mdq LKq Awq crq kq _ INVq)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8v & KR & K8 & KO & U24 & U32 & EB & SVV & _).
  cbv beta in SVV. set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  destruct (txt_keep Mq EKq) as (DEFq & ACCq & _). destruct txt_facts as (D0 & D47 & DNZ & DLOC).
  pose proof IRq as (G2 & G8' & G21' & G20 & G22).
  set (cur := dptr + j) in *.
  assert (CURR : 1 <= cur /\ cur + 1 <= dptr + n) by (subst cur; clear - Hj DNZ D0; lia).
  destruct (PMBSR1.vis_scan L ar C HI LY HIok _ FF LKq crq Awq Mq mdq dptr n HHq (dloc_of kq DLOC) cur ltac:(subst cur; clear - Hj; lia)) as [VIS1 VIS2]. fold H in VIS1, VIS2.

  destruct (u8_at_of_defined Mq cur ltac:(clear - CURR D47 D0; lia) (DEFq (cur - dptr) ltac:(subst cur; clear - Hj; lia))) as (b & Hb & U8b')
    || destruct (u8_at_of_defined Mq cur ltac:(clear - CURR D47 D0; lia) ltac:(replace cur with (dptr + (cur - dptr)) by (clear; lia); apply DEFq; subst cur; clear - Hj; lia)) as (b & Hb & U8b').
  assert (U8b : L5.u8_at RSEGS MV cur b) by (apply (proj2 (L5A.u8_at_vis H Mq cur b ltac:(intros i Hi; replace (cur + i) with cur by (clear - Hi; lia); exact VIS1) ltac:(clear - CURR; lia) ltac:(clear - CURR D47; lia))); exact U8b').
  assert (SHB : exists kk, rdn RSEGS MV (Z_to_bv 64 (cur / 8 + SBL)) 1%nat = Some [Z_to_bv 8 kk] /\ (kk = 0 \/ (1 <= kk <= 7 /\ cur mod 8 < kk))).
  { assert (EMV : MV (Z_to_bv 64 (cur / 8 + SBL)) = Mq (Z_to_bv 64 (cur / 8 + SBL))) by (unfold MV, mrestrict; change (cur / 8 + SBL) with (HeapIfaceA.S cur); rewrite VIS2; reflexivity).
    destruct (ACCq cur ltac:(subst cur; clear - Hj; lia)) as [B0|(v & Bv & Hv & Hm')].
    - exists 0. split; [| left; reflexivity]. cbn [rdn]. rewrite EMV. unfold byte_at, HeapIfaceA.S, HeapIfaceA.SB in B0. rewrite B0. reflexivity.
    - exists v. split; [| right; split; [exact Hv| exact Hm']]. cbn [rdn]. rewrite EMV. unfold byte_at, HeapIfaceA.S, HeapIfaceA.SB in Bv. rewrite Bv. reflexivity. }
  destruct SHB as (kk & RD & Hkk).

  destruct (chk1 fxq Rq MV cur kk G8 G20 ltac:(clear - CURR D47; lia) RD Hkk) as (Rc & MSc & KSc).

  assert (SP0 : 0 <= sp < 2 ^ 64) by (clear - SPR; lia). assert (OVR : 0 <= ov < 2 ^ 64) by (clear - OR; lia). assert (OKR : 0 <= osk < 2 ^ 64) by (clear - KR; lia).
  assert (FS : fstat MV sp) by (split; [exact IC0|]; split; [exact CSBv|]; split; [exact CUARv|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR]).
  assert (FOVq : fov MV sp ov osk) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov|]; split; [exact Z8|]; split; [exact ODJ|]; split; [exact U8v|]; split; [exact KR| exact K8]).
  assert (IRc : inregsL Rc sp ov) by (split; [rewrite (KSc 2%nat) by lia; exact G2|]; split; [rewrite (KSc 8%nat) by lia; exact G8'|]; split; [rewrite (KSc 21%nat) by lia; exact G21'|]; split; [rewrite (KSc 20%nat) by lia; exact G20| rewrite (KSc 22%nat) by lia; exact G22]).
  assert (CUP : cur + 1 <= sp - 80).
  { destruct LOC as [(B & m' & Hin & X1 & X2)|[(X1 & X2)|[(X1 & X2)|(X1 & X2)]]].
    - assert (HinLB : In (B, m') LB) by (unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hin).
      pose proof (WB _ HinLB) as ((_ & _ & _ & _ & Xc & _) & _). cbn [fst snd] in Xc. clear - CURR X2 Xc SLO. lia.
    - unfold PMSPA.o_tb, PMSPA.o_p in X2. cbn [pa_off_p PeCLayoutB.CADDR_B] in X2. clear - CURR X2 F2 FSCEIL SLO. lia.
    - exfalso. unfold n in Hj. rewrite X2 in Hj. cbn in Hj. clear - Hj. lia.
    - pose proof X1 as (f & Hf & Y1 & Y2). pose proof (WF f Hf) as (W1 & W2 & _). unfold FS_BYTES in W2. clear - CURR Y2 W2 FSCEIL SLO. lia. }
  destruct (u_runD fxq Rc MV sp ov osk cur (n - j) b SP0 OVR OKR ltac:(clear - CURR CUP SPR D47; lia) ltac:(clear - Hj N26; lia) ltac:(clear - Hb; lia) IRc
              ltac:(rewrite (KSc 9%nat) by lia; exact G8) ltac:(rewrite (KSc 19%nat) by lia; exact G21) ltac:(rewrite (KSc 18%nat) by lia; exact G18) ltac:(rewrite (KSc 10%nat) by lia; exact G10q)
              FS FOVq ltac:(clear - CURR CUP SPR D47; lia) ltac:(clear - Hj N26; lia) U8b Hb ltac:(left; exact CUP))
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & S8 & S18 & S21 & T1 & T10 & T11 & C65).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq fxq fx3 Rq 0xad50c R3 0xb120c M3v (fun a0 => sp - 65 <= a0 < sp - 65 + 1) K HHq AMq
           ltac:(eapply msteps_trans; [exact MSc| exact MS3]) MG3).
  { intros a0 Ha0 Hn. apply FRZ3; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
    - clear - Wa SLO SPT; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV M3 md3 LKq Awq crq kq (pl_size n + j)).
  { apply (PEBEKC.inv_frame L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq M3 mdq md3 LKq Awq crq kq (pl_size n + j) (sp - 65) (sp - 65 + 1) INVq);
      [clear; lia| clear; lia| exact MGM3| exact FR3| exact (FC_but Mq M3 (sp - 65) (sp - 65 + 1) ltac:(clear; lia) FR3 FCq)| exact HH3| exact AM3| exact MRT3]. }
  assert (IR3 : inregsL R3 sp ov) by exact (inregsL_kept Rc R3 IRc KS3).
  pose proof IR3 as (G2' & _).
  assert (QCS3 : csk R3).
  { apply (csk_keptI Rc R3); [| exact KS3]. intros jj Hjj. rewrite (KSc jj) by (revert Hjj; clear; intros Hjj; cbn in Hjj; decompose [or] Hjj; try contradiction; subst; lia). exact (QCS jj Hjj). }
  apply (PEBEKC.pb_call L ar C HI P LY HIok PO PB 80 CSK HFR CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb xlo xhi s en k HH K0 ENT FRM FRS FOK SP32 FC FC_frame CRED
           (pl_size n + j) (sp - 65) (xhi + NB) 0xad52c fx3 R3 M3 md3 LKq Awq crq kq INV3 HBN ltac:(unfold NB; clear - Hj; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(split; [clear; lia| reflexivity]) T1 G2' T10 T11 QCS3).
  intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 RP4.
  replace (pl_size n + j + 1) with (pl_size n + (j + 1)) in INV4 by (clear; lia).
  pose proof (inregsL_after R3 R4 IR3 RP4) as IR4. pose proof (csk_after R3 R4 QCS3 RP4) as QCS4.
  assert (F8 : getr R4 (reg 9) = Z_to_bv 64 cur) by (rewrite (L5SAR.cs_of_preserved R3 R4 9 RP4) by inl; rewrite S8, (KSc 9%nat) by lia; exact G8).
  assert (F21 : getr R4 (reg 19) = Z_to_bv 64 cur) by (rewrite (L5SAR.cs_of_preserved R3 R4 19 RP4) by inl; rewrite S21, (KSc 19%nat) by lia; exact G21).
  assert (F18 : getr R4 (reg 18) = Z_to_bv 64 (n - j)) by (rewrite (L5SAR.cs_of_preserved R3 R4 18 RP4) by inl; rewrite S18, (KSc 18%nat) by lia; exact G18).
  pose proof INV4 as (FC4 & _ & _ & _ & AM4 & _ & _ & HH4 & _).
  pose proof (PEBEKC.vis_facts L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC M4 md4 LK4 Aw4 cr4 k4 _ INV4)
    as (IC4 & CSB4 & CUAR4 & _ & _ & SWR4 & _ & _ & _ & Zov4 & _ & _ & Z84 & _ & _ & U84 & _ & _ & _ & _ & _ & _ & SVV4 & _). cbv beta in SVV4.
  set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  assert (FS4 : fstat MV4 sp) by (split; [exact IC4|]; split; [exact CSB4|]; split; [exact CUAR4|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR4]).
  assert (FOV4 : fov MV4 sp ov osk) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov4|]; split; [exact Z84|]; split; [exact ODJ|]; split; [exact U84|]; split; [exact KR| exact K8]).
  destruct (Z.eq_dec (j + 1) n) as [LAST|MORE].
  -
    replace (n - j) with 1 in F18 by (clear - LAST; lia).
    assert (R0 : 0 <= r < 2 ^ 64) by (clear - Hr1; lia).
    destruct FC4 as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64).
    assert (FCv : fcells R r MV4 sp) by (unfold fcells; repeat split; (apply SVV4; [clear; lia| clear; lia| assumption])).
    destruct (u_runM0 fx4 R4 R MV4 sp ov cur r SP0 OVR ltac:(clear - CURR CUP SPR D47; lia) R0 IR4 F8 F21 F18 FS4 ltac:(clear - CURR CUP SPR D47; lia) FCv RAok Rsp QCS4)
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & RP5).
    rewrite LAST in INV4. fold NB in INV4.
    exact (fin fx4 R4 M4 md4 LK4 Aw4 cr4 k4 0xad52c fx5 R5 M5v INV4 MS5 MG5 FRZ5 RP5).
  -
    destruct (u_runM1 fx4 R4 MV4 sp ov osk cur (n - j) SP0 OVR OKR ltac:(clear - CURR CUP SPR D47; lia) ltac:(clear - Hj N26; lia) IR4 F8 F21 F18 FS4 FOV4 ltac:(clear - CURR CUP SPR D47; lia) ltac:(clear - Hj MORE N26; lia))
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & KS5 & T8 & T21 & T18 & T10x).
    apply (step_ro (pl_size n + (j + 1)) fx4 R4 M4 md4 LK4 Aw4 cr4 k4 0xad52c 0xad50c fx5 R5 M5v INV4 MS5 MG5 FRZ5).
    intros md5 INV5.
    apply (IH (j + 1) fx5 R5 M4 md5 LK4 Aw4 cr4 k4); [clear - Hm MORE Hj; lia| clear - Hj MORE; lia| exact INV5| exact (inregsL_kept R4 R5 IR4 KS5)| | | | exact (csk_keptI R4 R5 QCS4 KS5)| exact T10x].
    + rewrite T8. f_equal. subst cur. clear; lia.
    + rewrite T21. f_equal. subst cur. clear; lia.
    + rewrite T18. f_equal. clear; lia.
Qed.

Lemma sv_facts Mq mdq LKq Awq crq kq a : INV Mq mdq LKq Awq crq kq a ->
  fsv (mrestrict (ahid Awq mdq) Mq) sp sv dptr n.
Proof.
  intros INVq. entry_facts. frame_facts. pose proof N0 as HN0.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  destruct txt_facts as (D0 & D47 & DNZ & DLOC).
  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (BRB0 : forall b, In b LBc0 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRB; apply INC0; exact Hb).
  pose proof (PEBEKC.ws_wapp L ar C HI HIok R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK) as WAPP.
  assert (OW : forall i, sv <= i < sv + 16 -> L5.outside Ws i).
  { intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold PESK.o_sink. cbn [pe_off_sink PeCLayoutB.EADDR_B]. clear - Hi SVF; lia. }
  destruct (PMKB.agA_obj L ar LBc0 FF sp 20480 Ws M Mq EKq WAPP FRB sv 16 AOSV OW) as [AG SH].
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq sv 16 sp 20480 HHq (PMKB.aobj_of_aobjA FF sv 16 AOSV SV8) ltac:(clear; lia) ltac:(reflexivity))
    as ((S1 & S2 & S3 & S4 & S5) & SBIG & SDEF' & SVIS & SVSH & SCL & SCLSH).
  assert (ACq : PMSPA.accA Mq sv 16) by exact (PMFA.accA_agree M Mq sv 16 SH ACSV).
  pose proof (PMKB.obj_shadow_vis L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq sv 16 HHq AOSV SV8 ltac:(clear; lia) ltac:(reflexivity) ACq) as ZS. change (16 / 8) with 2 in ZS.
  unfold fsv. split; [clear - S1 S3; lia|]. split; [exact SV8|]. split; [clear - SBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia|]. split; [exact ZS|].
  split. { intros jj Hjj. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
           replace ((sv + 8) / 8 + SBL + jj) with (sv / 8 + HeapIfaceA.SB + 1) by (unfold HeapIfaceA.SB; clear - SV8 Hjj; Lia.lia). apply (ZS 1). clear; Lia.lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  split; [left; clear - S2 SLO; lia|].
  split; [apply (proj2 (L5A.u64_at_vis _ Mq sv dptr (L5A.avis_sub _ sv 16 sv 8 SVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - S1; lia) ltac:(clear - S3; lia)));
          apply (L5C.u64_at_agree RSEGS M Mq); [intros i Hi; apply AG; clear - Hi; lia| clear - S1; lia| clear - S3; lia| exact U0]|].
  split; [apply (proj2 (L5A.u64_at_vis _ Mq (sv + 8) n (L5A.avis_sub _ sv 16 (sv + 8) 8 SVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - S1; lia) ltac:(clear - S3; lia)));
          apply (L5C.u64_at_agree RSEGS M Mq); [intros i Hi; apply AG; clear - Hi; lia| clear - S1; lia| clear - S3; lia| exact U8]|].
  split; [clear - D0 D47 HN0; lia| clear - HN0 N26; lia].
Qed.

Lemma main : srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xad3e8 M model) K.
Proof.
  entry_facts. frame_facts. pose proof AM as (Mh & MI). pose proof PLS as HPL. pose proof N0 as HN0.
  destruct txt_facts as (D0 & D47 & DNZ & DLOC).
  pose proof (PEBEKC.vis_entry L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 A10 CPRE)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8v & KR & K8 & KO & G2 & G10 & G1 & RAr & RB).
  cbv beta in RB. set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  assert (SP0 : 0 <= sp < 2 ^ 64) by (clear - SPR; lia). assert (OVR : 0 <= ov < 2 ^ 64) by (clear - OR; lia). assert (OKR : 0 <= osk < 2 ^ 64) by (clear - KR; lia).
  assert (FS : fstat MV sp) by (split; [exact IC0|]; split; [exact CSBv|]; split; [exact CUARv|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR]).
  assert (FOV0 : fov MV sp ov osk) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov|]; split; [exact Z8|]; split; [exact ODJ|]; split; [exact U8v|]; split; [exact KR| exact K8]).

  assert (INV0like : fsv MV sp sv dptr n).
  { pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
    pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model sv 16 sp 20480 HH (PMKB.aobj_of_aobjA FF sv 16 AOSV SV8) ltac:(clear; lia) ltac:(reflexivity))
      as ((S1 & S2 & S3 & S4 & S5) & SBIG & SDEF' & SVIS & SVSH & SCL & SCLSH).
    pose proof (PMKB.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model sv 16 HH AOSV SV8 ltac:(clear; lia) ltac:(reflexivity) ACSV) as ZS. change (16 / 8) with 2 in ZS.
    unfold fsv. split; [clear - S1 S3; lia|]. split; [exact SV8|]. split; [clear - SBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia|]. split; [exact ZS|].
    split. { intros jj Hjj. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
             replace ((sv + 8) / 8 + SBL + jj) with (sv / 8 + HeapIfaceA.SB + 1) by (unfold HeapIfaceA.SB; clear - SV8 Hjj; Lia.lia). apply (ZS 1). clear; Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split; [left; clear - S2 SLO; lia|].
    split; [exact (proj2 (L5A.u64_at_vis _ M sv dptr (L5A.avis_sub _ sv 16 sv 8 SVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - S1; lia) ltac:(clear - S3; lia)) U0)|].
    split; [exact (proj2 (L5A.u64_at_vis _ M (sv + 8) n (L5A.avis_sub _ sv 16 (sv + 8) 8 SVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - S1; lia) ltac:(clear - S3; lia)) U8)|].
    split; [clear - D0 D47 HN0; lia| clear - HN0 N26; lia]. }
  pose proof INV0like as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  assert (SVR : 0 <= sv < 2 ^ 64) by (clear - V1; lia). assert (ECR : 0 <= PMSPA.o_ec AD fb < 2 ^ 64) by (unfold PMSPA.o_ec; cbn [pa_off_ec PeCLayoutB.CADDR_B]; clear - F1 F2 FSAPP FSCEIL SLO SPR; lia).
  assert (DPR : 0 <= dptr < 2 ^ 64) by (clear - V9; lia). assert (NR : 0 <= n < 2 ^ 64) by (clear - V10; lia).

  destruct (u_runA fx R MV sp ov osk sv (PMSPA.o_ec AD fb) dptr n r SP0 OVR OKR SVR ECR DPR NR G2 G10 A11 A13 G1 RAr FS FOV0 INV0like)
    as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & IR1 & T10 & T11 & FC1).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xad3e8 R1 0xb4350 M1v (fun a0 => sp - 80 <= a0 < sp - 80 + 80) K HH AM MS1 MG1).
  { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
    - clear - Wa SLO SPT; lia. }
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (FCM1 : FC M1).
  { destruct FC1 as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64). rewrite <- VIS1 in C8, C16, C24, C32, C40, C48, C56, C64.
    unfold FC, fcells. repeat split; (apply RB; [clear; lia| clear; lia| assumption]). }
  pose proof (PEBEKC.inv_start L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 FC CPRE
                M1 md1 MGM1 FR1 FCM1 HH1 AM1 MRT1) as INV1.
  pose proof IR1 as (Q2 & _).
  assert (QCS1 : csk R1) by (intros jj Hjj; exact (KS1 jj Hjj)).

  apply (val_call fx1 R1 M1 md1 LK Aw cr INV1 T1 Q2 T10 T11 QCS1).
  intros fx2 R2 M2 md2 INV2 RP2 V11.
  assert (IR2 : inregsA R2 sp ov sv (PMSPA.o_ec AD fb)).
  { destruct IR1 as (I2 & I8 & I9 & I18 & I19 & I20 & I21 & I22). pose proof (fun jj Hjj => L5SAR.cs_of_preserved R1 R2 jj RP2 Hjj) as Rc.
    split; [rewrite (Rc 2%nat) by inl; exact I2|]. split; [rewrite (Rc 8%nat) by inl; exact I8|]. split; [rewrite (Rc 9%nat) by inl; exact I9|].
    split; [rewrite (Rc 18%nat) by inl; exact I18|]. split; [rewrite (Rc 19%nat) by inl; exact I19|]. split; [rewrite (Rc 20%nat) by inl; exact I20|].
    split; [rewrite (Rc 21%nat) by inl; exact I21| rewrite (Rc 22%nat) by inl; exact I22]. }
  pose proof (csk_after R1 R2 QCS1 RP2) as QCS2.

  pose proof (PEBEKC.vis_facts L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC M2 md2 LK Aw cr k 0 INV2)
    as (IC2 & CSB2 & CUAR2 & _ & _ & SWR2 & _ & _ & _ & Zov2 & _ & _ & Z82 & _ & _ & U82 & _).
  set (H2 := ahid Aw md2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (FS2 : fstat MV2 sp) by (split; [exact IC2|]; split; [exact CSB2|]; split; [exact CUAR2|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR2]).
  assert (FOV2 : fov MV2 sp ov osk) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov2|]; split; [exact Z82|]; split; [exact ODJ|]; split; [exact U82|]; split; [exact KR| exact K8]).
  pose proof (sv_facts M2 md2 LK Aw cr k 0 INV2) as FSV2. fold H2 MV2 in FSV2.
  destruct (u_runB fx2 R2 MV2 sp ov osk sv (PMSPA.o_ec AD fb) dptr n SP0 OVR OKR SVR ECR DPR NR IR2 V11 FS2 FOV2 FSV2)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & S8 & S18 & S21 & T1' & T10' & T11').
  apply (step_ro 0 fx2 R2 M2 md2 LK Aw cr k 0xad454 0xafe84 fx3 R3 M3v INV2 MS3 MG3 FRZ3).
  intros md3 INV3.
  assert (IR3 : inregsA R3 sp ov sv (PMSPA.o_ec AD fb)).
  { destruct IR2 as (I2 & I8 & I9 & I18 & I19 & I20 & I21 & I22).
    split; [rewrite (KS3 2%nat) by inl; exact I2|]. split; [rewrite (KS3 8%nat) by inl; exact I8|]. split; [rewrite S8; exact I9|].
    split; [rewrite S18; exact I18|]. split; [rewrite S21; exact I19|]. split; [rewrite (KS3 20%nat) by inl; exact I20|].
    split; [rewrite (KS3 21%nat) by inl; exact I21| rewrite (KS3 22%nat) by inl; exact I22]. }
  pose proof (csk_keptI R2 R3 QCS2 KS3) as QCS3. pose proof IR3 as (Q2' & _).

  apply (pl_call fx3 R3 M2 md3 LK Aw cr INV3 T1' Q2' T10' T11' QCS3).
  intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 RP4.
  assert (IR4 : inregsA R4 sp ov sv (PMSPA.o_ec AD fb)).
  { destruct IR3 as (I2 & I8 & I9 & I18 & I19 & I20 & I21 & I22). pose proof (fun jj Hjj => L5SAR.cs_of_preserved R3 R4 jj RP4 Hjj) as Rc.
    split; [rewrite (Rc 2%nat) by inl; exact I2|]. split; [rewrite (Rc 8%nat) by inl; exact I8|]. split; [rewrite (Rc 9%nat) by inl; exact I9|].
    split; [rewrite (Rc 18%nat) by inl; exact I18|]. split; [rewrite (Rc 19%nat) by inl; exact I19|]. split; [rewrite (Rc 20%nat) by inl; exact I20|].
    split; [rewrite (Rc 21%nat) by inl; exact I21| rewrite (Rc 22%nat) by inl; exact I22]. }
  pose proof (csk_after R3 R4 QCS3 RP4) as QCS4.
  pose proof INV4 as (FC4 & _ & _ & _ & AM4 & _ & _ & HH4 & _).
  pose proof (PEBEKC.vis_facts L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC M4 md4 LK4 Aw4 cr4 k4 _ INV4)
    as (IC4 & CSB4 & CUAR4 & _ & _ & SWR4 & _ & _ & _ & Zov4 & _ & _ & Z84 & _ & _ & U84 & _ & _ & _ & _ & _ & _ & SVV4 & _). cbv beta in SVV4.
  set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  assert (FS4 : fstat MV4 sp) by (split; [exact IC4|]; split; [exact CSB4|]; split; [exact CUAR4|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR4]).
  assert (FOV4 : fov MV4 sp ov osk) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov4|]; split; [exact Z84|]; split; [exact ODJ|]; split; [exact U84|]; split; [exact KR| exact K8]).
  pose proof (sv_facts M4 md4 LK4 Aw4 cr4 k4 _ INV4) as FSV4. fold H4 MV4 in FSV4.
  destruct (Z.eq_dec n 0) as [NZ0|NZ1].
  -
    assert (R0 : 0 <= r < 2 ^ 64) by (clear - Hr1; lia).
    destruct FC4 as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64).
    assert (FCv : fcells R r MV4 sp) by (unfold fcells; repeat split; (apply SVV4; [clear; lia| clear; lia| assumption])).
    assert (FSV4' : fsv MV4 sp sv dptr 0) by (rewrite <- NZ0; exact FSV4).
    destruct (u_runC0 fx4 R4 R MV4 sp ov osk sv (PMSPA.o_ec AD fb) dptr r SP0 OVR OKR SVR ECR DPR R0 IR4 FS4 FOV4 FSV4' FCv RAok Rsp QCS4)
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & RP5).
    assert (ENB : pl_size n = NB) by (unfold NB; rewrite NZ0; clear; lia).
    rewrite ENB in INV4.
    exact (fin fx4 R4 M4 md4 LK4 Aw4 cr4 k4 0xad4a8 fx5 R5 M5v INV4 MS5 MG5 FRZ5 RP5).
  -
    assert (D1 : 1 <= dptr <= 140737488355326).
    { split; [clear - DNZ NZ1 HN0; lia|].
      destruct LOC as [(B & m' & Hin & X1 & X2)|[(X1 & X2)|[(X1 & X2)|(X1 & X2)]]].
      - assert (HinLB : In (B, m') LB) by (unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hin).
        pose proof (WB _ HinLB) as ((_ & _ & _ & _ & Xc & _) & _). cbn [fst snd] in Xc. clear - X1 X2 Xc SLO SHI SPT HN0. lia.
      - unfold PMSPA.o_tb, PMSPA.o_p in X2. cbn [pa_off_p PeCLayoutB.CADDR_B] in X2. clear - X2 F2 FSCEIL SLO SHI SPT HN0. lia.
      - exfalso. apply NZ1. unfold n. rewrite X2. reflexivity.
      - pose proof X1 as (f & Hf & Y1 & Y2). pose proof (WF f Hf) as (W1 & W2 & _). unfold FS_BYTES in W1, W2. clear - Y1 Y2 W1 W2 FSCEIL FSAPP SLO SHI SPT HN0; lia. }
    destruct (u_runC1 fx4 R4 MV4 sp ov osk sv (PMSPA.o_ec AD fb) dptr n SP0 OVR OKR SVR ECR DPR NR IR4 FS4 FOV4 FSV4 ltac:(clear - NZ1 HN0; lia) D1)
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & KS5 & IRL5 & T8 & T21 & T18 & T10y).
    apply (step_ro (pl_size n) fx4 R4 M4 md4 LK4 Aw4 cr4 k4 0xad4a8 0xad50c fx5 R5 M5v INV4 MS5 MG5 FRZ5).
    intros md5 INV5.
    apply (pbk (Z.to_nat n) 0 fx5 R5 M4 md5 LK4 Aw4 cr4 k4); [rewrite Z2Nat.id by (clear - HN0; lia); clear; lia| clear - NZ1 HN0; lia| replace (pl_size n + 0) with (pl_size n) by (clear; lia); exact INV5| exact IRL5| | | | exact (csk_kept R4 R5 QCS4 KS5)| exact T10y].
    + rewrite T8. f_equal. clear; lia.
    + rewrite T21. f_equal. clear; lia.
    + rewrite T18. f_equal. clear; lia.
Qed.
End Call.

Theorem v_key_ok : PECSB.v_key_spec L ar HI P.
Proof.
  unfold PECSB.v_key_spec, PECSPA.v_key_spec, PECSPA.eslot_spec. cbn [pe_key EE PeCLayoutB.EADDR_B].
  intros PMODE d fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 AK CPRE INCS POK MP NB HB CRED KONT.
  destruct AK as ((sv & A11 & SV8 & AOSV & ACSV & SVF & U0 & U8 & BYT & BOK & N26 & DEF & ACC & LOC) & A13 & UV).
  rewrite L5K.rl11 in A11. rewrite L5K.rl13 in A13.
  destruct d as [dptr l]. cbn [fst snd] in *.
  destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad].
  assert (N26' : Z.of_nat (length l) < 2 ^ 26) by exact N26.
  assert (EKEY : e_key (Z.of_nat (length l)) (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad)
          = ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + (pl_size (Z.of_nat (length l)) + Z.of_nat (length l))) (xhi + (pl_size (Z.of_nat (length l)) + Z.of_nat (length l))) xbad).
  { unfold e_key, e_put_length. replace (INT64_MAX <? Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; unfold INT64_MAX; clear - N26'; lia).
    unfold w_out. cbn. f_equal; clear; lia. }
  rewrite EKEY in HB, KONT. cbn [s_hi] in HB.
  exact (main PMODE dptr sv l fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
           HH AM K0 ENT FRM FRS FOK SP32 A10 A11 A13 SV8 SVF AOSV ACSV U0 U8 BYT BOK N26 DEF ACC LOC UV CPRE INCS POK MP HB CRED KONT).
Qed.
End WithHeap.
End PEBENCK.
