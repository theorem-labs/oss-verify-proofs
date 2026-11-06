(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PmModelFactsA PmStep PeStepA PmParKit PeASrcKit PeAParKit LibIfaceAB PmAUar PeASrcRead1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrame PeCFrameA PeCValSpecA PeEncKit PeACReset1 PeAEncNtbSpec PeAEncKitC PeAEncKey PeAEncStrP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_ac560_ac564 Ea0_code_ac48c_ac49c Ea0_code_ac4cc_ac4d4.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAENCST.
#[local] Transparent e_end_value.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).
Abbreviation SBL := 2147450880.

Definition CSK : list nat := [3; 4; 25; 26; 27]%nat.

Definition CSI : list nat := [2; 8; 9; 21; 22; 3; 4; 25; 26; 27]%nat.

Lemma chk1s fx R M cur k :
  getr R (reg 18) = Z_to_bv 64 cur -> getr R (reg 21) = Z_to_bv 64 SBL -> 0 <= cur < 2 ^ 47 ->
  rdn RSEGS M (Z_to_bv 64 (cur / 8 + SBL)) 1%nat = Some [Z_to_bv 8 k] ->
  (k = 0 \/ (1 <= k <= 7 /\ cur mod 8 < k)) ->
  exists R', msteps RSEGS (mst fx R 0xac4dc M) (mst fx R' 0xac4ec M)
    /\ (forall j, j <> 10%nat -> j <> 11%nat -> (j < 32)%nat -> getr R' (reg j) = getr R (reg j)).
Proof.
  intros A8 A20 Hc RD Hk.
  assert (N10 : (reg 10) <> 0%bv) by (intros X; discriminate X). assert (N11 : (reg 11) <> 0%bv) by (intros X; discriminate X).
  set (R1 := regupd R (reg 10) (v_srli (getr R (reg 18)) (bv_unsigned (3%bv : bv 6)))).
  set (R2 := regupd R1 (reg 10) (v_add (getr R1 (reg 10)) (getr R1 (reg 21)))).
  set (R3 := regupd R2 (reg 10) (v_lb (Z_to_bv 8 k))).
  assert (E1 : getr R1 (reg 10) = Z_to_bv 64 (cur / 8)).
  { unfold R1. rewrite (getr_same _ _ _ N10), A8. change (bv_unsigned (3%bv : bv 6)) with 3. unfold v_srli. rewrite Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by Lia.lia. rewrite Z.shiftr_div_pow2 by Lia.lia. reflexivity. }
  assert (E1o : forall j, j <> 10%nat -> (j < 32)%nat -> getr R1 (reg j) = getr R (reg j)) by (intros j Hj Hl; unfold R1; apply getr_other; apply PEAENCK.reg_index_neq; Lia.lia).
  assert (E2 : getr R2 (reg 10) = Z_to_bv 64 (cur / 8 + SBL)).
  { unfold R2. rewrite (getr_same _ _ _ N10), E1, (E1o 21%nat) by Lia.lia. rewrite A20. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite !Z.mod_small by Lia.lia. reflexivity. }
  assert (E2o : forall j, j <> 10%nat -> (j < 32)%nat -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj Hl; unfold R2; apply getr_other; apply PEAENCK.reg_index_neq; Lia.lia).
  assert (E3 : getr R3 (reg 10) = Z_to_bv 64 k).
  { unfold R3. rewrite (getr_same _ _ _ N10). unfold v_lb. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap. change (bv_modulus 8) with 256. change (bv_half_modulus 8) with 128.
    rewrite (Z.mod_small k) by Lia.lia. rewrite (Z.mod_small (k + 128)) by Lia.lia. rewrite !Z.mod_small by Lia.lia. Lia.lia. }
  assert (E3o : forall j, j <> 10%nat -> (j < 32)%nat -> getr R3 (reg j) = getr R2 (reg j)) by (intros j Hj Hl; unfold R3; apply getr_other; apply PEAENCK.reg_index_neq; Lia.lia).
  assert (MS3 : msteps RSEGS (mst fx R 0xac4dc M) (mst fx R3 0xac4e8 M)).
  { eapply msteps_trans.
    { eapply (PEAENCK.gstep fx R R1 M 0xac4dc 0xac4e0 _ W_ac48c F_ac48c); [rewrite (step_srli RSEGS R (Z_to_bv 64 0xac4dc) M (seg_rom RSEGS) W_ac48c _ _ _ F_ac48c eq_refl D_ac48c); reflexivity| apply PEAENCK.addi_lit; Lia.lia]. }
    eapply msteps_trans.
    { eapply (PEAENCK.gstep fx R1 R2 M 0xac4e0 0xac4e4 _ W_ac490 F_ac490); [rewrite (step_add RSEGS R1 (Z_to_bv 64 0xac4e0) M (seg_rom RSEGS) W_ac490 _ _ _ F_ac490 eq_refl D_ac490); reflexivity| apply PEAENCK.addi_lit; Lia.lia]. }
    eapply (PEAENCK.gstep fx R2 R3 M 0xac4e4 0xac4e8 _ W_ac494 F_ac494).
    { rewrite (step_lb RSEGS R2 (Z_to_bv 64 0xac4e4) M (seg_rom RSEGS) W_ac494 _ _ _ (Z_to_bv 8 k) F_ac494 eq_refl D_ac494); [reflexivity|].
      rewrite L5K.rl10, E2. change (bv_signed (0%bv : bv 12)) with 0. rewrite PEAENCK.addi_lit by Lia.lia. rewrite Z.add_0_r. exact RD. }
    apply PEAENCK.addi_lit; Lia.lia. }
  destruct Hk as [K0|(K17 & KM)].
  - exists R3. split.
    + eapply msteps_trans; [exact MS3|]. eapply (PEAENCK.gstep fx R3 R3 M 0xac4e8 0xac4ec _ W_ac498 F_ac498).
      { rewrite (step_bne_ft RSEGS R3 (Z_to_bv 64 0xac4e8) M (seg_rom RSEGS) W_ac498 _ _ _ F_ac498 eq_refl D_ac498); [reflexivity|].
        rewrite L5K.rl10, E3, K0. unfold getr. cbn [bv_eqb Z.eqb]. apply c_eq_refl. }
      apply PEAENCK.addi_lit; Lia.lia.
    + intros j H10 H11 Hl. rewrite (E3o j), (E2o j), (E1o j) by Lia.lia. reflexivity.
  - set (R4 := regupd R3 (reg 11) (v_andi (getr R3 (reg 18)) (bv_signed (7%bv : bv 12)))).
    assert (E4 : getr R4 (reg 11) = Z_to_bv 64 (cur mod 8)).
    { unfold R4. rewrite (getr_same _ _ _ N11), (E3o 18%nat), (E2o 18%nat), (E1o 18%nat) by Lia.lia. rewrite A8. change (bv_signed (7%bv : bv 12)) with 7.
      unfold v_andi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite (Z.mod_small cur) by Lia.lia. rewrite (Z.mod_small 7) by Lia.lia. rewrite PEAENCK.land7 by Lia.lia. rewrite !Z.mod_small by Lia.lia. reflexivity. }
    assert (E4o : forall j, j <> 11%nat -> (j < 32)%nat -> getr R4 (reg j) = getr R3 (reg j)) by (intros j Hj Hl; unfold R4; apply getr_other; apply PEAENCK.reg_index_neq; Lia.lia).
    exists R4. split.
    + eapply msteps_trans; [exact MS3|]. eapply msteps_trans.
      { eapply (PEAENCK.gstep fx R3 R3 M 0xac4e8 0xac51c _ W_ac498 F_ac498).
        - rewrite (step_bne_tk RSEGS R3 (Z_to_bv 64 0xac4e8) M (seg_rom RSEGS) W_ac498 _ _ _ F_ac498 eq_refl D_ac498); [reflexivity|].
          rewrite L5K.rl10, E3. replace (getr R3 (0%bv : bv 5)) with (Z_to_bv 64 0) by reflexivity. apply c_eq_neq. rewrite !L5.unsigned_lit by (clear - K17; Lia.lia). clear - K17. Lia.lia.
        - unfold btgt. vm_compute. reflexivity. }
      eapply msteps_trans.
      { eapply (PEAENCK.gstep fx R3 R4 M 0xac51c 0xac520 _ W_ac4cc F_ac4cc); [rewrite (step_andi RSEGS R3 (Z_to_bv 64 0xac51c) M (seg_rom RSEGS) W_ac4cc _ _ _ F_ac4cc eq_refl D_ac4cc); reflexivity| apply PEAENCK.addi_lit; Lia.lia]. }
      eapply (PEAENCK.gstep fx R4 R4 M 0xac520 0xac4ec _ W_ac4d0 F_ac4d0).
      * rewrite (step_blt_tk RSEGS R4 (Z_to_bv 64 0xac520) M (seg_rom RSEGS) W_ac4d0 _ _ _ F_ac4d0 eq_refl D_ac4d0); [reflexivity|].
        rewrite L5K.rl11, L5K.rl10, E4, (E4o 10%nat) by Lia.lia. rewrite E3. unfold c_lts, bv_lts. unfold bv_signed. rewrite !Z_to_bv_unsigned.
        unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
        rewrite (Z.mod_small (cur mod 8)) by Lia.lia. rewrite (Z.mod_small k) by Lia.lia. rewrite !Z.mod_small by Lia.lia. apply Z.ltb_lt. Lia.lia.
      * unfold btgt. vm_compute. reflexivity.
    + intros j H10 H11 Hl. rewrite (E4o j), (E3o j), (E2o j), (E1o j) by Lia.lia. reflexivity.
Qed.

Definition inregsM (R : bvmap 5 word) (sp ov sv ec sh8 : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R (reg 8) = Z_to_bv 64 ov /\ getr R (reg 9) = Z_to_bv 64 (ov + 8) /\ getr R (reg 18) = Z_to_bv 64 sv /\ getr R (reg 19) = Z_to_bv 64 ec
  /\ getr R (reg 21) = Z_to_bv 64 SBL /\ getr R (reg 22) = Z_to_bv 64 sh8.

Definition inregsV (R : bvmap 5 word) (sp ov sv ec sh8 : Z) : Prop :=
  inregsM R sp ov sv ec sh8 /\ getr R (reg 20) = Z_to_bv 64 (sv + 8) /\ getr R (reg 23) = Z_to_bv 64 (sv / 8 + SBL) /\ getr R (reg 24) = Z_to_bv 64 ((sv + 8) / 8 + SBL).

Definition inregsL (R : bvmap 5 word) (sp ov sh8 : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R (reg 8) = Z_to_bv 64 ov /\ getr R (reg 9) = Z_to_bv 64 (ov + 8) /\ getr R (reg 21) = Z_to_bv 64 SBL /\ getr R (reg 22) = Z_to_bv 64 sh8.

Definition inregsE (R : bvmap 5 word) (sp ov : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R (reg 8) = Z_to_bv 64 ov /\ getr R (reg 21) = Z_to_bv 64 SBL.
Definition fstat (M : word -> option byte) (sp : Z) : Prop :=
  L5.img_clear M 1253376 1286144 /\ L5.u64_at RSEGS M 1317368 SBL /\ L5.u32_at RSEGS M 1317376 1 /\ 140735332487264 <= sp <= 140737488355328 /\ sp mod 16 = 0
  /\ L5.writable RSEGS M (sp - 96) 96.
Definition fov (M : word -> option byte) (sp ov osk : Z) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ ((sp - 96) + 96 <= ov \/ ov + 56 <= (sp - 96))
  /\ L5.u64_at RSEGS M (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0.
Definition fsv (M : word -> option byte) (sp sv dptr n : Z) : Prop :=
  4096 <= sv <= 140737488355312 /\ sv mod 8 = 0 /\ (2147446784 + 17592186048512 <= sv \/ sv + 16 <= 2147446784)
  /\ L5KA.zeros_at M (sv / 8 + SBL) 2 /\ L5KA.zeros_at M ((sv + 8) / 8 + SBL) 1 /\ (sv + 16 <= (sp - 96) \/ (sp - 96) + 96 <= sv)
  /\ L5.u64_at RSEGS M sv dptr /\ L5.u64_at RSEGS M (sv + 8) n /\ 0 <= dptr <= 140737488355328 /\ 0 <= n <= 67108864.
Definition fcells (R0 : bvmap 5 word) (r : Z) (M : word -> option byte) (sp : Z) : Prop :=
  L5.u64_at RSEGS M (sp - 8) r /\ L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8))) /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9)))
  /\ L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18))) /\ L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (sp - 64) (bv_unsigned (getr R0 (reg 22)))
  /\ L5.u64_at RSEGS M (sp - 72) (bv_unsigned (getr R0 (reg 23))) /\ L5.u64_at RSEGS M (sp - 80) (bv_unsigned (getr R0 (reg 24))).

Definition rest (R0 R' : bvmap 5 word) (r sp : Z) : Prop :=
  getr R' (reg 1) = Z_to_bv 64 r /\ getr R' (reg 2) = Z_to_bv 64 sp
  /\ getr R' (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) /\ getr R' (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9)))
  /\ getr R' (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) /\ getr R' (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) /\ getr R' (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20)))
  /\ getr R' (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) /\ getr R' (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22)))
  /\ getr R' (reg 23) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 23))) /\ getr R' (reg 24) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 24))).

Definition runA (lo hi byo mk : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk sv tg ec r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= sv < 2 ^ 64 -> 0 <= tg < 2 ^ 64 -> 0 <= ec < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 ov -> getr R (reg 11) = Z_to_bv 64 sv -> getr R (reg 12) = Z_to_bv 64 tg -> getr R (reg 14) = Z_to_bv 64 ec ->
    getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
    fstat M sp -> fov M sp ov osk -> lo <= tg <= hi -> 4096 <= sv <= 140737488355312 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp - 96 + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac3d8 M) (mst fx' R' 0xaf02c M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 0xac460 /\ inregsM R' sp ov sv ec ((ov + 8) / 8 + SBL) /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp + byo)
      /\ L5.u8_at RSEGS M' (sp + byo) mk /\ fcells R r M' sp.

Definition runB : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk sv ec sh8 dptr n : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= sv < 2 ^ 64 -> 0 <= ec < 2 ^ 64 -> 0 <= sh8 < 2 ^ 64 -> 0 <= dptr < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    inregsM R sp ov sv ec sh8 -> fstat M sp -> fov M sp ov osk -> fsv M sp sv dptr n ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac460 M) (mst fx' R' 0xb1068 M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)) /\ inregsV R' sp ov sv ec sh8
      /\ getr R' (reg 1) = Z_to_bv 64 0xac490 /\ getr R' (reg 10) = Z_to_bv 64 dptr /\ getr R' (reg 11) = Z_to_bv 64 n.

Definition runCe : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov sv ec sh8 v : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= sv < 2 ^ 64 -> 0 <= ec < 2 ^ 64 -> 0 <= sh8 < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
    inregsV R sp ov sv ec sh8 -> getr R (reg 11) = Z_to_bv 64 v -> fstat M sp -> 1 <= v <= 6 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac490 M) (mst fx' R' 0xae310 M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)) /\ inregsV R' sp ov sv ec sh8
      /\ getr R' (reg 1) = Z_to_bv 64 0xac4a4 /\ getr R' (reg 10) = Z_to_bv 64 ec /\ getr R' (reg 11) = Z_to_bv 64 7.

Definition runR : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    inregsE R sp ov -> fstat M sp -> fcells R0 r M sp -> L5.ra_ok r -> getr R0 (reg 2) = Z_to_bv 64 sp -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac4a4 M) (mst fx' R' r M')
      /\ regs_preserved R0 R'.

Definition runCo : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk sv ec sh8 dptr n : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= sv < 2 ^ 64 -> 0 <= ec < 2 ^ 64 -> 0 <= sh8 < 2 ^ 64 -> 0 <= dptr < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    inregsV R sp ov sv ec sh8 -> getr R (reg 11) = Z_to_bv 64 0 -> fstat M sp -> fov M sp ov osk -> fsv M sp sv dptr n ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac490 M) (mst fx' R' 0xae710 M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)) /\ inregsV R' sp ov sv ec sh8
      /\ getr R' (reg 1) = Z_to_bv 64 0xac4bc /\ getr R' (reg 10) = Z_to_bv 64 ov /\ getr R' (reg 11) = Z_to_bv 64 n.

Definition runD0 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk sv ec sh8 dptr : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= sv < 2 ^ 64 -> 0 <= ec < 2 ^ 64 -> 0 <= sh8 < 2 ^ 64 -> 0 <= dptr < 2 ^ 64 ->
    inregsV R sp ov sv ec sh8 -> fstat M sp -> fov M sp ov osk -> fsv M sp sv dptr 0 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac4bc M) (mst fx' R' 0xac52c M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)) /\ inregsE R' sp ov.

Definition runD1 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk sv ec sh8 dptr n : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= sv < 2 ^ 64 -> 0 <= ec < 2 ^ 64 -> 0 <= sh8 < 2 ^ 64 -> 0 <= dptr < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    inregsV R sp ov sv ec sh8 -> fstat M sp -> fov M sp ov osk -> fsv M sp sv dptr n -> 1 <= n -> 1 <= dptr <= 140737488355326 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac4bc M) (mst fx' R' 0xac4dc M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)) /\ inregsL R' sp ov sh8
      /\ getr R' (reg 18) = Z_to_bv 64 dptr /\ getr R' (reg 20) = Z_to_bv 64 dptr /\ getr R' (reg 19) = Z_to_bv 64 n.

Definition runE : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk sh8 cur cnt b : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= sh8 < 2 ^ 64 -> 0 <= cur < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
    inregsL R sp ov sh8 -> getr R (reg 18) = Z_to_bv 64 cur -> getr R (reg 20) = Z_to_bv 64 cur -> getr R (reg 19) = Z_to_bv 64 cnt ->
    fstat M sp -> fov M sp ov osk -> L5KA.zeros_at M sh8 1 -> 2147451393 <= sh8 <= 19791209299968 ->
    1 <= cur <= 140737488355326 -> 1 <= cnt <= 67108864 -> L5.u8_at RSEGS M cur b -> 0 <= b <= 255 ->
    (cur + 1 <= sp - 96 \/ (sp - 96) + 96 <= cur) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 81 <= i < sp - 81 + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac4ec M) (mst fx' R' 0xaf02c M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)) /\ getr R' (reg 18) = getr R (reg 18) /\ getr R' (reg 19) = getr R (reg 19) /\ getr R' (reg 20) = getr R (reg 20)
      /\ getr R' (reg 1) = Z_to_bv 64 0xac508 /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp - 81)
      /\ L5.u8_at RSEGS M' (sp - 81) b.

Definition runM0 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov sh8 cur : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= sh8 < 2 ^ 64 -> 0 <= cur < 2 ^ 64 ->
    inregsL R sp ov sh8 -> getr R (reg 18) = Z_to_bv 64 cur -> getr R (reg 20) = Z_to_bv 64 cur -> getr R (reg 19) = Z_to_bv 64 1 ->
    fstat M sp -> 1 <= cur <= 140737488355326 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac508 M) (mst fx' R' 0xac52c M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)) /\ inregsE R' sp ov.

Definition runM1 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov sh8 cur cnt : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= sh8 < 2 ^ 64 -> 0 <= cur < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 ->
    inregsL R sp ov sh8 -> getr R (reg 18) = Z_to_bv 64 cur -> getr R (reg 20) = Z_to_bv 64 cur -> getr R (reg 19) = Z_to_bv 64 cnt ->
    fstat M sp -> 1 <= cur <= 140737488355326 -> 2 <= cnt <= 67108864 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac508 M) (mst fx' R' 0xac4dc M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)) /\ inregsL R' sp ov sh8
      /\ getr R' (reg 18) = Z_to_bv 64 (cur + 1) /\ getr R' (reg 20) = Z_to_bv 64 (cur + 1) /\ getr R' (reg 19) = Z_to_bv 64 (cnt - 1).

Definition runE0 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov osk eb r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    inregsE R sp ov -> fstat M sp -> fov M sp ov osk -> L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1 ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) eb -> 0 <= eb <= 140737488355328 -> fcells R0 r M sp -> L5.ra_ok r ->
    getr R0 (reg 2) = Z_to_bv 64 sp -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac52c M) (mst fx' R' r M')
      /\ regs_preserved R0 R'.

Definition runE1 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov osk eb ed cn r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 -> 0 <= cn < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    inregsE R sp ov -> fstat M sp -> fov M sp ov osk -> L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1 ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) ed -> 4096 <= eb <= 140737488355328 -> 4120 <= ed <= 140737488355328 -> ed mod 8 = 0 ->
    24 <= ed - eb <= 100000 -> L5.writable RSEGS M (ed - 24) 24 -> (2147446784 + 17592186048512 <= ed - 24 \/ (ed - 24) + 24 <= 2147446784) ->
    L5KA.zeros_at M ((ed - 8) / 8 + SBL) 1 ->
    ((ed - 24) + 24 <= (sp - 96) \/ (sp - 96) + 96 <= (ed - 24)) -> ((ed - 24) + 24 <= ov \/ ov + 56 <= (ed - 24)) -> L5.u64_at RSEGS M (ed - 8) cn ->
    fcells R0 r M sp -> L5.ra_ok r -> getr R0 (reg 2) = Z_to_bv 64 sp -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (ed - 8 <= i < ed - 8 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac52c M) (mst fx' R' r M')
      /\ regs_preserved R0 R'
      /\ L5.u64_at RSEGS M' (ed - 8) ((cn + 1) mod 2 ^ 64).

Local Ltac kept_tac KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Local Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEAENCSTP.aligned; assumption | lia]).
Local Ltac wid G := let H := fresh in pose proof (bv_unsigned_in_range 64 G) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Local Ltac junk R i := let G := fresh "J" in assert (G : getr R (reg i) = Z_to_bv 64 (bv_unsigned (getr R (reg i)))) by (symmetry; apply PMPK.word_id); wid (getr R (reg i)).
Local Ltac junks R := junk R 10%nat; junk R 11%nat; junk R 12%nat; junk R 13%nat; junk R 14%nat.
Local Ltac wids R0 := wid (getr R0 (reg 8)); wid (getr R0 (reg 9)); wid (getr R0 (reg 18)); wid (getr R0 (reg 19)); wid (getr R0 (reg 20)); wid (getr R0 (reg 21)); wid (getr R0 (reg 22)); wid (getr R0 (reg 23)); wid (getr R0 (reg 24)).

Lemma preserved_of_rest (R R0 R3 : bvmap 5 word) (r sp : Z) (KS : list nat) :
  (forall j, In j CSK -> In j KS) -> (forall x, In x KS -> getr R3 (reg x) = getr R (reg x)) -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
  getr R0 (reg 2) = Z_to_bv 64 sp -> rest R0 R3 r sp -> regs_preserved R0 R3.
Proof.
  intros SUB KS3 QCS Rsp (T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24). apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
  repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8; apply PMPK.word_id | rewrite T9; apply PMPK.word_id | rewrite T18; apply PMPK.word_id
                                          | rewrite T19; apply PMPK.word_id | rewrite T20; apply PMPK.word_id | rewrite T21; apply PMPK.word_id | rewrite T22; apply PMPK.word_id
                                          | rewrite T23; apply PMPK.word_id | rewrite T24; apply PMPK.word_id
                                          | rewrite (KS3 _) by (apply SUB; inl); apply QCS; inl ] |]). destruct Hj.
Qed.

Section RunA.
Local Ltac runA_tac CONC :=
  unfold runA; intros fx R M sp ov osk sv tg ec r H1 H2 H3 H4 H5 H6 G2 G10 G11 G12 G14 G1 RA (K0 & K1 & K2 & K3 & K4 & K5) FOV TGR SVR;
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9);
  let HO := fresh "HO" in let HS := fresh "HS" in let HT := fresh "HT" in let HE := fresh "HE" in let Hr := fresh "Hr" in
  assert (HO : bv_unsigned (getr R (reg 10)) = ov) by (rewrite G10; apply L5.unsigned_lit; exact H2);
  assert (HS : bv_unsigned (getr R (reg 11)) = sv) by (rewrite G11; apply L5.unsigned_lit; exact H4);
  assert (HT : bv_unsigned (getr R (reg 12)) = tg) by (rewrite G12; apply L5.unsigned_lit; exact H5);
  assert (HE : bv_unsigned (getr R (reg 14)) = ec) by (rewrite G14; apply L5.unsigned_lit; exact H6);
  assert (Hr : bv_unsigned (getr R (reg 1)) = r) by (rewrite G1; apply L5.unsigned_lit; destruct RA as [Hr1 Hr2]; clear - Hr1; lia);
  wids R;
  let P := fresh "P" in
  pose proof (CONC fx R M (fun j => match j with 2%nat => sp | 41%nat => osk | _ => 0 end)) as P; cbn beta iota in P; rewrite !HO, !HS, !HT in P;
  feedP P; rewrite Hr in P;
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & _ & _ & T18 & T19 & T21 & T22 & B1 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8);
  exists fx1, R1, M1; split; [exact MG1|]; split; [exact FRZ1|]; split; [exact MS1|]; split; [kept_tac KS1|];
  split; [exact T1|]; split; [split; [exact T2|]; split; [rewrite T8; exact G10|]; split; [exact T9|]; split; [rewrite T18; exact G11|]; split; [rewrite T19; exact G14|]; split; [exact T21| exact T22]|];
  split; [exact T10|]; split; [exact T11|]; split; [exact B1|];
  split; [exact S8|]; split; [exact S16|]; split; [exact S24|]; split; [exact S32|]; split; [exact S40|]; split; [exact S48|]; split; [exact S56|]; split; [exact S64|]; split; [exact S72| exact S80].
Lemma u_runAh : runA 2 3 (-83) 72. Proof. runA_tac PEAENCSTP.aqSAh_conc. Qed.
Lemma u_runAs0 : runA 0 1 (-82) 83. Proof. runA_tac PEAENCSTP.aqSAs0_conc. Qed.
Lemma u_runAs4 : runA 4 31 (-82) 83. Proof. runA_tac PEAENCSTP.aqSAs4_conc. Qed.
End RunA.

Lemma u_runB : runB.
Proof.
  unfold runB. intros fx R M sp ov osk sv ec sh8 dptr n H1 H2 H3 H4 H5 H6 H7 H8 (G2 & G8 & G9 & G18 & G19 & G21 & G22) (K0 & K1 & K2 & K3 & K4 & K5) FOV FSV.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9). destruct FSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  junks R.
  pose proof (PEAENCSTP.aqSB_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => sv | 14%nat => ec | 33%nat => dptr | 34%nat => n | 38%nat => sh8 | 41%nat => osk
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T10 & T11 & T20 & T23 & T24).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split. { split; [| split; [exact T20| split; [exact T23| exact T24]]].
           split; [rewrite (KS1 2%nat) by inl; exact G2|]. split; [rewrite (KS1 8%nat) by inl; exact G8|]. split; [rewrite (KS1 9%nat) by inl; exact G9|].
           split; [rewrite (KS1 18%nat) by inl; exact G18|]. split; [rewrite (KS1 19%nat) by inl; exact G19|]. split; [rewrite (KS1 21%nat) by inl; exact G21| rewrite (KS1 22%nat) by inl; exact G22]. }
  split; [exact T1|]. split; [exact T10| exact T11].
Qed.

Lemma inregsV_kept R1 R2 sp ov sv ec sh8 (KS : list nat) :
  inregsV R1 sp ov sv ec sh8 -> (forall x, In x KS -> getr R2 (reg x) = getr R1 (reg x)) ->
  (forall j, In j [2; 8; 9; 18; 19; 20; 21; 22; 23; 24]%nat -> In j KS) -> inregsV R2 sp ov sv ec sh8.
Proof.
  intros ((G2 & G8 & G9 & G18 & G19 & G21 & G22) & G20 & G23 & G24) KSF SUB.
  assert (E : forall j, In j [2; 8; 9; 18; 19; 20; 21; 22; 23; 24]%nat -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; apply KSF; apply SUB; exact Hj).
  split; [split; [rewrite (E 2%nat) by inl; exact G2|]; split; [rewrite (E 8%nat) by inl; exact G8|]; split; [rewrite (E 9%nat) by inl; exact G9|];
          split; [rewrite (E 18%nat) by inl; exact G18|]; split; [rewrite (E 19%nat) by inl; exact G19|]; split; [rewrite (E 21%nat) by inl; exact G21| rewrite (E 22%nat) by inl; exact G22]|].
  split; [rewrite (E 20%nat) by inl; exact G20|]. split; [rewrite (E 23%nat) by inl; exact G23| rewrite (E 24%nat) by inl; exact G24].
Qed.
Lemma inregsL_kept R1 R2 sp ov sh8 (KS : list nat) :
  inregsL R1 sp ov sh8 -> (forall x, In x KS -> getr R2 (reg x) = getr R1 (reg x)) -> (forall j, In j [2; 8; 9; 21; 22]%nat -> In j KS) -> inregsL R2 sp ov sh8.
Proof.
  intros (G2 & G8 & G9 & G21 & G22) KSF SUB.
  assert (E : forall j, In j [2; 8; 9; 21; 22]%nat -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; apply KSF; apply SUB; exact Hj).
  split; [rewrite (E 2%nat) by inl; exact G2|]. split; [rewrite (E 8%nat) by inl; exact G8|]. split; [rewrite (E 9%nat) by inl; exact G9|].
  split; [rewrite (E 21%nat) by inl; exact G21| rewrite (E 22%nat) by inl; exact G22].
Qed.
Local Ltac subl := intros jj Hjj; cbn in Hjj; decompose [or] Hjj; try contradiction; subst; inl.

Lemma u_runCe : runCe.
Proof.
  unfold runCe. intros fx R M sp ov sv ec sh8 v H1 H2 H3 H4 H5 H6 IRV G11 (K0 & K1 & K2 & K3 & K4 & K5) VR.
  pose proof IRV as ((G2 & G8 & G9 & G18 & G19 & G21 & G22) & G20 & G23 & G24). junk R 10%nat. junk R 12%nat. junk R 13%nat. junk R 14%nat.
  pose proof (PEAENCSTP.aqSCe_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => sv | 14%nat => ec | 35%nat => v | 38%nat => sh8 | 39%nat => sv / 8 + SBL | 54%nat => (sv + 8) / 8 + SBL
      | 55%nat => bv_unsigned (getr R (reg 10)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
  cbn beta iota in P.
  assert (Q39 : 0 <= sv / 8 + SBL < 2 ^ 64) by (clear - H3; Lia.lia). assert (Q54 : 0 <= (sv + 8) / 8 + SBL < 2 ^ 64) by (clear - H3; Lia.lia).
  feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T10 & T11).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [exact (inregsV_kept R R1 sp ov sv ec sh8 _ IRV KS1 ltac:(subl))|]. split; [exact T1|]. split; [exact T10| exact T11].
Qed.

Lemma u_runR : runR.
Proof.
  unfold runR. intros fx R R0 M sp ov r H1 H2 H3 (G2 & G8 & G21) (K0 & K1 & K2 & K3 & K4 & K5) (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80) RA R0sp QCS.
  junks R. wids R0.
  pose proof (PEAENCSTP.aqSR_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 44%nat => r
      | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19))
      | 49%nat => bv_unsigned (getr R0 (reg 20)) | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23)) | 53%nat => bv_unsigned (getr R0 (reg 24))
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T18 & T19 & T20 & T21 & T22 & T23 & T24).
  pose proof RA as (Hr1 & Hr2).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac5b0 W_ac560 r F_ac560 eq_refl D_ac560 T1 ltac:(lia) Hr2) as MSR.
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
  apply (preserved_of_rest R R0 R1 r sp PEAENCSTP.KS_aqSR ltac:(subl) KS1 QCS R0sp).
  split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [exact T19|]. split; [exact T20|]. split; [exact T21|]. split; [exact T22|]. split; [exact T23| exact T24].
Qed.

Lemma u_runCo : runCo.
Proof.
  unfold runCo. intros fx R M sp ov osk sv ec sh8 dptr n H1 H2 H3 H4 H5 H6 H7 H8 IRV G11 (K0 & K1 & K2 & K3 & K4 & K5) FOV FSV.
  pose proof IRV as ((G2 & G8 & G9 & G18 & G19 & G21 & G22) & G20 & G23 & G24).
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9). destruct FSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  junk R 10%nat. junk R 12%nat. junk R 13%nat. junk R 14%nat.
  assert (Q39 : 0 <= sv / 8 + SBL < 2 ^ 64) by (clear - H4; Lia.lia). assert (Q54 : 0 <= (sv + 8) / 8 + SBL < 2 ^ 64) by (clear - H4; Lia.lia).
  assert (Z39 : L5KA.zeros_at M (sv / 8 + SBL) 2) by exact V4. assert (Z54 : L5KA.zeros_at M ((sv + 8) / 8 + SBL) 1) by exact V5.
  assert (R39 : 2147451392 <= sv / 8 + SBL <= 19791209299968) by (clear - V1; Lia.lia). assert (R54 : 2147451393 <= (sv + 8) / 8 + SBL <= 19791209299968) by (clear - V1; Lia.lia).
  pose proof (PEAENCSTP.aqSCo_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => sv | 14%nat => ec | 33%nat => dptr | 34%nat => n | 38%nat => sh8 | 39%nat => sv / 8 + SBL | 41%nat => osk | 54%nat => (sv + 8) / 8 + SBL
      | 55%nat => bv_unsigned (getr R (reg 10)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T10 & T11).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [exact (inregsV_kept R R1 sp ov sv ec sh8 _ IRV KS1 ltac:(subl))|]. split; [exact T1|]. split; [exact T10| exact T11].
Qed.

Lemma u_runD0 : runD0.
Proof.
  unfold runD0. intros fx R M sp ov osk sv ec sh8 dptr H1 H2 H3 H4 H5 H6 H7 IRV (K0 & K1 & K2 & K3 & K4 & K5) FOV FSV.
  pose proof IRV as ((G2 & G8 & G9 & G18 & G19 & G21 & G22) & G20 & G23 & G24).
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9). destruct FSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  junks R.
  assert (Q39 : 0 <= sv / 8 + SBL < 2 ^ 64) by (clear - H4; Lia.lia). assert (Q54 : 0 <= (sv + 8) / 8 + SBL < 2 ^ 64) by (clear - H4; Lia.lia).
  assert (Z39 : L5KA.zeros_at M (sv / 8 + SBL) 2) by exact V4. assert (Z54 : L5KA.zeros_at M ((sv + 8) / 8 + SBL) 1) by exact V5.
  assert (R39 : 2147451392 <= sv / 8 + SBL <= 19791209299968) by (clear - V1; Lia.lia). assert (R54 : 2147451393 <= (sv + 8) / 8 + SBL <= 19791209299968) by (clear - V1; Lia.lia).
  pose proof (PEAENCSTP.aqSD0_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => sv | 14%nat => ec | 33%nat => dptr | 38%nat => sh8 | 39%nat => sv / 8 + SBL | 41%nat => osk | 54%nat => (sv + 8) / 8 + SBL
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & _ & _).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [rewrite (KS1 2%nat) by inl; exact G2|]. split; [rewrite (KS1 8%nat) by inl; exact G8| rewrite (KS1 21%nat) by inl; exact G21].
Qed.

Lemma u_runD1 : runD1.
Proof.
  unfold runD1. intros fx R M sp ov osk sv ec sh8 dptr n H1 H2 H3 H4 H5 H6 H7 H8 IRV (K0 & K1 & K2 & K3 & K4 & K5) FOV FSV N1 D1.
  pose proof IRV as ((G2 & G8 & G9 & G18 & G19 & G21 & G22) & G20 & G23 & G24).
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9). destruct FSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  junks R.
  assert (V9' : 1 <= dptr <= 140737488355326) by exact D1. assert (V10' : 1 <= n <= 67108864) by (clear - N1 V10; lia). clear V9 V10.
  assert (Q39 : 0 <= sv / 8 + SBL < 2 ^ 64) by (clear - H4; Lia.lia). assert (Q54 : 0 <= (sv + 8) / 8 + SBL < 2 ^ 64) by (clear - H4; Lia.lia).
  assert (Z39 : L5KA.zeros_at M (sv / 8 + SBL) 2) by exact V4. assert (Z54 : L5KA.zeros_at M ((sv + 8) / 8 + SBL) 1) by exact V5.
  assert (R39 : 2147451392 <= sv / 8 + SBL <= 19791209299968) by (clear - V1; Lia.lia). assert (R54 : 2147451393 <= (sv + 8) / 8 + SBL <= 19791209299968) by (clear - V1; Lia.lia).
  pose proof (PEAENCSTP.aqSD1_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => sv | 14%nat => ec | 33%nat => dptr | 34%nat => n | 38%nat => sh8 | 39%nat => sv / 8 + SBL | 41%nat => osk | 54%nat => (sv + 8) / 8 + SBL
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & _ & T18 & T19 & T20).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [exact (inregsL_kept R R1 sp ov sh8 _ (conj G2 (conj G8 (conj G9 (conj G21 G22)))) KS1 ltac:(subl))|].
  split; [exact T18|]. split; [exact T20| exact T19].
Qed.

Lemma u_runE : runE.
Proof.
  unfold runE. intros fx R M sp ov osk sh8 cur cnt b H1 H2 H3 H4 H5 H6 H7 (G2 & G8 & G9 & G21 & G22) G18 G20 G19 (K0 & K1 & K2 & K3 & K4 & K5) FOV Z38 R38 C1 N1 U8 B8 CD.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9). junks R.
  pose proof (PEAENCSTP.aqSE_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 36%nat => cur | 37%nat => cnt | 38%nat => sh8 | 40%nat => b | 41%nat => osk
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T10 & T11 & C81).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [apply KS1; inl|]. split; [apply KS1; inl|]. split; [apply KS1; inl|]. split; [exact T1|]. split; [exact T10|]. split; [exact T11| exact C81].
Qed.

Lemma u_runM0 : runM0.
Proof.
  unfold runM0. intros fx R M sp ov sh8 cur H1 H2 H3 H4 (G2 & G8 & G9 & G21 & G22) G18 G20 G19 (K0 & K1 & K2 & K3 & K4 & K5) C1.
  junks R.
  pose proof (PEAENCSTP.aqSM0_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 36%nat => cur | 38%nat => sh8
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & _ & _ & _).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [rewrite (KS1 2%nat) by inl; exact G2|]. split; [rewrite (KS1 8%nat) by inl; exact G8| rewrite (KS1 21%nat) by inl; exact G21].
Qed.

Lemma u_runM1 : runM1.
Proof.
  unfold runM1. intros fx R M sp ov sh8 cur cnt H1 H2 H3 H4 H5 (G2 & G8 & G9 & G21 & G22) G18 G20 G19 (K0 & K1 & K2 & K3 & K4 & K5) C1 N2.
  junks R.
  pose proof (PEAENCSTP.aqSM1_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 36%nat => cur | 37%nat => cnt | 38%nat => sh8
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T18 & T19 & T20).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|].
  split; [exact (inregsL_kept R R1 sp ov sh8 _ (conj G2 (conj G8 (conj G9 (conj G21 G22)))) KS1 ltac:(subl))|].
  split; [exact T18|]. split; [exact T20| exact T19].
Qed.

Lemma u_runE0 : runE0.
Proof.
  unfold runE0. intros fx R R0 M sp ov osk eb r H1 H2 H3 H4 H5 (G2 & G8 & G21) (K0 & K1 & K2 & K3 & K4 & K5) FOV Z24 Z32 U24 U32 EB (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80) RA R0sp QCS.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9). junks R. wids R0.
  pose proof (PEAENCSTP.aqSE0_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 38%nat => eb | 44%nat => r
      | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19))
      | 49%nat => bv_unsigned (getr R0 (reg 20)) | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23)) | 53%nat => bv_unsigned (getr R0 (reg 24))
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24).
  pose proof RA as (Hr1 & Hr2).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac5b0 W_ac560 r F_ac560 eq_refl D_ac560 T1 ltac:(lia) Hr2) as MSR.
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
  apply (preserved_of_rest R R0 R1 r sp PEAENCSTP.KS_aqSE0 ltac:(subl) KS1 QCS R0sp).
  split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [exact T19|]. split; [exact T20|]. split; [exact T21|]. split; [exact T22|]. split; [exact T23| exact T24].
Qed.

Lemma u_runE1 : runE1.
Proof.
  unfold runE1. intros fx R R0 M sp ov osk eb ed cn r H1 H2 H3 H4 H5 H6 H7 (G2 & G8 & G21) (K0 & K1 & K2 & K3 & K4 & K5) FOV Z24 Z32 U24 U32 EB ED ED8 LEN WR24 EBIG ZC EDS EDO UC
    (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80) RA R0sp QCS.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9). junks R. wids R0.
  assert (LEN' : 24 <= ed + (-1) * eb <= 100000) by (clear - LEN; lia).
  pose proof RA as (Hr1 & Hr2).
  destruct (Z.eq_dec cn 18446744073709551615) as [CW|CNW].
  - pose proof (PEAENCSTP.aqSE1w_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 38%nat => eb | 39%nat => ed | 44%nat => r
        | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19))
        | 49%nat => bv_unsigned (getr R0 (reg 20)) | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23)) | 53%nat => bv_unsigned (getr R0 (reg 24))
        | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
    cbn beta iota in P. rewrite <- CW in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & CC).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac5b0 W_ac560 r F_ac560 eq_refl D_ac560 T1 ltac:(lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
    split; [| rewrite CW; change ((18446744073709551615 + 1) mod 2 ^ 64) with 0; exact CC].
    apply (preserved_of_rest R R0 R1 r sp PEAENCSTP.KS_aqSE1w ltac:(subl) KS1 QCS R0sp).
    split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [exact T19|]. split; [exact T20|]. split; [exact T21|]. split; [exact T22|]. split; [exact T23| exact T24].
  - assert (CNR : 0 <= cn <= 18446744073709551614) by (clear - H6 CNW; lia).
    pose proof (PEAENCSTP.aqSE1_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 38%nat => eb | 39%nat => ed | 42%nat => cn | 44%nat => r
        | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19))
        | 49%nat => bv_unsigned (getr R0 (reg 20)) | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23)) | 53%nat => bv_unsigned (getr R0 (reg 24))
        | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | 58%nat => bv_unsigned (getr R (reg 13)) | 59%nat => bv_unsigned (getr R (reg 14)) | _ => 0 end)) as P.
    cbn beta iota in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & CC).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac5b0 W_ac560 r F_ac560 eq_refl D_ac560 T1 ltac:(lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
    split; [| rewrite Z.mod_small by (clear - CNR; lia); exact CC].
    apply (preserved_of_rest R R0 R1 r sp PEAENCSTP.KS_aqSE1 ltac:(subl) KS1 QCS R0sp).
    split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [exact T19|]. split; [exact T20|]. split; [exact T21|]. split; [exact T22|]. split; [exact T23| exact T24].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMA.ly_as0 L C LY.

Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Hypothesis PUTL : PECSA.put_length_spec L ar HI P.
Hypothesis MKEC : PECSA.make_ec_spec L ar HI.
Hypothesis VAL : PECVSA.validate_fun_spec RSEGS AD L ar HI (pe_validate_enc EE).

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (dptr sv tg : Z) (l : list Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z).
Variables (xstk : list pstate) (xpos : Z) (xmore xdone xhalt : bool) (xdepth : Z) (xec : bool) (xestk : list eitem) (xedepth xlo xhi : Z) (xbad : bool).
Variables (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Let X : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad.
Let XS (a : Z) : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + a) (xhi + a) xbad.

Let XE : st := ST xstk xpos xmore xdone xhalt xdepth true xestk xedepth (xlo + 1) (xhi + 1) xbad.
Let n : Z := Z.of_nat (length l).

Let NB : Z := 1 + (pl_size n + n).
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
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 tg.
Hypothesis TG : 0 <= tg < 32.
Hypothesis A14 : getr R (reg 14) = Z_to_bv 64 (PMSPA.o_ec AD fb).
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
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_enc p X.
Hypothesis HB1 : PESKA.spa_hb P (xhi + 1).
Hypothesis HBN : utf8_valid l = true -> PESKA.spa_hb P (xhi + NB).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.

Hypothesis KONTv : utf8_valid l = true -> forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (e_end_value (XS NB)) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.
Hypothesis KONTe : utf8_valid l = false -> forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p XE s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Definition FC (Mx : word -> option byte) : Prop := fcells R r Mx sp.
Let LB : list (Z * Z) := PEC.owned s en k ++ LBX.
Let LBc0 : list (Z * Z) := PM.parser_own s ++ LBX.
Let Ws : list L5.range := [(PESK.o_sink EE fb, 24)].

Let Wt : list L5.range := (PESK.o_sink EE fb, 24) :: (PMSPA.o_ec AD fb, 16) :: PMSPA.err_W AD.
Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH;
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl3 in Rgp; rewrite L5K.rl4 in Rtp.
Local Ltac frame_facts :=
  pose proof FOK as ((rs & Hfb) & Fal);
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & _);
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6); cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6; change (ff_bytes 5) with 2048 in F1, F2, F3, F4, F5, F6;
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP; unfold FS_BYTES in F1, F2, F3, F4, F5, F6, FSAPP, FSCEIL, FSIMG.
Local Ltac name_objs :=
  set (ov := PMSPA.o_v AD fb) in *; set (osk := PESK.o_sink EE fb) in *; set (oec := PMSPA.o_ec AD fb) in *;
  assert (Eov : ov = fb + 496) by reflexivity; assert (Eosk : osk = fb + 432) by reflexivity; assert (Eoec : oec = fb + 1120) by reflexivity.

Lemma FC_frame M1 M2 : (forall a, sp - 96 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros AG (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80). entry_facts.
  assert (SV : forall a0 w, sp - 96 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; clear - Hi H1 H2; lia| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC, fcells. repeat (split; [apply SV; [clear; lia| clear; lia| assumption]|]). apply SV; [clear; lia| clear; lia| assumption].
Qed.

Lemma FC_but M1 M2 lo hi : hi <= sp - 80 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros Hhi AG (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80). entry_facts.
  assert (SV : forall a0 w, sp - 80 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; [clear - Hi H1 H2 SLO SHI SPT; lia| clear - Hi H1 Hhi; lia]| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC, fcells. repeat (split; [apply SV; [clear; lia| clear; lia| assumption]|]). apply SV; [clear; lia| clear; lia| assumption].
Qed.
Lemma HFR : 96 = 32 \/ 96 = 64 \/ 96 = 80 \/ 96 = 96. Proof. right; right; right; reflexivity. Qed.
Lemma CSK3 : In 3%nat CSK. Proof. inl. Qed.
Lemma CSK4 : In 4%nat CSK. Proof. inl. Qed.
Lemma CSKall j : In j CSK -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.
Lemma CSIall j : In j CSI -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.
Lemma CSKI j : In j CSK -> In j CSI. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.
Lemma PLS : 2 <= pl_size n <= 9. Proof. unfold pl_size. repeat destruct (_ <=? _); lia. Qed.
Lemma N0 : 0 <= n. Proof. unfold n. clear. lia. Qed.
Lemma MPa a : PECSPA.mp_enc p (XS a).
Proof. destruct MP as (Q1 & Q2 & Q3 & Q4). cbn [s_lo s_hi s_bad s_estk s_edepth X] in Q1, Q2, Q3, Q4. unfold PECSPA.mp_enc. cbn [s_lo s_hi s_bad s_estk s_edepth XS]. split; [clear - Q1; lia|]. split; [exact Q2|]. split; [exact Q3| exact Q4]. Qed.

Abbreviation INV := (PEAEKC.inv L ar HI P M model LBX FF LK Aw cr sp fb xlo xhi s en k FC).
Abbreviation csk := (PEAEKC.csk CSK R).

Lemma csk_after R1 R2 : csk R1 -> regs_preserved R1 R2 -> csk R2.
Proof. intros QCS RP j Hj. rewrite (L5SAR.cs_of_preserved R1 R2 j RP (CSKall j Hj)). exact (QCS j Hj). Qed.
Lemma csk_kept R1 R2 : csk R1 -> (forall j, In j CSK -> getr R2 (reg j) = getr R1 (reg j)) -> csk R2.
Proof. intros QCS KS j Hj. rewrite (KS j Hj). exact (QCS j Hj). Qed.
Lemma csk_keptI R1 R2 : csk R1 -> (forall j, In j CSI -> getr R2 (reg j) = getr R1 (reg j)) -> csk R2.
Proof. intros QCS KS j Hj. rewrite (KS j (CSKI j Hj)). exact (QCS j Hj). Qed.
Lemma inregsM_after R1 R2 sv' ec' sh8 : inregsM R1 sp (PMSPA.o_v AD fb) sv' ec' sh8 -> regs_preserved R1 R2 -> inregsM R2 sp (PMSPA.o_v AD fb) sv' ec' sh8.
Proof.
  intros (G2 & G8 & G9 & G18 & G19 & G21 & G22) RP. pose proof (fun jj Hjj => L5SAR.cs_of_preserved R1 R2 jj RP Hjj) as Rc.
  split; [rewrite (Rc 2%nat) by inl; exact G2|]. split; [rewrite (Rc 8%nat) by inl; exact G8|]. split; [rewrite (Rc 9%nat) by inl; exact G9|].
  split; [rewrite (Rc 18%nat) by inl; exact G18|]. split; [rewrite (Rc 19%nat) by inl; exact G19|]. split; [rewrite (Rc 21%nat) by inl; exact G21| rewrite (Rc 22%nat) by inl; exact G22].
Qed.
Lemma inregsV_after R1 R2 sv' ec' sh8 : inregsV R1 sp (PMSPA.o_v AD fb) sv' ec' sh8 -> regs_preserved R1 R2 -> inregsV R2 sp (PMSPA.o_v AD fb) sv' ec' sh8.
Proof.
  intros (IM & G20 & G23 & G24) RP. pose proof (fun jj Hjj => L5SAR.cs_of_preserved R1 R2 jj RP Hjj) as Rc.
  split; [exact (inregsM_after R1 R2 sv' ec' sh8 IM RP)|].
  split; [rewrite (Rc 20%nat) by inl; exact G20|]. split; [rewrite (Rc 23%nat) by inl; exact G23| rewrite (Rc 24%nat) by inl; exact G24].
Qed.
Lemma inregsE_afterV R1 R2 sv' ec' sh8 : inregsV R1 sp (PMSPA.o_v AD fb) sv' ec' sh8 -> regs_preserved R1 R2 -> inregsE R2 sp (PMSPA.o_v AD fb).
Proof.
  intros ((G2 & G8 & G9 & G18 & G19 & G21 & G22) & _) RP. pose proof (fun jj Hjj => L5SAR.cs_of_preserved R1 R2 jj RP Hjj) as Rc.
  split; [rewrite (Rc 2%nat) by inl; exact G2|]. split; [rewrite (Rc 8%nat) by inl; exact G8| rewrite (Rc 21%nat) by inl; exact G21].
Qed.
Lemma inregsE_after R1 R2 : inregsE R1 sp (PMSPA.o_v AD fb) -> regs_preserved R1 R2 -> inregsE R2 sp (PMSPA.o_v AD fb).
Proof.
  intros (G2 & G8 & G21) RP. pose proof (fun jj Hjj => L5SAR.cs_of_preserved R1 R2 jj RP Hjj) as Rc.
  split; [rewrite (Rc 2%nat) by inl; exact G2|]. split; [rewrite (Rc 8%nat) by inl; exact G8| rewrite (Rc 21%nat) by inl; exact G21].
Qed.

Lemma txt_facts : 0 <= dptr /\ dptr + n <= 2 ^ 47 /\ (n = 0 \/ 0 < dptr)
  /\ (n = 0 \/ (ar_fs ar <= dptr /\ dptr + n <= ar_fs ar + FS_BYTES) \/ (exists q m, In (q, m) (PM.parser_own s) /\ q <= dptr /\ dptr + n <= q + m)).
Proof.
  entry_facts. frame_facts.
  destruct LOC as [(B & m & Hin & X1 & X2)|[(X1 & X2)|[(X1 & X2)|(X1 & X2)]]].
  - assert (HinLB : In (B, m) LB) by (unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hin).
    pose proof (WB _ HinLB) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
    split; [clear - X1 Q0; Lia.lia|]. split; [clear - X2 Q4 SLO SHI SPT; Lia.lia|]. split; [right; clear - X1 Q0; Lia.lia|]. right; right. exists B, m. split; [exact Hin| split; [exact X1| exact X2]].
  - unfold PMSPA.o_tb, PMSPA.o_p in X1, X2. cbn [pa_off_p PeCLayoutA.CADDR_A] in X1, X2.
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
  apply KX3. apply (PEAEKC.inv_frame L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq Mq mdq md3 LKq Awq crq kq a sp sp INVq);
    [clear; lia| clear; lia| intros w D; exact D| intros i _ _; reflexivity| exact FCq| exact HH3| exact AM3| exact MRT3].
Qed.

Lemma inv_callee0 Mq mdq LKq Awq crq kq a M2 md2 scr :
  INV Mq mdq LKq Awq crq kq a -> 0 <= scr <= 16384 ->
  L5CA.ahpres L ar (PEC.owned s en kq ++ LBX) FF (sp - 96) scr [] Mq M2 ->
  ri_inv HI (PEC.owned s en kq ++ LBX) FF LKq crq Awq M2 (vml_of md2) -> L5CA.amodel_ok Awq md2 -> model_rt mdq md2 ->
  INV M2 md2 LKq Awq crq kq a.
Proof.
  intros INVq Hscr HP2 HH2 AM2 MRT2. entry_facts. frame_facts.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  set (LBq := PEC.owned s en kq ++ LBX) in *.
  assert (XINCq : incl LBc0 LBq) by (unfold LBc0, LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINCq : incl (PEC.enc_own en) LBq) by (unfold LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (KINCq : incl (PESK.sink_own kq) LBq) by (unfold LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHq) as BRBq.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq) as FRBq.
  set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  assert (Eov : ov = fb + 496) by reflexivity. assert (Eosk : osk = fb + 432) by reflexivity.
  assert (FRAME12 : forall a0, sp - 96 <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT; lia| intros Y; clear - Ha0 Y; lia].
    - intros r0 []. }
  assert (EK12 : L5SAR.ek L ar LBq FF sp 20480 [] Mq M2).
  { apply (L5SAR.ek_callee L ar LBq [] FF [] sp 20480 (sp - 96) scr [] [] Mq M2 HP2); [clear - Hscr; lia| clear - Hscr; lia| intros a0 _ O; exact O]. }
  assert (DK12 : L5SAR.dk L ar LBq FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar LBq [] FF [] sp 20480 (sp - 96) scr [] Mq M2 HP2); clear - Hscr; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKA.astk_after_ahpres L ar LBq FF Mq M2 sp 20480 (sp - 96) scr [] ASTKq HP2); [clear - Hscr; lia| clear - Hscr; lia| clear - Hscr; lia| exact STOP]. }
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKA.stksh_keepA L ar LBq FF sp 20480 [] Mq M2 EK12 PMKA.wapp_nil (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact SZq].
    apply (PEAEKC.SPd8 sp SP32). reflexivity. }
  unfold PEAEKC.inv. split; [exact (FC_frame Mq M2 FRAME12 FCq)|]. split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|]. split; [exact ILKq|]. split; [exact IAWq|].
  split; [exact HH2|].
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LBq FF sp 20480 [] Mq M2 EK12 PMKA.wapp_nil FRBq BRBq ov fb en (PEAEKC.AOF FF fb FOK ov 56 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact EINCq| | exact EAq].
    - intros i _ r0 [].
    - intros _ i _ r0 []. }
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LBq FF sp 20480 [] Mq M2 EK12 PMKA.wapp_nil FRBq BRBq P osk kq (PEAEKC.AOF FF fb FOK osk 24 ltac:(clear - Eosk; lia) ltac:(clear - Eosk; lia))); [| exact KINCq| | exact SKAq].
    - intros i _ r0 [].
    - intros _ i _ r0 []. }
  split; [exact CLq|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (L5SAR.ek_W L ar LBc0 FF sp 20480 Ws [] Mq M2 (PMKA.ek_sublb L ar LBq LBc0 FF sp 20480 [] Mq M2 XINCq EK12) ltac:(intros a0 O r0 [])))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKA.dk_sublb L ar LBq LBc0 FF sp 20480 Mq M2 XINCq DK12))|].
  exact CKq.
Qed.

Lemma txt_keep Mq : L5SAR.ek L ar LBc0 FF sp 20480 Ws M Mq -> L5.defined Mq dptr n /\ PMSPA.accA Mq dptr n /\ L5.bytes_at RSEGS Mq dptr l.
Proof.
  intros EK. entry_facts. frame_facts.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (BRB0 : forall b, In b LBc0 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRB; apply INC0; exact Hb).
  pose proof (PEAEKC.ws_wapp L ar C HI HIok R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK) as WAPP.
  set (osk := PESK.o_sink EE fb) in *. assert (Eosk : osk = fb + 432) by reflexivity.
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply (PEAEKC.AOF FF fb FOK); clear - Eosk; lia).
  destruct LOC as [(B & m & Hin & X1 & X2)|[(X1 & X2)|[(X1 & X2)|(X1 & X2)]]].
  - assert (Hin0 : In (B, m) LBc0) by (unfold LBc0; apply in_or_app; left; exact Hin).
    assert (HinLB : In (B, m) LB) by (apply INC0; exact Hin0).
    assert (OW : forall i, B <= i < B + m -> L5.outside Ws i).
    { intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk.
      destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ B m osk 24 HH HinLB AOSK) as [Y|Y]; clear - Hi Y; lia. }
    destruct (PMKA.agA_blk L ar LBc0 FF sp 20480 Ws M Mq EK WAPP BRB0 B m Hin0 OW) as [AG SH].
    pose proof (BRB0 _ Hin0) as [B0 B47]. cbn [fst snd] in B0, B47.
    split; [apply (L5C.defined_agree M Mq dptr n); [intros i Hi; apply AG; clear - Hi X1 X2; lia| exact DEF]|].
    split; [apply (PMFA.accA_agree M Mq dptr n); [intros x Hx; apply SH; clear - Hx X1 X2; lia| exact ACC]|].
    apply (L5C.bytes_at_agree RSEGS M Mq dptr l); [intros i Hi; apply AG; fold n in Hi; clear - Hi X1 X2; lia| clear - X1 B0; lia| fold n; clear - X2 B47; lia| exact BYT].
  - unfold PMSPA.o_tb, PMSPA.o_p in X1, X2. cbn [pa_off_p PeCLayoutA.CADDR_A] in X1, X2.
    assert (AOT : PMSPA.aobjA FF dptr n) by (apply (PEAEKC.AOF FF fb FOK); clear - X1 X2; pose proof N0; lia).
    assert (OW : forall i, dptr <= i < dptr + n -> L5.outside Ws i) by (intros i Hi r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; fold osk; clear - Hi X1 X2 Eosk; lia).
    destruct (PMKA.agA_obj L ar LBc0 FF sp 20480 Ws M Mq EK WAPP FRB dptr n AOT OW) as [AG SH].
    split; [apply (L5C.defined_agree M Mq dptr n); [exact AG| exact DEF]|].
    split; [apply (PMFA.accA_agree M Mq dptr n); [exact SH| exact ACC]|].
    apply (L5C.bytes_at_agree RSEGS M Mq dptr l); [exact AG| clear - X1 F1 FSAPP; Lia.lia| fold n; clear - X2 F2 FSCEIL SLO SHI SPT; Lia.lia| exact BYT].
  - unfold n. rewrite X1, X2. cbn. split; [intros i Hi; exfalso; clear - Hi; Lia.lia|]. split; [intros x Hx; exfalso; clear - Hx; Lia.lia|]. intros i Hi. cbn in Hi. exfalso. clear - Hi. Lia.lia.
  - pose proof X1 as (f & Hf & Y1 & Y2). pose proof (WF f Hf) as (W1 & W2 & _). unfold FS_BYTES in W1, W2.
    assert (OW : forall i, dptr <= i < dptr + n -> L5.outside Ws i) by (intros i Hi r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; fold osk; clear - Hi X2 Eosk; lia).
    destruct (PMKA.agA_obj L ar LBc0 FF sp 20480 Ws M Mq EK WAPP FRB dptr n X1 OW) as [AG SH].
    split; [apply (L5C.defined_agree M Mq dptr n); [exact AG| exact DEF]|].
    split; [apply (PMFA.accA_agree M Mq dptr n); [exact SH| exact ACC]|].
    apply (L5C.bytes_at_agree RSEGS M Mq dptr l); [exact AG| clear - Y1 W1 FSAPP; Lia.lia| fold n; clear - Y2 W2 FSCEIL SLO SHI SPT; Lia.lia| exact BYT].
Qed.

Lemma SP16' : (sp - 96) mod 16 = 0.
Proof. pose proof (PEAEKC.A16' sp SP32) as A. replace (sp - 96) with (sp + (-6) * 16) by (clear; Lia.lia). rewrite Z_mod_plus_full. exact A. Qed.

Lemma val_call a (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  INV Mq mdq LKq Awq crq kq a ->
  getr Rq (reg 1) = Z_to_bv 64 0xac490 -> getr Rq (reg 2) = Z_to_bv 64 (sp - 96) -> getr Rq (reg 10) = Z_to_bv 64 dptr -> getr Rq (reg 11) = Z_to_bv 64 n -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 v, INV M2 md2 LKq Awq crq kq a -> regs_preserved Rq R2 -> getr R2 (reg 11) = Z_to_bv 64 v -> 0 <= v < 7 -> (v = 0 <-> utf8_valid l = true) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xac490 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xb1068 Mq mdq) K.
Proof.
  intros INVq Q1 Q2 Q10 Q11 QCS KX. entry_facts. frame_facts.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  destruct (txt_keep Mq EKq) as (DEFq & ACCq & BYTq).
  destruct txt_facts as (D0 & D47 & DNZ & DLOC).
  destruct (PEAEKC.keepf L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS Mq EKq)
    as (_ & _ & _ & BASEq & _).
  set (LBq := PEC.owned s en kq ++ LBX) in *.
  assert (ASTKv : L5CA.astk ar Mq (sp - 96) 12288).
  { apply (L5SAR.astk_sub ar Mq Mq sp 20480 96 12288 ASTKq); [intros w D; exact D| clear; lia| clear; lia| clear; lia| exact SP16']. }
  pose proof VAL as VX. unfold PECVSA.validate_fun_spec in VX. cbn [pe_validate_enc EE PeCLayoutA.EADDR_A] in VX.
  unfold PMSPA.cfg.
  apply (VX fxq Rq Mq mdq K LBq FF LKq Awq crq dptr n (sp - 96) 0xac490 l HHq AMq K0); clear VX.
  { split; [rewrite L5K.rl1; exact Q1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3, (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4, (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split; [exact ASTKv|].
    apply (PMKA.shadow_zero_sub Mq (sp - 20480) 2560); [apply (PEAEKC.SPd8 sp SP32); reflexivity| | clear; lia| clear; lia| clear; lia| exact SZq].
    replace (sp - 96 - 12288) with (sp - 12384) by (clear; lia). apply (PEAEKC.SPd8 sp SP32). reflexivity. }
  { apply (PEAEKC.ffroomA_mono 4 0 FF LK LKq FRM ILKq NDFq). clear; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { split; [exact N0| exact N26]. }
  { exact D0. } { exact DNZ. } { exact D47. } { exact DEFq. } { exact ACCq. }
  { intros a0 Ha. apply (PMASR1.vis_scan L ar C HI LY HIok _ FF LKq crq Awq Mq mdq dptr n HHq); [| exact Ha].
    destruct DLOC as [Y|[Y|(q & m & Hin & Y1 & Y2)]]; [left; exact Y| right; left; exact Y| right; right; exists q, m].
    split; [unfold LBq, PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hin| split; [exact Y1| exact Y2]]. }
  { change (PMSPA.pm_scr 0) with 12288.
    destruct LOC as [(B & m & Hin & X1 & X2)|[(X1 & X2)|[(X1 & X2)|(X1 & X2)]]].
    - right. right. assert (HinLB : In (B, m) LB) by (unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hin).
      pose proof (WB _ HinLB) as ((_ & _ & _ & _ & Xc & _) & _). cbn [fst snd] in Xc. clear - X2 Xc SLO. lia.
    - right. right. unfold PMSPA.o_tb, PMSPA.o_p in X2. cbn [pa_off_p PeCLayoutA.CADDR_A] in X2. clear - X2 F2 FSCEIL SLO. lia.
    - left. unfold n. rewrite X2. reflexivity.
    - right. right. pose proof X1 as (f & Hf & Y1 & Y2). pose proof (WF f Hf) as (W1 & W2 & _). unfold FS_BYTES in W2. clear - Y2 W2 FSCEIL SLO. lia. }
  { exact BASEq. }
  { exact BYTq. } { reflexivity. } { exact BOK. }
  intros fx8 R8 M8 md8 v RP8 FBT8 MG8 MRT8 AM8 HH8 V11 Hv HV.
  assert (AH8 : L5CA.ahpres L ar LBq FF (sp - 96) 12288 [] Mq M8).
  { apply (PMAUAR.ahpres_of_frame_but L ar C HI LY HIok LBq FF LKq crq Awq Mq M8 (vml_of mdq) (sp - 96) 12288 HHq);
      [clear - SPT; lia| clear - SLO; lia| clear; lia| exact FBT8| exact MG8|].
    pose proof ASTKv as (_ & _ & _ & _ & X' & _). exact X'. }
  apply (KX fx8 R8 M8 md8 v).
  - exact (inv_callee0 Mq mdq LKq Awq crq kq a M8 md8 12288 INVq ltac:(clear; lia) AH8 HH8 AM8 MRT8).
  - exact RP8.
  - rewrite <- L5K.rl11. exact V11.
  - exact Hv.
  - exact HV.
Qed.

Lemma pl_call (UVt : utf8_valid l = true) (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  INV Mq mdq LKq Awq crq kq 1 ->
  getr Rq (reg 1) = Z_to_bv 64 0xac4bc -> getr Rq (reg 2) = Z_to_bv 64 (sp - 96) -> getr Rq (reg 10) = Z_to_bv 64 (PMSPA.o_v AD fb) -> getr Rq (reg 11) = Z_to_bv 64 n -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, INV M2 md2 LK2 Aw2 cr2 k2 (1 + pl_size n) -> regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xac4bc M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xae710 Mq mdq) K.
Proof.
  intros INVq Q1 Q2 Q10 Q11 QCS KX. entry_facts. frame_facts.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  pose proof PLS as HPL. pose proof N0 as HN0.
  pose proof (PEAEKC.inv_cpre L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
                HH ENT FOK FC CPRE INCS Mq mdq LKq Awq crq kq 1 (xlo + 1) (xhi + 1) INVq eq_refl eq_refl) as CPq.
  pose proof PUTL as PX. unfold PECSA.put_length_spec, PECSPA.put_length_spec in PX. cbn [pe_put_length EE PeCLayoutA.EADDR_A] in PX.
  unfold PMSPA.cfg.
  apply (PX PMODE fxq Rq Mq mdq K LBX FF LKq Awq crq (sp - 96) 0xac4bc fb cat n p (XS 1) s str sm en kq e HHq AMq K0); clear PX.
  { split; [rewrite L5K.rl1; exact Q1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3, (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4, (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 3) with 18432. change (18432 / 8) with 2304. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 96 18432 ASTKq); [intros w D; exact D| clear; lia| clear; lia| clear; lia| exact SP16'].
    - apply (PMKA.shadow_zero_sub Mq (sp - 20480) 2560); [apply (PEAEKC.SPd8 sp SP32); reflexivity| | clear; lia| clear; lia| clear; lia| exact SZq].
      replace (sp - 96 - 18432) with (sp - 18528) by (clear; lia). apply (PEAEKC.SPd8 sp SP32). reflexivity. }
  { apply (PEAEKC.ffroomA_mono 4 3 FF LK LKq FRM ILKq NDFq). clear; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  { exact FOK. }
  { exact SP16'. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { unfold INT64_MAX. clear - HN0 N26; lia. }
  { exact CPq. }
  { exact INCS. }
  { exact POK. }
  { exact (MPa 1). }
  { cbn [s_hi XS]. apply (PESKA.spao_hb_mono L P PO (xhi + NB)); [exact (HBN UVt)| unfold NB; clear - HN0; Lia.lia]. }
  { unfold PMSP.credit_le, PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CRED, CKq |- *. cbn [fst snd] in CRED, CKq |- *. clear - CRED CKq. lia. }
  intros fx2 R2 M2 md2 LK2 Aw2 k2 cr2 RP2 CP2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 3) with 18432 in HP2.
  set (LBY := PM.parser_own s ++ PEC.enc_own en ++ LBX) in *.
  set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  assert (Eov : ov = fb + 496) by reflexivity. assert (Eosk : osk = fb + 432) by reflexivity.
  assert (XINCq : incl LBc0 LBY) by (unfold LBc0, LBY; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (OWs : forall a0, sp - 20480 <= a0 < sp -> L5.outside Ws a0).
  { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold osk. clear - Ha0 Eosk F2 FSCEIL SLO; lia. }
  assert (FRAME12 : forall a0, sp - 96 <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT; lia| intros Y; clear - Ha0 Y; lia].
    - apply OWs. clear - Ha0; lia. }
  assert (EK12 : L5SAR.ek L ar LBY FF sp 20480 Ws Mq M2).
  { apply (L5SAR.ek_callee L ar LBY [] FF [] sp 20480 (sp - 96) 18432 Ws Ws Mq M2 HP2); [clear; lia| clear; lia| intros a0 _ O; exact O]. }
  assert (DK12 : L5SAR.dk L ar LBY FF sp 20480 Mq M2) by (apply (L5SAR.dk_callee L ar LBY [] FF [] sp 20480 (sp - 96) 18432 Ws Mq M2 HP2); clear; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKA.astk_after_ahpres L ar LBY FF Mq M2 sp 20480 (sp - 96) 18432 Ws ASTKq HP2); [clear; lia| clear; lia| clear; lia| exact STOP]. }
  pose proof (PEAEKC.ws_wapp L ar C HI HIok R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK) as WAPP.
  assert (SZ2 : shadow_zero M2 (sp - 20480) 2560).
  { apply (PMKA.stksh_keepA L ar LBY FF sp 20480 Ws Mq M2 EK12 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply (PEAEKC.SPd8 sp SP32); reflexivity| clear; lia| exact SZq]. }
  pose proof CP2 as (_ & _ & EA2 & _ & SKA2 & _ & _ & _ & _ & CL2 & _).
  unfold PMSPA.o_v, PESK.o_sink in EA2, SKA2. fold ov in EA2. fold osk in SKA2.
  destruct CL2 as (_ & _ & _ & _ & _ & _ & _ & Lz2 & _). cbn [s_lo s_hi w_out XS] in Lz2.
  apply (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2); [| exact RP2].
  unfold PEAEKC.inv. split; [exact (FC_frame Mq M2 FRAME12 FCq)|]. split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|].
  split; [intros x Hx; apply ILKq; apply ILK2; exact Hx|]. split; [intros x Hx; apply IAW2; apply IAWq; exact Hx|].
  split; [exact HH2|].
  split; [exact EA2|]. split; [exact SKA2|].
  split; [clear - Lz2; lia|].
  split; [exact (L5SAR.ek_trans L ar LBc0 FF sp 20480 Ws M Mq M2 EKq (PMKA.ek_sublb L ar LBY LBc0 FF sp 20480 Ws Mq M2 XINCq EK12))|].
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M2 DKq (PMKA.dk_sublb L ar LBY LBc0 FF sp 20480 Mq M2 XINCq DK12))|].
  unfold PMSP.credit_keep, PECA.pot_encA, PEC.credit_add in CKq, CK2 |- *. cbn [fst snd] in CKq, CK2 |- *. clear - CKq CK2. lia.
Qed.

Lemma dloc_of kq : (n = 0 \/ (ar_fs ar <= dptr /\ dptr + n <= ar_fs ar + FS_BYTES) \/ (exists q m, In (q, m) (PM.parser_own s) /\ q <= dptr /\ dptr + n <= q + m)) ->
  (n = 0 \/ (ar_fs ar <= dptr /\ dptr + n <= ar_fs ar + FS_BYTES) \/ (exists q m, In (q, m) (PEC.owned s en kq ++ LBX) /\ q <= dptr /\ dptr + n <= q + m)).
Proof.
  intros [Y|[Y|(q & m & Hin & Y1 & Y2)]]; [left; exact Y| right; left; exact Y| right; right; exists q, m].
  split; [apply in_or_app; left; unfold PEC.owned; apply in_or_app; left; exact Hin| split; [exact Y1| exact Y2]].
Qed.

Lemma sv_facts Mq mdq LKq Awq crq kq a : INV Mq mdq LKq Awq crq kq a ->
  fsv (mrestrict (ahid Awq mdq) Mq) sp sv dptr n.
Proof.
  intros INVq. entry_facts. frame_facts. pose proof N0 as HN0.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  destruct txt_facts as (D0 & D47 & DNZ & DLOC).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (BRB0 : forall b, In b LBc0 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRB; apply INC0; exact Hb).
  pose proof (PEAEKC.ws_wapp L ar C HI HIok R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK) as WAPP.
  assert (OW : forall i, sv <= i < sv + 16 -> L5.outside Ws i).
  { intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold PESK.o_sink. cbn [pe_off_sink PeCLayoutA.EADDR_A]. clear - Hi SVF; lia. }
  destruct (PMKA.agA_obj L ar LBc0 FF sp 20480 Ws M Mq EKq WAPP FRB sv 16 AOSV OW) as [AG SH].
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq sv 16 sp 20480 HHq (PMKA.aobj_of_aobjA FF sv 16 AOSV SV8) ltac:(clear; lia) ltac:(reflexivity))
    as ((S1 & S2 & S3 & S4 & S5) & SBIG & SDEF' & SVIS & SVSH & SCL & SCLSH).
  assert (ACq : PMSPA.accA Mq sv 16) by exact (PMFA.accA_agree M Mq sv 16 SH ACSV).
  pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq sv 16 HHq AOSV SV8 ltac:(clear; lia) ltac:(reflexivity) ACq) as ZS. change (16 / 8) with 2 in ZS.
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

Lemma wt_wapp : PMKA.wapp Wt.
Proof.
  entry_facts. frame_facts. unfold Wt. apply PMKA.wapp_cons; [| apply PMKA.wapp_cons].
  - cbn [fst snd]. unfold PESK.o_sink. cbn [pe_off_sink PeCLayoutA.EADDR_A]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
  - cbn [fst snd]. unfold PMSPA.o_ec, PMSP.o_ec. cbn [pa_off_ec PeCLayoutA.CADDR_A]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - F1 F2 FSAPP. lia.
  - intros rr Hin. unfold PMSPA.err_W, PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit PeCLayoutA.CADDR_A] in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI.
    destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia.
Qed.
Lemma wt_ws a : L5.outside Wt a -> L5.outside Ws a.
Proof. intros O r0 [<-|[]]. apply O. unfold Wt. left; reflexivity. Qed.
Lemma wt_wenc a : L5.outside (PEC.W_enc AD EE fb) a -> L5.outside Wt a.
Proof.
  intros O r0 Hin. apply O. unfold PEC.W_enc. cbn [app]. unfold Wt in Hin.
  destruct Hin as [<-|[<-|Hin]]; [right; left; reflexivity| right; right; left; reflexivity| right; right; right; exact Hin].
Qed.

Lemma wt_rng rr a : In rr Wt -> L5.in_rng rr a ->
  (PESK.o_sink EE fb <= a < PESK.o_sink EE fb + 24) \/ (PMSP.o_ec AD fb <= a < PMSP.o_ec AD fb + 16) \/ (0x674080 <= a < 0x674082) \/ (0x695ad0 <= a < 0x695cf0).
Proof.
  intros Hin Hr. unfold Wt in Hin. unfold L5.in_rng in Hr.
  destruct Hin as [<-|[<-|Hin]]; [cbn [fst snd] in Hr; left; exact Hr| cbn [fst snd] in Hr; right; left; exact Hr|].
  right; right. unfold PMSPA.err_W, PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit PeCLayoutA.CADDR_A] in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [left; exact Hr| right; clear - Hr; lia].
Qed.

Lemma keepf2 Mi : L5SAR.ek L ar LBc0 FF sp 20480 Wt M Mi ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mi (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s /\ PM.iss_at RSEGS AD PMSPA.accA Mi (PMSPA.o_is AD fb) str sm
  /\ L5.u64_at RSEGS Mi (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) /\ PMSTA.base_okA RSEGS AD Mi
  /\ PEC.content_ok RSEGS AD Mi fb p (PM.p_src s) str sm /\ PMSPA.accA Mi (PMSPA.o_p AD fb) PECA.RDR_BYTES.
Proof.
  intros EK. entry_facts. frame_facts. name_objs. set (op := PMSPA.o_p AD fb) in *. set (ois := PMSPA.o_is AD fb) in *.
  assert (Eop : op = fb + 592) by reflexivity. assert (Eois : ois = fb + 96) by reflexivity.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (BRc0 : forall x, In x LBc0 -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by (intros x Hx; apply BRB; apply INC0; exact Hx).
  assert (PINC : incl (PM.parser_own s) LBc0) by (unfold LBc0; apply incl_appl; apply incl_refl).
  assert (SINC : incl (PM.vs_own str) LBc0) by (unfold LBc0; apply incl_appr; exact INCS).
  pose proof wt_wapp as WAPP.
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply (PEAEKC.AOF FF fb FOK); clear - Eosk; lia).
  assert (AOEC : PMSPA.aobjA FF oec 16) by (apply (PEAEKC.AOF FF fb FOK); clear - Eoec; lia).
  assert (AOIS : PMSPA.aobjA FF ois 272) by (apply (PEAEKC.AOF FF fb FOK); clear - Eois; lia).
  assert (I8 : ois mod 8 = 0) by (rewrite Eois; replace (fb + 96) with (fb + 8 * 12) by (clear; lia); apply (PEAEKC.FB8 FF fb FOK)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ois 272 sp 20480 HH (PMKA.aobj_of_aobjA FF ois 272 AOIS I8) ltac:(clear; lia) ltac:(reflexivity)) as ((I1 & _) & _).
  assert (OUT : forall i, ~ (osk <= i < osk + 24) -> ~ (oec <= i < oec + 16) -> ~ (0x674080 <= i < 0x674082) -> ~ (0x695ad0 <= i < 0x695cf0) -> L5.outside Wt i).
  { intros i N1 N2 N3 N4 rr Hin Hr. destruct (wt_rng rr i Hin Hr) as [Y|[Y|[Y|Y]]]; [exact (N1 Y)| exact (N2 Y)| exact (N3 Y)| exact (N4 Y)]. }
  assert (OUTB : forall q m, In (q, m) LBc0 -> PMKA.blk_out Wt q m).
  { intros q m Hq i Hi. pose proof (INC0 _ Hq) as HqLB.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m osk 24 HH HqLB AOSK) as [Xa|Xa];
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HH HqLB AOEC) as [Xb|Xb];
    destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH HqLB) as [Xc|Xc]; apply OUT; clear - Xa Xb Xc Hi; lia. }
  assert (OUTO : forall a m, (a + m <= osk \/ osk + 24 <= a) -> (a + m <= oec \/ oec + 16 <= a) -> 0x698000 <= a -> forall i, a <= i < a + m -> L5.outside Wt i)
    by (intros a m Xa Xb Xc i Hi; apply OUT; clear - Xa Xb Xc Hi; lia).
  assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc0) by (apply PINC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  split.
  { apply (PMKA.parser_keepA RSEGS AD L ar LBc0 FF sp 20480 Wt M Mi EK WAPP FRB BRc0 op ois s (PEAEKC.AOF FF fb FOK op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)) PINC); [| | | | exact PA].
    - apply OUTO; clear - Eop Eosk Eoec Eois I1; lia.
    - apply OUTB. exact Iq.
    - apply OUTB. apply PINC. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
    - intros c n0 q E1. apply OUTB. apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E1. right; right; left. reflexivity. }
  split.
  { apply (PMKA.iss_keepA RSEGS AD L ar LBc0 FF sp 20480 Wt M Mi EK WAPP FRB BRc0 ois str sm AOIS SINC); [| | exact IA].
    - apply OUTO; clear - Eosk Eoec Eois I1; lia.
    - intros c n0 q E1. refine (OUTB q c _). apply SINC. unfold PM.vs_own. rewrite E1. left. reflexivity. }
  split.
  { apply (PMKA.u64_keepA RSEGS L ar LBc0 FF sp 20480 Wt M Mi EK WAPP FRB (op + 384) ov (PEAEKC.AOF FF fb FOK (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF].
    apply OUTO; clear - Eop Eov Eosk Eoec Eois I1; lia. }
  split.
  { apply (PMAPAR.base_keepW L ar C LY LBc0 FF sp 20480 Wt M Mi EK); [| | | | exact BASE].
    - intros a Ha. apply OUT; clear - Ha Eosk Eoec Eois I1; lia.
    - intros a Ha. apply OUT; clear - Ha Eosk Eoec Eois I1; lia.
    - apply OUT; clear - Eosk Eoec Eois I1; lia.
    - intros a Ha. apply OUT; clear - Ha Eosk Eoec Eois I1; lia. }
  split.
  { apply (PEAEKC.content_keepA' L ar LBc0 FF sp 20480 Wt M Mi fb p s str sm op EK WAPP FRB BRc0 AOIS); [| exact SINC| exact Iq| exact OUTB| exact IA| exact PA| exact CONT].
    fold ois. apply OUTO; clear - Eosk Eoec Eois I1; lia. }
  exact (PMKA.acc_keepA' L ar LBc0 FF sp 20480 Wt M Mi EK WAPP FRB op 392 (PEAEKC.AOF FF fb FOK op 392 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)) ACCR).
Qed.

Definition inve (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit) (ki : PESK.sink) : Prop :=
  FC Mi /\ L5CA.astk ar Mi sp 20480 /\ shadow_zero Mi (sp - 20480) 2560
  /\ model_rt model mdi /\ L5CA.amodel_ok Awi mdi /\ incl LKi LK /\ incl Aw Awi
  /\ ri_inv HI (PEC.owned s en ki ++ LBX) FF LKi cri Awi Mi (vml_of mdi)
  /\ PECA.enc_atA RSEGS EE L ar Mi (PMSPA.o_v AD fb) fb en /\ PESKA.sink_atA RSEGS L ar P Mi (PESK.o_sink EE fb) ki
  /\ xlo + 1 <= PESK.sk_z ki <= xhi + 1
  /\ L5SAR.ek L ar LBc0 FF sp 20480 Wt M Mi /\ L5SAR.dk L ar LBc0 FF sp 20480 M Mi
  /\ PMSP.credit_keep cr cri (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en ki)
  /\ PMSPA.ec_at RSEGS Mi (PMSPA.o_ec AD fb) 7 (pa_errcat_obj AD) /\ PESTA.err_okA RSEGS AD AAD EE Mi true.

Lemma ec_call (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  INV Mq mdq LKq Awq crq kq 1 ->
  getr Rq (reg 1) = Z_to_bv 64 0xac4a4 -> getr Rq (reg 2) = Z_to_bv 64 (sp - 96) -> getr Rq (reg 10) = Z_to_bv 64 (PMSPA.o_ec AD fb) -> getr Rq (reg 11) = Z_to_bv 64 7 -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2, inve M2 md2 LK2 Aw2 crq kq -> regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xac4a4 M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xae310 Mq mdq) K.
Proof.
  intros INVq Q1 Q2 Q10 Q11 QCS KX. entry_facts. frame_facts. name_objs.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  destruct (PEAEKC.keepf L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS Mq EKq)
    as (_ & _ & _ & BASEq & ERRq & _ & ECSq & _).
  assert (ECD : L5.defined Mq oec 16 /\ PMSPA.accA Mq oec 16).
  { unfold PECA.ec_stateA in ECSq. fold oec in ECSq.
    destruct xec; [destruct ECSq as (v0 & _ & (_ & _ & D' & A')); exact (conj D' A')| destruct ECSq as (_ & _ & D' & A'); exact (conj D' A')]. }
  set (LBq := PEC.owned s en kq ++ LBX) in *.
  assert (XINCq : incl LBc0 LBq) by (unfold LBc0, LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto).
  assert (EINCq : incl (PEC.enc_own en) LBq) by (unfold LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  assert (KINCq : incl (PESK.sink_own kq) LBq) by (unfold LBq, PEC.owned; intros x Hx; rewrite ?in_app_iff; tauto).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHq) as BRBq.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq) as FRBq.
  assert (AOSK : PMSPA.aobjA FF osk 24) by (apply (PEAEKC.AOF FF fb FOK); clear - Eosk; lia).
  assert (AOEC : PMSPA.aobjA FF oec 16) by (apply (PEAEKC.AOF FF fb FOK); clear - Eoec; lia).
  assert (K8 : osk mod 8 = 0) by (rewrite Eosk; replace (fb + 432) with (fb + 8 * 54) by (clear; lia); apply (PEAEKC.FB8 FF fb FOK)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq osk 24 sp 20480 HHq (PMKA.aobj_of_aobjA FF osk 24 AOSK K8) ltac:(clear; lia) ltac:(reflexivity)) as ((KOSK & _) & _).
  pose proof MKEC as MX. unfold PECSA.make_ec_spec, PECSPA.make_ec_spec in MX.
  unfold PMSPA.cfg.
  apply (MX fxq Rq Mq mdq K LBq FF LKq Awq crq oec 7 (sp - 96) 0xac4a4 e HHq AMq K0); clear MX.
  { split; [rewrite L5K.rl1; exact Q1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3, (QCS 3%nat CSK3); exact Rgp|]. split; [rewrite L5K.rl4, (QCS 4%nat CSK4); exact Rtp|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 20480 96 14336 ASTKq); [intros w D; exact D| clear; lia| clear; lia| clear; lia| exact SP16'].
    - apply (PMKA.shadow_zero_sub Mq (sp - 20480) 2560); [apply (PEAEKC.SPd8 sp SP32); reflexivity| | clear; lia| clear; lia| clear; lia| exact SZq].
      replace (sp - 96 - 14336) with (sp - 14432) by (clear; lia). apply (PEAEKC.SPd8 sp SP32). reflexivity. }
  { apply (PEAEKC.ffroomA_mono 4 1 FF LK LKq FRM ILKq NDFq). clear; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { clear; lia. }
  { exact AOEC. }
  { rewrite Eoec. replace (fb + 1120) with (fb + 8 * 140) by (clear; lia). apply (PEAEKC.FB8 FF fb FOK). }
  { exact (proj1 ECD). }
  { exact (proj2 ECD). }
  { exact BASEq. }
  { exact ERRq. }
  intros fx6 R6 M6 md6 LK6 Aw6 RP6 EC6 ERR6 HP6 MRT6 ILK6 IAW6 AM6 HH6.
  change (PMSPA.pm_scr 1) with 14336 in HP6.
  set (W2 := (oec, 16) :: (if e then [] else PMSPA.err_W AD)) in HP6.
  assert (W2R : forall rr a0, In rr W2 -> L5.in_rng rr a0 -> (oec <= a0 < oec + 16) \/ (0x674080 <= a0 < 0x674082) \/ (0x695ad0 <= a0 < 0x695cf0)).
  { intros rr a0 Hin Hr. unfold W2 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|Hin]; [left; cbn [fst snd] in Hr; exact Hr|]. right. destruct e; [destruct Hin|].
    unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PeCLayoutA.CADDR_A] in Hin.
    destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [left; exact Hr| right; clear - Hr; lia]. }
  assert (WT2 : forall a0, L5.outside Wt a0 -> L5.outside W2 a0).
  { intros a0 O rr Hin. unfold W2 in Hin. destruct Hin as [<-|Hin]; [apply O; unfold Wt; right; left; reflexivity|]. destruct e; [destruct Hin|].
    apply O. unfold Wt. right; right. exact Hin. }
  assert (OW2 : forall a0, sp - 20480 <= a0 < sp -> L5.outside W2 a0).
  { intros a0 Ha0 rr Hin Hr. destruct (W2R rr a0 Hin Hr) as [Y|[Y|Y]]; clear - Ha0 Y Eoec Eosk KOSK F2 FSCEIL SLO; lia. }
  assert (FRAME12 : forall a0, sp - 96 <= a0 < sp -> M6 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP6 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT; lia| intros Y; clear - Ha0 Y; lia].
    - apply OW2. clear - Ha0; lia. }
  assert (EK6 : L5SAR.ek L ar LBq FF sp 20480 W2 Mq M6).
  { apply (L5SAR.ek_callee L ar LBq [] FF [] sp 20480 (sp - 96) 14336 W2 W2 Mq M6 HP6); [clear; lia| clear; lia| intros a0 _ O; exact O]. }
  assert (DK6 : L5SAR.dk L ar LBq FF sp 20480 Mq M6) by (apply (L5SAR.dk_callee L ar LBq [] FF [] sp 20480 (sp - 96) 14336 W2 Mq M6 HP6); clear; lia).
  assert (ASTK6 : L5CA.astk ar M6 sp 20480).
  { apply (PMKA.astk_after_ahpres L ar LBq FF Mq M6 sp 20480 (sp - 96) 14336 W2 ASTKq HP6); [clear; lia| clear; lia| clear; lia| exact STOP]. }
  assert (WAPP2 : PMKA.wapp W2).
  { intros rr Hin. unfold W2 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; [cbn [fst snd]; clear - Eoec F1 F2 FSAPP; lia|].
    destruct e; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PeCLayoutA.CADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
  assert (SZ6 : shadow_zero M6 (sp - 20480) 2560).
  { apply (PMKA.stksh_keepA L ar LBq FF sp 20480 W2 Mq M6 EK6 WAPP2 (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply (PEAEKC.SPd8 sp SP32); reflexivity| clear; lia| exact SZq]. }
  assert (OUTB2 : forall q m, In (q, m) LBq -> forall i, q <= i < q + m -> L5.outside W2 i).
  { intros q m Hq i Hi rr Hin Hr. destruct (W2R rr i Hin Hr) as [Y|[Y|Y]].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HHq Hq AOEC) as [Z'|Z']; clear - Hi Y Z'; lia.
    - destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HHq Hq) as [Z'|Z']; clear - Hi Y Z'; lia.
    - destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HHq Hq) as [Z'|Z']; clear - Hi Y Z'; lia. }
  assert (EA6 : PECA.enc_atA RSEGS EE L ar M6 ov fb en).
  { apply (PECFA.enc_keepA RSEGS EE L ar LBq FF sp 20480 W2 Mq M6 EK6 WAPP2 FRBq BRBq ov fb en (PEAEKC.AOF FF fb FOK ov 56 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact EINCq| | exact EAq].
    - intros i Hi rr Hin Hr. destruct (W2R rr i Hin Hr) as [Y|[Y|Y]]; clear - Hi Y Eov Eoec Eosk KOSK; lia.
    - intros Hk. unfold PMKA.blk_out. apply OUTB2. apply EINCq. unfold PEC.enc_own. destruct (Z.eqb_spec (PEC.en_k en) 0) as [E0|E0]; [exfalso; clear - Hk E0; lia| left; reflexivity]. }
  assert (SKA6 : PESKA.sink_atA RSEGS L ar P M6 osk kq).
  { apply (PECFA.sink_keepA RSEGS L ar LBq FF sp 20480 W2 Mq M6 EK6 WAPP2 FRBq BRBq P osk kq AOSK); [| exact KINCq| | exact SKAq].
    - intros i Hi rr Hin Hr. destruct (W2R rr i Hin Hr) as [Y|[Y|Y]]; clear - Hi Y Eoec Eosk KOSK; lia.
    - intros Hk. unfold PMKA.blk_out. apply OUTB2. apply KINCq. unfold PESK.sink_own. destruct (Z.eqb_spec (PESK.sk_c kq) 0) as [E0|E0]; [exfalso; clear - Hk E0; lia| left; reflexivity]. }
  apply (KX fx6 R6 M6 md6 LK6 Aw6); [| exact RP6].
  unfold inve. split; [exact (FC_frame Mq M6 FRAME12 FCq)|]. split; [exact ASTK6|]. split; [exact SZ6|].
  split; [exact (L5LZ.model_rt_trans model mdq md6 MRTq MRT6)|]. split; [exact AM6|].
  split; [intros x Hx; apply ILKq; apply ILK6; exact Hx|]. split; [intros x Hx; apply IAW6; apply IAWq; exact Hx|].
  split; [exact HH6|].
  split; [exact EA6|]. split; [exact SKA6|]. split; [exact CLq|].
  split.
  { apply (L5SAR.ek_trans L ar LBc0 FF sp 20480 Wt M Mq M6).
    - exact (L5SAR.ek_W L ar LBc0 FF sp 20480 Wt Ws M Mq EKq wt_ws).
    - exact (L5SAR.ek_W L ar LBc0 FF sp 20480 Wt W2 Mq M6 (PMKA.ek_sublb L ar LBq LBc0 FF sp 20480 W2 Mq M6 XINCq EK6) WT2). }
  split; [exact (L5SAR.dk_trans L ar LBc0 FF sp 20480 M Mq M6 DKq (PMKA.dk_sublb L ar LBq LBc0 FF sp 20480 Mq M6 XINCq DK6))|].
  split; [exact CKq|]. split; [exact EC6| exact ERR6].
Qed.

Lemma vis_facts_e Mq mdq LKq Awq crq kq : inve Mq mdq LKq Awq crq kq ->
  let H := ahid Awq mdq in let MV := mrestrict H Mq in
  L5.img_clear MV 1253376 1286144 /\ L5.u64_at RSEGS MV 1317368 SBL /\ L5.u32_at RSEGS MV 1317376 1
  /\ 140735332487168 + 20480 <= sp <= 140737488355328 /\ sp mod 16 = 0 /\ L5.writable RSEGS MV (sp - 96) 96
  /\ (forall a0 v, sp - 96 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS Mq a0 v -> L5.u64_at RSEGS MV a0 v) /\ FC Mq.
Proof.
  intros INV6. entry_facts.
  pose proof INV6 as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & _).
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C Mq LYa ST) as (GOT & CSB & CUAR & _).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LKq crq Awq Mq mdq sp 20480 96 HHq ASTKq ltac:(clear; lia)) as (_ & _ & SWR).
  split; [apply L5A.img_clear_mrestrict; exact GOT|].
  split; [apply (proj2 (L5A.u64_at_vis H Mq 1317368 SBL (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
  split; [apply (proj2 (L5A.u32_at_vis H Mq 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
  split; [clear - SLO SHI SPT; lia|]. split; [exact (PEAEKC.A16' sp SP32)|]. split; [exact SWR|].
  split; [| exact FCq].
  intros a0 v Ha1 Ha2 U. apply (proj2 (L5A.u64_at_vis H Mq a0 v (VIS a0 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact U.
Qed.

Lemma fin_err (UVf : utf8_valid l = false) (fxq : FPState) Rq Mq mdq LKq Awq crq kq pcq (fx3 : FPState) R3 M3v :
  inve Mq mdq LKq Awq crq kq ->
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 r M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) -> regs_preserved R R3 ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INV6 MS3 MG3 FRZ3 RP3. entry_facts.
  pose proof INV6 as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq & ECq & ERRq).
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
  destruct (keepf2 Mq EKq) as (PA' & IA' & VREF' & BASE' & CONT' & ACCR').
  destruct CPRE as (_ & _ & _ & _ & _ & _ & _ & TBOK & _ & CL & _ & _ & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad X] in Lmore, Ldone, Ldepth, Lstk, Lpos, Lestk, Ledepth, Lz, Lbad.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq fxq fx3 Rq pcq R3 r M3v K HHq AMq MS3 MG3 FRZ3).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree Mq M3 AG3) as EM. subst M3.
  apply (KONTe UVf fx3 R3 Mq md3 LKq Awq en kq true crq).
  - exact RP3.
  - unfold PECA.crun_preA.
    split; [exact PA'|]. split; [exact IA'|]. split; [exact EAq|]. split; [exact VREF'|]. split; [exact SKAq|].
    split; [exact BASE'|]. split; [exact ERRq|]. split; [exact TBOK|]. split; [exact CONT'|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad XE].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
      split; [exact Lestk|]. split; [exact Ledepth|]. split; [clear - CLq; lia| exact Lbad]. }
    cbn [s_ec XE]. split; [unfold PECA.ec_stateA; exists 7; split; [clear; lia| exact ECq]|]. split; [intros _; reflexivity| exact ACCR'].
  - intros _; reflexivity.
  - change (PMSPA.pm_scr 4) with 20480. apply (L5SAR.ahpres_of L ar LBc0 FF sp 20480 _ M Mq); [| exact SDEFq| exact DKq].
    apply (L5SAR.ek_W L ar LBc0 FF sp 20480 _ Wt M Mq EKq). exact wt_wenc.
  - exact CKq.
  - exact (L5LZ.model_rt_trans model mdq md3 MRTq MRT3).
  - exact ILKq.
  - exact IAWq.
  - exact AM3.
  - exact HH3.
Qed.

Lemma ev_tail (UVt : utf8_valid l = true) (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  INV Mq mdq LKq Awq crq kq NB -> inregsE Rq sp (PMSPA.o_v AD fb) -> csk Rq ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xac52c Mq mdq) K.
Proof.
  intros INVq IRq QCS. entry_facts.
  pose proof (PEAEKC.vis_facts L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq mdq LKq Awq crq kq NB INVq)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8v & KR & K8 & KO & U24 & U32 & EB & SVV & FCq).
  cbv beta in SVV. set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (_ & _ & _ & _ & _ & Lestk & _). cbn [s_estk X] in Lestk.
  destruct FCq as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80).
  assert (FCv : fcells R r MV sp) by (unfold fcells; repeat split; (apply SVV; [clear; lia| clear; lia| assumption])).
  assert (OVR : 0 <= ov < 2 ^ 64) by (clear - OR; lia). assert (OKR : 0 <= osk < 2 ^ 64) by (clear - KR; lia). assert (SP0 : 0 <= sp < 2 ^ 64) by (clear - SPR; lia).
  assert (R0 : 0 <= r < 2 ^ 64) by (clear - Hr1; lia).
  assert (FS : fstat MV sp) by (split; [exact IC0|]; split; [exact CSBv|]; split; [exact CUARv|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR]).
  assert (FOVq : fov MV sp ov osk) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov|]; split; [exact Z8|]; split; [exact ODJ|]; split; [exact U8v|]; split; [exact KR| exact K8]).
  destruct xestk as [|e1 rr] eqn:HXS.
  - rewrite Lestk in U32. cbn [rev length Z.of_nat Z.mul] in U32. rewrite Z.add_0_r in U32.
    destruct (u_runE0 fxq Rq R MV sp ov osk (PEC.en_b en) r SP0 OVR OKR ltac:(clear - EB; lia) R0 IRq FS FOVq Z24 Z32 U24 U32 ltac:(clear - EB; lia) FCv RAok Rsp QCS)
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & RP3).
    exact (PEAEKC.finish_ro L ar C HI P LY HIok 96 NB HFR R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec [] xedepth xlo xhi xbad s str sm en k e
             HH ENT FOK FC CPRE INCS (KONTv UVt) NB 0xac52c fxq Rq Mq mdq LKq Awq crq kq fx3 R3 M3v INVq eq_refl eq_refl MS3 MG3 FRZ3 RP3).
  - pose proof (PEAEKC.vis_facts_top L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e
                  HH ENT FOK FC CPRE MP Mq mdq LKq Awq crq kq NB e1 rr INVq eq_refl)
      as (HLEN & EKP & EB1 & ED2 & ALend & ED3 & WR24 & EB6 & ZC & EDS & OVA & TCv & E1C & E1OK & BINe & EDC & EBC & _).
    cbv beta in HLEN, ED2, ALend, ED3, WR24, EB6, ZC, EDS, OVA, TCv, EDC. fold H MV ov in WR24, ZC, TCv, OVA, EDS. fold H in ZC. fold MV in ZC.
    rewrite HLEN in U32. set (ed := PEC.en_b en + 24 * (Z.of_nat (length rr) + 1)) in *.
    destruct (u_runE1 fxq Rq R MV sp ov osk (PEC.en_b en) ed (ei_cnt e1) r SP0 OVR OKR ltac:(clear - EB; lia) ltac:(clear - EB1 ED2; lia) E1C R0 IRq FS FOVq Z24 Z32 U24 U32
              ltac:(clear - EB EB1; lia) ltac:(clear - EB1 ED2 ED3; lia) ALend ED3 WR24 EB6 ZC EDS OVA TCv FCv RAok Rsp QCS)
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & RP3 & CC).
    exact (PEAEKC.finish_bump L ar C HI P LY HIok 96 NB HFR R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e
             HH ENT FOK FC CPRE INCS MP CRED (KONTv UVt) NB 0xac52c fxq Rq Mq mdq LKq Awq crq kq fx3 R3 M3v e1 rr INVq eq_refl eq_refl MS3 MG3 FRZ3 CC RP3).
Qed.

Lemma pbk (UVt : utf8_valid l = true) (m : nat) : forall (j : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq,
  Z.of_nat m = n - j -> 0 <= j < n ->
  INV Mq mdq LKq Awq crq kq (1 + pl_size n + j) ->
  inregsL Rq sp (PMSPA.o_v AD fb) ((PMSPA.o_v AD fb + 8) / 8 + SBL) ->
  getr Rq (reg 18) = Z_to_bv 64 (dptr + j) -> getr Rq (reg 20) = Z_to_bv 64 (dptr + j) -> getr Rq (reg 19) = Z_to_bv 64 (n - j) -> csk Rq ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xac4dc Mq mdq) K.
Proof.
  induction m as [|m IH]; intros j fxq Rq Mq mdq LKq Awq crq kq Hm Hj INVq IRq G18 G20 G19 QCS; [exfalso; clear - Hm Hj; lia|].
  entry_facts. frame_facts. pose proof PLS as HPL.
  pose proof INVq as (FCq & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & EAq & SKAq & CLq & EKq & DKq & CKq).
  pose proof (PEAEKC.vis_facts L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq mdq LKq Awq crq kq _ INVq)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8v & KR & K8 & KO & U24 & U32 & EB & SVV & _).
  cbv beta in SVV. set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  set (sh8 := (ov + 8) / 8 + SBL) in *.
  destruct (txt_keep Mq EKq) as (DEFq & ACCq & _). destruct txt_facts as (D0 & D47 & DNZ & DLOC).
  pose proof IRq as (G2 & G8 & G9 & G21 & G22).
  set (cur := dptr + j) in *.
  assert (CURR : 1 <= cur /\ cur + 1 <= dptr + n) by (subst cur; clear - Hj DNZ D0; lia).
  destruct (PMASR1.vis_scan L ar C HI LY HIok _ FF LKq crq Awq Mq mdq dptr n HHq (dloc_of kq DLOC) cur ltac:(subst cur; clear - Hj; lia)) as [VIS1 VIS2]. fold H in VIS1, VIS2.

  destruct (PEAENCK.u8_at_of_defined Mq cur ltac:(clear - CURR D47 D0; lia) (DEFq (cur - dptr) ltac:(subst cur; clear - Hj; lia))) as (b & Hb & U8b')
    || destruct (PEAENCK.u8_at_of_defined Mq cur ltac:(clear - CURR D47 D0; lia) ltac:(replace cur with (dptr + (cur - dptr)) by (clear; lia); apply DEFq; subst cur; clear - Hj; lia)) as (b & Hb & U8b').
  assert (U8b : L5.u8_at RSEGS MV cur b) by (apply (proj2 (L5A.u8_at_vis H Mq cur b ltac:(intros i Hi; replace (cur + i) with cur by (clear - Hi; lia); exact VIS1) ltac:(clear - CURR; lia) ltac:(clear - CURR D47; lia))); exact U8b').
  assert (SHB : exists kk, rdn RSEGS MV (Z_to_bv 64 (cur / 8 + SBL)) 1%nat = Some [Z_to_bv 8 kk] /\ (kk = 0 \/ (1 <= kk <= 7 /\ cur mod 8 < kk))).
  { assert (EMV : MV (Z_to_bv 64 (cur / 8 + SBL)) = Mq (Z_to_bv 64 (cur / 8 + SBL))) by (unfold MV, mrestrict; change (cur / 8 + SBL) with (HeapIfaceA.S cur); rewrite VIS2; reflexivity).
    destruct (ACCq cur ltac:(subst cur; clear - Hj; lia)) as [B0|(v & Bv & Hv & Hm')].
    - exists 0. split; [| left; reflexivity]. cbn [rdn]. rewrite EMV. unfold byte_at, HeapIfaceA.S, HeapIfaceA.SB in B0. rewrite B0. reflexivity.
    - exists v. split; [| right; split; [exact Hv| exact Hm']]. cbn [rdn]. rewrite EMV. unfold byte_at, HeapIfaceA.S, HeapIfaceA.SB in Bv. rewrite Bv. reflexivity. }
  destruct SHB as (kk & RD & Hkk).

  destruct (chk1s fxq Rq MV cur kk G18 G21 ltac:(clear - CURR D47; lia) RD Hkk) as (Rc & MSc & KSc).

  assert (SP0 : 0 <= sp < 2 ^ 64) by (clear - SPR; lia). assert (OVR : 0 <= ov < 2 ^ 64) by (clear - OR; lia). assert (OKR : 0 <= osk < 2 ^ 64) by (clear - KR; lia).
  assert (SH8R : 2147451393 <= sh8 <= 19791209299968) by (subst sh8; clear - OR; Lia.lia).
  assert (FS : fstat MV sp) by (split; [exact IC0|]; split; [exact CSBv|]; split; [exact CUARv|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR]).
  assert (FOVq : fov MV sp ov osk) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov|]; split; [exact Z8|]; split; [exact ODJ|]; split; [exact U8v|]; split; [exact KR| exact K8]).
  assert (IRc : inregsL Rc sp ov sh8) by (split; [rewrite (KSc 2%nat) by lia; exact G2|]; split; [rewrite (KSc 8%nat) by lia; exact G8|]; split; [rewrite (KSc 9%nat) by lia; exact G9|]; split; [rewrite (KSc 21%nat) by lia; exact G21| rewrite (KSc 22%nat) by lia; exact G22]).
  assert (CUP : cur + 1 <= sp - 96).
  { destruct LOC as [(B & m' & Hin & X1 & X2)|[(X1 & X2)|[(X1 & X2)|(X1 & X2)]]].
    - assert (HinLB : In (B, m') LB) by (unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hin).
      pose proof (WB _ HinLB) as ((_ & _ & _ & _ & Xc & _) & _). cbn [fst snd] in Xc. clear - CURR X2 Xc SLO. lia.
    - unfold PMSPA.o_tb, PMSPA.o_p in X2. cbn [pa_off_p PeCLayoutA.CADDR_A] in X2. clear - CURR X2 F2 FSCEIL SLO. lia.
    - exfalso. unfold n in Hj. rewrite X2 in Hj. cbn in Hj. clear - Hj. lia.
    - pose proof X1 as (f & Hf & Y1 & Y2). pose proof (WF f Hf) as (W1 & W2 & _). unfold FS_BYTES in W2. clear - CURR Y2 W2 FSCEIL SLO. lia. }
  destruct (u_runE fxq Rc MV sp ov osk sh8 cur (n - j) b SP0 OVR OKR ltac:(clear - SH8R; lia) ltac:(clear - CURR CUP SPR D47; lia) ltac:(clear - Hj N26; lia) ltac:(clear - Hb; lia) IRc
              ltac:(rewrite (KSc 18%nat) by lia; exact G18) ltac:(rewrite (KSc 20%nat) by lia; exact G20) ltac:(rewrite (KSc 19%nat) by lia; exact G19)
              FS FOVq Z8 SH8R ltac:(clear - CURR CUP SPR D47; lia) ltac:(clear - Hj N26; lia) U8b Hb ltac:(left; exact CUP))
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & S18 & S19 & S20 & T1 & T10 & T11 & C81).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq fxq fx3 Rq 0xac4dc R3 0xaf02c M3v (fun a0 => sp - 81 <= a0 < sp - 81 + 1) K HHq AMq
           ltac:(eapply msteps_trans; [exact MSc| exact MS3]) MG3).
  { intros a0 Ha0 Hn. apply FRZ3; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
    - clear - Wa SLO SPT; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV M3 md3 LKq Awq crq kq (1 + pl_size n + j)).
  { apply (PEAEKC.inv_frame L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq M3 mdq md3 LKq Awq crq kq (1 + pl_size n + j) (sp - 81) (sp - 81 + 1) INVq);
      [clear; lia| clear; lia| exact MGM3| exact FR3| exact (FC_but Mq M3 (sp - 81) (sp - 81 + 1) ltac:(clear; lia) FR3 FCq)| exact HH3| exact AM3| exact MRT3]. }
  assert (IR3 : inregsL R3 sp ov sh8) by exact (inregsL_kept Rc R3 sp ov sh8 CSI IRc KS3 ltac:(intros jj Hjj; cbn in Hjj; decompose [or] Hjj; try contradiction; subst; inl)).
  pose proof IR3 as (G2' & _).
  assert (QCS3 : csk R3).
  { apply (csk_keptI Rc R3); [| exact KS3]. intros jj Hjj. rewrite (KSc jj) by (revert Hjj; clear; intros Hjj; cbn in Hjj; decompose [or] Hjj; try contradiction; subst; lia). exact (QCS jj Hjj). }
  apply (PEAEKC.pb_call L ar C HI P LY HIok PO PB 96 CSK HFR CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb xlo xhi s en k HH K0 ENT FRM FRS FOK SP32 FC FC_frame CRED
           (1 + pl_size n + j) (sp - 81) (xhi + NB) 0xac508 fx3 R3 M3 md3 LKq Awq crq kq INV3 (HBN UVt) ltac:(unfold NB; clear - Hj; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(split; [clear; lia| reflexivity]) T1 G2' T10 T11 QCS3).
  intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 RP4.
  replace (1 + pl_size n + j + 1) with (1 + pl_size n + (j + 1)) in INV4 by (clear; lia).
  pose proof (csk_after R3 R4 QCS3 RP4) as QCS4.
  assert (IR4 : inregsL R4 sp ov sh8).
  { destruct IR3 as (I2 & I8 & I9 & I21 & I22). pose proof (fun jj Hjj => L5SAR.cs_of_preserved R3 R4 jj RP4 Hjj) as R4c.
    split; [rewrite (R4c 2%nat) by inl; exact I2|]. split; [rewrite (R4c 8%nat) by inl; exact I8|]. split; [rewrite (R4c 9%nat) by inl; exact I9|].
    split; [rewrite (R4c 21%nat) by inl; exact I21| rewrite (R4c 22%nat) by inl; exact I22]. }
  assert (F18 : getr R4 (reg 18) = Z_to_bv 64 cur) by (rewrite (L5SAR.cs_of_preserved R3 R4 18 RP4) by inl; rewrite S18, (KSc 18%nat) by lia; exact G18).
  assert (F20 : getr R4 (reg 20) = Z_to_bv 64 cur) by (rewrite (L5SAR.cs_of_preserved R3 R4 20 RP4) by inl; rewrite S20, (KSc 20%nat) by lia; exact G20).
  assert (F19 : getr R4 (reg 19) = Z_to_bv 64 (n - j)) by (rewrite (L5SAR.cs_of_preserved R3 R4 19 RP4) by inl; rewrite S19, (KSc 19%nat) by lia; exact G19).
  pose proof INV4 as (FC4 & _ & _ & _ & AM4 & _ & _ & HH4 & _).
  pose proof (PEAEKC.vis_facts L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC M4 md4 LK4 Aw4 cr4 k4 _ INV4)
    as (IC4 & CSB4 & CUAR4 & _ & _ & SWR4 & _).
  set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  assert (FS4 : fstat MV4 sp) by (split; [exact IC4|]; split; [exact CSB4|]; split; [exact CUAR4|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR4]).
  destruct (Z.eq_dec (j + 1) n) as [LAST|MORE].
  -
    replace (n - j) with 1 in F19 by (clear - LAST; lia).
    destruct (u_runM0 fx4 R4 MV4 sp ov sh8 cur SP0 OVR ltac:(clear - SH8R; lia) ltac:(clear - CURR CUP SPR D47; lia) IR4 F18 F20 F19 FS4 ltac:(clear - CURR CUP SPR D47; lia))
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & KS5 & IRE5).
    apply (step_ro (1 + pl_size n + (j + 1)) fx4 R4 M4 md4 LK4 Aw4 cr4 k4 0xac508 0xac52c fx5 R5 M5v INV4 MS5 MG5 FRZ5).
    intros md5 INV5. rewrite LAST in INV5. replace (1 + pl_size n + n) with NB in INV5 by (unfold NB; clear; lia).
    exact (ev_tail UVt fx5 R5 M4 md5 LK4 Aw4 cr4 k4 INV5 IRE5 (csk_keptI R4 R5 QCS4 KS5)).
  -
    destruct (u_runM1 fx4 R4 MV4 sp ov sh8 cur (n - j) SP0 OVR ltac:(clear - SH8R; lia) ltac:(clear - CURR CUP SPR D47; lia) ltac:(clear - Hj N26; lia) IR4 F18 F20 F19 FS4
              ltac:(clear - CURR CUP SPR D47; lia) ltac:(clear - Hj MORE N26; lia))
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & KS5 & IRL5 & T18 & T20 & T19).
    apply (step_ro (1 + pl_size n + (j + 1)) fx4 R4 M4 md4 LK4 Aw4 cr4 k4 0xac508 0xac4dc fx5 R5 M5v INV4 MS5 MG5 FRZ5).
    intros md5 INV5.
    apply (IH (j + 1) fx5 R5 M4 md5 LK4 Aw4 cr4 k4); [clear - Hm MORE Hj; lia| clear - Hj MORE; lia| exact INV5| exact IRL5| | | | exact (csk_keptI R4 R5 QCS4 KS5)].
    + rewrite T18. f_equal. subst cur. clear; lia.
    + rewrite T20. f_equal. subst cur. clear; lia.
    + rewrite T19. f_equal. clear; lia.
Qed.

Lemma main : srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xac3d8 M model) K.
Proof.
  entry_facts. frame_facts. pose proof AM as (Mh & MI). pose proof PLS as HPL. pose proof N0 as HN0.
  destruct txt_facts as (D0 & D47 & DNZ & DLOC).
  pose proof (PEAEKC.vis_entry L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 A10 CPRE)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8v & KR & K8 & KO & G2 & G10 & G1 & RAr & RB).
  cbv beta in RB. set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *. set (oec := PMSPA.o_ec AD fb) in *.
  set (sh8 := (ov + 8) / 8 + SBL).
  assert (SP0 : 0 <= sp < 2 ^ 64) by (clear - SPR; lia). assert (OVR : 0 <= ov < 2 ^ 64) by (clear - OR; lia). assert (OKR : 0 <= osk < 2 ^ 64) by (clear - KR; lia).
  assert (SH8R : 0 <= sh8 < 2 ^ 64) by (subst sh8; clear - OR; Lia.lia).
  assert (FS : fstat MV sp) by (split; [exact IC0|]; split; [exact CSBv|]; split; [exact CUARv|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR]).
  assert (FOV0 : fov MV sp ov osk) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov|]; split; [exact Z8|]; split; [exact ODJ|]; split; [exact U8v|]; split; [exact KR| exact K8]).

  assert (INV0like : fsv MV sp sv dptr n).
  { pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
    pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model sv 16 sp 20480 HH (PMKA.aobj_of_aobjA FF sv 16 AOSV SV8) ltac:(clear; lia) ltac:(reflexivity))
      as ((S1 & S2 & S3 & S4 & S5) & SBIG & SDEF' & SVIS & SVSH & SCL & SCLSH).
    pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model sv 16 HH AOSV SV8 ltac:(clear; lia) ltac:(reflexivity) ACSV) as ZS. change (16 / 8) with 2 in ZS.
    unfold fsv. split; [clear - S1 S3; lia|]. split; [exact SV8|]. split; [clear - SBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia|]. split; [exact ZS|].
    split. { intros jj Hjj. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
             replace ((sv + 8) / 8 + SBL + jj) with (sv / 8 + HeapIfaceA.SB + 1) by (unfold HeapIfaceA.SB; clear - SV8 Hjj; Lia.lia). apply (ZS 1). clear; Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split; [left; clear - S2 SLO; lia|].
    split; [exact (proj2 (L5A.u64_at_vis _ M sv dptr (L5A.avis_sub _ sv 16 sv 8 SVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - S1; lia) ltac:(clear - S3; lia)) U0)|].
    split; [exact (proj2 (L5A.u64_at_vis _ M (sv + 8) n (L5A.avis_sub _ sv 16 (sv + 8) 8 SVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - S1; lia) ltac:(clear - S3; lia)) U8)|].
    split; [clear - D0 D47 HN0; lia| clear - HN0 N26; lia]. }
  pose proof INV0like as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  assert (SVR : 0 <= sv < 2 ^ 64) by (clear - V1; lia). assert (ECR : 0 <= oec < 2 ^ 64) by (subst oec; unfold PMSPA.o_ec; cbn [pa_off_ec PeCLayoutA.CADDR_A]; clear - F1 F2 FSAPP FSCEIL SLO SPR; lia).
  assert (DPR : 0 <= dptr < 2 ^ 64) by (clear - V9; lia). assert (NR : 0 <= n < 2 ^ 64) by (clear - V10; lia). assert (TGR : 0 <= tg < 2 ^ 64) by (clear - TG; lia).

  assert (RA : exists byo mk, (byo = -83 \/ byo = -82) /\ exists (fx' : FPState) R' M', mem_grows MV M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp - 96 + 96) -> M' (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac3d8 MV) (mst fx' R' 0xaf02c M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 0xac460 /\ inregsM R' sp ov sv oec sh8 /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp + byo)
      /\ L5.u8_at RSEGS M' (sp + byo) mk /\ fcells R r M' sp).
  { destruct (Z_lt_ge_dec tg 2) as [T1|T1]; [| destruct (Z_lt_ge_dec tg 4) as [T2|T2]].
    - exists (-82), 83. split; [right; reflexivity|]. exact (u_runAs0 fx R MV sp ov osk sv tg oec r SP0 OVR OKR SVR TGR ECR G2 G10 A11 A12 A14 G1 RAr FS FOV0 ltac:(clear - T1 TG; lia) ltac:(clear - V1; lia)).
    - exists (-83), 72. split; [left; reflexivity|]. exact (u_runAh fx R MV sp ov osk sv tg oec r SP0 OVR OKR SVR TGR ECR G2 G10 A11 A12 A14 G1 RAr FS FOV0 ltac:(clear - T1 T2; lia) ltac:(clear - V1; lia)).
    - exists (-82), 83. split; [right; reflexivity|]. exact (u_runAs4 fx R MV sp ov osk sv tg oec r SP0 OVR OKR SVR TGR ECR G2 G10 A11 A12 A14 G1 RAr FS FOV0 ltac:(clear - T2 TG; lia) ltac:(clear - V1; lia)). }
  destruct RA as (byo & mk & BYO & fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & IR1 & T10 & T11 & B1 & FC1).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xac3d8 R1 0xaf02c M1v (fun a0 => sp - 96 <= a0 < sp - 96 + 96) K HH AM MS1 MG1).
  { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
    - clear - Wa SLO SPT; lia. }
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (FCM1 : FC M1).
  { destruct FC1 as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80). rewrite <- VIS1 in C8, C16, C24, C32, C40, C48, C56, C64, C72, C80.
    unfold FC, fcells. repeat split; (apply RB; [clear; lia| clear; lia| assumption]). }
  pose proof (PEAEKC.inv_start L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 FC CPRE
                M1 md1 MGM1 FR1 FCM1 HH1 AM1 MRT1) as INV1.
  pose proof IR1 as (Q2 & _).
  assert (QCS1 : csk R1) by (intros jj Hjj; exact (KS1 jj Hjj)).

  apply (PEAEKC.pb_call L ar C HI P LY HIok PO PB 96 CSK HFR CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb xlo xhi s en k HH K0 ENT FRM FRS FOK SP32 FC FC_frame CRED
           0 (sp + byo) (xhi + 1) 0xac460 fx1 R1 M1 md1 LK Aw cr k INV1 HB1 ltac:(clear; lia) ltac:(clear - BYO; lia) ltac:(clear - BYO; lia) ltac:(split; [clear; lia| reflexivity]) T1 Q2 T10 T11 QCS1).
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 RP2. change (0 + 1) with 1 in INV2.
  pose proof (inregsM_after R1 R2 sv oec sh8 IR1 RP2) as IR2. pose proof (csk_after R1 R2 QCS1 RP2) as QCS2.

  pose proof (PEAEKC.vis_facts L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC M2 md2 LK2 Aw2 cr2 k2 1 INV2)
    as (IC2 & CSB2 & CUAR2 & _ & _ & SWR2 & _ & _ & _ & Zov2 & _ & _ & Z82 & _ & _ & U82 & _).
  set (H2 := ahid Aw2 md2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (FS2 : fstat MV2 sp) by (split; [exact IC2|]; split; [exact CSB2|]; split; [exact CUAR2|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR2]).
  assert (FOV2 : fov MV2 sp ov osk) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov2|]; split; [exact Z82|]; split; [exact ODJ|]; split; [exact U82|]; split; [exact KR| exact K8]).
  pose proof (sv_facts M2 md2 LK2 Aw2 cr2 k2 1 INV2) as FSV2. fold H2 MV2 in FSV2.
  destruct (u_runB fx2 R2 MV2 sp ov osk sv oec sh8 dptr n SP0 OVR OKR SVR ECR SH8R DPR NR IR2 FS2 FOV2 FSV2)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & IRV3 & T1' & T10' & T11').
  apply (step_ro 1 fx2 R2 M2 md2 LK2 Aw2 cr2 k2 0xac460 0xb1068 fx3 R3 M3v INV2 MS3 MG3 FRZ3).
  intros md3 INV3.
  pose proof (csk_keptI R2 R3 QCS2 KS3) as QCS3. pose proof IRV3 as ((Q2' & _) & _).

  apply (val_call 1 fx3 R3 M2 md3 LK2 Aw2 cr2 k2 INV3 T1' Q2' T10' T11' QCS3).
  intros fx4 R4 M4 md4 v INV4 RP4 V11 Hv HV.
  pose proof (inregsV_after R3 R4 sv oec sh8 IRV3 RP4) as IRV4. pose proof (csk_after R3 R4 QCS3 RP4) as QCS4.
  pose proof (PEAEKC.vis_facts L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC M4 md4 LK2 Aw2 cr2 k2 1 INV4)
    as (IC4 & CSB4 & CUAR4 & _ & _ & SWR4 & _ & _ & _ & Zov4 & _ & _ & Z84 & _ & _ & U84 & _).
  set (H4 := ahid Aw2 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  assert (FS4 : fstat MV4 sp) by (split; [exact IC4|]; split; [exact CSB4|]; split; [exact CUAR4|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR4]).
  assert (FOV4 : fov MV4 sp ov osk) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov4|]; split; [exact Z84|]; split; [exact ODJ|]; split; [exact U84|]; split; [exact KR| exact K8]).
  pose proof (sv_facts M4 md4 LK2 Aw2 cr2 k2 1 INV4) as FSV4. fold H4 MV4 in FSV4.
  destruct (Z.eq_dec v 0) as [V0|V0].
  -
    assert (UVt : utf8_valid l = true) by (apply (proj1 HV); exact V0). rewrite V0 in V11.
    destruct (u_runCo fx4 R4 MV4 sp ov osk sv oec sh8 dptr n SP0 OVR OKR SVR ECR SH8R DPR NR IRV4 V11 FS4 FOV4 FSV4)
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & KS5 & IRV5 & T1'' & T10'' & T11'').
    apply (step_ro 1 fx4 R4 M4 md4 LK2 Aw2 cr2 k2 0xac490 0xae710 fx5 R5 M5v INV4 MS5 MG5 FRZ5).
    intros md5 INV5.
    pose proof (csk_keptI R4 R5 QCS4 KS5) as QCS5. pose proof IRV5 as ((Q2'' & _) & _).

    apply (pl_call UVt fx5 R5 M4 md5 LK2 Aw2 cr2 k2 INV5 T1'' Q2'' T10'' T11'' QCS5).
    intros fx6 R6 M6 md6 LK6 Aw6 cr6 k6 INV6 RP6.
    pose proof (inregsV_after R5 R6 sv oec sh8 IRV5 RP6) as IRV6. pose proof (csk_after R5 R6 QCS5 RP6) as QCS6.
    pose proof (PEAEKC.vis_facts L ar C HI P LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC M6 md6 LK6 Aw6 cr6 k6 _ INV6)
      as (IC6 & CSB6 & CUAR6 & _ & _ & SWR6 & _ & _ & _ & Zov6 & _ & _ & Z86 & _ & _ & U86 & _).
    set (H6 := ahid Aw6 md6) in *. set (MV6 := mrestrict H6 M6) in *.
    assert (FS6 : fstat MV6 sp) by (split; [exact IC6|]; split; [exact CSB6|]; split; [exact CUAR6|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR6]).
    assert (FOV6 : fov MV6 sp ov osk) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov6|]; split; [exact Z86|]; split; [exact ODJ|]; split; [exact U86|]; split; [exact KR| exact K8]).
    pose proof (sv_facts M6 md6 LK6 Aw6 cr6 k6 _ INV6) as FSV6. fold H6 MV6 in FSV6.
    destruct (Z.eq_dec n 0) as [NZ0|NZ1].
    +
      assert (FSV6' : fsv MV6 sp sv dptr 0) by (rewrite <- NZ0; exact FSV6).
      destruct (u_runD0 fx6 R6 MV6 sp ov osk sv oec sh8 dptr SP0 OVR OKR SVR ECR SH8R DPR IRV6 FS6 FOV6 FSV6')
        as (fx7 & R7 & M7v & MG7 & FRZ7 & MS7 & KS7 & IRE7).
      apply (step_ro (1 + pl_size n) fx6 R6 M6 md6 LK6 Aw6 cr6 k6 0xac4bc 0xac52c fx7 R7 M7v INV6 MS7 MG7 FRZ7).
      intros md7 INV7. replace (1 + pl_size n) with NB in INV7 by (unfold NB; rewrite NZ0; clear; lia).
      exact (ev_tail UVt fx7 R7 M6 md7 LK6 Aw6 cr6 k6 INV7 IRE7 (csk_keptI R6 R7 QCS6 KS7)).
    +
      assert (D1 : 1 <= dptr <= 140737488355326).
      { split; [clear - DNZ NZ1 HN0; lia|].
        destruct LOC as [(B & m' & Hin & X1 & X2)|[(X1 & X2)|[(X1 & X2)|(X1 & X2)]]].
        - assert (HinLB : In (B, m') LB) by (unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hin).
          pose proof (WB _ HinLB) as ((_ & _ & _ & _ & Xc & _) & _). cbn [fst snd] in Xc. clear - X1 X2 Xc SLO SHI SPT HN0. lia.
        - unfold PMSPA.o_tb, PMSPA.o_p in X2. cbn [pa_off_p PeCLayoutA.CADDR_A] in X2. clear - X2 F2 FSCEIL SLO SHI SPT HN0. lia.
        - exfalso. apply NZ1. unfold n. rewrite X2. reflexivity.
        - pose proof X1 as (f & Hf & Y1 & Y2). pose proof (WF f Hf) as (W1 & W2 & _). unfold FS_BYTES in W1, W2. clear - Y1 Y2 W1 W2 FSCEIL FSAPP SLO SHI SPT HN0; lia. }
      destruct (u_runD1 fx6 R6 MV6 sp ov osk sv oec sh8 dptr n SP0 OVR OKR SVR ECR SH8R DPR NR IRV6 FS6 FOV6 FSV6 ltac:(clear - NZ1 HN0; lia) D1)
        as (fx7 & R7 & M7v & MG7 & FRZ7 & MS7 & KS7 & IRL7 & T18 & T20 & T19).
      apply (step_ro (1 + pl_size n) fx6 R6 M6 md6 LK6 Aw6 cr6 k6 0xac4bc 0xac4dc fx7 R7 M7v INV6 MS7 MG7 FRZ7).
      intros md7 INV7.
      apply (pbk UVt (Z.to_nat n) 0 fx7 R7 M6 md7 LK6 Aw6 cr6 k6); [rewrite Z2Nat.id by (clear - HN0; lia); clear; lia| clear - NZ1 HN0; lia| replace (1 + pl_size n + 0) with (1 + pl_size n) by (clear; lia); exact INV7| exact IRL7| | | | exact (csk_keptI R6 R7 QCS6 KS7)].
      * rewrite T18. f_equal. clear; lia.
      * rewrite T20. f_equal. clear; lia.
      * rewrite T19. f_equal. clear; lia.
  -
    assert (UVf : utf8_valid l = false) by (destruct (utf8_valid l); [exfalso; apply V0; apply (proj2 HV); reflexivity| reflexivity]).
    destruct (u_runCe fx4 R4 MV4 sp ov sv oec sh8 v SP0 OVR SVR ECR SH8R ltac:(clear - Hv; lia) IRV4 V11 FS4 ltac:(clear - Hv V0; lia))
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & KS5 & IRV5 & T1'' & T10'' & T11'').
    apply (step_ro 1 fx4 R4 M4 md4 LK2 Aw2 cr2 k2 0xac490 0xae310 fx5 R5 M5v INV4 MS5 MG5 FRZ5).
    intros md5 INV5.
    pose proof (csk_keptI R4 R5 QCS4 KS5) as QCS5. pose proof IRV5 as ((Q2'' & _) & _).
    apply (ec_call fx5 R5 M4 md5 LK2 Aw2 cr2 k2 INV5 T1'' Q2'' T10'' T11'' QCS5).
    intros fx6 R6 M6 md6 LK6 Aw6 INV6 RP6.
    pose proof (inregsE_afterV R5 R6 sv oec sh8 IRV5 RP6) as IRE6. pose proof (csk_after R5 R6 QCS5 RP6) as QCS6.
    pose proof (vis_facts_e M6 md6 LK6 Aw6 cr2 k2 INV6) as (IC6 & CSB6 & CUAR6 & _ & _ & SWR6 & SVV6 & FC6). cbv beta in SVV6.
    set (H6 := ahid Aw6 md6) in *. set (MV6 := mrestrict H6 M6) in *.
    assert (FS6 : fstat MV6 sp) by (split; [exact IC6|]; split; [exact CSB6|]; split; [exact CUAR6|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR6]).
    assert (R0 : 0 <= r < 2 ^ 64) by (clear - Hr1; lia).
    destruct FC6 as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80).
    assert (FCv : fcells R r MV6 sp) by (unfold fcells; repeat split; (apply SVV6; [clear; lia| clear; lia| assumption])).
    destruct (u_runR fx6 R6 R MV6 sp ov r SP0 OVR R0 IRE6 FS6 FCv RAok Rsp QCS6) as (fx7 & R7 & M7v & MG7 & FRZ7 & MS7 & RP7).
    exact (fin_err UVf fx6 R6 M6 md6 LK6 Aw6 cr2 k2 0xac4a4 fx7 R7 M7v INV6 MS7 MG7 FRZ7 RP7).
Qed.
End Call.

Theorem v_string_ok : PECSA.v_string_spec L ar HI P.
Proof.
  unfold PECSA.v_string_spec, PECSPA.v_string_spec, PECSPA.eslot_spec. cbn [pe_string EE PeCLayoutA.EADDR_A].
  intros PMODE d fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 AK CPRE INCS POK MP NB HB CRED KONT.
  destruct AK as ((sv & A11 & SV8 & AOSV & ACSV & SVF & U0 & U8 & BYT & BOK & N26 & DEF & ACC & LOC) & A14 & (tg & TG & A12)).
  rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12. rewrite L5K.rl14 in A14.
  destruct d as [dptr l]. cbn [fst snd] in *.
  destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad].
  assert (N26' : Z.of_nat (length l) < 2 ^ 26) by exact N26.
  destruct (utf8_valid l) eqn:UVl.
  - assert (ESTR : e_string true (Z.of_nat (length l)) (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad)
            = e_end_value (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + (1 + (pl_size (Z.of_nat (length l)) + Z.of_nat (length l)))) (xhi + (1 + (pl_size (Z.of_nat (length l)) + Z.of_nat (length l)))) xbad)).
    { unfold e_string, e_put_length. replace (INT64_MAX <? Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; unfold INT64_MAX; clear - N26'; lia).
      unfold w_out. cbn [s_stk s_pos s_more s_done s_halt s_depth s_ec s_estk s_edepth s_lo s_hi s_bad]. f_equal. f_equal; clear; lia. }
    rewrite ESTR in HB, KONT.
    assert (HB1 : PESKA.spa_hb P (xhi + 1)).
    { apply (PESKA.spao_hb_mono L P PO _ _ HB). unfold e_end_value. cbn [s_estk s_hi]. pose proof (PLS l) as HPL; pose proof (N0 l) as HN0; destruct xestk; cbn [s_hi w_estk]; clear - HPL HN0; lia. }
    refine (main PMODE dptr sv tg l fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
             HH AM K0 ENT FRM FRS FOK SP32 A10 A11 A12 TG A14 SV8 SVF AOSV ACSV U0 U8 BYT BOK N26 DEF ACC LOC CPRE INCS POK MP HB1 _ CRED _ _).
    + intros _. revert HB. unfold e_end_value. cbn [s_estk s_hi]. destruct xestk; cbn [s_hi w_estk]; intros HB; exact HB.
    + intros _. exact KONT.
    + intros E. exfalso. rewrite UVl in E. discriminate E.
  - assert (ESTR : e_string false (Z.of_nat (length l)) (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad)
            = ST xstk xpos xmore xdone xhalt xdepth true xestk xedepth (xlo + 1) (xhi + 1) xbad) by reflexivity.
    rewrite ESTR in HB, KONT. cbn [s_hi] in HB.
    refine (main PMODE dptr sv tg l fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
             HH AM K0 ENT FRM FRS FOK SP32 A10 A11 A12 TG A14 SV8 SVF AOSV ACSV U0 U8 BYT BOK N26 DEF ACC LOC CPRE INCS POK MP HB _ CRED _ _).
    + intros E. exfalso. rewrite UVl in E. discriminate E.
    + intros E. exfalso. rewrite UVl in E. discriminate E.
    + intros _. exact KONT.
Qed.
End WithHeap.
End PEAENCST.
