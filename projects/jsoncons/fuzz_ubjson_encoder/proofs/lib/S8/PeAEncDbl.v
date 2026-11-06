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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PmModelFactsA PmStep PeStepA PmParKit PeASrcKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrame PeCFrameA PeEncKit PeACReset1 PeAEncNtbSpec PeAEncNtbFSpec PeAEncNtbF PeAEncKitD FPSteps PeFPSteps PeAEncDblP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_ab7a4_ab7ac Ea0_code_ab7d0_ab7d8 Ea0_code_ab7dc_ab7e4 Ea0_code_ab7f8_ab7fc Ea0_code_ab818_ab81c Ea0_code_ab88c_ab894 Ea0_code_ab898_ab89c.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAENCD.
#[local] Transparent e_end_value.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).
Abbreviation SBL := 2147450880.
Abbreviation PB := 0xaf02c.
Abbreviation EV := 0xab874.
Abbreviation WF32 := 0xb0c38.
Abbreviation WF64 := 0xb0cf0.

Definition CSK : list nat := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition CSI : list nat := [2; 8; 9; 18; 3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.
Lemma writable_grows M M' a n : mem_grows M M' -> L5.writable RSEGS M a n -> L5.writable RSEGS M' a n.
Proof. intros G W d k Hd Hk. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Lemma bvs12 (i : bv 12) z : bv_signed i = z -> forall x, x + bv_signed i = x + z. Proof. intros -> x. reflexivity. Qed.

Definition inregs (R : bvmap 5 word) (sp ov : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 8) = Z_to_bv 64 ov /\ getr R (reg 9) = Z_to_bv 64 (ov + 8) /\ getr R (reg 18) = Z_to_bv 64 SBL.
Definition fstat (M : word -> option byte) (sp : Z) : Prop :=
  L5.img_clear M 1253376 1286144 /\ L5.u64_at RSEGS M 1317368 SBL /\ L5.u32_at RSEGS M 1317376 1 /\ 140735332487232 <= sp <= 140737488355328 /\ sp mod 16 = 0
  /\ L5.writable RSEGS M (sp - 64) 64.
Definition fov (M : word -> option byte) (sp ov osk : Z) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5.writable RSEGS M ov 56 /\ ((sp - 64) + 64 <= ov \/ ov + 56 <= (sp - 64))
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1
  /\ L5.u64_at RSEGS M (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0.

Definition fcells (R0 : bvmap 5 word) (r : Z) (M : word -> option byte) (sp : Z) : Prop :=
  L5.u64_at RSEGS M (sp - 8) r /\ L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8))) /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9)))
  /\ L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18))) /\ L5.defined M (sp - 48) 16.

Definition runA : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 ov -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
    L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 SBL -> L5.u32_at RSEGS M 1317376 1 -> 140735332487232 <= sp <= 140737488355328 -> sp mod 16 = 0 ->
    L5.writable RSEGS M (sp - 64) 64 -> fov M sp ov osk ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 64 <= i < sp - 64 + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xab7e0 M) (mst fx' R' 0xab820 M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ inregs R' sp ov /\ fcells R r M' sp.

Definition runC (v byo raC : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 ->
    inregs R sp ov -> getr R (reg 10) = Z_to_bv 64 osk -> getr R (reg 11) = Z_to_bv 64 v -> fstat M sp -> 4096 <= ov <= 140737488355272 -> ov mod 8 = 0 -> 4096 <= osk <= 140737488355304 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp + byo <= i < sp + byo + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xab834 M) (mst fx' R' PB M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 raC /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp + byo).

Definition runW (pcF wr raW : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 ->
    inregs R sp ov -> fstat M sp -> 4096 <= ov <= 140737488355272 -> ov mod 8 = 0 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pcF M) (mst fx' R' wr M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 raW /\ getr R' (reg 10) = Z_to_bv 64 (ov + 8).

Definition runJ : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 ->
    inregs R sp ov -> fstat M sp ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xab854 M) (mst fx' R' EV M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)).

Definition runE0 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov osk eb r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    inregs R sp ov -> fstat M sp -> fov M sp ov osk ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) eb -> 0 <= eb <= 140737488355328 -> fcells R0 r M sp -> L5.ra_ok r ->
    getr R0 (reg 2) = Z_to_bv 64 sp -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R EV M) (mst fx' R' r M')
      /\ regs_preserved R0 R'.

Definition runE1 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov osk eb ed cn r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 -> 0 <= cn < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    inregs R sp ov -> fstat M sp -> fov M sp ov osk ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) ed -> 4096 <= eb <= 140737488355328 -> 4120 <= ed <= 140737488355328 -> ed mod 8 = 0 ->
    24 <= ed - eb <= 100000 -> (ed <= 65536 \/ 6914048 <= eb) -> L5.writable RSEGS M (ed - 24) 24 -> (2147446784 + 17592186048512 <= ed - 24 \/ (ed - 24) + 24 <= 2147446784) ->
    L5KA.zeros_at M ((ed - 8) / 8 + SBL) 1 ->
    ((ed - 24) + 24 <= (sp - 64) \/ (sp - 64) + 64 <= (ed - 24)) -> ((ed - 24) + 24 <= ov \/ ov + 56 <= (ed - 24)) -> L5.u64_at RSEGS M (ed - 8) cn ->
    fcells R0 r M sp -> L5.ra_ok r -> getr R0 (reg 2) = Z_to_bv 64 sp -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (ed - 8 <= i < ed - 8 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R EV M) (mst fx' R' r M')
      /\ regs_preserved R0 R'
      /\ L5.u64_at RSEGS M' (ed - 8) ((cn + 1) mod 2 ^ 64).

Local Ltac kept_tac KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Local Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEAENCDP.aligned; assumption | apply wid | apply wrng | L5SAR.greg | L5SAR.gmem | lia]).

Local Ltac midV R sp ov osk eb ed cn r R0 :=
  constr:(fun j : nat => match j with 2%nat => sp | 10%nat => ov | 41%nat => osk | 38%nat => eb | 39%nat => ed | 42%nat => cn | 44%nat => r
     | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | 47%nat => bv_unsigned (getr R0 (reg 18))
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end).

Local Ltac imm_tac := match goal with |- _ + bv_signed ?i = _ => let v := eval vm_compute in (bv_signed i) in change (bv_signed i) with v end.

Lemma u_runA : runA.
Proof.
  intros fx R M sp ov osk r Hsp Hov Hosk G2 G10 G1 RA K0 K1 K2 K3 K4 K5 FOV.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12).
  assert (Hr : bv_unsigned (getr R (reg 1)) = r) by (rewrite G1; apply L5.unsigned_lit; destruct RA as [Hr1 Hr2]; clear - Hr1; lia).

  pose proof (PEAENCDP.afdA_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P. feedP P. rewrite Hr in P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T2 & S32 & S24 & S16 & S8).

  destruct (PEFX.fsd_run RSEGS fx1 R1 M1 0xab7f4 W_ab7a4 _ _ _ (sp - 40) F_ab7a4 eq_refl D_ab7a4 ltac:(imm_tac; rewrite L5K.rl2, T2, L5.unsigned_lit by (clear - K3; lia); clear; lia)
              ltac:(clear - K3; lia) ltac:(clear - K3; lia) ltac:(apply (writable_grows M M1 _ _ MG1); apply (L5.writable_sub _ _ (sp - 64) 64 (sp - 40) 8 K5); clear; lia) ltac:(clear; lia) ltac:(clear; lia))
    as (M2 & MS2 & MG2 & FRZ2 & DEF2).
  change (0xab7f4 + 4) with 0xab7f8 in MS2.
  destruct (PEFX.fsd_run RSEGS fx1 R1 M2 0xab7f8 W_ab7a8 _ _ _ (sp - 48) F_ab7a8 eq_refl D_ab7a8 ltac:(imm_tac; rewrite L5K.rl2, T2, L5.unsigned_lit by (clear - K3; lia); clear; lia)
              ltac:(clear - K3; lia) ltac:(clear - K3; lia) ltac:(apply (writable_grows M M2 _ _ (mem_grows_trans M M1 M2 MG1 MG2)); apply (L5.writable_sub _ _ (sp - 64) 64 (sp - 48) 8 K5); clear; lia) ltac:(clear; lia) ltac:(clear; lia))
    as (M3 & MS3 & MG3 & FRZ3 & DEF3).
  change (0xab7f8 + 4) with 0xab7fc in MS3.
  pose proof (mem_grows_trans M M1 M3 MG1 (mem_grows_trans M1 M2 M3 MG2 MG3)) as MG13.
  assert (FRZ13 : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 64 <= i < sp - 64 + 64) -> M3 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn. rewrite (FRZ3 i Hi) by (clear - Hn; lia). rewrite (FRZ2 i Hi) by (clear - Hn; lia). exact (FRZ1 i Hi Hn). }
  assert (AG3 : forall a n, (a + n <= sp - 64 \/ sp <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M3 a n).
  { intros a n Ha Ha0 Ha1 i Hi. apply FRZ13; [clear - Hi Ha0 Ha1; lia| clear - Hi Ha; lia]. }
  assert (AGc : forall a, sp - 32 <= a -> a + 8 <= sp -> L5C.agree_on M1 M3 a 8).
  { intros a Ha1 Ha2 i Hi. rewrite (FRZ3 i) by (clear - Hi Ha1 Ha2 K3; lia). apply FRZ2; clear - Hi Ha1 Ha2 K3; lia. }
  assert (HO : bv_unsigned (getr R1 (reg 10)) = ov) by (rewrite (KS1 10%nat) by inl; rewrite G10; apply L5.unsigned_lit; exact Hov).

  pose proof (PEAENCDP.afdA3_conc fx1 R1 M3 (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P. rewrite !HO in P.
  L5SAR.feed P ltac:(first [ assumption | unfold PEAENCDP.aligned; assumption
    | intros i Hi; rewrite FRZ13; [apply K0; exact Hi | clear - Hi; lia | clear - Hi K3; lia]
    | apply (L5C.u64_at_agree RSEGS M M3); [apply AG3; [clear - K3 O1 O6; lia| clear - O1; lia| clear - O1; lia] | clear - O1; lia | clear - O1; lia | assumption]
    | apply (PMF.u32_at_agree RSEGS M M3); [apply AG3; clear - K3; lia | clear; lia | clear; lia | assumption]
    | apply (writable_grows M M3 _ _ MG13); assumption
    | apply (L5KA.zeros_at_agree1 M M3); [intros i Hi; apply FRZ13; [clear - Hi O1; lia | clear - Hi O1 K3; lia] | assumption]
    | lia ]).
  destruct P as (fx4 & R4 & M4 & MG4 & _ & FRZ4 & MS4 & KS4 & T8 & T9 & _ & _ & T18).
  pose proof (L5SAR.mem_eq_of_agree M3 M4 ltac:(intros a; apply FRZ4)) as EM. subst M4.
  exists fx4, R4, M3. split; [exact MG13|]. split; [exact FRZ13|].
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MS4]]]|].
  split; [intros j Hj; rewrite (KS4 j) by (revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl); apply KS1; revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|].
  split. { unfold inregs. split; [rewrite (KS4 2%nat) by inl; exact T2|]. split; [rewrite T8; rewrite (KS1 10%nat) by inl; exact G10|]. split; [exact T9| exact T18]. }
  unfold fcells. split; [apply (L5C.u64_at_agree RSEGS M1 M3); [apply AGc; clear; lia| clear - K3; lia| clear - K3; lia| exact S8]|].
  split; [apply (L5C.u64_at_agree RSEGS M1 M3); [apply AGc; clear; lia| clear - K3; lia| clear - K3; lia| exact S16]|].
  split; [apply (L5C.u64_at_agree RSEGS M1 M3); [apply AGc; clear; lia| clear - K3; lia| clear - K3; lia| exact S24]|].
  split; [apply (L5C.u64_at_agree RSEGS M1 M3); [apply AGc; clear; lia| clear - K3; lia| clear - K3; lia| exact S32]|].
  intros i Hi. destruct (Z_lt_le_dec i 8) as [Lo|Hi2].
  - apply (DEF3 i). clear - Hi Lo; lia.
  - rewrite (FRZ3 (sp - 48 + i)); [| clear - Hi Hi2 K3 Hsp; lia| clear - Hi Hi2; lia].
    replace (sp - 48 + i) with (sp - 40 + (i - 8)) by (clear; lia). apply (DEF2 (i - 8)). clear - Hi Hi2; lia.
Qed.

Definition runF1 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> frm_zero (@fp_csr fx) ->
    inregs R sp ov -> fstat M sp -> 4096 <= ov <= 140737488355272 -> ov mod 8 = 0 -> L5.u64_at RSEGS M (ov + 8) osk -> 4096 <= osk <= 140737488355304 -> osk mod 8 = 0 ->
    exists fx' R',
         msteps RSEGS (mst fx R 0xab820 M) (mst fx' R' 0xab82c M)
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 10) = Z_to_bv 64 osk.
Definition runF2 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte),
    frm_zero (@fp_csr fx) ->
    exists fx' (v : Z), (v = 0 \/ v = 1)
      /\ msteps RSEGS (mst fx R 0xab82c M) (mst fx' (regupd R (reg 11) (Z_to_bv 64 v)) 0xab834 M).

Lemma u_runF1 : runF1.
Proof.
  intros fx R M sp ov osk Hsp Hov Hosk FZ (G2 & G8 & G9 & G18) (K0 & K1 & K2 & K3 & K4 & K5) OR O8 U8 KR K8.
  destruct (PEFX.fsgnj_run RSEGS fx R M 0xab820 W_ab7d0 _ _ _ _ _ F_ab7d0 eq_refl D_ab7d0 ltac:(clear; lia) ltac:(clear; lia)) as (fx1 & MS1 & CS1).
  change (0xab820 + 4) with 0xab824 in MS1.
  destruct (PEFX.fcvt_dyn_run RSEGS fx1 R M 0xab824 W_ab7d4 _ _ _ _ _ F_ab7d4 eq_refl D_ab7d4 (or_introl eq_refl) ltac:(rewrite CS1; exact FZ) (or_intror eq_refl) ltac:(clear; lia) ltac:(clear; lia)) as (fx2 & FZ2 & MS2).
  change (0xab824 + 4) with 0xab828 in MS2.
  let mv := midV R sp ov osk 0 0 0 0 R in pose proof (PEAENCDP.afdB_conc fx2 R M mv) as P. cbn beta iota in P. feedP P.
  destruct P as (fx3 & R3 & M3 & MG3 & _ & FRZ3 & MS3 & KS3 & T10).
  pose proof (L5SAR.mem_eq_of_agree M M3 ltac:(intros a; apply FRZ3)) as EM. subst M3.
  exists fx3, R3. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]|]. split; [kept_tac KS3| exact T10].
Qed.
Lemma u_runF2 : runF2.
Proof.
  intros fx R M FZ.
  destruct (PEFX.fcvt_dyn_run RSEGS fx R M 0xab82c W_ab7dc _ _ _ _ _ F_ab7dc eq_refl D_ab7dc (or_intror eq_refl) FZ ltac:(left; vm_compute; intros XX; discriminate XX) ltac:(clear; lia) ltac:(clear; lia)) as (fx1 & FZ1 & MS1).
  change (0xab82c + 4) with 0xab830 in MS1.
  destruct (PEFX.fcmp_run RSEGS fx1 R M 0xab830 W_ab7e0 _ _ _ _ _ F_ab7e0 eq_refl D_ab7e0 eq_refl FZ1 ltac:(clear; lia) ltac:(clear; lia)) as (fx2 & v & Hv & _ & MS2).
  change (0xab830 + 4) with 0xab834 in MS2. rewrite L5K.rl11 in MS2.
  exists fx2, v. split; [exact Hv|]. eapply msteps_trans; [exact MS1| exact MS2].
Qed.

Local Ltac runC_tac C_conc :=
  intros fx R M sp ov osk Hsp Hov Hosk (G2 & G8 & G9 & G18) G10 G11 (K0 & K1 & K2 & K3 & K4 & K5) OR O8 KR;
  let P := fresh "P" in let mv := midV R sp ov osk 0 0 0 0 R in pose proof (C_conc fx R M mv) as P; cbn beta iota in P; feedP P;
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T11 & _);
  exists fx1, R1, M1; split; [exact MG1|]; split; [intros i Hi Hn; apply FRZ1; [exact Hi| clear - Hn; lia]|]; split; [exact MS1|]; split; [kept_tac KS1|];
  split; [exact T1|]; split; [rewrite (KS1 10%nat) by inl; exact G10| first [exact T11 | rewrite T11; f_equal; clear; lia]].
Lemma u_runCf : runC 1 (-50) 0xab848. Proof. unfold runC. runC_tac PEAENCDP.afdCf_conc. Qed.
Lemma u_runCd : runC 0 (-49) 0xab868. Proof. unfold runC. runC_tac PEAENCDP.afdCd_conc. Qed.

Local Ltac runW_tac PCF W_F F_F D_F W_conc :=
  intros fx R M sp ov Hsp Hov (G2 & G8 & G9 & G18) (K0 & K1 & K2 & K3 & K4 & K5) OR O8;
  let fx1 := fresh "fx1" in let MS1 := fresh "MS1" in
  destruct (PEFX.fsgnj_run RSEGS fx R M PCF W_F _ _ _ _ _ F_F eq_refl D_F ltac:(clear; lia) ltac:(clear; lia)) as (fx1 & MS1 & _);
  let pc4 := eval vm_compute in (PCF + 4) in change (PCF + 4) with pc4 in MS1;
  let P := fresh "P" in let mv := midV R sp ov 0 0 0 0 0 R in pose proof (W_conc fx1 R M mv) as P; cbn beta iota in P; feedP P;
  destruct P as (fx2 & R2 & M2 & MG2 & _ & FRZ2 & MS2 & KS2 & T1 & T10);
  exists fx2, R2, M2; split; [exact MG2|]; split; [exact FRZ2|];
  split; [eapply msteps_trans; [exact MS1| exact MS2]|];
  split; [kept_tac KS2|]; split; [exact T1| exact T10].
Lemma u_runWf : runW 0xab848 WF32 0xab854. Proof. unfold runW. runW_tac 0xab848 W_ab7f8 F_ab7f8 D_ab7f8 PEAENCDP.afdWf_conc. Qed.
Lemma u_runWd : runW 0xab868 WF64 0xab874. Proof. unfold runW. runW_tac 0xab868 W_ab818 F_ab818 D_ab818 PEAENCDP.afdWd_conc. Qed.

Lemma u_runJ : runJ.
Proof.
  intros fx R M sp ov Hsp Hov (G2 & G8 & G9 & G18) (K0 & K1 & K2 & K3 & K4 & K5).
  let mv := midV R sp ov 0 0 0 0 0 R in pose proof (PEAENCDP.afdJf_conc fx R M mv) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1| kept_tac KS1].
Qed.

Lemma regs_end (R R0 R3 : bvmap 5 word) (sp : Z) (KS : list nat) :
  (forall j, In j CSK -> In j KS) -> (forall x, In x KS -> getr R3 (reg x) = getr R (reg x)) -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
  getr R0 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 2) = Z_to_bv 64 sp ->
  getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> regs_preserved R0 R3.
Proof.
  intros SUB KS3 QCS Rsp T2 T8 T9 T18. apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
  repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8; apply Z_to_bv_bv_unsigned | rewrite T9; apply Z_to_bv_bv_unsigned | rewrite T18; apply Z_to_bv_bv_unsigned
                                          | rewrite (KS3 _) by (apply SUB; inl); apply QCS; inl ] |]). destruct Hj.
Qed.

Lemma e_tail (fx1 : FPState) R1 M1 (sp r : Z) :
  0 <= sp < 2 ^ 64 -> 140735332487232 <= sp -> getr R1 (reg 2) = Z_to_bv 64 (sp - 64) -> getr R1 (reg 1) = Z_to_bv 64 r -> getr R1 (reg 10) = Z_to_bv 64 1 -> L5.ra_ok r ->
  L5.defined M1 (sp - 48) 16 ->
  L5.img_clear M1 1253376 1286144 -> L5.u64_at RSEGS M1 1317368 SBL -> L5.u32_at RSEGS M1 1317376 1 -> sp <= 140737488355328 -> sp mod 16 = 0 -> L5.writable RSEGS M1 (sp - 64) 64 ->
  exists fx' R', msteps RSEGS (mst fx1 R1 0xab8dc M1) (mst fx' R' r M1)
    /\ (forall x, In x PEAENCDP.KS_afdZ -> getr R' (reg x) = getr R1 (reg x)) /\ getr R' (reg 2) = Z_to_bv 64 sp.
Proof.
  intros Hsp SLO T2 T1 T10 RA DEF K0 K1 K2 K3 K4 K5. pose proof RA as (Hr1 & Hr2).
  destruct (PEFX.fld_run RSEGS fx1 R1 M1 0xab8dc W_ab88c _ _ _ (sp - 40) F_ab88c eq_refl D_ab88c ltac:(imm_tac; rewrite L5K.rl2, T2, L5.unsigned_lit by (clear - Hsp SLO; lia); clear; lia)
              ltac:(clear - SLO; lia) ltac:(clear - Hsp; lia) ltac:(apply (L5.defined_sub M1 (sp - 48) 16); [exact DEF| clear; lia| clear; lia]) ltac:(clear; lia) ltac:(clear; lia)) as (fx2 & MS2 & _).
  change (0xab8dc + 4) with 0xab8e0 in MS2.
  destruct (PEFX.fld_run RSEGS fx2 R1 M1 0xab8e0 W_ab890 _ _ _ (sp - 48) F_ab890 eq_refl D_ab890 ltac:(imm_tac; rewrite L5K.rl2, T2, L5.unsigned_lit by (clear - Hsp SLO; lia); clear; lia)
              ltac:(clear - SLO; lia) ltac:(clear - Hsp; lia) ltac:(apply (L5.defined_sub M1 (sp - 48) 16); [exact DEF| clear; lia| clear; lia]) ltac:(clear; lia) ltac:(clear; lia)) as (fx3 & MS3 & _).
  change (0xab8e0 + 4) with 0xab8e4 in MS3.
  pose proof (PEAENCDP.afdZ_conc fx3 R1 M1 (fun j => match j with 2%nat => sp | 56%nat => bv_unsigned (getr R1 (reg 11)) | 57%nat => bv_unsigned (getr R1 (reg 12)) | _ => 0 end)) as P. cbn beta iota in P. feedP P.
  destruct P as (fx4 & R4 & M4 & MG4 & _ & FRZ4 & MS4 & KS4 & T2').
  pose proof (L5SAR.mem_eq_of_agree M1 M4 ltac:(intros a; apply FRZ4)) as EM. subst M4.
  assert (T1' : getr R4 (reg 1) = Z_to_bv 64 r) by (rewrite (KS4 1%nat) by inl; exact T1).
  pose proof (PMK.ret_to RSEGS fx4 R4 M1 0xab8e8 W_ab898 r F_ab898 eq_refl D_ab898 T1' ltac:(clear - Hr1; lia) Hr2) as MSR.
  exists fx4, R4. split; [eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| eapply msteps_trans; [exact MS4| exact MSR]]]|]. split; [exact KS4| exact T2'].
Qed.

Lemma u_runE0 : runE0.
Proof.
  unfold runE0. intros fx R R0 M sp ov osk eb r H1 H2 H3 H5 H6 IR FS FOV U24 U32 EB (C8 & C16 & C24 & C32 & CDEF) RA R0sp QCS.
  pose proof IR as (G2 & G8 & G9 & G18). pose proof FS as (K0 & K1 & K2 & K3 & K4 & K5).
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12).
  let mv := midV R sp ov osk eb eb 0 r R0 in pose proof (PEAENCDP.afdE0_conc fx R M mv) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T8 & T9 & T10 & _ & T18).
  pose proof (L5SAR.mem_eq_of_agree M M1 ltac:(intros a; apply FRZ1)) as EM. subst M1.
  destruct (e_tail fx1 R1 M sp r H1 ltac:(clear - K3; lia) ltac:(rewrite (KS1 2%nat) by inl; exact G2) T1 T10 RA CDEF K0 K1 K2 ltac:(clear - K3; lia) K4 K5) as (fx5 & R5 & MS5 & KS5 & T2).
  exists fx5, R5, M. split; [apply mem_grows_refl|]. split; [intros; reflexivity|]. split; [eapply msteps_trans; [exact MS1| exact MS5]|].
  apply (regs_end R R0 R5 sp CSK); [intros j Hj; exact Hj| | exact QCS| exact R0sp| exact T2| | |].
  - intros x Hx. rewrite (KS5 x) by (revert Hx; clear; intros Hx; apply (PEEK.sub_in PEAENCDP.KS_afdZ CSK); [vm_compute; reflexivity| exact Hx]).
      apply KS1. revert Hx; clear; intros Hx. apply (PEEK.sub_in PEAENCDP.KS_afdE0 CSK); [vm_compute; reflexivity| exact Hx].
  - rewrite (KS5 8%nat) by inl. exact T8.
  - rewrite (KS5 9%nat) by inl. exact T9.
  - rewrite (KS5 18%nat) by inl. exact T18.
Qed.

Lemma u_runE1 : runE1.
Proof.
  unfold runE1. intros fx R R0 M sp ov osk eb ed cn r H1 H2 H3 H5 H6 H7 H8 IR FS FOV U24 U32 EB ED AL8 LEN IMGA WR24 NSH ZC DJS DJO UC (C8 & C16 & C24 & C32 & CDEF) RA R0sp QCS.
  pose proof IR as (G2 & G8 & G9 & G18). pose proof FS as (K0 & K1 & K2 & K3 & K4 & K5).
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12).
  assert (CDEFa : forall M1, (forall i, 0 <= i < 2 ^ 64 -> ~ (ed - 8 <= i < ed - 8 + 8) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> L5.defined M1 (sp - 48) 16).
  { intros M1 FRZ. apply (L5C.defined_agree M M1); [| exact CDEF]. intros i Hi. apply FRZ; [clear - Hi K3; lia| clear - Hi DJS; lia]. }
  destruct (Z.eq_dec cn 18446744073709551615) as [CW|CNW].
  - rewrite CW in UC.
    let mv := midV R sp ov osk eb ed cn r R0 in pose proof (PEAENCDP.afdE1w_conc fx R M mv) as P. cbn beta iota in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T8 & T9 & T10 & _ & T18 & CC).
    destruct (e_tail fx1 R1 M1 sp r H1 ltac:(clear - K3; lia) ltac:(rewrite (KS1 2%nat) by inl; exact G2) T1 T10 RA (CDEFa M1 FRZ1)
                ltac:(intros i Hi; rewrite FRZ1; [apply K0; exact Hi| clear - Hi; lia| clear - Hi EB LEN IMGA; lia])
                ltac:(apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FRZ1; [clear - Hi; lia| clear - Hi EB LEN IMGA; lia]| clear; lia| clear; lia| exact K1])
                ltac:(apply (PMF.u32_at_agree RSEGS M M1); [intros i Hi; apply FRZ1; [clear - Hi; lia| clear - Hi EB LEN IMGA; lia]| clear; lia| clear; lia| exact K2])
                ltac:(clear - K3; lia) K4 ltac:(apply (writable_grows M M1 _ _ MG1); exact K5)) as (fx5 & R5 & MS5 & KS5 & T2).
    exists fx5, R5, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MS5]|].
    split; [| rewrite CW; change ((18446744073709551615 + 1) mod 2 ^ 64) with 0; exact CC].
    apply (regs_end R R0 R5 sp CSK); [intros j Hj; exact Hj| | exact QCS| exact R0sp| exact T2| | |].
    + intros x Hx. rewrite (KS5 x) by (revert Hx; clear; intros Hx; apply (PEEK.sub_in PEAENCDP.KS_afdZ CSK); [vm_compute; reflexivity| exact Hx]).
      apply KS1. revert Hx; clear; intros Hx. apply (PEEK.sub_in PEAENCDP.KS_afdE1w CSK); [vm_compute; reflexivity| exact Hx].
    + rewrite (KS5 8%nat) by inl. exact T8.
    + rewrite (KS5 9%nat) by inl. exact T9.
    + rewrite (KS5 18%nat) by inl. exact T18.
  - let mv := midV R sp ov osk eb ed cn r R0 in pose proof (PEAENCDP.afdE1_conc fx R M mv) as P. cbn beta iota in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T8 & T9 & T10 & _ & T18 & CC).
    destruct (e_tail fx1 R1 M1 sp r H1 ltac:(clear - K3; lia) ltac:(rewrite (KS1 2%nat) by inl; exact G2) T1 T10 RA (CDEFa M1 FRZ1)
                ltac:(intros i Hi; rewrite FRZ1; [apply K0; exact Hi| clear - Hi; lia| clear - Hi EB LEN IMGA; lia])
                ltac:(apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FRZ1; [clear - Hi; lia| clear - Hi EB LEN IMGA; lia]| clear; lia| clear; lia| exact K1])
                ltac:(apply (PMF.u32_at_agree RSEGS M M1); [intros i Hi; apply FRZ1; [clear - Hi; lia| clear - Hi EB LEN IMGA; lia]| clear; lia| clear; lia| exact K2])
                ltac:(clear - K3; lia) K4 ltac:(apply (writable_grows M M1 _ _ MG1); exact K5)) as (fx5 & R5 & MS5 & KS5 & T2).
    exists fx5, R5, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MS5]|].
    split; [| rewrite Z.mod_small by (clear - H7 CNW; lia); exact CC].
    apply (regs_end R R0 R5 sp CSK); [intros j Hj; exact Hj| | exact QCS| exact R0sp| exact T2| | |].
    + intros x Hx. rewrite (KS5 x) by (revert Hx; clear; intros Hx; apply (PEEK.sub_in PEAENCDP.KS_afdZ CSK); [vm_compute; reflexivity| exact Hx]).
      apply KS1. revert Hx; clear; intros Hx. apply (PEEK.sub_in PEAENCDP.KS_afdE1 CSK); [vm_compute; reflexivity| exact Hx].
    + rewrite (KS5 8%nat) by inl. exact T8.
    + rewrite (KS5 9%nat) by inl. exact T9.
    + rewrite (KS5 18%nat) by inl. exact T18.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis PBH : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Let NTBF32 := PEAENTBF.ntb_f32_ok L ar C HI P LY HIok PO PBH.
Let NTBF64 := PEAENTBF.ntb_f64_ok L ar C HI P LY HIok PO PBH.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z).
Variables (xstk : list pstate) (xpos : Z) (xmore xdone xhalt : bool) (xdepth : Z) (xec : bool) (xestk : list eitem) (xedepth xlo xhi : Z) (xbad : bool).
Variables (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Let X : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad.
Let XS (a : Z) : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + a) (xhi + a) xbad.
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 4.
Hypothesis FRM : PMSPA.ffroomA 4 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis MP : PECSPA.mp_enc p X.
Hypothesis HB9 : PESKA.spa_hb P (xhi + 9).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.
Hypothesis KONT : forall (w : Z) (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' -> (w = 5 \/ w = 9) ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (e_end_value (XS w)) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Definition FC (Mx : word -> option byte) : Prop := fcells R r Mx sp.
Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH;
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp.

Lemma FC_frame M1 M2 : (forall a, sp - 64 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros AG (C8 & C16 & C24 & C32 & CDEF). entry_facts.
  assert (SV : forall a0 w, sp - 64 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; clear - Hi H1 H2; lia| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC, fcells. repeat (split; [apply SV; [clear; lia| clear; lia| assumption]|]).
  apply (L5C.defined_agree M1 M2); [| exact CDEF]. intros i Hi. apply AG. clear - Hi; lia.
Qed.

Lemma FC_but M1 M2 lo hi : hi <= sp - 48 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros Hhi AG (C8 & C16 & C24 & C32 & CDEF). entry_facts.
  assert (SV : forall a0 w, sp - 48 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; [clear - Hi H1 H2 SLO SHI SPT; lia| clear - Hi H1 Hhi; lia]| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC, fcells. repeat (split; [apply SV; [clear; lia| clear; lia| assumption]|]).
  apply (L5C.defined_agree M1 M2); [| exact CDEF]. intros i Hi. apply AG; [clear - Hi SLO SHI SPT; lia| clear - Hi Hhi; lia].
Qed.
Lemma HFR : 64 = 32 \/ 64 = 64. Proof. right; reflexivity. Qed.
Lemma CSK3 : In 3%nat CSK. Proof. inl. Qed.
Lemma CSK4 : In 4%nat CSK. Proof. inl. Qed.
Lemma CSKall j : In j CSK -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.
Lemma CSIall j : In j CSI -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.

Lemma KONTw (w : Z) : (w = 5 \/ w = 9) ->
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
         (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
    regs_preserved R R' ->
    PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (e_end_value (XS w)) s str sm en' k' e' cat -> (e = true -> e' = true) ->
    L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
    PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
    model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
    ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.
Proof. intros Hw fx' R' M' model' LK' Aw' en' k' e' cr' RP. exact (KONT w fx' R' M' model' LK' Aw' en' k' e' cr' RP Hw). Qed.

Abbreviation INV := (PEAEKD.inv L ar HI P M model LBX FF LK Aw cr sp fb xlo xhi s en k FC).
Abbreviation csk := (PEAEKD.csk CSK R).

Lemma inregs_after R1 R2 ov : inregs R1 sp ov -> csk R1 -> regs_preserved R1 R2 -> inregs R2 sp ov /\ csk R2.
Proof.
  intros (G2 & G8 & G9 & G18) QCS RP. split.
  - split; [rewrite (L5SAR.cs_of_preserved R1 R2 2 RP) by inl; exact G2|]. split; [rewrite (L5SAR.cs_of_preserved R1 R2 8 RP) by inl; exact G8|].
    split; [rewrite (L5SAR.cs_of_preserved R1 R2 9 RP) by inl; exact G9|]. rewrite (L5SAR.cs_of_preserved R1 R2 18 RP) by inl; exact G18.
  - intros j Hj. rewrite (L5SAR.cs_of_preserved R1 R2 j RP (CSKall j Hj)). exact (QCS j Hj).
Qed.
Lemma inregs_kept R1 R2 ov : inregs R1 sp ov -> csk R1 -> (forall j, In j CSI -> getr R2 (reg j) = getr R1 (reg j)) -> inregs R2 sp ov /\ csk R2.
Proof.
  intros (G2 & G8 & G9 & G18) QCS KS. split.
  - split; [rewrite (KS 2%nat) by inl; exact G2|]. split; [rewrite (KS 8%nat) by inl; exact G8|]. split; [rewrite (KS 9%nat) by inl; exact G9|].
    rewrite (KS 18%nat) by inl; exact G18.
  - intros j Hj. rewrite (KS j) by (revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl). exact (QCS j Hj).
Qed.

Lemma vis Mq mdq LKq Awq crq kq a : INV Mq mdq LKq Awq crq kq a ->
  let MV := mrestrict (ahid Awq mdq) Mq in
  fstat MV sp /\ fov MV sp (PMSPA.o_v AD fb) (PESK.o_sink EE fb) /\ fcells R r MV sp
  /\ L5.u64_at RSEGS MV (PMSPA.o_v AD fb + 24) (PEC.en_b en) /\ L5.u64_at RSEGS MV (PMSPA.o_v AD fb + 32) (PEC.en_b en + 24 * Z.of_nat (length (PEC.en_stk en)))
  /\ 0 <= PEC.en_b en <= 2 ^ 47.
Proof.
  intros INVq. entry_facts.
  pose proof (PEAEKD.vis_facts L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq mdq LKq Awq crq kq a INVq)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8 & KR & K8 & KO & U24 & U32 & EB & SVV & FCq).
  cbv beta in SVV. pose proof INVq as (_ & _ & _ & _ & _ & _ & _ & HHq & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq HHq) as (_ & VIS & _).
  destruct FCq as (C8 & C16 & C24 & C32 & CDEF).
  split. { split; [exact IC0|]. split; [exact CSBv|]. split; [exact CUARv|]. split; [clear - SPR; lia|]. split; [exact A16'| exact SWR]. }
  split. { split; [exact OR|]. split; [exact O8|]. split; [exact OBIG|]. split; [exact Zov|]. split; [exact OWR|]. split; [exact ODJ|].
           split; [exact Z8|]. split; [exact Z24|]. split; [exact Z32|]. split; [exact U8|]. split; [exact KR| exact K8]. }
  split. { split; [| split; [| split; [| split]]]; [apply SVV; [clear; lia| clear; lia| exact C8] | apply SVV; [clear; lia| clear; lia| exact C16]
           | apply SVV; [clear; lia| clear; lia| exact C24] | apply SVV; [clear; lia| clear; lia| exact C32] |].
           apply (proj2 (L5A.defined_vis (ahid Awq mdq) Mq (sp - 48) 16 (VIS (sp - 48) 16 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)))). exact CDEF. }
  split; [exact U24|]. split; [exact U32| exact EB].
Qed.

Lemma tailE w (fxq : FPState) Rq Mq mdq LKq Awq crq kq : (w = 5 \/ w = 9) ->
  INV Mq mdq LKq Awq crq kq w -> inregs Rq sp (PMSPA.o_v AD fb) -> csk Rq ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq EV Mq mdq) K.
Proof.
  intros Hw INVq IRq QCS. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq w INVq) as (FS & FOVq & FCv & U24 & U32 & EB). cbv beta in FS, FOVq, FCv, U24, U32.
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  pose proof FS as (_ & _ & _ & SPR & _). pose proof FOVq as (OR & _ & _ & _ & _ & _ & _ & _ & _ & _ & KR & _).
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (_ & _ & _ & _ & _ & Lestk & _). cbn [s_estk X] in Lestk.
  assert (OVR : 0 <= ov < 2 ^ 64) by (clear - OR; lia). assert (OKR : 0 <= osk < 2 ^ 64) by (clear - KR; lia).
  assert (SP0 : 0 <= sp < 2 ^ 64) by (clear - SPR; lia).
  pose proof (KONTw w Hw) as KONT'.
  destruct xestk as [|e1 rr] eqn:HXS.
  - rewrite Lestk in U32. cbn [rev length Z.of_nat Z.mul] in U32. rewrite Z.add_0_r in U32.
    destruct (u_runE0 fxq Rq R MV sp ov osk (PEC.en_b en) r SP0 OVR OKR ltac:(clear - EB; lia) ltac:(clear - Hr1; lia) IRq FS FOVq U24 U32 ltac:(clear - EB; lia) FCv RAok Rsp QCS)
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & RP3).
    exact (PEAEKD.finish_ro L ar C HI P LY HIok 64 w HFR R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec [] xedepth xlo xhi xbad s str sm en k e
             HH ENT FOK FC CPRE INCS KONT' w EV fxq Rq Mq mdq LKq Awq crq kq fx3 R3 M3v INVq eq_refl eq_refl MS3 MG3 FRZ3 RP3).
  - pose proof (PEAEKD.vis_facts_top L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e
                  HH ENT FOK FC CPRE MP Mq mdq LKq Awq crq kq w e1 rr INVq eq_refl)
      as (HLEN & EKP & EB1 & ED2 & ALend & ED3 & WR24 & EB6 & ZC & EDS & OVA & TCv & E1C & E1OK & BINe & EDC & EBC & _).
    cbv beta in HLEN, ED2, ALend, ED3, WR24, EB6, ZC, EDS, OVA, TCv, EDC. fold H MV ov in WR24, ZC, TCv, OVA, EDS. fold H in ZC. fold MV in ZC.
    rewrite HLEN in U32. set (ed := PEC.en_b en + 24 * (Z.of_nat (length rr) + 1)) in *.
    pose proof INVq as (_ & _ & _ & _ & _ & _ & _ & _ & EAq & _).
    assert (IMGA : ed <= 65536 \/ 6914048 <= PEC.en_b en).
    { destruct EAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EBLK & _). destruct (EBLK EKP) as (_ & _ & ABR & _).
      destruct ABR as (_ & ABI & _). rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in ABI. clear - ABI EDC. unfold PEC.ESZ in *. lia. }
    destruct (u_runE1 fxq Rq R MV sp ov osk (PEC.en_b en) ed (ei_cnt e1) r SP0 OVR OKR ltac:(clear - EB; lia) ltac:(clear - EB1 ED2; lia) E1C ltac:(clear - Hr1; lia) IRq FS FOVq U24 U32
              ltac:(clear - EB EB1; lia) ltac:(clear - EB1 ED2 ED3; lia) ALend ED3 IMGA WR24 EB6 ZC EDS OVA TCv FCv RAok Rsp QCS)
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & RP3 & CC).
    exact (PEAEKD.finish_bump L ar C HI P LY HIok 64 w HFR R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e
             HH ENT FOK FC CPRE INCS MP CRED KONT' w EV fxq Rq Mq mdq LKq Awq crq kq fx3 R3 M3v e1 rr INVq eq_refl eq_refl MS3 MG3 FRZ3 CC RP3).
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
  apply KX3. apply (PEAEKD.inv_frame L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq Mq mdq md3 LKq Awq crq kq a sp sp INVq);
    [clear; lia| clear; lia| intros w D; exact D| intros i _ _; reflexivity| exact FCq| exact HH3| exact AM3| exact MRT3].
Qed.

Lemma stepJ (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  INV Mq mdq LKq Awq crq kq 5 -> inregs Rq sp (PMSPA.o_v AD fb) -> csk Rq ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xab854 Mq mdq) K.
Proof.
  intros INVq IRq QCS.
  destruct (vis Mq mdq LKq Awq crq kq 5 INVq) as (FS & FOVq & _). cbv beta in FS, FOVq. pose proof FS as (_ & _ & _ & SPR & _). pose proof FOVq as (OR & _).
  destruct (u_runJ fxq Rq (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) ltac:(clear - SPR; lia) ltac:(clear - OR; lia) IRq FS) as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3).
  apply (step_ro 5 fxq Rq Mq mdq LKq Awq crq kq 0xab854 EV fx3 R3 M3v INVq MS3 MG3 FRZ3).
  intros md3 INV3. destruct (inregs_kept Rq R3 _ IRq QCS KS3) as [IR3 QCS3]. exact (tailE 5 fx3 R3 Mq md3 LKq Awq crq kq (or_introl eq_refl) INV3 IR3 QCS3).
Qed.

Lemma stepW pcF wr raW kb (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  runW pcF wr raW -> PENTBAF.ntbf_specA RSEGS AD L ar HI wr kb P -> (1 + kb = 5 \/ 1 + kb = 9) -> L5.ra_ok raW ->
  INV Mq mdq LKq Awq crq kq 1 -> inregs Rq sp (PMSPA.o_v AD fb) -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, INV M2 md2 LK2 Aw2 cr2 k2 (1 + kb) -> inregs R2 sp (PMSPA.o_v AD fb) -> csk R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 raW M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcF Mq mdq) K.
Proof.
  intros RW NTB HKB RAW INVq IRq QCS KX.
  destruct (vis Mq mdq LKq Awq crq kq 1 INVq) as (FS & FOVq & _). cbv beta in FS, FOVq. pose proof FS as (_ & _ & _ & SPR & _). pose proof FOVq as (OR & O8 & _).
  destruct (RW fxq Rq (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) ltac:(clear - SPR; lia) ltac:(clear - OR; lia) IRq FS OR O8)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T10).
  apply (step_ro 1 fxq Rq Mq mdq LKq Awq crq kq pcF wr fx3 R3 M3v INVq MS3 MG3 FRZ3).
  intros md3 INV3. destruct (inregs_kept Rq R3 _ IRq QCS KS3) as [IR3 QCS3]. pose proof IR3 as (G2 & _).
  apply (PEAEKD.wr_callf L ar C HI P LY HIok 64 CSK HFR CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb xlo xhi s en k HH K0 ENT FRM FRS FOK SP32 FC FC_frame CRED
           1 kb wr (xhi + 9) raW fx3 R3 Mq md3 LKq Awq crq kq NTB INV3 HB9 ltac:(clear - HKB; lia) ltac:(clear - HKB; lia) RAW T1 G2 T10 QCS3).
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 RP2. destruct (inregs_after R3 R2 _ IR3 QCS3 RP2) as [IR2 QCS2]. exact (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 IR2 QCS2).
Qed.

Lemma stepC v byo raC (fxq : FPState) Rq Mq mdq LKq Awq crq kq : runC v byo raC -> (byo = -50 \/ byo = -49) -> L5.ra_ok raC ->
  INV Mq mdq LKq Awq crq kq 0 -> inregs Rq sp (PMSPA.o_v AD fb) -> csk Rq -> getr Rq (reg 10) = Z_to_bv 64 (PESK.o_sink EE fb) -> getr Rq (reg 11) = Z_to_bv 64 v ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, INV M2 md2 LK2 Aw2 cr2 k2 1 -> inregs R2 sp (PMSPA.o_v AD fb) -> csk R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 raC M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xab834 Mq mdq) K.
Proof.
  intros RC BYO RAC INVq IRq QCS Q10 Q11 KX. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq 0 INVq) as (FS & FOVq & FCv & _). cbv beta in FS, FOVq. pose proof FS as (_ & _ & _ & SPR & _). pose proof FOVq as (OR & O8 & _ & _ & _ & _ & _ & _ & _ & _ & KR & _).
  pose proof INVq as (FCq & _ & _ & _ & AMq & _ & _ & HHq & _).
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
  destruct (RC fxq Rq MV sp (PMSPA.o_v AD fb) (PESK.o_sink EE fb) ltac:(clear - SPR; lia) ltac:(clear - OR; lia) ltac:(clear - KR; lia) IRq Q10 Q11 FS OR O8 KR)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T10 & T11).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq fxq fx3 Rq 0xab834 R3 PB M3v (fun a0 => sp + byo <= a0 < sp + byo + 1) K HHq AMq MS3 MG3).
  { intros a0 Ha0 Hn. apply FRZ3; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT BYO; lia| intros Y; clear - Y; lia].
    - clear - Wa SLO SPT BYO; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV M3 md3 LKq Awq crq kq 0).
  { apply (PEAEKD.inv_frame L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq M3 mdq md3 LKq Awq crq kq 0 (sp + byo) (sp + byo + 1) INVq);
      [clear - BYO; lia| clear - BYO; lia| exact MGM3| exact FR3| exact (FC_but Mq M3 (sp + byo) (sp + byo + 1) ltac:(clear - BYO; lia) FR3 FCq)| exact HH3| exact AM3| exact MRT3]. }
  destruct (inregs_kept Rq R3 _ IRq QCS KS3) as [IR3 QCS3]. pose proof IR3 as (G2 & _).
  apply (PEAEKD.pb_call L ar C HI P LY HIok PO PBH 64 CSK HFR CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb xlo xhi s en k HH K0 ENT FRM FRS FOK SP32 FC FC_frame CRED
           0 (sp + byo) (xhi + 9) raC fx3 R3 M3 md3 LKq Awq crq kq INV3 HB9 ltac:(clear; lia) ltac:(clear - BYO; lia) ltac:(clear - BYO; lia) RAC T1 G2 T10 T11 QCS3).
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 RP2. destruct (inregs_after R3 R2 _ IR3 QCS3 RP2) as [IR2 QCS2].
  exact (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 IR2 QCS2).
Qed.

Lemma main : srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xab7e0 M model) K.
Proof.
  entry_facts. pose proof AM as (Mh & MI).
  pose proof (PEAEKD.vis_entry L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 A10 CPRE)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8 & KR & K8 & KO & G2 & G10 & G1 & RAr & RB).
  cbv beta in RB. set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  assert (FOV0 : fov MV sp ov osk).
  { split; [exact OR|]. split; [exact O8|]. split; [exact OBIG|]. split; [exact Zov|]. split; [exact OWR|]. split; [exact ODJ|].
    split; [exact Z8|]. split; [exact Z24|]. split; [exact Z32|]. split; [exact U8|]. split; [exact KR| exact K8]. }

  destruct (u_runA fx R MV sp ov osk r ltac:(clear - SPR; lia) ltac:(clear - OR; lia) ltac:(clear - KR; lia) G2 G10 G1 RAr IC0 CSBv CUARv ltac:(clear - SPR; lia) A16' SWR FOV0)
    as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & IR1 & FC1).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xab7e0 R1 0xab820 M1v (fun a0 => sp - 64 <= a0 < sp - 64 + 64) K HH AM MS1 MG1).
  { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
    - clear - Wa SLO SPT; lia. }
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M1 md1 HH1) as (_ & VIS & _). rewrite HID1 in VIS.
  assert (FCM1 : FC M1).
  { destruct FC1 as (C8 & C16 & C24 & C32 & CDEF). rewrite <- VIS1 in C8, C16, C24, C32, CDEF.
    unfold FC, fcells. repeat (split; [apply RB; [clear; lia| clear; lia| assumption]|]).
    apply (proj1 (L5A.defined_vis H M1 (sp - 48) 16 (VIS (sp - 48) 16 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)))). exact CDEF. }
  pose proof (PEAEKD.inv_start L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 FC CPRE
                M1 md1 MGM1 FR1 FCM1 HH1 AM1 MRT1) as INV1.
  clear VIS.

  apply (srz_fz RSEGS SCFG); [exact K0|]. cbn [cfg_ms PMSPA.cfg ms_fcsr]. intros FZ1.
  destruct (vis M1 md1 LK Aw cr k 0 INV1) as (FS1 & FOV1 & _). cbv beta in FS1, FOV1.
  pose proof FOV1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & U8' & _).
  destruct (u_runF1 fx1 R1 (mrestrict (ahid Aw md1) M1) sp ov osk ltac:(clear - SPR; lia) ltac:(clear - OR; lia) ltac:(clear - KR; lia) FZ1 IR1 FS1 OR O8 U8' KR K8) as (fx2 & R2 & MS2 & KS2 & T10).
  apply (step_ro 0 fx1 R1 M1 md1 LK Aw cr k 0xab820 0xab82c fx2 R2 (mrestrict (ahid Aw md1) M1) INV1 MS2 (mem_grows_refl _) ltac:(intros i _; reflexivity)).
  intros md2 INV2. destruct (inregs_kept R1 R2 _ IR1 KS1 KS2) as [IR2 QCS2].
  apply (srz_fz RSEGS SCFG); [exact K0|]. cbn [cfg_ms PMSPA.cfg ms_fcsr]. intros FZ2.
  destruct (u_runF2 fx2 R2 (mrestrict (ahid Aw md2) M1) FZ2) as (fx3 & v & Hv & MS3).
  apply (step_ro 0 fx2 R2 M1 md2 LK Aw cr k 0xab82c 0xab834 fx3 (regupd R2 (reg 11) (Z_to_bv 64 v)) (mrestrict (ahid Aw md2) M1) INV2 MS3 (mem_grows_refl _) ltac:(intros i _; reflexivity)).
  intros md3 INV3.
  assert (IR3 : inregs (regupd R2 (reg 11) (Z_to_bv 64 v)) sp ov) by (destruct IR2 as (Y2 & Y8 & Y9 & Y18); unfold inregs; rewrite !PEFX.regupd_other_idx by (clear; lia); repeat split; assumption).
  assert (QCS3 : csk (regupd R2 (reg 11) (Z_to_bv 64 v))).
  { intros j Hj. rewrite PEFX.regupd_other_idx; [exact (QCS2 j Hj)| | | clear; lia];
      revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; clear; lia. }
  assert (Q10 : getr (regupd R2 (reg 11) (Z_to_bv 64 v)) (reg 10) = Z_to_bv 64 osk) by (rewrite PEFX.regupd_other_idx by (clear; lia); exact T10).
  assert (Q11 : getr (regupd R2 (reg 11) (Z_to_bv 64 v)) (reg 11) = Z_to_bv 64 v) by (apply PEFX.regupd_same_idx; clear; lia).

  destruct Hv as [-> | ->].
  -
    apply (stepC 0 (-49) 0xab868 fx3 _ M1 md3 LK Aw cr k u_runCd ltac:(right; reflexivity) ltac:(split; [clear; lia| reflexivity]) INV3 IR3 QCS3 Q10 Q11).
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 IR4 QCS4.
    apply (stepW 0xab868 WF64 0xab874 8 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runWd NTBF64 ltac:(right; reflexivity) ltac:(split; [clear; lia| reflexivity]) INV4 IR4 QCS4).
    intros fx5 R5 M5 md5 LK5 Aw5 cr5 k5 INV5 IR5 QCS5.
    exact (tailE 9 fx5 R5 M5 md5 LK5 Aw5 cr5 k5 (or_intror eq_refl) INV5 IR5 QCS5).
  -
    apply (stepC 1 (-50) 0xab848 fx3 _ M1 md3 LK Aw cr k u_runCf ltac:(left; reflexivity) ltac:(split; [clear; lia| reflexivity]) INV3 IR3 QCS3 Q10 Q11).
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 IR4 QCS4.
    apply (stepW 0xab848 WF32 0xab854 4 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runWf NTBF32 ltac:(left; reflexivity) ltac:(split; [clear; lia| reflexivity]) INV4 IR4 QCS4).
    intros fx5 R5 M5 md5 LK5 Aw5 cr5 k5 INV5 IR5 QCS5.
    exact (stepJ fx5 R5 M5 md5 LK5 Aw5 cr5 k5 INV5 IR5 QCS5).
Qed.
End Call.

Theorem v_double_ok : PECSA.v_double_spec L ar HI P.
Proof.
  unfold PECSA.v_double_spec, PECSPA.v_double_spec. cbn [pe_double EE PeCLayoutA.EADDR_A].
  intros PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 A13 CPRE INCS POK MP HB CRED KONT.
  destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad]. cbn [s_hi] in HB.
  assert (ESC : forall w, e_scalar w w (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad)
          = e_end_value (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + w) (xhi + w) xbad)) by reflexivity.
  apply (main PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
           HH AM K0 ENT FRM FRS FOK SP32 A10 CPRE INCS MP HB CRED).
  intros w fx' R' M' model' LK' Aw' en' k' e' cr' RP Hw. rewrite <- (ESC w). exact (KONT fx' R' M' model' LK' Aw' en' k' e' cr' w RP Hw).
Qed.
End WithHeap.
End PEAENCD.
