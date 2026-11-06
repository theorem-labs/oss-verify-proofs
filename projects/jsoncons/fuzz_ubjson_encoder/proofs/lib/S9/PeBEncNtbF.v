(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5CoreSpecsAB0S9 L5StepARB0S9 L5CoreBRB0S9 L5ADetailHRB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PnStatics PmModelFactsA PmStep PeStepAB0 PmParStep PmParKit PeBSrcKit PeBParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrameA PeBCReset1 PmBUarK PmBUar PeBPbIndSpec PeBEncNtbSpec PeBEncNtbFSpec PeBEncNtbFP FPSteps PeFPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_b3c10_b3c14 Eb0_code_b3c3c_b3c40 Eb0_code_b3ca0_b3ca4 Eb0_code_b3dd8_b3ddc Eb0_code_b3de0_b3de4 Eb0_code_b3e1c_b3e20 Eb0_code_b3e48_b3e4c Eb0_code_b3ea8_b3eac Eb0_code_b4018_b401c Eb0_code_b4020_b4024.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENTBF.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).
Abbreviation SBL := 2147450880.
Abbreviation SM0 := 0x5ec3c.
Abbreviation PBIPC := 0xb2794.

Definition own (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
  /\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))) /\ L5.defined M (E - 96) 8.
Definition ocell (E : Z) (a : Z) : Prop := E - 96 <= a < E.
Lemma own_agree E R M1 M1' : 0 <= E - 96 -> E <= 2 ^ 64 ->
  own E R M1 -> (forall a, ocell E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own E R M1'.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12) AG. unfold own, ocell in *.
  repeat split; first [ eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]
                      | intros j Hj; rewrite AG by lia; apply C12; exact Hj ].
Qed.
Lemma writable_grows M M' a n : mem_grows M M' -> L5.writable RSEGS M a n -> L5.writable RSEGS M' a n.
Proof. intros G W d k Hd Hk. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.

Definition rest (R0 R' : bvmap 5 word) : Prop :=
  forall j, In j [8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%nat -> getr R' (reg j) = getr R0 (reg j).
Lemma rest_of_own (R0 R' : bvmap 5 word) :
  getr R' (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R' (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R' (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R' (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R' (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R' (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  getr R' (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) -> getr R' (reg 23) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 23))) ->
  getr R' (reg 24) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 24))) -> getr R' (reg 25) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 25))) ->
  rest R0 R'.
Proof.
  intros T8 T9 T18 T19 T20 T21 T22 T23 T24 T25 j Hj.
  repeat (destruct Hj as [<-|Hj]; [first [rewrite T8 | rewrite T9 | rewrite T18 | rewrite T19 | rewrite T20 | rewrite T21 | rewrite T22 | rewrite T23 | rewrite T24 | rewrite T25]; apply Z_to_bv_bv_unsigned|]).
  destruct Hj.
Qed.

Definition CSK : list nat := [3; 4; 26; 27]%nat.
Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.
Lemma byte_at_of_u8 (M : word -> option byte) a : L5.u8_at RSEGS M a 0 -> M (Z_to_bv 64 a) <> None -> byte_at M a 0.
Proof.
  intros U D. unfold L5.u8_at in U. cbn [rdn] in U. unfold byte_at. destruct (M (Z_to_bv 64 a)) as [b|]; [|congruence].
  cbn in U. congruence.
Qed.
Lemma u8_at_of_defined (M : word -> option byte) a : 0 <= a < 2 ^ 64 -> M (Z_to_bv 64 a) <> None -> exists b, 0 <= b <= 255 /\ L5.u8_at RSEGS M a b.
Proof.
  intros Ha D. destruct (M (Z_to_bv 64 a)) as [bb|] eqn:E; [|congruence]. exists (bv_unsigned bb).
  pose proof (bv_unsigned_in_range 8 bb) as NB. change (bv_modulus 8) with 256 in NB. split; [lia|].
  unfold L5.u8_at. cbn [rdn]. rewrite E. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Definition sfacts (M : word -> option byte) (sp : Z) : Prop :=
  L5.img_clear M 1273856 1306624 /\ L5.u64_at RSEGS M 1335544 SBL /\ L5.u32_at RSEGS M 1335552 1 /\
  140735332487296 <= sp <= 140737488355328 /\ sp mod 32 = 0 /\ L5.writable RSEGS M (sp - 128) 128.

Definition ffacts (M : word -> option byte) (sp F fl : Z) (zsh : bool) : Prop :=
  4096 <= F <= 140737488355264 /\ F mod 32 = 0 /\ L5.defined M F 64 /\ L5.writable RSEGS M F 64 /\
  (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784) /\ L5.writable RSEGS M (F / 8 + SBL) 8 /\
  (if zsh then L5KA.zeros_at M (F / 8 + SBL) 8 else True) /\
  L5.u64_at RSEGS M (F + 56) fl /\ 4096 <= fl <= 140737488355327 /\ L5.writable RSEGS M fl 1 /\
  (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 64 <= fl \/ fl + 1 <= F) /\
  ((sp - 128) + 128 <= F \/ F + 64 <= sp - 128) /\ ((sp - 128) + 128 <= fl \/ fl + 1 <= sp - 128).

Definition wrunAF (pc0 smra : Z) (rSB : nat) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp : Z),
    0 <= sp < 2 ^ 64 -> getr R (reg 2) = Z_to_bv 64 sp -> sfacts M sp ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 <= i < sp - 128 + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pc0 M) (mst fx' R' SM0 M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 smra /\ getr R' (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R' (reg 8) = Z_to_bv 64 sp /\ getr R' (reg 9) = Z_to_bv 64 (sp - 128)
      /\ getr R' (reg 19) = getr R (reg 10) /\ getr R' (reg rSB) = Z_to_bv 64 SBL
      /\ own sp R M'.

Definition lregs (R : bvmap 5 word) (sp F rr END : Z) (rF2 rSH : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R (reg 8) = Z_to_bv 64 sp /\ getr R (reg 9) = Z_to_bv 64 (sp - 128) /\ getr R (reg 18) = Z_to_bv 64 F
  /\ getr R (reg 19) = Z_to_bv 64 rr /\ getr R (reg 20) = Z_to_bv 64 (F + 32) /\ getr R (reg rF2) = Z_to_bv 64 F /\ getr R (reg rSH) = Z_to_bv 64 (F / 8 + SBL)
  /\ getr R (reg 25) = Z_to_bv 64 (sp - 128 + END).

Definition wrunBF (smra lra TMP VAL END : Z) (rSB rF2 rSH : nat) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp rr F fl : Z),
    0 <= sp < 2 ^ 64 -> 0 <= rr < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - 128) -> getr R (reg 8) = Z_to_bv 64 sp -> getr R (reg 9) = Z_to_bv 64 (sp - 128) -> getr R (reg 10) = Z_to_bv 64 F ->
    getr R (reg 19) = Z_to_bv 64 rr -> getr R (reg rSB) = Z_to_bv 64 SBL ->
    sfacts M sp -> ffacts M sp F fl true ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 120 <= i < sp - 120 + 24) -> ~ (F <= i < F + 24) -> ~ (F + 32 <= i < F + 32 + 8) -> ~ (F / 8 + SBL <= i < F / 8 + SBL + 8) ->
            M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R smra M) (mst fx' R' PBIPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 lra /\ getr R' (reg 10) = Z_to_bv 64 (F + 32) /\ getr R' (reg 11) = Z_to_bv 64 (sp - 128 + TMP) /\ getr R' (reg 24) = Z_to_bv 64 (sp - 128 + VAL)
      /\ lregs R' sp F rr END rF2 rSH
      /\ L5.u64_at RSEGS M' (F + 32) rr /\ L5.u8_at RSEGS M' (F / 8 + 2147450884) 0.

Definition wrunM (lra TMP VAL END : Z) (rF2 rSH : nat) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp rr F fl p nb : Z),
    0 <= sp < 2 ^ 64 -> 0 <= rr < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= nb < 2 ^ 64 ->
    lregs R sp F rr END rF2 rSH -> getr R (reg 24) = Z_to_bv 64 p ->
    sfacts M sp -> ffacts M sp F fl false ->
    4096 <= p <= 140737488355326 -> 128 - END + 2 <= sp - p <= 128 - VAL -> L5.u8_at RSEGS M (p + 1) nb -> 0 <= nb <= 255 ->
    (F + 64 <= p \/ p + 2 <= F) -> (F / 8 + SBL + 8 <= p \/ p + 2 <= F / 8 + SBL) -> (fl + 1 <= p \/ p + 2 <= fl) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 + TMP <= i < sp - 128 + TMP + 1) -> ~ (F + 32 <= i < F + 32 + 8) -> ~ (F / 8 + 2147450884 <= i < F / 8 + 2147450884 + 1) ->
            M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R lra M) (mst fx' R' PBIPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 lra /\ getr R' (reg 10) = Z_to_bv 64 (F + 32) /\ getr R' (reg 11) = Z_to_bv 64 (sp - 128 + TMP) /\ getr R' (reg 24) = Z_to_bv 64 (p + 1)
      /\ lregs R' sp F rr END rF2 rSH
      /\ L5.u64_at RSEGS M' (F + 32) rr /\ L5.u8_at RSEGS M' (F / 8 + 2147450884) 0.

Definition wrunLF (lra END : Z) (rF2 rSH : nat) : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp rr F fl r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= rr < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    lregs R sp F rr END rF2 rSH -> getr R (reg 24) = Z_to_bv 64 (sp - 128 + END - 1) ->
    sfacts M sp -> ffacts M sp F fl false -> own sp R0 M -> getr R0 (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (F <= i < F + 8) -> ~ (F / 8 + SBL <= i < F / 8 + SBL + 8) -> ~ (fl <= i < fl + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R lra M) (mst fx' R' r M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 2) = Z_to_bv 64 sp /\ rest R0 R'
      /\ L5.u8_at RSEGS M' fl 0.

Ltac greg1 KS :=
  first [ assumption
        | lazymatch goal with |- getr ?R1 (reg ?n) = _ =>
            first [ lazymatch goal with H : getr R1 (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end
                  | rewrite (KS n) by inl; lazymatch goal with H : getr _ (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end ] end ].
Ltac gks KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEBENTBFP.aligned; assumption | apply wid | apply wrng | L5SAR.greg | L5SAR.gmem | lia]).

Ltac imm_tac := match goal with |- _ + bv_signed ?i = _ => let v := eval vm_compute in (bv_signed i) in change (bv_signed i) with v end.

Ltac sfacts_via AG K0 K1 K2 K3 K4 K5 MG :=
  first [ assumption | unfold PEBENTBFP.aligned; assumption | apply wid | apply wrng
        | intros i Hi; rewrite (AG i); [apply K0; exact Hi | clear - Hi; lia | clear - Hi K3; lia]
        | eapply (L5C.u64_at_agree RSEGS); [ | | | exact K1]; [intros i Hi; apply (AG i); [clear - Hi; lia| clear - Hi K3; lia] | clear; lia | clear; lia]
        | eapply (PMF.u32_at_agree RSEGS); [ | | | exact K2]; [intros i Hi; apply (AG i); [clear - Hi; lia| clear - Hi K3; lia] | clear; lia | clear; lia]
        | apply (writable_grows _ _ _ _ MG); exact K5
        | L5SAR.greg | L5SAR.gmem | lia ].

Ltac wrun_tacAF A1_conc A2_conc A3_conc FSDPC W_D F_D D_D FMVPC W_F F_F D_F :=
  intros fx R M sp Hsp G2 (K0 & K1 & K2 & K3 & K4 & K5);

  let P := fresh "P" in
  pose proof (A1_conc fx R M (fun j => match j with 2%nat => sp | 43%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) as P; cbn beta iota in P; feedP P;
  let KS1 := fresh "KS1" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T2 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8);

  let MS2 := fresh "MS2" in let MG2 := fresh "MG2" in let FRZ2 := fresh "FRZ2" in let DEF2 := fresh "DEF2" in
  destruct (PEFX.fsd_run RSEGS fx1 R1 M1 FSDPC W_D _ _ _ (sp - 96) F_D eq_refl D_D ltac:(imm_tac; rewrite L5K.rl2, T2, L5.unsigned_lit by (clear - K3; lia); clear; lia)
              ltac:(clear - K3; lia) ltac:(clear - K3; lia)
              ltac:(apply (writable_grows M M1 _ _ MG1); apply (L5.writable_sub _ _ (sp - 128) 128 (sp - 96) 8 K5); clear; lia) ltac:(clear; lia) ltac:(clear; lia))
    as (M2 & MS2 & MG2 & FRZ2 & DEF2);
  let pc1 := eval vm_compute in (FSDPC + 4) in change (FSDPC + 4) with pc1 in MS2;
  let MG02 := fresh "MG02" in pose proof (mem_grows_trans M M1 M2 MG1 MG2) as MG02;
  let AG := fresh "AG" in
  assert (AG : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 <= i < sp - 128 + 128) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    by (intros i Hi Hn; rewrite (FRZ2 i Hi) by (clear - Hn; lia); exact (FRZ1 i Hi Hn));

  let P := fresh "P" in
  pose proof (A2_conc fx1 R1 M2 (fun j => match j with 2%nat => sp | 43%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) as P; cbn beta iota in P;
  L5SAR.feed P ltac:(first [rewrite (KS1 10%nat) by inl; apply wid | sfacts_via AG K0 K1 K2 K3 K4 K5 MG02]);
  let KS3 := fresh "KS3" in
  destruct P as (fx3 & R3 & M3 & MG3 & _ & FRZ3 & MS3 & KS3 & T8 & T9 & T10 & T11 & T19 & TSB);
  pose proof (L5SAR.mem_eq_of_agree M2 M3 ltac:(intros a; apply FRZ3)) as EM3; subst M3;

  let MS4 := fresh "MS4" in
  destruct (PEFX.fsgnj_run RSEGS fx3 R3 M2 FMVPC W_F _ _ _ _ _ F_F eq_refl D_F ltac:(clear; lia) ltac:(clear; lia)) as (fx4 & MS4 & _);
  let pc2 := eval vm_compute in (FMVPC + 4) in change (FMVPC + 4) with pc2 in MS4;

  let P := fresh "P" in
  pose proof (A3_conc fx4 R3 M2 (fun j => match j with 2%nat => sp | 43%nat => bv_unsigned (getr R (reg 10)) | 55%nat => bv_unsigned (getr R3 (reg 10)) | _ => 0 end)) as P; cbn beta iota in P;
  L5SAR.feed P ltac:(first [rewrite (KS3 2%nat) by inl; exact T2 | sfacts_via AG K0 K1 K2 K3 K4 K5 MG02]);
  let KS5 := fresh "KS5" in
  destruct P as (fx5 & R5 & M5 & MG5 & _ & FRZ5 & MS5 & KS5 & T1 & T10');
  pose proof (L5SAR.mem_eq_of_agree M2 M5 ltac:(intros a; apply FRZ5)) as EM5; subst M5;
  exists fx5, R5, M2; split; [exact MG02|]; split; [exact AG|];
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| eapply msteps_trans; [exact MS4| exact MS5]]]]|];
  split; [intros j Hj; rewrite (KS5 j) by (revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl);
          rewrite (KS3 j) by (revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl);
          apply KS1; revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|];
  split; [exact T1|]; split; [rewrite (KS5 2%nat), (KS3 2%nat) by inl; exact T2|]; split; [rewrite (KS5 8%nat) by inl; exact T8|]; split; [rewrite (KS5 9%nat) by inl; exact T9|];
  split; [rewrite (KS5 19%nat) by inl; rewrite T19; symmetry; apply wid|]; split; [rewrite (KS5 _) by inl; exact TSB|];

  let AGS := fresh "AGS" in
  assert (AGS : forall a w, sp - 88 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a w -> L5.u64_at RSEGS M2 a w)
    by (intros a w Ha1 Ha2 U; apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply FRZ2; [clear - Hi Ha1 Ha2 Hsp K3; lia| clear - Hi Ha1 Ha2; lia]| clear - Ha1 K3; lia| clear - Ha2 Hsp; lia| exact U]);
  unfold own; repeat split; first [apply AGS; [clear; lia| clear; lia| assumption] | exact DEF2].

Ltac wrun_tacBF B1_conc B2_conc FMVPC W_F F_F D_F RLV RV :=
  intros fx R M sp rr F fl Hsp Hrr HF Hfl G2 G8 G9 G10 G19 GSB (K0 & K1 & K2 & K3 & K4 & K5) FF0;
  pose proof FF0 as (FR1 & FAL & FDEF & FWR & FBIG & FSHW & FSHZ & FLC & FLR & FLW & FLBIG & FLA & FDJ & FLDJ);

  let P := fresh "P" in
  pose proof (B1_conc fx R M (fun j => match j with 2%nat => sp | 43%nat => rr | 47%nat => F | 48%nat => fl
                                    | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P;
  cbn beta iota in P; feedP P;
  let KS1 := fresh "KS1" in let Q1 := fresh "Q" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & Q1);

  let v := fresh "v" in let Hv := fresh "Hv" in let MSF := fresh "MSF" in
  destruct (PEFX.fmv_xf_run RSEGS fx1 R1 M1 FMVPC W_F _ _ _ F_F eq_refl D_F ltac:(first [left; reflexivity | right; reflexivity]) eq_refl ltac:(clear; lia) ltac:(clear; lia)) as (v & Hv & MSF);
  rewrite RLV in MSF;
  let pc1 := eval vm_compute in (FMVPC + 4) in change (FMVPC + 4) with pc1 in MSF;

  let AG := fresh "AG" in
  lazymatch type of FRZ1 with forall i, _ -> ~ (?lo <= i < ?hi) -> _ =>
    assert (AG : forall a n, (a + n <= lo \/ hi <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M1 a n)
      by (intros a n Ha Ha0 Ha1 i Hi; apply FRZ1; [clear - Hi Ha0 Ha1; lia| clear - Hi Ha; lia]) end;
  let P2 := fresh "P2" in
  pose proof (B2_conc fx1 (regupd R1 (reg RV) (Z_to_bv 64 v)) M1 (fun j => match j with 2%nat => sp | 43%nat => rr | 47%nat => F | 48%nat => fl | 33%nat => v | _ => 0 end)) as P2;
  cbn beta iota in P2; decompose [and] Q1;
  L5SAR.feed P2 ltac:(first [ assumption | unfold PEBENTBFP.aligned; assumption | apply wrng
    | rewrite PEFX.regupd_same_idx by (clear; lia); reflexivity
    | rewrite PEFX.regupd_other_idx by (clear; lia); first [assumption | apply wid | rewrite (KS1 _) by inl; assumption]
    | intros i Hi; rewrite FRZ1; [apply K0; exact Hi | clear - Hi; lia | clear - Hi K3; lia]
    | apply (L5C.u64_at_agree RSEGS M M1); [apply AG; [first [clear - K3; lia | clear - FDJ; lia] | clear - FR1; lia| clear - FR1; lia] | clear - FR1; lia | clear - FR1; lia | assumption]
    | apply (PMF.u32_at_agree RSEGS M M1); [apply AG; [clear - K3; lia| clear; lia| clear; lia] | clear; lia | clear; lia | assumption]
    | apply (writable_grows M M1); [exact MG1 | assumption]
    | apply (L5.defined_grows M M1); [exact MG1 | assumption]
    | apply (L5KA.zeros_at_agree1 M M1); [intros i Hi; apply FRZ1; [clear - Hi FR1; unfold SB in *; lia | clear - Hi FR1 K3; unfold SB in *; lia] | assumption]
    | lia ]);
  let KS2 := fresh "KS2" in let Q2 := fresh "Q" in
  destruct P2 as (fx2 & R2 & M2 & MG2 & _ & FRZ2 & MS2 & KS2 & Q2);
  exists fx2, R2, M2; split; [exact (mem_grows_trans M M1 M2 MG1 MG2)|];
  split; [intros i Hi N1 N2 N3 N4; rewrite (FRZ2 i Hi); [apply FRZ1; [exact Hi| clear - N1; lia] | clear - N1; lia| clear - N2; lia| clear - N3; lia| clear - N4; lia]|];
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MSF| exact MS2]]|];
  decompose [and] Q2;
  split; [intros j Hj; rewrite (KS2 j) by (revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl);
          rewrite PEFX.regupd_other_idx by (revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; lia);
          apply KS1; revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|];
  unfold lregs; repeat split;
  first [ assumption
        | greg1 KS2
        | rewrite (KS2 _) by inl; rewrite PEFX.regupd_other_idx by (clear; lia); greg1 KS1 ].

Ltac wrun_tacM M_conc :=
  intros fx R M sp rr F fl p nb Hsp Hrr HF Hfl Hp Hnb LR G24 (K0 & K1 & K2 & K3 & K4 & K5) FF0 P1 P2 P3 P4 P5 P6 P7;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & GF2 & GSH & G25);
  let P := fresh "P" in
  pose proof (M_conc fx R M (fun j => match j with 2%nat => sp | 43%nat => rr | 47%nat => F | 48%nat => fl | 36%nat => p | 40%nat => nb
                                    | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P;
  cbn beta iota in P; unfold ffacts in FF0; decompose [and] FF0; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia]|];
  split; [exact MS1|];
  decompose [and] P; split; [gks KS|]; unfold lregs; repeat split; greg1 KS.

Ltac wrun_tacLF L1_conc Z_conc FLDPC W_D F_D D_D RETPC W_S F_S D_S :=
  intros fx R R0 M sp rr F fl r Hsp Hrr HF Hfl LR G24 (K0 & K1 & K2 & K3 & K4 & K5) FF0 OWN0 Hra RA;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & GF2 & GSH & G25);
  unfold own in OWN0; destruct OWN0 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & D96);
  let Hr1 := fresh "Hr1" in let Hr2 := fresh "Hr2" in pose proof RA as (Hr1 & Hr2);
  rewrite Hra, L5.unsigned_lit in S8 by (clear - Hr1; lia);

  let P := fresh "P" in
  pose proof (L1_conc fx R M (fun j => match j with 2%nat => sp | 43%nat => rr | 47%nat => F | 48%nat => fl | 64%nat => r
                                    | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9)) | 67%nat => bv_unsigned (getr R0 (reg 18))
                                    | 68%nat => bv_unsigned (getr R0 (reg 19)) | 69%nat => bv_unsigned (getr R0 (reg 20)) | 70%nat => bv_unsigned (getr R0 (reg 21))
                                    | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23)) | 73%nat => bv_unsigned (getr R0 (reg 24))
                                    | 74%nat => bv_unsigned (getr R0 (reg 25))
                                    | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P;
  cbn beta iota in P; pose proof FF0 as (FR1 & FAL & FDEF & FWR & FBIG & FSHW & FSHZ & FLC & FLR & FLW & FLBIG & FLA & FDJ & FLDJ); feedP P;
  let KS1 := fresh "KS1" in let T1 := fresh "T1" in let Q1 := fresh "Q" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & Q1);

  let MS2 := fresh "MS2" in
  destruct (PEFX.fld_run RSEGS fx1 R1 M1 FLDPC W_D _ _ _ (sp - 96) F_D eq_refl D_D
              ltac:(imm_tac; rewrite L5K.rl2; rewrite (KS1 2%nat) by inl; rewrite G2, L5.unsigned_lit by (clear - K3; lia); clear; lia)
              ltac:(clear - K3; lia) ltac:(clear - K3; lia)
              ltac:(intros i Hi; rewrite (FRZ1 (sp - 96 + i)); [apply D96; exact Hi| clear - Hi K3 Hsp; lia| clear - Hi K3 FDJ; lia| clear - Hi K3 FR1; unfold SB; lia| clear - Hi K3 FLDJ; lia])
              ltac:(clear; lia) ltac:(clear; lia)) as (fx2 & MS2 & _);
  let pc1 := eval vm_compute in (FLDPC + 4) in change (FLDPC + 4) with pc1 in MS2;

  let P := fresh "P" in
  pose proof (Z_conc fx2 R1 M1 (fun j => match j with 2%nat => sp | 55%nat => bv_unsigned (getr R1 (reg 10)) | 56%nat => bv_unsigned (getr R1 (reg 11)) | 57%nat => bv_unsigned (getr R1 (reg 12)) | _ => 0 end)) as P;
  cbn beta iota in P; L5SAR.feed P ltac:(first [assumption | apply wid | apply wrng | rewrite (KS1 2%nat) by inl; exact G2 | lia]);
  let KS3 := fresh "KS3" in let T2 := fresh "T2" in
  destruct P as (fx3 & R3 & M3 & MG3 & _ & FRZ3 & MS3 & KS3 & T2);
  pose proof (L5SAR.mem_eq_of_agree M1 M3 ltac:(intros a; apply FRZ3)) as EM3; subst M3;

  let MSR := fresh "MSR" in
  pose proof (PMK.ret_to RSEGS fx3 R3 M1 RETPC W_S r F_S eq_refl D_S ltac:(rewrite (KS3 1%nat) by inl; exact T1) ltac:(clear - Hr1; lia) Hr2) as MSR;
  exists fx3, R3, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia]|];
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MSR]]]|];
  decompose [and] Q1;
  split; [intros j Hj; rewrite (KS3 j) by (revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl); apply KS1; revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|];
  split; [exact T2|]; split; [| assumption];
  apply rest_of_own; rewrite (KS3 _) by inl; greg1 KS1.

Lemma f32_runA : wrunAF 0xb3c2c 0xb3c9c 21.
Proof. unfold wrunAF. wrun_tacAF PEBENTBFP.bntbf32A1_conc PEBENTBFP.bntbf32A2_conc PEBENTBFP.bntbf32A3_conc 0xb3c60 W_b3c10 F_b3c10 D_b3c10 0xb3c8c W_b3c3c F_b3c3c D_b3c3c. Qed.
Lemma f32_runB : wrunBF 0xb3c9c 0xb3d8c 27 28 32 21 22 21.
Proof. unfold wrunBF. wrun_tacBF PEBENTBFP.bntbf32B1_conc PEBENTBFP.bntbf32B2_conc 0xb3cf0 W_b3ca0 F_b3ca0 D_b3ca0 L5K.rl13 13%nat. Qed.
Lemma f32_runM : wrunM 0xb3d8c 27 28 32 22 21. Proof. unfold wrunM. wrun_tacM PEBENTBFP.bntbf32M_conc. Qed.
Lemma f32_runL : wrunLF 0xb3d8c 32 22 21.
Proof. unfold wrunLF. wrun_tacLF PEBENTBFP.bntbf32L1_conc PEBENTBFP.bntbf32Z_conc 0xb3e28 W_b3dd8 F_b3dd8 D_b3dd8 0xb3e30 W_b3de0 F_b3de0 D_b3de0. Qed.

Lemma f64_runA : wrunAF 0xb3e38 0xb3ea8 22.
Proof. unfold wrunAF. wrun_tacAF PEBENTBFP.bntbf64A1_conc PEBENTBFP.bntbf64A2_conc PEBENTBFP.bntbf64A3_conc 0xb3e6c W_b3e1c F_b3e1c D_b3e1c 0xb3e98 W_b3e48 F_b3e48 D_b3e48. Qed.
Lemma f64_runB : wrunBF 0xb3ea8 0xb3fcc 23 24 32 22 21 22.
Proof. unfold wrunBF. wrun_tacBF PEBENTBFP.bntbf64B1_conc PEBENTBFP.bntbf64B2_conc 0xb3ef8 W_b3ea8 F_b3ea8 D_b3ea8 L5K.rl16 16%nat. Qed.
Lemma f64_runM : wrunM 0xb3fcc 23 24 32 21 22. Proof. unfold wrunM. wrun_tacM PEBENTBFP.bntbf64M_conc. Qed.
Lemma f64_runL : wrunLF 0xb3fcc 32 21 22.
Proof. unfold wrunLF. wrun_tacLF PEBENTBFP.bntbf64L1_conc PEBENTBFP.bntbf64Z_conc 0xb4068 W_b4018 F_b4018 D_b4018 0xb4070 W_b4020 F_b4020 D_b4020. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMB.ly_as0 L C LY.

Hypothesis PBI : PEPBI.push_back_indZ_specA RSEGS AD L ar HI PBIPC P.

Section Writer.
Variables (pc0 smra lra TMP VAL END : Z) (KB : Z) (rF2 rSH : nat).
Hypothesis RUNA : wrunAF pc0 smra rSH.
Hypothesis RUNB : wrunBF smra lra TMP VAL END rSH rF2 rSH.
Hypothesis RUNM : wrunM lra TMP VAL END rF2 rSH.
Hypothesis RUNL : wrunLF lra END rF2 rSH.
Hypothesis HKB : 1 <= KB <= 8.
Hypothesis HEND : END = VAL + KB /\ TMP + 1 = VAL /\ 16 <= TMP /\ END <= 32.
Hypothesis SMRA : 0 <= smra < 2 ^ 64 /\ smra mod 2 = 0.
Hypothesis RAOK : L5.ra_ok lra.
Hypothesis HRF2 : In rF2 [21; 22]%nat /\ In rSH [21; 22]%nat.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (rr o sp r h : Z) (k : PESK.sink).
Hypothesis HH : ri_inv HI (PESK.sink_own k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 2.
Hypothesis FRM : PMSPA.ffroomA 2 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 rr.
Hypothesis RRO : L5.u64_at RSEGS M rr o.
Hypothesis ALrr : rr mod 8 = 0.
Hypothesis AOrr : PMSPA.aobjA FF rr 8.
Hypothesis ACCrr : PMSPA.accA M rr 8.
Hypothesis RRdj : o + 24 <= rr \/ rr + 8 <= o.
Hypothesis SKA : PESKA.sink_atA RSEGS L ar P M o k.
Hypothesis AOo : PMSPA.aobjA FF o 24.
Hypothesis ALo : o mod 8 = 0.
Hypothesis HBh : PESKA.spa_hb P h.
Hypothesis ZKB : PESK.sk_z k + KB <= h.
Hypothesis CRED : PMSP.credit_le (PESKA.spa_pot P (PESK.sk_c k)) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (cr' : credit) (k' : PESK.sink),
        regs_preserved R R' -> PESK.sk_z k' = PESK.sk_z k + KB -> PESKA.sink_atA RSEGS L ar P M' o k' ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 2) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PESKA.spa_pot P (PESK.sk_c k)) (PESKA.spa_pot P (PESK.sk_c k')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PESK.sink_own k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Let Ws : list L5.range := [(o, 24)].
Let spc : Z := sp - 128.
Definition csk (Ri : bvmap 5 word) : Prop := forall j, In j CSK -> getr Ri (reg j) = getr R (reg j).

Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 2) with 16384 in ASTK, STKSH; change (16384 / 8) with 2048 in STKSH;
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2); pose proof RAOK as (Hra1 & Hra2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl3 in Rgp; rewrite L5K.rl4 in Rtp;
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & NDF & _).

Lemma SPd8 d : d mod 8 = 0 -> (sp - d) mod 8 = 0.
Proof.
  intros Hd. pose proof (Z.div_mod sp 32 ltac:(lia)) as E0. rewrite SP32, Z.add_0_r in E0. pose proof (Z.div_mod d 8 ltac:(lia)) as E1. rewrite Hd, Z.add_0_r in E1.
  rewrite E0, E1. replace (32 * (sp / 32) - 8 * (d / 8)) with ((4 * (sp / 32) - d / 8) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma SPd16 d : d mod 16 = 0 -> (sp - d) mod 16 = 0.
Proof.
  intros Hd. pose proof (Z.div_mod sp 32 ltac:(lia)) as E0. rewrite SP32, Z.add_0_r in E0. pose proof (Z.div_mod d 16 ltac:(lia)) as E1. rewrite Hd, Z.add_0_r in E1.
  rewrite E0, E1. replace (32 * (sp / 32) - 16 * (d / 16)) with ((2 * (sp / 32) - d / 16) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma ws_wapp : PMKB.wapp Ws.
Proof.
  entry_facts. pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model o 24 sp 16384 HH (PMKB.aobj_of_aobjA FF o 24 AOo ALo) ltac:(lia) ltac:(reflexivity)) as (_ & OBIG & _).
  unfold Ws. apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG. lia.
Qed.

Lemma rr_facts : 6930432 <= rr /\ rr + 8 <= ahl_ceil ar /\ rr + 8 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= rr \/ rr + 8 <= 2147446784)
                 /\ 6930432 <= o /\ o + 24 <= ahl_ceil ar /\ o + 24 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= o \/ o + 24 <= 2147446784)
                 /\ ahl_ceil ar + 4096 + 16384 <= sp /\ sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47.
Proof.
  entry_facts.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model rr 8 sp 16384 HH (PMKB.aobj_of_aobjA FF rr 8 AOrr ALrr) ltac:(lia) ltac:(reflexivity)) as ((Q1 & Q2 & Q3 & _) & QBIG & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model o 24 sp 16384 HH (PMKB.aobj_of_aobjA FF o 24 AOo ALo) ltac:(lia) ltac:(reflexivity)) as ((O1 & O2 & O3 & _) & OBIG & _).
  repeat split; first [assumption | clear - SPT; lia].
Qed.

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Let G_ := PMBUK.gctx L ar HI LBX FF LK Aw sp 16384 spc (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PESK.sink_own k).
Hypothesis G : G_.
Let FF' : list fframe := (F, 0, spc + 32) :: FF.
Let BINV := PMBUK.binv L ar HI M model LBX FF LK Aw sp 16384 spc (own sp R) F 0 Ws.

Hypothesis APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (PESK.sink_own k ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n ->
    (a + n <= F \/ F + 64 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + 8 <= a) /\ (a + n <= fl \/ fl + 1 <= a).

Definition sinv (Mi : word -> option byte) (cri : credit) (ki : PESK.sink) (j : Z) : Prop :=
  PESKA.sink_atA RSEGS L ar P Mi o ki /\ PESK.sk_z ki = PESK.sk_z k + j /\ L5.u64_at RSEGS Mi rr o /\ PMSPA.accA Mi rr 8
  /\ PMSP.credit_keep cr cri (PESKA.spa_pot P (PESK.sk_c k)) (PESKA.spa_pot P (PESK.sk_c ki))
  /\ shadow_zero Mi (sp - 16384) 2048.

Lemma g_facts :
  4096 <= F /\ F + 64 <= 2 ^ 47 /\ 6930432 <= F /\ F mod 32 = 0 /\ F / 8 * 8 = F /\ (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784)
  /\ 4096 <= fl /\ fl + 1 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 64 <= fl \/ fl + 1 <= F)
  /\ F + 64 <= ahl_ceil ar /\ fl + 1 <= ahl_ceil ar /\ incl LK2 LK
  /\ (rr + 8 <= F \/ F + 64 <= rr) /\ (rr + 8 <= F / 8 + SB \/ F / 8 + SB + 8 <= rr) /\ (rr + 8 <= fl \/ fl + 1 <= rr)
  /\ (o + 24 <= F \/ F + 64 <= o) /\ (o + 24 <= F / 8 + SB \/ F / 8 + SB + 8 <= o) /\ (o + 24 <= fl \/ fl + 1 <= o)
  /\ ar_fs ar <= F /\ F + 64 <= ar_fs ar + FS_BYTES.
Proof.
  entry_facts. pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model rr 8 sp 16384 HH (PMKB.aobj_of_aobjA FF rr 8 AOrr ALrr) ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & _ & _ & QCL & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model o 24 sp 16384 HH (PMKB.aobj_of_aobjA FF o 24 AOo ALo) ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & _ & _ & OCL & _).
  destruct (APART rr 8 sp 16384 QCL ltac:(clear; lia)) as (AqF & AqS & AqL).
  destruct (APART o 24 sp 16384 OCL ltac:(clear; lia)) as (AoF & AoS & AoL).
  repeat split; first [assumption | clear - GFR; lia | clear - GF8; lia | clear - GFLR; lia].
Qed.

Lemma vis_factsW Mc mdc LKc crc Awc kc :
  BINV (PESK.sink_own kc) Mc mdc LKc crc Awc ->
  let MV := mrestrict (ahid Awc mdc) Mc in
  sfacts MV sp /\ ffacts MV sp F fl false /\ own sp R MV
  /\ (forall a n, spc <= a -> a + n <= sp -> L5A.avis (ahid Awc mdc) a n) /\ L5A.avis (ahid Awc mdc) F 64 /\ L5A.avis (ahid Awc mdc) (F / 8 + SB) 8 /\ L5A.avis (ahid Awc mdc) fl 1.
Proof.
  intros BI MV. entry_facts.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & _).
  pose proof rr_facts as (_ & _ & _ & _ & _ & _ & _ & _ & SLO' & SHI' & SPT').
  destruct (PMBUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 16384 spc (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PESK.sink_own k) G
              Ws (PESK.sink_own kc) Mc mdc LKc crc Awc BI)
    as ((W0 & W1 & W2 & W3 & W4) & OWNv & (FD & FW & FSW & FLC & FLW) & (_ & VFL & VF & VS & VSH)).
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold MV in W0, W1, W2, W3, W4, OWNv, FD, FW, FSW, FLC, FLW.
  replace (sp - spc) with 128 in W0, VS by (unfold spc; clear; lia).
  split. { split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [clear - SLO' SHI' SPT'; lia|]. split; [exact SP32| exact W0]. }
  split. { unfold ffacts. replace (F + 56) with (F + 64 - 8) by (clear; lia).
           repeat split; first [exact FD | exact FW | exact FSW | exact FLC | exact FLW | exact I | clear - GF1 GF2 GF32 GFBIG GL1 GL2 GLBIG GFLA GFC GLC SLO'; lia]. }
  split. exact OWNv.
  split. { intros a n H1 H2. replace a with (spc + (a - spc)) by (clear; lia). eapply L5A.avis_sub; [exact VS| clear - H1; lia| clear - H1 H2; lia]. }
  split. exact VF. split. exact VSH. exact VFL.
Qed.

Lemma frame_agree (Ma Mb : word -> option byte) (Wp : Z -> Prop) :
  (forall a, Wp a -> (spc <= a < sp) \/ (F <= a < F + 64) \/ (F / 8 + SB <= a < F / 8 + SB + 8)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  (forall a, 0 <= a -> a + 1 <= ahl_ceil ar -> (a + 1 <= F \/ F + 64 <= a) -> (2147446784 + 17592186048512 <= a \/ a + 1 <= 2147446784) ->
      Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a))
  /\ (forall x, 0 <= x -> x + 1 <= 2 ^ 47 -> (x + 1 <= F \/ F + 64 <= x) -> Mb (Z_to_bv 64 (HeapIfaceA.S x)) = Ma (Z_to_bv 64 (HeapIfaceA.S x))).
Proof.
  intros WP AG. entry_facts.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & _).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  split.
  - intros a H0 H1 H2 H3. apply AG; [clear - H0 H1 SPT; Lia.lia|]. intros X. destruct (WP a X) as [Y|[Y|Y]].
    + unfold spc in Y. clear - Y H1 SLO. Lia.lia.
    + clear - Y H2. Lia.lia.
    + unfold SB in Y. clear - Y H3 GF1 GF2 GF8. Lia.lia.
  - intros x H0 H1 H2. apply AG; [unfold HeapIfaceA.S, SB; clear - H0 H1; Lia.lia|]. intros X. destruct (WP _ X) as [Y|[Y|Y]]; unfold HeapIfaceA.S, SB in Y.
    + unfold spc in Y. clear - Y H0 H1 SLO SPT. Lia.lia.
    + clear - Y H0 H1 GFBIG. Lia.lia.
    + clear - Y H2 GF8. Lia.lia.
Qed.

Lemma sinv_agree (Ma Mb : word -> option byte) (Wp : Z -> Prop) LKc crc Awc V kc j :
  ri_inv HI (PESK.sink_own kc ++ LBX) FF' LKc crc Awc Ma V ->
  (forall a, Wp a -> (spc <= a < sp) \/ (F <= a < F + 64) \/ (F / 8 + SB <= a < F / 8 + SB + 8)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  sinv Ma crc kc j -> sinv Mb crc kc j.
Proof.
  intros HHc WP AG (SKAc & ZJ & RRc & ACCc & CKc & SZc). entry_facts.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AqF & AqS & AqL & AoF & AoS & AoL & GFS1 & GFS2).
  pose proof rr_facts as (Q1' & Q2' & Q3' & QBIG & O1 & O2 & O3 & OBIG & _).
  destruct (frame_agree Ma Mb Wp WP AG) as [AGa AGs].
  unfold sinv. split.
  - apply (PECFA.sink_atA_agree RSEGS L ar Ma Mb P o kc); [clear - O1; lia| clear - O3; lia| | | exact SKAc].
    + split; [intros i Hi; apply AGa; clear - Hi O1 O2 O3 OBIG AoF; lia| intros x Hx; apply AGs; clear - Hx O1 O3 AoF; lia].
    + intros Hp. assert (IN : In (PESK.sk_b kc, PESK.sk_c kc) (PESK.sink_own kc ++ LBX)).
      { apply in_or_app. left. unfold PESK.sink_own. replace (PESK.sk_c kc =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
      destruct (L5ADHR.blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ (PESK.sink_own kc ++ LBX) [] HHc (eq_sym (app_nil_r _)) _ IN) as ((B0 & _ & _ & _ & BCEIL & (_ & BAPP & B47)) & BFS).
      cbn [fst snd] in B0, BCEIL, BAPP, B47, BFS. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAPP. unfold FS_BYTES in BFS, GFS2.
      split; [clear - B0; lia|]. split; [clear - B47; lia|].
      split; [intros i Hi; apply AGa; clear - Hi B0 BCEIL BAPP BFS GFS1 GFS2; lia| intros x Hx; apply AGs; clear - Hx B0 B47 BFS GFS1 GFS2; lia].
  - split; [exact ZJ|]. split.
    + eapply L5C.u64_at_agree; [| | | exact RRc]; [intros i Hi; apply AGa; clear - Hi Q1' Q2' Q3' QBIG AqF; lia| clear - Q1'; lia| clear - Q3'; lia].
    + split; [| split; [exact CKc|]].
      * intros x Hx. unfold byte_at. rewrite (AGs x); [exact (ACCc x Hx)| clear - Hx Q1'; lia| clear - Hx Q3'; lia| clear - Hx AqF; lia].
      * intros jj Hjj. pose proof (SZc jj Hjj) as Z0. unfold byte_at in Z0 |- *.
        replace (HeapIfaceA.S (sp - 16384) + jj) with (HeapIfaceA.S (sp - 16384 + jj * 8)) in Z0 |- * by (unfold HeapIfaceA.S; rewrite Z.div_add by (clear; lia); clear; lia).
        rewrite (AGs (sp - 16384 + jj * 8)); [exact Z0| clear - Hjj SLO SPT; lia| clear - Hjj SHI SPT; lia| clear - Hjj GFC SLO; lia].
Qed.

Lemma pbw (j : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  BINV (PESK.sink_own kq) Mq mdq LKq crq Awq -> sinv Mq crq kq j -> 0 <= j -> j + 1 <= KB ->
  getr Rq (reg 1) = Z_to_bv 64 lra -> getr Rq (reg 2) = Z_to_bv 64 spc -> getr Rq (reg 10) = Z_to_bv 64 (F + 32) -> getr Rq (reg 11) = Z_to_bv 64 (spc + TMP) -> csk Rq ->
  L5.u64_at RSEGS Mq (F + 32) rr -> L5.u8_at RSEGS Mq (F / 8 + 2147450884) 0 ->
  (forall (fx2 : FPState) R2 Mx mdx LKx Awx crx kx, BINV (PESK.sink_own kx) Mx mdx LKx crx Awx -> sinv Mx crx kx (j + 1) -> regs_preserved Rq R2 ->
      (forall a, spc <= a < sp -> Mx (Z_to_bv 64 a) = Mq (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 lra Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq PBIPC Mq mdq) K.
Proof.
  intros BI SI J0 J1 Q1 Q2 Q10 Q11 QCS UQ USH KX. entry_facts.
  pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AqF & AqS & AqL & AoF & AoS & AoL).
  pose proof rr_facts as (Q1' & Q2' & Q3' & QBIG & O1 & O2 & O3 & OBIG & _).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). change (ff_bytes 0 / 8) with 8 in B10.
  pose proof SI as (SKAq & ZJ & RRq & ACCq & CKq & SZq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  pose proof B6 as (_ & _ & _ & _ & SDEFq & _).
  destruct (vis_factsW Mq mdq LKq crq Awq kq BI) as (_ & (_ & _ & FDv & _) & _ & VS & VF & VSH & VFL).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq rr 8 sp 16384 B1 (PMKB.aobj_of_aobjA FF' rr 8 (PMBUAR.aobjA_push FF rr 8 _ AOrr) ALrr) ltac:(lia) ltac:(reflexivity))
    as (_ & _ & RDEFq & _).
  assert (FRBq : forall f, In f FF' -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ B1).
  pose proof SKAq as (_ & _ & _ & _ & _ & KZCq & KCAPq & KC0q & KBLKq).
  assert (E8 : sp - 16384 = 8 * ((sp - 16384) / 8)) by (pose proof (Z.div_mod (sp - 16384) 8 ltac:(clear; lia)) as X; pose proof (SPd8 16384 eq_refl) as Y; clear - X Y; lia).

  pose proof PBI as PBX. unfold PEPBI.push_back_indZ_specA in PBX.
  apply (PBX PMODE fxq Rq Mq mdq K LBX FF' LKq Awq crq (F + 32) rr o (spc + TMP) spc lra kq B1 B2 K0); clear PBX.
  -
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RAOK|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792. split.
    + unfold spc. apply (L5SAR.astk_sub ar Mq Mq sp 16384 128 14336 B6 (mem_grows_refl Mq)); [clear; lia| clear; lia| clear; lia| apply SPd16; reflexivity].
    + unfold spc. apply (PMKB.shadow_zero_sub Mq (sp - 16384) 2048); [apply SPd8; reflexivity| replace (sp - 128 - 14336) with (sp - 14464) by (clear; lia); apply SPd8; reflexivity| clear; lia| clear; lia| clear; lia| exact SZq].
  -   apply (PMBUAR.ffroomA_push 2 1 FF LK LKq _ FRM B5); [exact NDFq| clear; lia].
  -   apply (PMBUAR.ffrsA_push FF sp spc F 0 (spc + 32) FRS); [clear; lia| unfold spc; clear; lia].
  - rewrite L5K.rl10. exact Q10.
  - rewrite L5K.rl11. exact Q11.
  - exact UQ.
  - exact ALrr.
  - clear - Q1'; lia.
  - exact RRq.
  - clear - O1; lia.
  -
    apply (proj1 (L5A.defined_vis (ahid Awq mdq) Mq (F + 32) 8 (L5A.avis_sub _ F 64 (F + 32) 8 VF ltac:(clear; lia) ltac:(clear; lia)))).
    intros i Hi. replace (F + 32 + i) with (F + (32 + i)) by (clear; lia). apply FDv. clear - Hi; lia.
  -
    intros x Hx. left. replace (HeapIfaceA.S x) with (F / 8 + 2147450884) by (unfold HeapIfaceA.S, SB; clear - Hx GF8; Lia.nia).
    apply byte_at_of_u8; [exact USH|]. replace (F / 8 + 2147450884) with (F / 8 + SB + 4) by (unfold SB; clear; lia). apply (B10 4). clear; lia.
  -   exists (F, 0, spc + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 0) with 64. clear; lia.
  - replace (F + 32) with ((F / 8 + 4) * 8) by (clear - GF8; lia). apply Z_mod_mult.
  - exact (PMBUAR.aobjA_push FF rr 8 _ AOrr).
  - exact RDEFq.
  - exact ACCq.
  - exact SKAq.
  - exact (PMBUAR.aobjA_push FF o 24 _ AOo).
  - exact ALo.
  -
    split. { intros i Hi. unfold spc. replace (sp - 128 + TMP + i) with (sp - 16384 + (16256 + TMP + i)) by (clear; lia). apply SDEFq. clear - Hi HEND HKB; lia. }
    split. { right. unfold spc. clear - O2 SLO HEND HKB; lia. }
    left. split; [unfold spc; clear - HEND HKB; lia|]. split; [unfold spc; clear - HEND HKB SHI; lia|].
    unfold HeapIfaceA.S. unfold spc. replace (sp - 128 + TMP) with (((sp - 16384) / 8) * 8 + (16256 + TMP)) by (clear - E8; lia). rewrite Z.div_add_l by (clear; lia).
    replace ((sp - 16384) / 8 + (16256 + TMP) / 8 + SB) with (HeapIfaceA.S (sp - 16384) + (16256 + TMP) / 8) by (unfold HeapIfaceA.S; clear; lia).
    apply SZq. split; [apply Z.div_pos; clear - HEND HKB; lia| apply Z.div_lt_upper_bound; clear - HEND HKB; lia].
  -
    intros ZC. apply (PESKA.spao_next L P PO (PESK.sk_c kq) h KCAPq); [intros Hc; exact (proj1 (proj2 (proj2 (proj2 (proj2 (KBLKq Hc))))))| exact HBh| clear - ZC ZJ ZKB J0 J1; lia].
  - unfold PMSP.credit_le, PMSP.credit_keep in CRED, CKq |- *. clear - CRED CKq. lia.
  -
    intros fx2 R2 Mx mdx LKx Awx crx b2 RP2 SKA2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
    change (PMSPA.pm_scr 1) with 14336 in HP2. set (k2 := PESK.sk_push kq b2) in *.
    assert (OWs : forall a0, sp - 16384 <= a0 < sp -> L5.outside Ws a0).
    { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha0 O2 SLO; lia. }
    assert (BI2 : BINV (PESK.sink_own k2) Mx mdx LKx crx Awx).
    { apply (PMBUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 16384 spc (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PESK.sink_own k) G
               Ws Ws (PESK.sink_own kq) [] (PESK.sink_own k2) Mq mdq LKq crq Awq Mx mdx LKx crx Awx 14336 Ws BI HP2 HH2 AM2 MRT2 IAW2 ILK2).
      - clear; lia.
      - unfold spc; clear; lia.
      - intros r0 a [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. change (ff_bytes 0 / 8) with 8. unfold ocell. split; [clear - Hr O2 SLO; lia| clear - Hr AoS; lia].
      - intros a _ Oa. exact Oa.
      - intros a Oa. exact Oa. }
    assert (EK12 : L5SAR.ek L ar LBX FF' sp 16384 Ws Mq Mx).
    { apply (L5SAR.ek_callee L ar LBX [] FF' [] sp 16384 spc 14336 Ws Ws Mq Mx HP2); [unfold spc; clear; lia| unfold spc; clear; lia| intros a0 _ O; exact O]. }
    pose proof ws_wapp as WAPP.
    apply (KX fx2 R2 Mx mdx LKx Awx crx k2 BI2); [| exact RP2|].
    + unfold sinv. split; [exact SKA2|].
      split; [unfold k2, PESK.sk_push; destruct (PESK.sk_z kq <? PESK.sk_c kq); cbn [PESK.sk_z]; clear - ZJ; lia|].
      split; [apply (PMKB.u64_keepA RSEGS L ar LBX FF' sp 16384 Ws Mq Mx EK12 WAPP FRBq rr o (PMBUAR.aobjA_push FF rr 8 _ AOrr)); [| exact RRq]; intros i Hi r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; clear - Hi RRdj; lia|].
      split; [exact (PMKB.acc_keepA' L ar LBX FF' sp 16384 Ws Mq Mx EK12 WAPP FRBq rr 8 (PMBUAR.aobjA_push FF rr 8 _ AOrr) ACCq)|].
      split; [unfold PMSP.credit_keep in CKq, CK2 |- *; clear - CKq CK2; lia|].
      apply (PMKB.stksh_keepA L ar LBX FF' sp 16384 Ws Mq Mx EK12 WAPP (sp - 16384) 2048); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq].
    + intros a Ha. pose proof HP2 as (P2 & _). apply P2. split; [unfold spc in Ha; clear - Ha SLO SHI SPT; lia|]. split.
      * unfold aclient, aclient_g. right; left. split; [unfold spc in Ha; clear - Ha SLO SHI SPT; lia| intros Y; clear - Ha Y; lia].
      * apply OWs. unfold spc in Ha; clear - Ha; lia.
Qed.

Lemma loop (m : nat) : forall (j : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq,
  Z.of_nat m = KB - 1 - j -> 0 <= j ->
  BINV (PESK.sink_own kq) Mq mdq LKq crq Awq -> sinv Mq crq kq (j + 1) ->
  lregs Rq sp F rr END rF2 rSH -> getr Rq (reg 24) = Z_to_bv 64 (spc + VAL + j) -> csk Rq ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq lra Mq mdq) K.
Proof.
  induction m as [|m IH]; intros j fxq Rq Mq mdq LKq Awq crq kq Hm J0 BI SI LR Q24 QCS.
  -
    assert (JE : j = KB - 1) by (clear - Hm; lia). entry_facts.
    pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AqF & AqS & AqL & AoF & AoS & AoL).
    pose proof rr_facts as (Q1' & Q2' & Q3' & QBIG & O1 & O2 & O3 & OBIG & _).
    pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof SI as (SKAq & ZJ & RRq & ACCq & CKq & SZq).
    destruct (vis_factsW Mq mdq LKq crq Awq kq BI) as (SFv & FFv & OWNv & VS & VF & VSH & VFL).
    set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
    unfold PMSPA.cfg.
    destruct (RUNL fxq Rq R MV sp rr F fl r ltac:(clear - SLO SHI SPT; lia) ltac:(clear - Q1' Q3'; lia) ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia)
                   LR ltac:(rewrite Q24; f_equal; unfold spc; clear - JE HEND; lia) SFv FFv OWNv Rra RAok)
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T2 & REST & FL0).
    apply (PMBUK.retire_core L ar C HI LYa HIok M model LBX FF LK Aw sp 16384 spc (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PESK.sink_own k) G
             Ws (PESK.sink_own kq) Mq mdq LKq crq Awq fxq fx3 Rq lra R3 r M3v K BI MS3 MG3).
    { intros a Ha Nw. unfold PMBUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw. change (64 / 8) with 8 in Nw.
      apply FRZ3; [exact Ha| intros X'; apply Nw; left; left; exact X'| intros X'; apply Nw; left; right; unfold SB; exact X'| intros X'; apply Nw; right; clear - X'; lia]. }
    { exact FL0. }
    intros Mf mdf FZf AHf MRTf AMf HHf.
    set (LBq := PESK.sink_own kq ++ LBX) in *.
    assert (EKf : L5SAR.ek L ar LBq FF 0 0 [] Mq Mf).
    { apply (PMBUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 16384 spc (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PESK.sink_own k)
               LBq LKq crq Awq Mq Mf _ [] (fun _ => False) G B1 (fun a X' => match X' with end)).
      intros a Ha N. apply FZf; [exact Ha| intros X'; apply N; left; exact X']. }
    pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ B1) as BRBq. pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ B1) as FRBq'.
    assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by (intros f Hf; apply FRBq'; right; exact Hf).
    apply (KONT fx3 R3 Mf mdf LKq Awq crq kq).
    + apply L5SAR.preserved_by_index. intros jj Hj. unfold L5SAR.cs_all in Hj.
      repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | apply REST; inl | rewrite (KS3 _) by inl; apply QCS; inl ] |]). destruct Hj.
    + rewrite ZJ, JE. clear; lia.
    + apply (PECFA.sink_keepA RSEGS L ar LBq FF 0 0 [] Mq Mf EKf PMKB.wapp_nil FRBq BRBq P o kq AOo); [intros i _ r0 []| unfold LBq; apply incl_appl; apply incl_refl| intros _ i _ r0 []| exact SKAq].
    + change (PMSPA.pm_scr 2) with 16384. exact AHf.
    + exact CKq.
    + exact MRTf.
    + exact B5.
    + exact B4.
    + exact AMf.
    + exact HHf.
  -
    assert (JB : j + 1 <= KB - 1) by (clear - Hm; lia). entry_facts.
    pose proof g_facts as (GF1 & GF2 & GF3 & GF32 & GF8 & GFBIG & GL1 & GL2 & GLBIG & GFLA & GFC & GLC & GLKI & AqF & AqS & AqL & AoF & AoS & AoL).
    pose proof rr_facts as (Q1' & Q2' & Q3' & QBIG & O1 & O2 & O3 & OBIG & _).
    pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof SI as (SKAq & ZJ & RRq & ACCq & CKq & SZq). pose proof B6 as (_ & _ & _ & _ & SDEFq & _).
    destruct (vis_factsW Mq mdq LKq crq Awq kq BI) as (SFv & FFv & OWNv & VS & VF & VSH & VFL).
    set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.

    set (p := spc + VAL + j).
    assert (PD : MV (Z_to_bv 64 (p + 1)) <> None).
    { pose proof (VS (p + 1) 1 ltac:(unfold p, spc; clear - J0 HEND HKB; lia) ltac:(unfold p, spc; clear - JB HEND HKB; lia) 0 ltac:(clear; lia)) as Hv.
      rewrite Z.add_0_r in Hv. unfold MV. rewrite (mrestrict_visible H Mq _ Hv).
      unfold p, spc. replace (sp - 128 + VAL + j + 1) with (sp - 16384 + (16257 + VAL + j)) by (clear; lia). apply SDEFq. clear - J0 JB HEND HKB; lia. }
    destruct (u8_at_of_defined MV (p + 1) ltac:(unfold p, spc; clear - J0 JB HEND HKB SLO SHI SPT; lia) PD) as (nb & NB & PNB).
    assert (PF : (F + 64 <= p \/ p + 2 <= F) /\ (F / 8 + SBL + 8 <= p \/ p + 2 <= F / 8 + SBL) /\ (fl + 1 <= p \/ p + 2 <= fl)
                 /\ 4096 <= p <= 140737488355326 /\ 128 - END + 2 <= sp - p <= 128 - VAL).
    { unfold p, spc. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      repeat split; clear - J0 JB HEND HKB SLO SHI SPT GF1 GF8 GFC GLC; Lia.lia. }
    destruct PF as (PF1 & PF2 & PF3 & PF4 & PF5).
    unfold PMSPA.cfg.
    destruct (RUNM fxq Rq MV sp rr F fl p nb ltac:(clear - SLO SHI SPT; lia) ltac:(clear - Q1' Q3'; lia) ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia)
                   ltac:(clear - PF4; lia) ltac:(clear - NB; lia) LR Q24 SFv FFv PF4 PF5 PNB NB PF1 PF2 PF3)
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T24 & LR3 & UQ3 & USH3).
    set (W3 := fun a => (spc + TMP <= a < spc + TMP + 1) \/ (F + 32 <= a < F + 32 + 8) \/ (F / 8 + 2147450884 <= a < F / 8 + 2147450884 + 1)).
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LKq crq Awq Mq mdq fxq fx3 Rq lra R3 PBIPC M3v W3 K B1 B2 MS3 MG3).
    { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; unfold spc; exact X'| intros X'; apply Hn; right; left; exact X'| intros X'; apply Hn; right; right; exact X']. }
    { intros a Ha Wa. split.
      - destruct Wa as [X'|[X'|X']].
        + unfold aclientw, aclient_g. right; left. split; [unfold spc in X'; clear - X' SLO SHI SPT HEND HKB; lia| intros Y; clear - Y; lia].
        + apply (L5SAR.fframe_client L ar _ FF' 0 0 F 0 (spc + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X'; lia].
        + apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 0 (spc + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
          unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - X' GF8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
      - destruct Wa as [X'|[X'|X']]; unfold spc in X'; unfold SB; clear - X' GF3 SLO SPT GF1 HEND HKB; lia. }
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H M3 = M3v) in VIS3.
    assert (BI3 : BINV (PESK.sink_own kq) M3 md3 LKq crq Awq).
    { apply (PMBUK.binv_piece L ar HI M model LBX FF LK Aw sp 16384 spc (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PESK.sink_own k) G
               Ws (PESK.sink_own kq) Mq mdq LKq crq Awq M3 md3 W3 BI HH3 AM3 MRT3 MGM3 FR3).
      intros a [X'|[X'|X']]; [left; split; [unfold spc in X' |- *; clear - X' HEND HKB; lia| unfold ocell; unfold spc in X'; clear - X' HEND HKB; lia]
                           | right; left; change (ff_bytes 0) with 64; clear - X'; lia
                           | right; right; change (ff_bytes 0 / 8) with 8; unfold SB; clear - X'; lia]. }
    assert (W3in : forall a, W3 a -> (spc <= a < sp) \/ (F <= a < F + 64) \/ (F / 8 + SB <= a < F / 8 + SB + 8)).
    { intros a [X'|[X'|X']]; [left; unfold spc in X' |- *; clear - X' HEND HKB; lia| right; left; clear - X'; lia| right; right; unfold SB; clear - X'; lia]. }
    assert (SI3 : sinv M3 crq kq (j + 1)) by exact (sinv_agree Mq M3 W3 LKq crq Awq _ kq (j + 1) B1 W3in FR3 SI).

    apply (pbw (j + 1) fx3 R3 M3 md3 LKq Awq crq kq BI3 SI3 ltac:(clear - J0; lia) ltac:(clear - JB; lia) T1 (proj1 LR3) T10 ltac:(unfold spc; rewrite T11; f_equal; clear; lia)
             ltac:(intros jj Hjj; rewrite (KS3 jj) by (revert Hjj; unfold CSK; intros Hjj; repeat (destruct Hjj as [<-|Hjj]; [inl|]); destruct Hjj); apply QCS; exact Hjj)).
    { apply (proj1 (L5A.u64_at_vis H M3 (F + 32) rr (L5A.avis_sub H F 64 (F + 32) 8 VF ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))). rewrite VIS3. exact UQ3. }
    { apply (proj1 (L5A.u8_at_vis H M3 (F / 8 + 2147450884) 0 (L5A.avis_sub H (F / 8 + SB) 8 (F / 8 + 2147450884) 1 VSH ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
               ltac:(clear - GF1; lia) ltac:(clear - GF2; unfold SB; lia))). rewrite VIS3. exact USH3. }
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 BI4 SI4 RP4 AG4.
    apply (IH (j + 1) fx4 R4 M4 md4 LK4 Aw4 cr4 k4 ltac:(clear - Hm; lia) ltac:(clear - J0; lia) BI4 SI4).
    + destruct LR3 as (E2 & E8 & E9 & E18 & E19 & E20 & EF2 & ESH & E25). unfold lregs.
      repeat split; first [ rewrite (L5SAR.cs_of_preserved R3 R4 2 RP4) by inl; exact E2 | rewrite (L5SAR.cs_of_preserved R3 R4 8 RP4) by inl; exact E8
                          | rewrite (L5SAR.cs_of_preserved R3 R4 9 RP4) by inl; exact E9 | rewrite (L5SAR.cs_of_preserved R3 R4 18 RP4) by inl; exact E18
                          | rewrite (L5SAR.cs_of_preserved R3 R4 19 RP4) by inl; exact E19 | rewrite (L5SAR.cs_of_preserved R3 R4 20 RP4) by inl; exact E20
                          | rewrite (L5SAR.cs_of_preserved R3 R4 25 RP4) by inl; exact E25
                          | rewrite (L5SAR.cs_of_preserved R3 R4 rF2 RP4) by (destruct HRF2 as ([<-|[<-|[]]] & _); inl); exact EF2
                          | rewrite (L5SAR.cs_of_preserved R3 R4 rSH RP4) by (destruct HRF2 as (_ & [<-|[<-|[]]]); inl); exact ESH ].
    + rewrite (L5SAR.cs_of_preserved R3 R4 24 RP4) by inl. rewrite T24. f_equal. unfold p; clear; lia.
    + intros jj Hjj. rewrite (L5SAR.cs_of_preserved R3 R4 jj RP4); [rewrite (KS3 jj); [apply QCS; exact Hjj|]|];
        revert Hjj; unfold CSK, L5SAR.cs_all; intros Hjj; repeat (destruct Hjj as [<-|Hjj]; [inl|]); destruct Hjj.
Qed.

End Frame.

Lemma writer_core : srealizes RSEGS SCFG (PMSPA.cfg RSEGS R pc0 M model) K.
Proof.
  entry_facts. pose proof AM as (Mh & MI).
  pose proof rr_facts as (Q1' & Q2' & Q3' & QBIG & O1 & O2 & O3 & OBIG & _).
  set (LB := PESK.sink_own k ++ LBX) in *.
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (IC0 : L5.img_clear MV 1273856 1306624) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (CSBv : L5.u64_at RSEGS MV 1335544 SBL) by (apply (proj2 (L5A.u64_at_vis H M 1335544 SBL (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (CUARv : L5.u32_at RSEGS MV 1335552 1) by (apply (proj2 (L5A.u32_at_vis H M 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 16384 128 HH ASTK ltac:(lia)) as (SL128 & SH128 & SWR).
  assert (SF0 : sfacts MV sp). { split; [exact IC0|]. split; [exact CSBv|]. split; [exact CUARv|]. split; [clear - SL128 SHI SPT; lia|]. split; [exact SP32| exact SWR]. }

  unfold PMSPA.cfg.
  destruct (RUNA fx R MV sp ltac:(clear - SL128 SHI SPT; lia) Rsp SF0) as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T19 & TSB & OWN1v).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R pc0 R1 SM0 M1v (fun a => sp - 128 <= a < sp - 128 + 128) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|clear - Wa SL128 SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL128 SHI SPT; lia| intros X'; clear - X' Wa; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 16384 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 16384 a HH SPT Hc) as [Y|Y]; [clear - Xa Y; lia| clear - Xa Y SL128; lia]. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 16384 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 16384 [] M M1 (fun a => sp - 128 <= a < sp - 128 + 128) FR1). intros a Ha Hc _ X'. apply (NCS0 a); [clear - X'; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 16384 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKB.ek_sublb L ar LB LBX FF sp 16384 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKB.dk_sublb L ar LB LBX FF sp 16384 M M1 INCX DK01f) as DK01.
  assert (OWN1 : own sp R M1).
  { apply (own_agree sp R M1v M1 ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1v). intros a Ha. unfold ocell in Ha.
    symmetry. rewrite <- VIS1. apply mrestrict_visible. replace a with (sp - 128 + (a - (sp - 128))) by (clear; lia). apply (VIS (sp - 128) 128); clear - Ha SL128 SHI SPT; lia. }

  assert (FRk0 : ff_room 0 FF LK) by (pose proof (FRM 0 ltac:(left; reflexivity)) as X'; unfold ff_room; clear - X'; lia).
  change SM0 with (PMB.SM_PC 0).
  apply (PMBUAR.uar_sm L ar C HI LY HIok 0 LBX (PESK.sink_own k) FF LK cr Aw sp 16384 spc (sp - 96) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K smra ltac:(left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { exact (proj2 SMRA). }
  { exact (proj1 SMRA). }
  { unfold spc. apply SPd16. reflexivity. }
  { unfold spc; clear; lia. } { unfold spc; clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk0. }
  { intros f Hf. exact (FRS f Hf). }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. change (64 - 8) with 56 in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *.
  fold LB in EK12f, DK12f, GHH2, APART.
  set (FF' := (F, 0, spc + 32) :: FF) in *.
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.

  assert (BI2 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 16384 spc (own sp R) F 0 Ws (PESK.sink_own k) M2 model2 LK2 cr Aw).
  { unfold PMBUK.binv. split; [exact GHH2|]. split; [exact AM2|]. split; [exact (L5LZ.model_rt_trans _ _ _ MRT1 MRT2)|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact ASTK2|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 16384 Ws [] M M2 EK02); intros a _ r0 []|].
    split; [exact DK02|].
    split; [apply (own_agree sp R M1 M2 ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1); intros a Ha; unfold ocell in Ha; apply AGF; unfold spc; clear - Ha; lia|].
    change (ff_bytes 0 / 8) with 8. apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 8 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  pose proof (g_facts F fl LK2 M2 model2 G APART) as (GF1 & GF2 & GF3 & _ & _ & _ & GL1 & GL2 & GLBIG & _ & GFC & GLC & _ & AqF & AqS & AqL & AoF & AoS & AoL & _).
  destruct (vis_factsW F fl LK2 M2 model2 G APART M2 model2 LK2 cr Aw k BI2) as (SFv & FFv & OWNv & VS2 & VF2 & VSH2 & VFL2). fold H2 in VS2, VF2, VSH2, VFL2. fold H2 MV2 in SFv, FFv, OWNv.
  assert (FFv' : ffacts MV2 sp F fl true).
  { destruct FFv as (X1 & X2 & X3 & X4 & X5 & X6 & _ & X8). unfold ffacts. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
    split; [exact X6|]. split; [exact FSHZ| exact X8]. }

  pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (L5SAR.ek_trans L ar LB FF sp 16384 [] M M1 M2 EK01f EK12f) as EK02f.
  assert (SI2 : sinv M2 cr k 0).
  { unfold sinv. split.
    - apply (PECFA.sink_keepA RSEGS L ar LB FF sp 16384 [] M M2 EK02f PMKB.wapp_nil FRB BRB P o k AOo); [intros i _ r0 []| unfold LB; apply incl_appl; apply incl_refl| intros _ i _ r0 []| exact SKA].
    - split; [clear; lia|]. split; [apply (PMKB.u64_keepA RSEGS L ar LB FF sp 16384 [] M M2 EK02f PMKB.wapp_nil FRB rr o AOrr); [intros i _ r0 []| exact RRO]|].
      split; [exact (PMKB.acc_keepA' L ar LB FF sp 16384 [] M M2 EK02f PMKB.wapp_nil FRB rr 8 AOrr ACCrr)|].
      split; [unfold PMSP.credit_keep; clear; lia|].
      apply (PMKB.stksh_keepA L ar LB FF sp 16384 [] M M2 EK02f PMKB.wapp_nil (sp - 16384) 2048); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact STKSH]. }

  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
  assert (HRR : bv_unsigned (getr R (reg 10)) = rr) by (rewrite <- L5K.rl10, A10; apply L5.unsigned_lit; clear - Q1' Q3'; lia).
  destruct (RUNB fx1 R2 MV2 sp rr F fl ltac:(clear - SL128 SHI SPT; lia) ltac:(clear - Q1' Q3'; lia) ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia)
                 ltac:(rewrite (R2c 2%nat) by inl; exact T2) ltac:(rewrite (R2c 8%nat) by inl; exact T8) ltac:(rewrite (R2c 9%nat) by inl; exact T9)
                 ltac:(rewrite <- L5K.rl10; exact G10) ltac:(rewrite (R2c 19%nat) by inl; rewrite T19, <- HRR; apply wid)
                 ltac:(rewrite (R2c rSH) by (destruct HRF2 as (_ & [<-|[<-|[]]]); inl); exact TSB) SFv FFv')
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1' & T10 & T11 & T24 & LR3 & UQ3 & USH3).
  set (W3 := fun a => (sp - 120 <= a < sp - 120 + 24) \/ ((F <= a < F + 24) \/ (F + 32 <= a < F + 32 + 8)) \/ (F / 8 + SBL <= a < F / 8 + SBL + 8)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 smra R3 PBIPC M3v W3 K GHH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; exact X'| intros X'; apply Hn; right; left; left; exact X'| intros X'; apply Hn; right; left; right; exact X'| intros X'; apply Hn; right; right; exact X']. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SL128 SHI SPT HEND HKB; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar _ FF' 0 0 F 0 (spc + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 0 (spc + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
        unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - X' GF8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
    - destruct Wa as [X'|[X'|X']]; unfold SB; clear - X' GF3 SL128 SPT GF1 HEND HKB; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (W3in : forall a, W3 a -> (spc <= a < sp) \/ (F <= a < F + 64) \/ (F / 8 + SB <= a < F / 8 + SB + 8)).
  { intros a [X'|[X'|X']]; [left; unfold spc; clear - X' HEND HKB; lia| right; left; clear - X'; lia| right; right; unfold SB; clear - X'; lia]. }
  assert (BI3 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 16384 spc (own sp R) F 0 Ws (PESK.sink_own k) M3 md3 LK2 cr Aw).
  { apply (PMBUK.binv_piece L ar HI M model LBX FF LK Aw sp 16384 spc (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PESK.sink_own k) G
             Ws (PESK.sink_own k) M2 model2 LK2 cr Aw M3 md3 W3 BI2 HH3 AM3 MRT3 MGM3 FR3).
    intros a [X'|[X'|X']]; [left; split; [unfold spc; clear - X' HEND HKB; lia| unfold ocell; clear - X' HEND HKB; lia]
                         | right; left; change (ff_bytes 0) with 64; clear - X'; lia | right; right; change (ff_bytes 0 / 8) with 8; unfold SB; clear - X'; lia]. }
  assert (SI3 : sinv M3 cr k 0) by exact (sinv_agree F fl LK2 M2 model2 G APART M2 M3 W3 LK2 cr Aw _ k 0 GHH2 W3in FR3 SI2).

  assert (QCS3 : csk R3).
  { intros jj Hjj. rewrite (KS3 jj) by (revert Hjj; unfold CSK; intros Hjj; repeat (destruct Hjj as [<-|Hjj]; [inl|]); destruct Hjj).
    rewrite (R2c jj) by (revert Hjj; unfold CSK; intros Hjj; repeat (destruct Hjj as [<-|Hjj]; [inl|]); destruct Hjj).
    apply KS1. exact Hjj. }
  apply (pbw F fl LK2 M2 model2 G APART 0 fx3 R3 M3 md3 LK2 Aw cr k BI3 SI3 ltac:(clear; lia) ltac:(clear - HKB; lia) T1' (proj1 LR3) T10 ltac:(unfold spc; exact T11) QCS3).
  { apply (proj1 (L5A.u64_at_vis H2 M3 (F + 32) rr (L5A.avis_sub H2 F 64 (F + 32) 8 VF2 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))). rewrite VIS3. exact UQ3. }
  { apply (proj1 (L5A.u8_at_vis H2 M3 (F / 8 + 2147450884) 0 (L5A.avis_sub H2 (F / 8 + SB) 8 (F / 8 + 2147450884) 1 VSH2 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
             ltac:(clear - GF1; lia) ltac:(clear - GF2; unfold SB; lia))). rewrite VIS3. exact USH3. }
  intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 BI4 SI4 RP4 AG4.
  apply (loop F fl LK2 M2 model2 G APART (Z.to_nat (KB - 1)) 0 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 ltac:(clear - HKB; lia) ltac:(clear; lia) BI4 SI4).
  + destruct LR3 as (E2 & E8 & E9 & E18 & E19 & E20 & EF2 & ESH & E25). unfold lregs.
    repeat split; first [ rewrite (L5SAR.cs_of_preserved R3 R4 2 RP4) by inl; exact E2 | rewrite (L5SAR.cs_of_preserved R3 R4 8 RP4) by inl; exact E8
                        | rewrite (L5SAR.cs_of_preserved R3 R4 9 RP4) by inl; exact E9 | rewrite (L5SAR.cs_of_preserved R3 R4 18 RP4) by inl; exact E18
                        | rewrite (L5SAR.cs_of_preserved R3 R4 19 RP4) by inl; exact E19 | rewrite (L5SAR.cs_of_preserved R3 R4 20 RP4) by inl; exact E20
                        | rewrite (L5SAR.cs_of_preserved R3 R4 25 RP4) by inl; exact E25
                        | rewrite (L5SAR.cs_of_preserved R3 R4 rF2 RP4) by (destruct HRF2 as ([<-|[<-|[]]] & _); inl); exact EF2
                        | rewrite (L5SAR.cs_of_preserved R3 R4 rSH RP4) by (destruct HRF2 as (_ & [<-|[<-|[]]]); inl); exact ESH ].
  + rewrite (L5SAR.cs_of_preserved R3 R4 24 RP4) by inl. rewrite T24. f_equal. unfold spc; clear; lia.
  + intros jj Hjj. rewrite (L5SAR.cs_of_preserved R3 R4 jj RP4); [apply QCS3; exact Hjj|].
      revert Hjj; unfold CSK, L5SAR.cs_all; intros Hjj; repeat (destruct Hjj as [<-|Hjj]; [inl|]); destruct Hjj.
Qed.
End Call.

Lemma writer_ok : PENTBBF.ntbf_specB RSEGS AD L ar HI pc0 KB P.
Proof.
  unfold PENTBBF.ntbf_specB. intros PMODE fx R M model K LBX FF LK Aw cr rr o sp r h k HH AM K0 ENT FRM FRS SP32 A10 RRO ALrr AOrr ACCrr RRdj SKA AOo ALo HBh ZKB CRED KONT.
  exact (writer_core PMODE fx R M model K LBX FF LK Aw cr rr o sp r h k HH AM K0 ENT FRM FRS SP32 A10 RRO ALrr AOrr ACCrr RRdj SKA AOo ALo HBh ZKB CRED KONT).
Qed.
End Writer.

Theorem ntb_f32_ok : PENTBBF.ntbf_specB RSEGS AD L ar HI 0xb3c2c 4 P.
Proof.
  apply (writer_ok 0xb3c2c 0xb3c9c 0xb3d8c 27 28 32 4 22 21 f32_runA f32_runB f32_runM f32_runL);
    clear; unfold L5.ra_ok; repeat split; first [reflexivity | lia | left; reflexivity | right; left; reflexivity].
Qed.
Theorem ntb_f64_ok : PENTBBF.ntbf_specB RSEGS AD L ar HI 0xb3e38 8 P.
Proof.
  apply (writer_ok 0xb3e38 0xb3ea8 0xb3fcc 23 24 32 8 21 22 f64_runA f64_runB f64_runM f64_runL);
    clear; unfold L5.ra_ok; repeat split; first [reflexivity | lia | left; reflexivity | right; left; reflexivity].
Qed.
End WithHeap.
End PEBENTBF.
