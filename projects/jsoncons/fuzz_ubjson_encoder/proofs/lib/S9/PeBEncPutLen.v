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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrameA PeEncKit PeBCReset1 PmBUarK PmBUar PeBPbIndSpec PeBEncNtbSpec PeBEncKit PeBEncKit3 PeBEncNtb PeBEncPutLenP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_b00f0_b00f4.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENCPL.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).
Abbreviation SBL := 2147450880.
Abbreviation SM0 := 0x5ec3c.
Abbreviation PBIPC := 0xb2794.
Abbreviation PBPC := 0xb120c.
Abbreviation EV := 0xb00b4.
Abbreviation INT64_MAX := 9223372036854775807.

Definition CSK : list nat := [3; 4; 24; 25; 26; 27]%nat.
Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.

Definition msfacts (b : Z) (MV : word -> option byte) : Prop :=
  L5.img_clear MV 1273856 1306624 /\ L5.u64_at RSEGS MV 1335544 SBL /\ L5.u32_at RSEGS MV 1335552 1 /\
  140735332487328 <= b <= 140737488355328 /\ b mod 32 = 0 /\ L5.writable RSEGS MV (b - 128) 128.

Definition runA (rs : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (b : Z),
    0 <= b -> b + rs < 2 ^ 64 -> getr R (reg 2) = Z_to_bv 64 (b + rs) ->
    L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 SBL -> L5.u32_at RSEGS M 1335552 1 ->
    140735332487328 <= b -> b + rs <= 140737488355328 -> b mod 32 = 0 -> L5.writable RSEGS M (b - 128) (128 + rs) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (b - 128 <= i < b - 128 + (128 + rs)) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xafe84 M) (mst fx' R' SM0 M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 0xafee8 /\ getr R' (reg 2) = Z_to_bv 64 (b - 128) /\ getr R' (reg 8) = Z_to_bv 64 (b + rs) /\ getr R' (reg 9) = Z_to_bv 64 (b - 128)
      /\ getr R' (reg 19) = getr R (reg 11) /\ getr R' (reg 20) = getr R (reg 10) /\ getr R' (reg 21) = Z_to_bv 64 SBL
      /\ PEBEK3.owns PEBEK3.SV9 (b + rs) R M'.

Definition lregs (R : bvmap 5 word) (b S F ov n : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (b - 128) /\ getr R (reg 8) = Z_to_bv 64 S /\ getr R (reg 9) = Z_to_bv 64 (b - 128) /\ getr R (reg 18) = Z_to_bv 64 F
  /\ getr R (reg 19) = Z_to_bv 64 n /\ getr R (reg 20) = Z_to_bv 64 (ov + 8) /\ getr R (reg 22) = Z_to_bv 64 (F / 8 + SBL) /\ getr R (reg 23) = Z_to_bv 64 F.

Definition ovfacts (M : word -> option byte) (b ov F fl : Z) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5.writable RSEGS M ov 56 /\ ((b - 128) + 128 <= ov \/ ov + 56 <= (b - 128))
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1
  /\ (ov + 56 <= F \/ F + 64 <= ov) /\ (ov + 56 <= fl \/ fl + 1 <= ov) /\ (ov / 8 + SBL + 7 <= F / 8 + SBL \/ F / 8 + SBL + 8 <= ov / 8 + SBL).

Definition runD (lo hi raD : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (b S ov n o F fl : Z),
    0 <= b < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (b - 128) -> getr R (reg 8) = Z_to_bv 64 S -> getr R (reg 9) = Z_to_bv 64 (b - 128) -> getr R (reg 10) = Z_to_bv 64 F ->
    getr R (reg 19) = Z_to_bv 64 n -> getr R (reg 20) = Z_to_bv 64 ov -> getr R (reg 21) = Z_to_bv 64 SBL ->
    msfacts b M -> PEBEK.ffacts 128 b F fl M true -> ovfacts M b ov F fl ->
    L5.u64_at RSEGS M (ov + 8) o -> 4096 <= o <= 140737488355304 -> o mod 8 = 0 -> lo <= n <= hi ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (b - 128 <= i < b - 128 + 56) -> ~ (F <= i < F + 24) -> ~ (F / 8 + SBL <= i < F / 8 + SBL + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xafee8 M) (mst fx' R' PBPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 raD /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 11) = Z_to_bv 64 (b - 73)
      /\ lregs R' b S F ov n /\ (lo = 0 -> getr R' (reg 21) = Z_to_bv 64 (F + 32)).

Definition runP8 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (b S ov n F fl : Z),
    0 <= b < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    lregs R b S F ov n -> getr R (reg 21) = Z_to_bv 64 (F + 32) -> msfacts b M -> PEBEK.ffacts 128 b F fl M false -> ovfacts M b ov F fl -> 0 <= n <= 255 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (b - 73 <= i < b - 73 + 1) -> ~ (F + 32 <= i < F + 32 + 8) -> ~ (F / 8 + 2147450884 <= i < F / 8 + 2147450884 + 1) ->
            M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xb000c M) (mst fx' R' PBIPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 0xb0024 /\ getr R' (reg 10) = Z_to_bv 64 (F + 32) /\ getr R' (reg 11) = Z_to_bv 64 (b - 73)
      /\ lregs R' b S F ov n /\ getr R' (reg 21) = Z_to_bv 64 (F + 32)
      /\ L5.u64_at RSEGS M' (F + 32) (ov + 8) /\ L5.u8_at RSEGS M' (F / 8 + 2147450884) 0.

Definition runW (pcW wr raW : Z) (lo hi : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (b S ov n F : Z),
    0 <= b < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= F < 2 ^ 64 ->
    lregs R b S F ov n -> msfacts b M -> 4096 <= ov <= 140737488355272 -> ov mod 8 = 0 -> lo <= n <= hi ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pcW M) (mst fx' R' wr M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 raW /\ getr R' (reg 11) = Z_to_bv 64 (ov + 8) /\ lregs R' b S F ov n.

Definition runJ (pcJ : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (b S ov n F fl : Z),
    0 <= b < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    lregs R b S F ov n -> msfacts b M -> PEBEK.ffacts 128 b F fl M false -> ovfacts M b ov F fl ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (F / 8 + 2147450884 <= i < F / 8 + 2147450884 + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pcJ M) (mst fx' R' EV M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ lregs R' b S F ov n.

Definition runE : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov n F fl r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    getr R (reg 8) = Z_to_bv 64 sp -> getr R (reg 18) = Z_to_bv 64 F -> getr R (reg 19) = Z_to_bv 64 n -> getr R (reg 20) = Z_to_bv 64 (ov + 8) ->
    getr R (reg 22) = Z_to_bv 64 (F / 8 + SBL) -> getr R (reg 23) = Z_to_bv 64 F ->
    L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 SBL -> L5.u32_at RSEGS M 1335552 1 -> 140735332487328 <= sp <= 140737488355328 -> sp mod 16 = 0 ->
    PEBEK.ffacts 128 sp F fl M false ->
    PEBEK3.owns PEBEK3.SV9 sp R0 M -> getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ PMBUK.Wret F fl 0 i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R EV M) (mst fx' R' r M')
      /\ L5.u8_at RSEGS M' fl 0 /\ regs_preserved R0 R'.

Ltac gks KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEBENCPLP.aligned; assumption | apply wid | apply wrng | L5SAR.greg | L5SAR.gmem | lia]).
Ltac greg1 KS :=
  first [ assumption
        | lazymatch goal with |- getr ?R1 (reg ?n) = _ =>
            first [ lazymatch goal with H : getr R1 (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end
                  | rewrite (KS n) by inl; lazymatch goal with H : getr _ (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end ] end ].

Ltac midV R b ov n o F fl r R0 :=
  constr:(fun j : nat => match j with 2%nat => b | 10%nat => ov | 11%nat => n | 41%nat => o | 47%nat => F | 48%nat => fl | 64%nat => r
     | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9)) | 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19))
     | 69%nat => bv_unsigned (getr R0 (reg 20)) | 70%nat => bv_unsigned (getr R0 (reg 21)) | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23))
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12))
     | 58%nat => bv_unsigned (getr R (reg 2)) | 59%nat => bv_unsigned (getr R (reg 9)) | _ => 0 end).

Ltac runA_fin :=
  let P := fresh "P" in
  lazymatch goal with H : exists fx', _ |- _ => rename H into P end;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|]; split; [intros i Hi N1; apply FRZ1; [exact Hi| clear - N1; lia]|]; split; [exact MS1|];
  decompose [and] P; split; [gks KS|]; unfold PEBEK3.owns, PEBEK3.SV9; repeat split; first [greg1 KS | L5SAR.gmem].
Lemma u_runA0 : runA 0.
Proof.
  intros fx R M b Hb0 Hb1 G2 K0 K1 K2 BLO BHI BAL BWR.
  pose proof (PEBENCPLP.bplA0_conc fx R M (fun j => match j with 2%nat => b | _ => 0 end)) as P. cbn beta iota in P. feedP P. runA_fin.
Qed.
Lemma u_runA16 : runA 16.
Proof.
  intros fx R M b Hb0 Hb1 G2 K0 K1 K2 BLO BHI BAL BWR.
  pose proof (PEBENCPLP.bplA16_conc fx R M (fun j => match j with 2%nat => b | _ => 0 end)) as P. cbn beta iota in P. feedP P. runA_fin.
Qed.

Ltac runD_tac CONC :=
  intros fx R M b S ov n o F fl Hb Hov Hn Ho HF Hfl G2 G8 G9 G10 G19 G20 G21 (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF UO OR1 OA HV;
  unfold PEBEK.ffacts in FF0; decompose [and] FF0; unfold ovfacts in OVF; decompose [and] OVF;
  let V := midV R b ov n o F fl 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs; repeat split; first [greg1 KS | intros Hlo; first [greg1 KS | exfalso; clear - Hlo; lia]].
Lemma u_runD8 : runD 0 255 0xb000c. Proof. runD_tac PEBENCPLP.bplD8_conc. Qed.
Lemma u_runD16 : runD 256 32767 0xb0064. Proof. runD_tac PEBENCPLP.bplD16_conc. Qed.
Lemma u_runD32 : runD 32768 2147483647 0xb00a8. Proof. runD_tac PEBENCPLP.bplD32_conc. Qed.
Lemma u_runD64 : runD 2147483648 INT64_MAX 0xaffc4. Proof. runD_tac PEBENCPLP.bplD64_conc. Qed.

Lemma u_runP8 : runP8.
Proof.
  intros fx R M b S ov n F fl Hb Hov Hn HF Hfl LR G21 (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF HV.
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G22 & G23). unfold PEBEK.ffacts in FF0; decompose [and] FF0. unfold ovfacts in OVF; decompose [and] OVF.
  let V := midV R b ov n 0 F fl 0 R in pose proof (PEBENCPLP.bplP8_conc fx R M V) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P).
  exists fx1, R1, M1. split; [exact MG1|].
  split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia]|].
  split; [exact MS1|]. decompose [and] P. split; [gks KS|]. unfold lregs. repeat split; greg1 KS.
Qed.

Ltac runW_tac CONC :=
  intros fx R M b S ov n F Hb Hov Hn HF LR (K0 & K1 & K2 & K3 & K4 & K5) OR1 OA1 HV;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G22 & G23);
  let V := midV R b ov n 0 F 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|]; split; [intros i Hi; apply FRZ1; exact Hi|]; split; [exact MS1|];
  decompose [and] P; split; [gks KS|]; unfold lregs; repeat split; greg1 KS.
Lemma u_runW16 : runW 0xb0064 0xb1bc4 0xb0070 256 32767. Proof. runW_tac PEBENCPLP.bplW16_conc. Qed.
Lemma u_runW32 : runW 0xb00a8 0xb1da4 EV 32768 2147483647. Proof. runW_tac PEBENCPLP.bplW32_conc. Qed.
Lemma u_runW64 : runW 0xaffc4 0xb1fa4 0xaffd0 2147483648 INT64_MAX. Proof. runW_tac PEBENCPLP.bplW64_conc. Qed.

Ltac runJ_tac CONC :=
  intros fx R M b S ov n F fl Hb Hov Hn HF Hfl LR (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G22 & G23); unfold PEBEK.ffacts in FF0; decompose [and] FF0; unfold ovfacts in OVF; decompose [and] OVF;
  let V := midV R b ov n 0 F fl 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  let REST := fresh "REST" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & REST);
  first [ let P' := fresh "P'" in destruct REST as [KS P']; decompose [and] P' | rename REST into KS ];
  exists fx1, R1, M1; split; [exact MG1|]; split; [intros i Hi N1; apply FRZ1; first [exact Hi | clear - N1; lia]|]; split; [exact MS1|];
  split; [gks KS|]; unfold lregs; repeat split; greg1 KS.
Lemma u_runJ8 : runJ 0xb0024. Proof. runJ_tac PEBENCPLP.bplJ8_conc. Qed.
Lemma u_runJ16 : runJ 0xb0070. Proof. runJ_tac PEBENCPLP.bplJ16_conc. Qed.
Lemma u_runJ64 : runJ 0xaffd0. Proof. runJ_tac PEBENCPLP.bplJ64_conc. Qed.

Lemma regs_end (R R0 R3 : bvmap 5 word) (sp : Z) (KS : list nat) :
  (forall j, In j CSK -> In j KS) -> (forall x, In x KS -> getr R3 (reg x) = getr R (reg x)) -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
  getr R0 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 2) = Z_to_bv 64 sp ->
  getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R3 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  getr R3 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) -> getr R3 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 23))) -> regs_preserved R0 R3.
Proof.
  intros SUB KS3 QCS Rsp T2 T8 T9 T18 T19 T20 T21 T22 T23. apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
  repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8; apply Z_to_bv_bv_unsigned | rewrite T9; apply Z_to_bv_bv_unsigned | rewrite T18; apply Z_to_bv_bv_unsigned
                                          | rewrite T19; apply Z_to_bv_bv_unsigned | rewrite T20; apply Z_to_bv_bv_unsigned | rewrite T21; apply Z_to_bv_bv_unsigned
                                          | rewrite T22; apply Z_to_bv_bv_unsigned | rewrite T23; apply Z_to_bv_bv_unsigned
                                          | rewrite (KS3 _) by (apply SUB; inl); apply QCS; inl ] |]). destruct Hj.
Qed.

Lemma u_runE : runE.
Proof.
  intros fx R R0 M sp ov n F fl r Hsp Hov Hn HF Hfl G8 G18 G19 G20 G22 G23 K0 K1 K2 SR SP16 FF0 OWN0 Hra R0sp RA QCS.
  unfold PEBEK.ffacts in FF0. decompose [and] FF0.
  unfold PEBEK3.owns, PEBEK3.SV9 in OWN0. destruct OWN0 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & _). pose proof RA as (Hr1 & Hr2).
  rewrite Hra, L5.unsigned_lit in S8 by (clear - Hr1; lia).
  let V := midV R sp ov n 0 F fl r R0 in pose proof (PEBENCPLP.bplE_conc fx R M V) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & T18 & T19 & T20 & T21 & T22 & T23 & FL0 & _).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xb0140 W_b00f0 r F_b00f0 eq_refl D_b00f0 T1 ltac:(clear - Hr1; lia) Hr2) as MSR.
  exists fx1, R1, M1. split; [exact MG1|].
  split; [intros i Hi N; unfold PMBUK.Wret in N; change (ff_bytes 0) with 64 in N; change (64 / 8) with 8 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N; lia| clear - N; lia| clear - N; lia]|].
  split; [eapply msteps_trans; [exact MS1| exact MSR]|]. split; [exact FL0|].
  apply (regs_end R R0 R1 sp PEBENCPLP.KS_bplE); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMB.ly_as0 L C LY.
Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Hypothesis PBI : PEPBI.push_back_indZ_specA RSEGS AD L ar HI PBIPC P.
Let NTB16 := PEBENTB.ntb_u16_ok L ar C HI P LY HIok PO PBI.
Let NTB32 := PEBENTB.ntb_u32_ok L ar C HI P LY HIok PO PBI.
Let NTB64 := PEBENTB.ntb_u64_ok L ar C HI P LY HIok PO PBI.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (n : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z).
Variables (xstk : list pstate) (xpos : Z) (xmore xdone xhalt : bool) (xdepth : Z) (xec : bool) (xestk : list eitem) (xedepth xlo xhi : Z) (xbad : bool).
Variables (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Let X : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad.
Let XS (a : Z) : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + a) (xhi + a) xbad.
Let W : Z := pl_size n.
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 3.
Hypothesis FRM : PMSPA.ffroomA 3 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP16 : sp mod 16 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis VR : 0 <= n <= INT64_MAX.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 n.
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis MP : PECSPA.mp_enc p X.
Hypothesis HBN : PESKA.spa_hb P (xhi + W).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (k' : PESK.sink) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (XS W) s str sm en k' e cat ->
        L5CA.ahpres L ar (PM.parser_own s ++ PEC.enc_own en ++ LBX) FF sp (PMSPA.pm_scr 3) [(PESK.o_sink EE fb, 24)] M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Let rs : Z := sp mod 32.
Let FR : Z := 128 + rs.
Let b : Z := sp - rs.
Lemma Hrs : rs = 0 \/ rs = 16.
Proof. unfold rs. clear - SP16. Lia.lia. Qed.
Lemma HFR : FR = 128 \/ FR = 144. Proof. unfold FR. destruct Hrs as [-> | ->]; [left|right]; reflexivity. Qed.
Lemma SPC32h : (sp - FR) mod 32 = 0.
Proof. unfold FR, rs. clear. Lia.lia. Qed.
Lemma B32 : b mod 32 = 0. Proof. unfold b, rs. clear. Lia.lia. Qed.
Lemma Eb : b = sp - FR + 128. Proof. unfold b, FR. clear. lia. Qed.
Lemma HSV : PEBEK3.SV9 = PEBEK3.SV9 \/ PEBEK3.SV9 = PEBEK3.SV11. Proof. left; reflexivity. Qed.
Lemma W1 : 2 <= W <= 9. Proof. unfold W. apply pl_size_pos. Qed.
Lemma HNB : 0 <= W. Proof. pose proof W1. lia. Qed.
Lemma CSK3 : In 3%nat CSK. Proof. inl. Qed.
Lemma CSK4 : In 4%nat CSK. Proof. inl. Qed.
Lemma CSKall j : In j CSK -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.
Lemma VRR : 0 <= n < 2 ^ 64. Proof. clear - VR. lia. Qed.

Local Notation K_vis_entry := (PEBEK3.vis_entry L ar C HI LY HIok FR HFR R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK SPC32h A10).
Local Notation K_start := (PEBEK3.start L ar C HI P LY HIok FR PEBEK3.SV9 HFR HSV fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH AM K0 ENT FRM FRS FOK SP16 SPC32h CPRE).
Local Notation K_vis_facts := (PEBEK3.vis_facts L ar C HI P LY HIok FR PEBEK3.SV9 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SPC32h).
Local Notation K_g_facts := (PEBEK3.g_facts L ar C HI LY HIok FR PEBEK3.SV9 HFR HSV R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK).
Local Notation K_inv_agree := (PEBEK3.inv_agree L ar C HI P LY HIok FR PEBEK3.SV9 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK).
Local Notation K_pb_call := (PEBEK3.pb_call L ar C HI P LY HIok PO PB FR PEBEK3.SV9 CSK HFR HSV CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP16 SPC32h CPRE CRED).
Local Notation K_pbi_call := (PEBEK3.pbi_call L ar C HI P LY HIok PO PBI FR PEBEK3.SV9 CSK HFR HSV CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP16 SPC32h CPRE CRED).
Local Notation K_wr_call := (PEBEK3.wr_call L ar C HI P LY HIok FR PEBEK3.SV9 CSK HFR HSV CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP16 SPC32h CPRE CRED).
Local Notation K_finish_pl := (PEBEK3.finish_pl L ar C HI P LY HIok FR W PEBEK3.SV9 HFR HSV R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS KONT).
Local Notation INV := (PEBEK3.inv L ar HI P FR PEBEK3.SV9 R M model LBX FF LK Aw cr sp fb xlo xhi s en k).

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMBUK.gctx L ar HI (PM.parser_own s ++ PEC.enc_own en ++ LBX) FF LK Aw sp 18432 (sp - FR) (sp - 8 * Z.of_nat (length PEBEK3.SV9)) sp (PEBEK3.ocell sp (Z.of_nat (length PEBEK3.SV9))) (PEBEK3.owns PEBEK3.SV9 sp R) F fl 0 LK2 M2 model2 cr (PEBEK3.EBX k).
Hypothesis APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar (PEBEK3.EBX k ++ (PM.parser_own s ++ PEC.enc_own en ++ LBX)) FF sp0 scr0 (a + i)) -> 0 < n0 ->
    (a + n0 <= F \/ F + 64 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a).

Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 3) with 18432 in ASTK, STKSH; pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl4 in Rtp;
  pose proof (K_g_facts F fl LK2 M2 model2 G APART) as GF; cbv beta in GF; destruct GF as (GF1 & GF2 & GF3 & _ & GF8 & _ & GL1 & GL2 & _);
  pose proof Hrs as HRS; pose proof Eb as EB.

Lemma lregs_after R1 R2 : lregs R1 b sp F (PMSPA.o_v AD fb) n -> (forall j, In j CSK -> getr R1 (reg j) = getr R (reg j)) -> regs_preserved R1 R2 ->
  lregs R2 b sp F (PMSPA.o_v AD fb) n /\ (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)).
Proof.
  intros (G2 & G8 & G9 & G18 & G19 & G20 & G22 & G23) QCS RP. split.
  - unfold lregs. repeat split; first [ rewrite (L5SAR.cs_of_preserved R1 R2 2 RP) by inl; exact G2 | rewrite (L5SAR.cs_of_preserved R1 R2 8 RP) by inl; exact G8
      | rewrite (L5SAR.cs_of_preserved R1 R2 9 RP) by inl; exact G9 | rewrite (L5SAR.cs_of_preserved R1 R2 18 RP) by inl; exact G18 | rewrite (L5SAR.cs_of_preserved R1 R2 19 RP) by inl; exact G19
      | rewrite (L5SAR.cs_of_preserved R1 R2 20 RP) by inl; exact G20 | rewrite (L5SAR.cs_of_preserved R1 R2 22 RP) by inl; exact G22 | rewrite (L5SAR.cs_of_preserved R1 R2 23 RP) by inl; exact G23 ].
  - intros j Hj. rewrite (L5SAR.cs_of_preserved R1 R2 j RP (CSKall j Hj)). exact (QCS j Hj).
Qed.
Lemma csk_kept (R1 R2 : bvmap 5 word) KS : (forall j, In j CSK -> In j KS) -> (forall x, In x KS -> getr R2 (reg x) = getr R1 (reg x)) ->
  (forall j, In j CSK -> getr R1 (reg j) = getr R (reg j)) -> forall j, In j CSK -> getr R2 (reg j) = getr R (reg j).
Proof. intros SUB KS3 Q j Hj. rewrite (KS3 j (SUB j Hj)). exact (Q j Hj). Qed.

Lemma vis Mq mdq LKq Awq crq kq a : INV F Mq mdq LKq Awq crq kq a ->
  let MV := mrestrict (ahid Awq mdq) Mq in
  msfacts b MV /\ 140735332487168 + 18432 <= sp <= 140737488355328 /\ PEBEK.ffacts 128 b F fl MV false /\ PEBEK.ffacts 128 sp F fl MV false
  /\ PEBEK3.owns PEBEK3.SV9 sp R MV /\ ovfacts MV b (PMSPA.o_v AD fb) F fl
  /\ L5.u64_at RSEGS MV (PMSPA.o_v AD fb + 8) (PESK.o_sink EE fb) /\ 4096 <= PESK.o_sink EE fb <= 140737488355304 /\ (PESK.o_sink EE fb) mod 8 = 0
  /\ L5A.avis (ahid Awq mdq) F 64 /\ L5A.avis (ahid Awq mdq) (F / 8 + SB) 8.
Proof.
  intros INVq. entry_facts.
  pose proof (K_vis_facts F fl LK2 M2 model2 G APART Mq mdq LKq Awq crq kq a INVq) as VF. cbv beta in VF.
  destruct VF as (SF & FFc & OWN & OF & _ & VFf & VSH & _).
  pose proof OF as (OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8 & KR & K8 & KO & U24 & U32 & EBR & AvF & AvS & AvL & _).
  destruct SF as (W1' & W2 & W3 & SR & SAL & SWR).
  destruct FFc as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14).
  pose proof B32 as BAL.
  split. { unfold msfacts. split; [exact W1'|]. split; [exact W2|]. split; [exact W3|]. split; [clear - SR HRS EB; lia|]. split; [exact BAL|].
           apply (L5.writable_sub _ _ (sp - FR) FR (b - 128) 128 SWR); clear - HRS EB; lia. }
  split; [exact SR|].
  split. { unfold PEBEK.ffacts. repeat split; first [assumption | clear - X1; lia | clear - X9; lia | clear - X13 HRS EB; lia | clear - X14 HRS EB; lia]. }
  split. { unfold PEBEK.ffacts. repeat split; first [assumption | clear - X1; lia | clear - X9; lia | clear - X13 HRS EB; lia | clear - X14 HRS EB; lia]. }
  split; [exact OWN|].
  split. { unfold ovfacts. repeat split; first [assumption | clear - OR; lia | clear - ODJ HRS EB; lia | clear - AvF O8 GF8; Lia.lia]. }
  split; [exact U8|]. split; [exact KR|]. split; [exact K8|]. split; [exact VFf| exact VSH].
Qed.

Lemma tailE (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  INV F Mq mdq LKq Awq crq kq W -> lregs Rq b sp F (PMSPA.o_v AD fb) n -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq EV Mq mdq) K.
Proof.
  intros INVq LRq QCS. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq W INVq) as (SF4 & SR & _ & FF4 & OWN4 & OF4 & _).
  pose proof OF4 as (OR4 & _). destruct SF4 as (W1' & W2 & W3 & _). destruct LRq as (_ & G8 & _ & G18 & G19 & G20 & G22 & G23).
  unfold PMSPA.cfg.
  destruct (u_runE fxq Rq R (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) n F fl r ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR4; lia) VRR ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia)
             G8 G18 G19 G20 G22 G23 W1' W2 W3 ltac:(clear - SR; lia) SP16 FF4 OWN4 Rra Rsp RAok QCS)
    as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & FL5 & RP5).
  exact (K_finish_pl F fl LK2 M2 model2 G APART W EV fxq Rq Mq mdq LKq Awq crq kq fx5 R5 M5v INVq eq_refl MS5 MG5 FRZ5 FL5 RP5).
Qed.

Lemma stepJ pcJ (fxq : FPState) Rq Mq mdq LKq Awq crq kq : runJ pcJ ->
  INV F Mq mdq LKq Awq crq kq W -> lregs Rq b sp F (PMSPA.o_v AD fb) n -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcJ Mq mdq) K.
Proof.
  intros RJ INVq LRq QCS. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq W INVq) as (SF & _ & FFc & _ & _ & OF & _ & _ & _ & VFf & VSH).
  pose proof OF as (OR & _). pose proof INVq as ((HHq & AMq & _) & _). pose proof SF as (_ & _ & _ & SR & _).
  destruct (RJ fxq Rq (mrestrict (ahid Awq mdq) Mq) b sp (PMSPA.o_v AD fb) n F fl ltac:(clear - SR; lia) ltac:(clear - OR; lia) VRR ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia) LRq SF FFc OF)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & LR3).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LKq crq Awq Mq mdq fxq fx3 Rq pcJ R3 EV M3v (fun a0 => F / 8 + 2147450884 <= a0 < F / 8 + 2147450884 + 1) K HHq AMq MS3 MG3).
  { intros a0 Ha Hn'. apply FRZ3; [exact Ha| exact Hn']. }
  { intros a0 Ha Wa. split.
    - apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 0 (sp - FR + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - Wa GF8. Lia.lia.
    - clear - Wa GF3; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV F M3 md3 LKq Awq crq kq W).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART Mq M3 (fun a0 => F / 8 + 2147450884 <= a0 < F / 8 + 2147450884 + 1) mdq md3 LKq crq Awq kq W INVq HH3 AM3 MRT3 MGM3); [| exact FR3].
    intros a0 X'. right; right. unfold SB. clear - X'; lia. }
  pose proof (csk_kept Rq R3 CSK (fun j Hj => Hj) KS3 QCS) as QCS3.
  exact (tailE fx3 R3 M3 md3 LKq Awq crq kq INV3 LR3 QCS3).
Qed.

Lemma stepW pcW wr raW lo hi kb (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  runW pcW wr raW lo hi -> PENTBB.ntb_specB RSEGS AD L ar HI wr kb P -> lo <= n <= hi -> 0 <= kb -> 1 + kb = W -> L5.ra_ok raW ->
  INV F Mq mdq LKq Awq crq kq 1 -> lregs Rq b sp F (PMSPA.o_v AD fb) n -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) ->
  (forall (fx2 : FPState) R2 Mx mdx LKx Awx crx kx, INV F Mx mdx LKx Awx crx kx W -> lregs R2 b sp F (PMSPA.o_v AD fb) n ->
      (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 raW Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcW Mq mdq) K.
Proof.
  intros RW NTB HV KB0 HW RAW INVq LRq QCS KX. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq 1 INVq) as (SF & _ & FFc & _ & _ & OF & _). pose proof OF as (OR & O8 & _). pose proof INVq as ((HHq & AMq & _) & _). pose proof SF as (_ & _ & _ & SR & _).
  destruct (RW fxq Rq (mrestrict (ahid Awq mdq) Mq) b sp (PMSPA.o_v AD fb) n F ltac:(clear - SR; lia) ltac:(clear - OR; lia) VRR ltac:(clear - GF1 GF2; lia) LRq SF OR O8 HV)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T11 & LR3).
  unfold PMSPA.cfg. apply (L5SAR.apiece_ro L ar C HI LYa HIok _ _ LKq crq Awq Mq mdq fxq fx3 Rq pcW R3 wr M3v K HHq AMq MS3 MG3 FRZ3).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree Mq M3 AG3) as EM. subst M3.
  assert (INV3 : INV F Mq md3 LKq Awq crq kq 1).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART Mq Mq (fun _ => False) mdq md3 LKq crq Awq kq 1 INVq HH3 AM3 MRT3 (mem_grows_refl Mq)); [intros a0 []| intros a0 _ _; reflexivity]. }
  pose proof (csk_kept Rq R3 CSK (fun j Hj => Hj) KS3 QCS) as QCS3.
  pose proof LR3 as (G2 & _).
  apply (K_wr_call F fl LK2 M2 model2 G APART 1 kb wr (xhi + W) raW fx3 R3 Mq md3 LKq Awq crq kq NTB INV3 HBN ltac:(clear - HW; lia) KB0 RAW T1 ltac:(rewrite G2; f_equal; unfold FR, b; clear; lia) T11 QCS3).
  intros fx2 R2 Mx mdx LKx Awx crx kx INVx RP2 _. destruct (lregs_after R3 R2 LR3 QCS3 RP2) as [LR2 QCS2]. rewrite HW in INVx. exact (KX fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2).
Qed.

Lemma stepP8 (fxq : FPState) Rq Mq mdq LKq Awq crq kq : n <= 255 -> 2 = W ->
  INV F Mq mdq LKq Awq crq kq 1 -> lregs Rq b sp F (PMSPA.o_v AD fb) n -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) ->
  getr Rq (reg 21) = Z_to_bv 64 (F + 32) ->
  (forall (fx2 : FPState) R2 Mx mdx LKx Awx crx kx, INV F Mx mdx LKx Awx crx kx W -> lregs R2 b sp F (PMSPA.o_v AD fb) n ->
      (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xb0024 Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xb000c Mq mdq) K.
Proof.
  intros HV HW INVq LRq QCS G21 KX. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq 1 INVq) as (SF & _ & FFc & _ & _ & OF & _ & _ & _ & VFf & VSH). pose proof OF as (OR & _). pose proof INVq as ((HHq & AMq & _) & _).
  pose proof SF as (_ & _ & _ & SR & _).
  destruct (u_runP8 fxq Rq (mrestrict (ahid Awq mdq) Mq) b sp (PMSPA.o_v AD fb) n F fl ltac:(clear - SR; lia) ltac:(clear - OR; lia) VRR ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia) LRq G21 SF FFc OF ltac:(clear - VR HV; lia))
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & LR3 & T21 & UQ3 & USH3).
  set (W3 := fun a0 => (b - 73 <= a0 < b - 73 + 1) \/ (F + 32 <= a0 < F + 32 + 8) \/ (F / 8 + 2147450884 <= a0 < F / 8 + 2147450884 + 1)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LKq crq Awq Mq mdq fxq fx3 Rq 0xb000c R3 PBIPC M3v W3 K HHq AMq MS3 MG3).
  { intros a0 Ha Hn'. apply FRZ3; [exact Ha| intros X'; apply Hn'; left; exact X'| intros X'; apply Hn'; right; left; exact X'| intros X'; apply Hn'; right; right; exact X']. }
  { intros a0 Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT HRS EB; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar _ _ 0 0 F 0 (sp - FR + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 0 (sp - FR + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - X' GF8. Lia.lia.
    - destruct Wa as [X'|[X'|X']]; unfold SB; clear - X' GF3 SLO SPT HRS EB; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV F M3 md3 LKq Awq crq kq 1).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART Mq M3 W3 mdq md3 LKq crq Awq kq 1 INVq HH3 AM3 MRT3 MGM3); [| exact FR3].
    intros a0 [X'|[X'|X']]; [left; split; [clear - X' HRS EB; lia| unfold PEBEK3.ocell, PEBEK3.SV9; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - X' HRS EB; lia]
                          | right; left; clear - X'; lia | right; right; unfold SB; clear - X'; lia]. }
  pose proof (csk_kept Rq R3 CSK (fun j Hj => Hj) KS3 QCS) as QCS3.
  refine (K_pbi_call F fl LK2 M2 model2 G APART 1 (F + 32) (b - 73) (xhi + W) 0xb0024 fx3 R3 M3 md3 LKq Awq crq kq INV3 HBN ltac:(clear - HW; lia) ltac:(clear - HRS EB; lia) ltac:(clear - HRS EB; lia)
           ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) ltac:(clear; lia) ltac:(replace (F + 32) with ((F / 8 + 4) * 8) by (clear - GF8; lia); apply Z_mod_mult) _ _ T1 ltac:(rewrite (proj1 LR3); f_equal; unfold FR, b; clear; lia) T10 T11 QCS3 _).
  { apply (proj1 (L5A.u64_at_vis (ahid Awq mdq) M3 (F + 32) _ (L5A.avis_sub _ F 64 (F + 32) 8 VFf ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))). rewrite VIS3. exact UQ3. }
  { replace ((F + 32) / 8 + SBL) with (F / 8 + 2147450884) by (clear - GF8; Lia.lia).
    apply (proj1 (L5A.u8_at_vis (ahid Awq mdq) M3 (F / 8 + 2147450884) 0 (L5A.avis_sub _ (F / 8 + SB) 8 (F / 8 + 2147450884) 1 VSH ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
             ltac:(clear - GF1; lia) ltac:(clear - GF2; unfold SB; lia))). rewrite VIS3. exact USH3. }
  intros fx2 R2 Mx mdx LKx Awx crx kx INVx RP2 _. destruct (lregs_after R3 R2 LR3 QCS3 RP2) as [LR2 QCS2]. replace (1 + 1) with W in INVx by (clear - HW; lia).
  exact (KX fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2).
Qed.
End Frame.

Lemma stepD lo hi raD : runD lo hi raD -> lo <= n <= hi -> L5.ra_ok raD ->
  (forall F fl LK2 M2 model2
      (G : PMBUK.gctx L ar HI (PM.parser_own s ++ PEC.enc_own en ++ LBX) FF LK Aw sp 18432 (sp - FR) (sp - 8 * Z.of_nat (length PEBEK3.SV9)) sp (PEBEK3.ocell sp (Z.of_nat (length PEBEK3.SV9))) (PEBEK3.owns PEBEK3.SV9 sp R) F fl 0 LK2 M2 model2 cr (PEBEK3.EBX k))
      (APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar (PEBEK3.EBX k ++ (PM.parser_own s ++ PEC.enc_own en ++ LBX)) FF sp0 scr0 (a + i)) -> 0 < n0 ->
                 (a + n0 <= F \/ F + 64 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a))
      (fx2 : FPState) R2 Mx mdx LKx Awx crx kx,
      INV F Mx mdx LKx Awx crx kx 1 -> lregs R2 b sp F (PMSPA.o_v AD fb) n -> (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)) ->
      (lo = 0 -> getr R2 (reg 21) = Z_to_bv 64 (F + 32)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 raD Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xafe84 M model) K.
Proof.
  intros RD HV RAD KX.
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in ASTK, STKSH. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. pose proof Hrs as HRS. pose proof Eb as EB. pose proof B32 as BAL.
  destruct K_vis_entry as (SF0 & E2 & E10 & E1 & _ & OVR). cbv beta in SF0. destruct SF0 as (Wi1 & Wi2 & Wi3 & SR & SAL & SWR).
  assert (RA : runA rs) by (destruct HRS as [E|E]; rewrite E; [exact u_runA0| exact u_runA16]).
  destruct (RA fx R (mrestrict (ahid Aw model) M) b ltac:(clear - SLO SPT HRS EB; lia) ltac:(clear - SHI SPT HRS EB; lia) ltac:(rewrite E2; f_equal; unfold b; clear; lia) Wi1 Wi2 Wi3
               ltac:(clear - SR HRS EB; lia) ltac:(clear - SR HRS EB; lia) BAL ltac:(replace (b - 128) with (sp - FR) by (clear - EB; lia); unfold FR; exact SWR))
    as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T19 & T20 & T21 & OWN1).
  replace (b + rs) with sp in T8, OWN1 by (unfold b; clear; lia).
  apply (K_start 0xafe84 0xafee8 fx1 R1 M1v MS1 MG1 ltac:(intros i Hi Ni; apply FRZ1; [exact Hi| clear - Ni EB; unfold FR in *; lia]) OWN1 T1 ltac:(rewrite T2; f_equal; clear - EB; lia) ltac:(apply KS1; inl) ltac:(clear; lia) ltac:(reflexivity)).
  intros F fl LK2 M2 model2 R2 G APART INV2 RP2 G10 ZSH.
  pose proof (K_g_facts F fl LK2 M2 model2 G APART) as GF. cbv beta in GF. destruct GF as (GF1 & GF2 & GF3 & _ & GF8 & _ & GL1 & GL2 & _).
  destruct (vis F fl LK2 M2 model2 G APART M2 model2 LK2 Aw cr k 0 INV2) as (SF2 & _ & FF2 & _ & OWN2 & OF2 & U8 & KR & K8 & VFf2 & VSH2).
  pose proof OF2 as (OR & _).
  assert (FF2' : PEBEK.ffacts 128 b F fl (mrestrict (ahid Aw model2) M2) true).
  { destruct FF2 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & X8). split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|]. split; [exact ZSH| exact X8]. }
  assert (R2c : forall j, In j L5SAR.cs_all -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
  destruct (RD fx1 R2 (mrestrict (ahid Aw model2) M2) b sp (PMSPA.o_v AD fb) n (PESK.o_sink EE fb) F fl ltac:(clear - SLO SHI SPT HRS EB; lia) ltac:(clear - OR; lia) VRR ltac:(clear - KR; lia) ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia)
             ltac:(rewrite (R2c 2%nat) by inl; exact T2) ltac:(rewrite (R2c 8%nat) by inl; exact T8) ltac:(rewrite (R2c 9%nat) by inl; exact T9) G10
             ltac:(rewrite (R2c 19%nat) by inl; rewrite T19; exact A11) ltac:(rewrite (R2c 20%nat) by inl; rewrite T20, <- L5K.rl10; exact A10) ltac:(rewrite (R2c 21%nat) by inl; exact T21)
             SF2 FF2' OF2 U8 KR K8 HV)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & U1 & U10 & U11 & LR3 & LR21).
  pose proof (conj LR3 LR21) as LR3full.
  pose proof INV2 as ((HH2 & AM2 & _) & _).
  set (W3 := fun a => (b - 128 <= a < b - 128 + 56) \/ (F <= a < F + 24) \/ (F / 8 + SBL <= a < F / 8 + SBL + 8)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 fx1 fx3 R2 0xafee8 R3 PBPC M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn'. apply FRZ3; [exact Ha| intros X'; apply Hn'; left; exact X'| intros X'; apply Hn'; right; left; exact X'| intros X'; apply Hn'; right; right; exact X']. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT HRS EB; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar _ _ 0 0 F 0 (sp - FR + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 0 (sp - FR + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - X' GF8. Lia.lia.
    - destruct Wa as [X'|[X'|X']]; unfold SB; clear - X' GF3 SLO SPT HRS EB; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV F M3 md3 LK2 Aw cr k 0).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART M2 M3 W3 model2 md3 LK2 cr Aw k 0 INV2 HH3 AM3 MRT3 MGM3); [| exact FR3].
    intros a [X'|[X'|X']]; [left; split; [clear - X' HRS EB; lia| unfold PEBEK3.ocell, PEBEK3.SV9; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - X' HRS EB; lia]
                         | right; left; clear - X'; lia | right; right; unfold SB; clear - X'; lia]. }
  assert (QCS3 : forall j, In j CSK -> getr R3 (reg j) = getr R (reg j)).
  { intros j Hj. rewrite (KS3 j Hj). rewrite (R2c j (CSKall j Hj)). apply KS1. exact Hj. }
  pose proof W1 as HW.
  apply (K_pb_call F fl LK2 M2 model2 G APART 0 (b - 73) (xhi + W) raD fx3 R3 M3 md3 LK2 Aw cr k INV3 HBN ltac:(clear - HW; lia) ltac:(clear - HRS EB; lia) ltac:(clear - HRS EB; lia) RAD U1 ltac:(rewrite (proj1 LR3); f_equal; clear - EB; lia) U10 U11 QCS3).
  intros fx2 R2' Mx mdx LKx Awx crx kx INVx RP2' _. destruct (lregs_after F R3 R2' LR3 QCS3 RP2') as [LR2 QCS2].
  apply (KX F fl LK2 M2 model2 G APART fx2 R2' Mx mdx LKx Awx crx kx INVx LR2 QCS2).
  intros Hlo. rewrite (L5SAR.cs_of_preserved R3 R2' 21 RP2') by inl. exact (proj2 LR3full Hlo).
Qed.

Lemma main : srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xafe84 M model) K.
Proof.
  pose proof W1 as HW.
  destruct (Z.le_gt_cases n 255) as [V8|V8'].
  { assert (HW2 : W = 2) by (unfold W, pl_size; replace (n <=? 255) with true by (symmetry; apply Z.leb_le; exact V8); reflexivity).
    apply (stepD 0 255 0xb000c u_runD8); [clear - VR V8; lia| split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 G21.
    apply (stepP8 F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx V8 (eq_sym HW2) INVx LR2 QCS2 (G21 eq_refl)).
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (stepJ F fl LK2 M2 model2 G APART 0xb0024 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ8 INV4 LR4 QCS4). }
  destruct (Z.le_gt_cases n 32767) as [V16|V16'].
  { assert (HW3 : W = 3).
    { unfold W, pl_size. replace (n <=? 255) with false by (symmetry; apply Z.leb_gt; exact V8'). replace (n <=? 32767) with true by (symmetry; apply Z.leb_le; exact V16). reflexivity. }
    apply (stepD 256 32767 0xb0064 u_runD16); [clear - V8' V16; lia| split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
    apply (stepW F fl LK2 M2 model2 G APART 0xb0064 0xb1bc4 0xb0070 256 32767 2 fx2 R2 Mx mdx LKx Awx crx kx u_runW16 NTB16); [clear - V8' V16; lia| clear; lia| clear - HW3; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (stepJ F fl LK2 M2 model2 G APART 0xb0070 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ16 INV4 LR4 QCS4). }
  destruct (Z.le_gt_cases n 2147483647) as [V32|V32'].
  { assert (HW5 : W = 5).
    { unfold W, pl_size. replace (n <=? 255) with false by (symmetry; apply Z.leb_gt; exact V8'). replace (n <=? 32767) with false by (symmetry; apply Z.leb_gt; exact V16').
      replace (n <=? 2147483647) with true by (symmetry; apply Z.leb_le; exact V32). reflexivity. }
    apply (stepD 32768 2147483647 0xb00a8 u_runD32); [clear - V16' V32; lia| split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
    apply (stepW F fl LK2 M2 model2 G APART 0xb00a8 0xb1da4 EV 32768 2147483647 4 fx2 R2 Mx mdx LKx Awx crx kx u_runW32 NTB32); [clear - V16' V32; lia| clear; lia| clear - HW5; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (tailE F fl LK2 M2 model2 G APART fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4). }
  assert (HW9 : W = 9).
  { unfold W, pl_size. replace (n <=? 255) with false by (symmetry; apply Z.leb_gt; exact V8'). replace (n <=? 32767) with false by (symmetry; apply Z.leb_gt; exact V16').
    replace (n <=? 2147483647) with false by (symmetry; apply Z.leb_gt; exact V32'). reflexivity. }
  apply (stepD 2147483648 INT64_MAX 0xaffc4 u_runD64); [clear - V32' VR; lia| split; [clear; lia| reflexivity]|].
  intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
  apply (stepW F fl LK2 M2 model2 G APART 0xaffc4 0xb1fa4 0xaffd0 2147483648 INT64_MAX 8 fx2 R2 Mx mdx LKx Awx crx kx u_runW64 NTB64); [clear - V32' VR; lia| clear; lia| clear - HW9; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
  intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
  exact (stepJ F fl LK2 M2 model2 G APART 0xaffd0 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ64 INV4 LR4 QCS4).
Qed.
End Call.

Theorem put_length_ok : PECSB.put_length_spec L ar HI P.
Proof.
  unfold PECSB.put_length_spec, PECSPA.put_length_spec. cbn [pe_put_length EE PeCLayoutB.EADDR_B].
  intros PMODE fx R M model K LBX FF LK Aw cr sp r fb cat n p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP16 A10 A11 VR CPRE INCS POK MP HB CRED KONT.
  rewrite L5K.rl11 in A11. unfold UbjRef.INT64_MAX in VR |- *.
  destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad]. cbn [s_hi] in HB.
  exact (main PMODE n fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
           HH AM K0 ENT FRM FRS FOK SP16 A10 VR A11 CPRE INCS HB CRED KONT).
Qed.
End WithHeap.
End PEBENCPL.
