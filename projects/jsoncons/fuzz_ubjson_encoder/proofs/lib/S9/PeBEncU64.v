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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrameA PeEncKit PeBCReset1 PmBUarK PmBUar PeBPbIndSpec PeBEncNtbSpec PeBEncKit PeBEncNtb PeBEncU64P.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_ac318_ac31c.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENCVU.
#[local] Transparent e_end_value.
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

Definition CSK : list nat := [3; 4; 26; 27]%nat.
Abbreviation PBPC := 0xb120c.
Abbreviation INT64_MAX := 9223372036854775807.
Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.

Definition runA : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp : Z),
    0 <= sp < 2 ^ 64 -> getr R (reg 2) = Z_to_bv 64 sp -> PEBEK.sfacts 128 sp M ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 <= i < sp - 128 + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac028 M) (mst fx' R' SM0 M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 0xac094 /\ getr R' (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R' (reg 8) = Z_to_bv 64 sp /\ getr R' (reg 9) = Z_to_bv 64 (sp - 128)
      /\ getr R' (reg 19) = getr R (reg 10) /\ getr R' (reg 20) = getr R (reg 11) /\ getr R' (reg 23) = Z_to_bv 64 SBL
      /\ PEBEK.owns PEBEK.SV11 sp R M'.

Definition lregs (R : bvmap 5 word) (sp F ov v : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R (reg 8) = Z_to_bv 64 sp /\ getr R (reg 9) = Z_to_bv 64 (sp - 128) /\ getr R (reg 18) = Z_to_bv 64 F
  /\ getr R (reg 19) = Z_to_bv 64 ov /\ getr R (reg 20) = Z_to_bv 64 v /\ getr R (reg 21) = Z_to_bv 64 (ov + 8) /\ getr R (reg 23) = Z_to_bv 64 SBL
  /\ getr R (reg 24) = Z_to_bv 64 F /\ getr R (reg 25) = Z_to_bv 64 (F / 8 + SBL).

Definition ovfacts (M : word -> option byte) (sp ov F fl : Z) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5.writable RSEGS M ov 56 /\ ((sp - 128) + 128 <= ov \/ ov + 56 <= (sp - 128))
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1
  /\ (ov + 56 <= F \/ F + 64 <= ov) /\ (ov + 56 <= fl \/ fl + 1 <= ov) /\ (ov / 8 + SBL + 7 <= F / 8 + SBL \/ F / 8 + SBL + 8 <= ov / 8 + SBL).

Definition runD (lo hi mk byo raD : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov v o F fl : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - 128) -> getr R (reg 8) = Z_to_bv 64 sp -> getr R (reg 9) = Z_to_bv 64 (sp - 128) -> getr R (reg 10) = Z_to_bv 64 F ->
    getr R (reg 19) = Z_to_bv 64 ov -> getr R (reg 20) = Z_to_bv 64 v -> getr R (reg 23) = Z_to_bv 64 SBL ->
    PEBEK.sfacts 128 sp M -> PEBEK.ffacts 128 sp F fl M true -> ovfacts M sp ov F fl ->
    L5.u64_at RSEGS M (ov + 8) o -> 4096 <= o <= 140737488355304 -> o mod 8 = 0 -> lo <= v <= hi ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 <= i < sp - 128 + 40) -> ~ (F <= i < F + 24) -> ~ (F / 8 + SBL <= i < F / 8 + SBL + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac094 M) (mst fx' R' PBPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 raD /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 11) = Z_to_bv 64 (sp - 128 + byo)
      /\ lregs R' sp F ov v /\ (lo = 0 -> getr R' (reg 22) = Z_to_bv 64 (F + 32)).

Definition runP8 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov v F fl : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    lregs R sp F ov v -> getr R (reg 22) = Z_to_bv 64 (F + 32) -> PEBEK.sfacts 128 sp M -> PEBEK.ffacts 128 sp F fl M false -> ovfacts M sp ov F fl -> 0 <= v <= 255 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 + 36 <= i < sp - 128 + 36 + 1) -> ~ (F + 32 <= i < F + 32 + 8) -> ~ (F / 8 + 2147450884 <= i < F / 8 + 2147450884 + 1) ->
            M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac1b8 M) (mst fx' R' PBIPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 0xac1d0 /\ getr R' (reg 10) = Z_to_bv 64 (F + 32) /\ getr R' (reg 11) = Z_to_bv 64 (sp - 128 + 36)
      /\ lregs R' sp F ov v /\ getr R' (reg 22) = Z_to_bv 64 (F + 32)
      /\ L5.u64_at RSEGS M' (F + 32) (ov + 8) /\ L5.u8_at RSEGS M' (F / 8 + 2147450884) 0.

Definition runW (pcW wr raW : Z) (lo hi : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov v F : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= F < 2 ^ 64 ->
    lregs R sp F ov v -> PEBEK.sfacts 128 sp M -> 4096 <= ov <= 140737488355272 -> ov mod 8 = 0 -> lo <= v <= hi ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pcW M) (mst fx' R' wr M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 raW /\ getr R' (reg 11) = Z_to_bv 64 (ov + 8) /\ lregs R' sp F ov v.

Definition runJ (pcJ : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov v F fl : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    lregs R sp F ov v -> PEBEK.sfacts 128 sp M -> PEBEK.ffacts 128 sp F fl M false -> ovfacts M sp ov F fl ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (F / 8 + 2147450884 <= i < F / 8 + 2147450884 + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pcJ M) (mst fx' R' 0xac264 M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ lregs R' sp F ov v.

Definition runE0 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov v F fl eb r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 ->
    lregs R sp F ov v -> PEBEK.sfacts 128 sp M -> PEBEK.ffacts 128 sp F fl M false -> ovfacts M sp ov F fl ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) eb -> 0 <= eb <= 140737488355328 ->
    PEBEK.owns PEBEK.SV11 sp R0 M -> getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ PMBUK.Wret F fl 0 i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac264 M) (mst fx' R' r M')
      /\ L5.u8_at RSEGS M' fl 0 /\ regs_preserved R0 R'.

Definition runE1 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov v F fl eb ed cn r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 -> 0 <= cn < 2 ^ 64 ->
    lregs R sp F ov v -> PEBEK.sfacts 128 sp M -> PEBEK.ffacts 128 sp F fl M false -> ovfacts M sp ov F fl ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) ed ->
    4096 <= eb -> 4120 <= ed <= 140737488355328 -> ed mod 8 = 0 -> 24 <= ed - eb <= 100000 -> L5.writable RSEGS M (ed - 24) 24 ->
    (2147446784 + 17592186048512 <= ed - 24 \/ (ed - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((ed - 8) / 8 + SBL) 1 ->
    ((ed - 24) + 24 <= (sp - 128) \/ (sp - 128) + 128 <= (ed - 24)) -> ((ed - 24) + 24 <= ov \/ ov + 56 <= (ed - 24)) ->
    ((ed - 24) + 24 <= F \/ F + 64 <= (ed - 24)) -> ((ed - 24) + 24 <= fl \/ fl + 1 <= (ed - 24)) -> ((ed - 24) / 8 + SBL + 3 <= F / 8 + SBL \/ F / 8 + SBL + 8 <= (ed - 24) / 8 + SBL) ->
    L5.u64_at RSEGS M (ed - 8) cn ->
    PEBEK.owns PEBEK.SV11 sp R0 M -> getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ PMBUK.Wret F fl 0 i -> ~ (ed - 8 <= i < ed - 8 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac264 M) (mst fx' R' r M')
      /\ L5.u64_at RSEGS M' (ed - 8) ((cn + 1) mod 2 ^ 64) /\ L5.u8_at RSEGS M' fl 0 /\ regs_preserved R0 R'.

Ltac gks KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEBENCVUP.aligned; assumption | apply wid | apply wrng | L5SAR.greg | L5SAR.gmem | lia]).
Ltac greg1 KS :=
  first [ assumption
        | lazymatch goal with |- getr ?R1 (reg ?n) = _ =>
            first [ lazymatch goal with H : getr R1 (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end
                  | rewrite (KS n) by inl; lazymatch goal with H : getr _ (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end ] end ].

Ltac midV R sp ov v o F fl eb ed cn r R0 :=
  constr:(fun j : nat => match j with 2%nat => sp | 10%nat => ov | 11%nat => v | 38%nat => eb | 39%nat => ed | 41%nat => o | 42%nat => cn | 47%nat => F | 48%nat => fl | 64%nat => r
     | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9)) | 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19))
     | 69%nat => bv_unsigned (getr R0 (reg 20)) | 70%nat => bv_unsigned (getr R0 (reg 21)) | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23))
     | 73%nat => bv_unsigned (getr R0 (reg 24)) | 74%nat => bv_unsigned (getr R0 (reg 25))
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end).

Lemma u_runA : runA.
Proof.
  intros fx R M sp Hsp G2 (K0 & K1 & K2 & K3 & K4 & K5).
  pose proof (PEBENCVUP.bvuA_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|].
  decompose [and] P. split; [gks KS|]. unfold PEBEK.owns, PEBEK.SV11. repeat split; first [greg1 KS | L5SAR.gmem].
Qed.

Ltac runD_tac CONC :=
  intros fx R M sp ov v o F fl Hsp Hov Hv Ho HF Hfl G2 G8 G9 G10 G19 G20 G23 (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF UO OR1 OA HV;
  unfold PEBEK.ffacts in FF0; decompose [and] FF0; unfold ovfacts in OVF; decompose [and] OVF;
  let V := midV R sp ov v o F fl 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs; repeat split; first [greg1 KS | intros Hlo; first [greg1 KS | exfalso; clear - Hlo; lia]].
Lemma u_runD8 : runD 0 255 85 35 0xac1b8. Proof. runD_tac PEBENCVUP.bvuD8_conc. Qed.
Lemma u_runD16 : runD 256 32767 73 37 0xac210. Proof. runD_tac PEBENCVUP.bvuD16_conc. Qed.
Lemma u_runD32 : runD 32768 2147483647 108 38 0xac258. Proof. runD_tac PEBENCVUP.bvuD32_conc. Qed.
Lemma u_runD64 : runD 2147483648 INT64_MAX 76 39 0xac170. Proof. runD_tac PEBENCVUP.bvuD64_conc. Qed.

Lemma u_runP8 : runP8.
Proof.
  intros fx R M sp ov v F fl Hsp Hov Hv HF Hfl LR G22 (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF HV.
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G24 & G25). unfold PEBEK.ffacts in FF0; decompose [and] FF0. unfold ovfacts in OVF; decompose [and] OVF.
  let V := midV R sp ov v 0 F fl 0 0 0 0 R in pose proof (PEBENCVUP.bvuP8_conc fx R M V) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P).
  exists fx1, R1, M1. split; [exact MG1|].
  split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia]|].
  split; [exact MS1|]. decompose [and] P. split; [gks KS|]. unfold lregs. repeat split; greg1 KS.
Qed.

Ltac runW_tac CONC :=
  intros fx R M sp ov v F Hsp Hov Hv HF LR (K0 & K1 & K2 & K3 & K4 & K5) OR1 OA1 HV;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G24 & G25);
  let V := midV R sp ov v 0 F 0 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|]; split; [intros i Hi; apply FRZ1; exact Hi|]; split; [exact MS1|];
  decompose [and] P; split; [gks KS|]; unfold lregs; repeat split; greg1 KS.
Lemma u_runW16 : runW 0xac210 0xb3614 0xac220 256 32767. Proof. runW_tac PEBENCVUP.bvuW16_conc. Qed.
Lemma u_runW32 : runW 0xac258 0xb37f8 0xac264 32768 2147483647. Proof. runW_tac PEBENCVUP.bvuW32_conc. Qed.
Lemma u_runW64 : runW 0xac170 0xb39f8 0xac17c 2147483648 INT64_MAX. Proof. runW_tac PEBENCVUP.bvuW64_conc. Qed.

Ltac runJ_tac CONC :=
  intros fx R M sp ov v F fl Hsp Hov Hv HF Hfl LR (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G24 & G25); unfold PEBEK.ffacts in FF0; decompose [and] FF0; unfold ovfacts in OVF; decompose [and] OVF;
  let V := midV R sp ov v 0 F fl 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  let REST := fresh "REST" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & REST);
  first [ let P' := fresh "P'" in destruct REST as [KS P']; decompose [and] P' | rename REST into KS ];
  exists fx1, R1, M1; split; [exact MG1|]; split; [intros i Hi N1; apply FRZ1; first [exact Hi | clear - N1; lia]|]; split; [exact MS1|];
  split; [gks KS|]; unfold lregs; repeat split; greg1 KS.
Lemma u_runJ8 : runJ 0xac1d0. Proof. runJ_tac PEBENCVUP.bvuJ8_conc. Qed.
Lemma u_runJ16 : runJ 0xac220. Proof. runJ_tac PEBENCVUP.bvuJ16_conc. Qed.
Lemma u_runJ64 : runJ 0xac17c. Proof. runJ_tac PEBENCVUP.bvuJ64_conc. Qed.

Lemma regs_end (R R0 R3 : bvmap 5 word) (sp : Z) (KS : list nat) :
  (forall j, In j CSK -> In j KS) -> (forall x, In x KS -> getr R3 (reg x) = getr R (reg x)) -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
  getr R0 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 2) = Z_to_bv 64 sp ->
  getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R3 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  getr R3 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) -> getr R3 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 23))) ->
  getr R3 (reg 24) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 24))) -> getr R3 (reg 25) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 25))) -> regs_preserved R0 R3.
Proof.
  intros SUB KS3 QCS Rsp T2 T8 T9 T18 T19 T20 T21 T22 T23 T24 T25. apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
  repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8; apply Z_to_bv_bv_unsigned | rewrite T9; apply Z_to_bv_bv_unsigned | rewrite T18; apply Z_to_bv_bv_unsigned
                                          | rewrite T19; apply Z_to_bv_bv_unsigned | rewrite T20; apply Z_to_bv_bv_unsigned | rewrite T21; apply Z_to_bv_bv_unsigned
                                          | rewrite T22; apply Z_to_bv_bv_unsigned | rewrite T23; apply Z_to_bv_bv_unsigned | rewrite T24; apply Z_to_bv_bv_unsigned
                                          | rewrite T25; apply Z_to_bv_bv_unsigned
                                          | rewrite (KS3 _) by (apply SUB; inl); apply QCS; inl ] |]). destruct Hj.
Qed.

Lemma u_runE0 : runE0.
Proof.
  intros fx R R0 M sp ov v F fl eb r Hsp Hov Hv HF Hfl Heb LR (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF U24 U32 EB OWN0 Hra R0sp RA QCS.
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G24 & G25). unfold PEBEK.ffacts in FF0. decompose [and] FF0. unfold ovfacts in OVF. decompose [and] OVF.
  unfold PEBEK.owns, PEBEK.SV11 in OWN0. destruct OWN0 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & _). pose proof RA as (Hr1 & Hr2).
  rewrite Hra, L5.unsigned_lit in S8 by (clear - Hr1; lia).
  let V := midV R sp ov v 0 F fl eb eb 0 r R0 in pose proof (PEBENCVUP.bvuE0_conc fx R M V) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & FL0 & _).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac368 W_ac318 r F_ac318 eq_refl D_ac318 T1 ltac:(clear - Hr1; lia) Hr2) as MSR.
  exists fx1, R1, M1. split; [exact MG1|].
  split; [intros i Hi N; unfold PMBUK.Wret in N; change (ff_bytes 0) with 64 in N; change (64 / 8) with 8 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N; lia| clear - N; lia| clear - N; lia]|].
  split; [eapply msteps_trans; [exact MS1| exact MSR]|]. split; [exact FL0|].
  apply (regs_end R R0 R1 sp PEBENCVUP.KS_bvuE0); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23| exact T24| exact T25].
Qed.

Lemma u_runE1 : runE1.
Proof.
  intros fx R R0 M sp ov v F fl eb ed cn r Hsp Hov Hv HF Hfl Heb Hed Hcn LR (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF U24 U32 EB1 ED1 ED8 LEN WR24 NSH ZC DJS DJO DJF DJL DJSH UC OWN0 Hra R0sp RA QCS.
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G24 & G25). unfold PEBEK.ffacts in FF0. decompose [and] FF0. unfold ovfacts in OVF. decompose [and] OVF.
  unfold PEBEK.owns, PEBEK.SV11 in OWN0. destruct OWN0 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & _). pose proof RA as (Hr1 & Hr2).
  rewrite Hra, L5.unsigned_lit in S8 by (clear - Hr1; lia).
  destruct (Z.eq_dec cn 18446744073709551615) as [CW|CNW].
  - rewrite CW in UC.
    let V := midV R sp ov v 0 F fl eb ed cn r R0 in pose proof (PEBENCVUP.bvuE1w_conc fx R M V) as P. cbn beta iota in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & FL0 & _ & CC).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac368 W_ac318 r F_ac318 eq_refl D_ac318 T1 ltac:(clear - Hr1; lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|].
    split; [intros i Hi N N2; unfold PMBUK.Wret in N; change (ff_bytes 0) with 64 in N; change (64 / 8) with 8 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N2; lia| clear - N; lia| clear - N; lia| clear - N; lia]|].
    split; [eapply msteps_trans; [exact MS1| exact MSR]|]. split; [rewrite CW; change ((18446744073709551615 + 1) mod 2 ^ 64) with 0; exact CC|]. split; [exact FL0|].
    apply (regs_end R R0 R1 sp PEBENCVUP.KS_bvuE1w); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23| exact T24| exact T25].
  - let V := midV R sp ov v 0 F fl eb ed cn r R0 in pose proof (PEBENCVUP.bvuE1_conc fx R M V) as P. cbn beta iota in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & FL0 & _ & CC).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac368 W_ac318 r F_ac318 eq_refl D_ac318 T1 ltac:(clear - Hr1; lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|].
    split; [intros i Hi N N2; unfold PMBUK.Wret in N; change (ff_bytes 0) with 64 in N; change (64 / 8) with 8 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N2; lia| clear - N; lia| clear - N; lia| clear - N; lia]|].
    split; [eapply msteps_trans; [exact MS1| exact MSR]|]. split; [rewrite Z.mod_small by (clear - Hcn CNW; lia); exact CC|]. split; [exact FL0|].
    apply (regs_end R R0 R1 sp PEBENCVUP.KS_bvuE1); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23| exact T24| exact T25].
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
Let NTB16 := PEBENTB.ntb_i16_ok L ar C HI P LY HIok PO PBI.
Let NTB32 := PEBENTB.ntb_i32_ok L ar C HI P LY HIok PO PBI.
Let NTB64 := PEBENTB.ntb_i64_ok L ar C HI P LY HIok PO PBI.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (v : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z).
Variables (xstk : list pstate) (xpos : Z) (xmore xdone xhalt : bool) (xdepth : Z) (xec : bool) (xestk : list eitem) (xedepth xlo xhi : Z) (xbad : bool).
Variables (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Let X : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad.
Let XS (a : Z) : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + a) (xhi + a) xbad.
Let W : Z := PECSPA.uint64_width v.
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 4.
Hypothesis FRM : PMSPA.ffroomA 4 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis VR : 0 <= v <= INT64_MAX.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 v.
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis MP : PECSPA.mp_enc p X.
Hypothesis HBN : PESKA.spa_hb P (xhi + W).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (e_end_value (XS W)) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Lemma HFR : 128 = 96 \/ 128 = 128. Proof. right; reflexivity. Qed.
Lemma HSV : PEBEK.SV11 = PEBEK.SV9 \/ PEBEK.SV11 = PEBEK.SV11. Proof. right; reflexivity. Qed.
Lemma W1 : 2 <= W <= 9. Proof. unfold W, PECSPA.uint64_width. repeat destruct (_ <=? _); lia. Qed.
Lemma HNB : 0 <= W. Proof. pose proof W1. lia. Qed.
Lemma CSK3 : In 3%nat CSK. Proof. inl. Qed.
Lemma CSK4 : In 4%nat CSK. Proof. inl. Qed.
Lemma CSKall j : In j CSK -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.

Local Notation K_vis_entry := (PEBEK.vis_entry L ar C HI LY HIok 128 HFR R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK SP32 A10).
Local Notation K_start := (PEBEK.start L ar C HI P LY HIok 128 PEBEK.SV11 HFR HSV fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 CPRE).
Local Notation K_vis_facts := (PEBEK.vis_facts L ar C HI P LY HIok 128 PEBEK.SV11 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32).
Local Notation K_g_facts := (PEBEK.g_facts L ar C HI LY HIok 128 PEBEK.SV11 HFR HSV R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK).
Local Notation K_inv_agree := (PEBEK.inv_agree L ar C HI P LY HIok 128 PEBEK.SV11 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK).
Local Notation K_pb_call := (PEBEK.pb_call L ar C HI P LY HIok PO PB 128 PEBEK.SV11 CSK HFR HSV CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 CPRE CRED).
Local Notation K_pbi_call := (PEBEK.pbi_call L ar C HI P LY HIok PO PBI 128 PEBEK.SV11 CSK HFR HSV CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 CPRE CRED).
Local Notation K_wr_call := (PEBEK.wr_call L ar C HI P LY HIok 128 PEBEK.SV11 CSK HFR HSV CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 CPRE CRED).
Local Notation INV := (PEBEK.inv L ar HI P 128 PEBEK.SV11 R M model LBX FF LK Aw cr sp fb xlo xhi s en k).

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMBUK.gctx L ar HI (PM.parser_own s ++ LBX) FF LK Aw sp 20480 (sp - 128) (sp - 8 * Z.of_nat (length PEBEK.SV11)) sp (PEBEK.ocell sp (Z.of_nat (length PEBEK.SV11))) (PEBEK.owns PEBEK.SV11 sp R) F fl 0 LK2 M2 model2 cr (PEBEK.EBX en k).
Hypothesis APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (PEBEK.EBX en k ++ (PM.parser_own s ++ LBX)) FF sp0 scr0 (a + i)) -> 0 < n ->
    (a + n <= F \/ F + 64 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + 8 <= a) /\ (a + n <= fl \/ fl + 1 <= a).

Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH; pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl4 in Rtp;
  pose proof (K_g_facts F fl LK2 M2 model2 G APART) as GF; cbv beta in GF; destruct GF as (GF1 & GF2 & GF3 & _ & GF8 & _ & GL1 & GL2 & _).

Lemma lregs_after R1 R2 : lregs R1 sp F (PMSPA.o_v AD fb) v -> (forall j, In j CSK -> getr R1 (reg j) = getr R (reg j)) -> regs_preserved R1 R2 ->
  lregs R2 sp F (PMSPA.o_v AD fb) v /\ (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)).
Proof.
  intros (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G24 & G25) QCS RP. split.
  - unfold lregs. repeat split; first [ rewrite (L5SAR.cs_of_preserved R1 R2 2 RP) by inl; exact G2 | rewrite (L5SAR.cs_of_preserved R1 R2 8 RP) by inl; exact G8
      | rewrite (L5SAR.cs_of_preserved R1 R2 9 RP) by inl; exact G9 | rewrite (L5SAR.cs_of_preserved R1 R2 18 RP) by inl; exact G18 | rewrite (L5SAR.cs_of_preserved R1 R2 19 RP) by inl; exact G19
      | rewrite (L5SAR.cs_of_preserved R1 R2 20 RP) by inl; exact G20 | rewrite (L5SAR.cs_of_preserved R1 R2 21 RP) by inl; exact G21 | rewrite (L5SAR.cs_of_preserved R1 R2 23 RP) by inl; exact G23
      | rewrite (L5SAR.cs_of_preserved R1 R2 24 RP) by inl; exact G24 | rewrite (L5SAR.cs_of_preserved R1 R2 25 RP) by inl; exact G25 ].
  - intros j Hj. rewrite (L5SAR.cs_of_preserved R1 R2 j RP (CSKall j Hj)). exact (QCS j Hj).
Qed.
Lemma csk_kept (R1 R2 : bvmap 5 word) KS : (forall j, In j CSK -> In j KS) -> (forall x, In x KS -> getr R2 (reg x) = getr R1 (reg x)) ->
  (forall j, In j CSK -> getr R1 (reg j) = getr R (reg j)) -> forall j, In j CSK -> getr R2 (reg j) = getr R (reg j).
Proof. intros SUB KS3 Q j Hj. rewrite (KS3 j (SUB j Hj)). exact (Q j Hj). Qed.

Lemma vis Mq mdq LKq Awq crq kq a : INV F Mq mdq LKq Awq crq kq a ->
  let MV := mrestrict (ahid Awq mdq) Mq in
  PEBEK.sfacts 128 sp MV /\ PEBEK.ffacts 128 sp F fl MV false /\ PEBEK.owns PEBEK.SV11 sp R MV /\ ovfacts MV sp (PMSPA.o_v AD fb) F fl
  /\ L5.u64_at RSEGS MV (PMSPA.o_v AD fb + 8) (PESK.o_sink EE fb) /\ 4096 <= PESK.o_sink EE fb <= 140737488355304 /\ (PESK.o_sink EE fb) mod 8 = 0
  /\ L5.u64_at RSEGS MV (PMSPA.o_v AD fb + 24) (PEC.en_b en) /\ L5.u64_at RSEGS MV (PMSPA.o_v AD fb + 32) (PEC.en_b en + 24 * Z.of_nat (length (PEC.en_stk en))) /\ 0 <= PEC.en_b en <= 2 ^ 47
  /\ L5A.avis (ahid Awq mdq) F 64 /\ L5A.avis (ahid Awq mdq) (F / 8 + SB) 8.
Proof.
  intros INVq. entry_facts.
  pose proof (K_vis_facts F fl LK2 M2 model2 G APART Mq mdq LKq Awq crq kq a INVq) as VF. cbv beta in VF.
  destruct VF as (SF & FFc & OWN & OF & _ & VFf & VSH & _).
  pose proof OF as (OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8 & KR & K8 & KO & U24 & U32 & EB & AvF & AvS & AvL & _).
  split; [exact SF|]. split; [exact FFc|]. split; [exact OWN|].
  split. { unfold ovfacts. repeat split; first [assumption | clear - OR; lia | clear - AvF O8 GF8; Lia.lia]. }
  split; [exact U8|]. split; [exact KR|]. split; [exact K8|]. split; [exact U24|]. split; [exact U32|]. split; [exact EB|]. split; [exact VFf| exact VSH].
Qed.

Lemma tailE (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  INV F Mq mdq LKq Awq crq kq W -> lregs Rq sp F (PMSPA.o_v AD fb) v -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xac264 Mq mdq) K.
Proof.
  intros INVq LRq QCS. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq W INVq) as (SF4 & FF4 & OWN4 & OF4 & _ & _ & _ & U24 & U32 & EB & _).
  pose proof OF4 as (OR4 & _).
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (_ & _ & _ & _ & _ & Lestk & _). cbn [s_estk X] in Lestk.
  unfold PMSPA.cfg.
  destruct xestk as [|e1 rr] eqn:HXS.
  - rewrite Lestk in U32. cbn [rev length Z.of_nat Z.mul] in U32. rewrite Z.add_0_r in U32.
    destruct (u_runE0 fxq Rq R (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) v F fl (PEC.en_b en) r ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR4; lia) ltac:(clear - VR; lia) ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia) ltac:(clear - EB; lia)
               LRq SF4 FF4 OF4 U24 U32 ltac:(clear - EB; lia) OWN4 Rra Rsp RAok QCS)
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & FL5 & RP5).
    exact (PEBEK.finish_ro L ar C HI P LY HIok 128 W PEBEK.SV11 HFR HSV R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec [] xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS KONT
             F fl LK2 M2 model2 G APART 0xac264 fxq Rq Mq mdq LKq Awq crq kq fx5 R5 M5v INVq eq_refl MS5 MG5 FRZ5 FL5 RP5).
  - pose proof (PEBEK.vis_facts_top L ar C HI P LY HIok 128 PEBEK.SV11 HFR HSV R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE MP
                  F fl LK2 M2 model2 G APART Mq mdq LKq Awq crq kq W e1 rr INVq eq_refl) as VT. cbv beta in VT.
    destruct VT as (HLEN & EKP & EB1 & ED2 & ALend & ED3 & WR24 & EB6 & ZC & EDS & OVA & TCv & E1C & E1OK & BINe & EDC & EBC & EDF & EDSH & EDFL & EDV).
    rewrite HLEN in U32. set (ed := PEC.en_b en + 24 * (Z.of_nat (length rr) + 1)) in *.
    destruct (u_runE1 fxq Rq R (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) v F fl (PEC.en_b en) ed (ei_cnt e1) r ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR4; lia) ltac:(clear - VR; lia) ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia)
               ltac:(clear - EB; lia) ltac:(clear - EB1 ED2 ED3; lia) E1C LRq SF4 FF4 OF4 U24 U32
               EB1 ltac:(clear - EB1 ED2 ED3; lia) ALend ED3 WR24 EB6 ZC EDS OVA EDF EDFL ltac:(clear - EDF ALend GF8; Lia.lia) TCv OWN4 Rra Rsp RAok QCS)
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & CC5 & FL5 & RP5).
    exact (PEBEK.finish_bump L ar C HI P LY HIok 128 W PEBEK.SV11 HFR HSV R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS MP KONT
             F fl LK2 M2 model2 G APART 0xac264 fxq Rq Mq mdq LKq Awq crq kq fx5 R5 M5v e1 rr INVq eq_refl MS5 MG5 FRZ5 CC5 FL5 RP5).
Qed.

Lemma stepJ pcJ (fxq : FPState) Rq Mq mdq LKq Awq crq kq : runJ pcJ ->
  INV F Mq mdq LKq Awq crq kq W -> lregs Rq sp F (PMSPA.o_v AD fb) v -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcJ Mq mdq) K.
Proof.
  intros RJ INVq LRq QCS. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq W INVq) as (SF & FFc & _ & OF & _ & _ & _ & _ & _ & _ & VFf & VSH).
  pose proof OF as (OR & _). pose proof INVq as ((HHq & AMq & _) & _).
  destruct (RJ fxq Rq (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) v F fl ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia) ltac:(clear - VR; lia) ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia) LRq SF FFc OF)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & LR3).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LKq crq Awq Mq mdq fxq fx3 Rq pcJ R3 0xac264 M3v (fun a0 => F / 8 + 2147450884 <= a0 < F / 8 + 2147450884 + 1) K HHq AMq MS3 MG3).
  { intros a0 Ha Hn. apply FRZ3; [exact Ha| exact Hn]. }
  { intros a0 Ha Wa. split.
    - apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - Wa GF8. Lia.lia.
    - clear - Wa GF3; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV F M3 md3 LKq Awq crq kq W).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART Mq M3 (fun a0 => F / 8 + 2147450884 <= a0 < F / 8 + 2147450884 + 1) mdq md3 LKq crq Awq kq W INVq HH3 AM3 MRT3 MGM3); [| exact FR3].
    intros a0 X'. right; right. unfold SB. clear - X'; lia. }
  apply (tailE fx3 R3 M3 md3 LKq Awq crq kq INV3 LR3). exact (csk_kept Rq R3 CSK (fun j Hj => Hj) KS3 QCS).
Qed.

Lemma stepW pcW wr raW lo hi kb (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  runW pcW wr raW lo hi -> PENTBB.ntb_specB RSEGS AD L ar HI wr kb P -> lo <= v <= hi -> 0 <= kb -> 1 + kb = W -> L5.ra_ok raW ->
  INV F Mq mdq LKq Awq crq kq 1 -> lregs Rq sp F (PMSPA.o_v AD fb) v -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) ->
  (forall (fx2 : FPState) R2 Mx mdx LKx Awx crx kx, INV F Mx mdx LKx Awx crx kx W -> lregs R2 sp F (PMSPA.o_v AD fb) v -> (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 raW Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcW Mq mdq) K.
Proof.
  intros RW NTB HV KB0 HW RAW INVq LRq QCS KX. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq 1 INVq) as (SF & FFc & _ & OF & _). pose proof OF as (OR & O8 & _). pose proof INVq as ((HHq & AMq & _) & _).
  destruct (RW fxq Rq (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) v F ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia) ltac:(clear - VR; lia) ltac:(clear - GF1 GF2; lia) LRq SF OR O8 HV)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T11 & LR3).
  unfold PMSPA.cfg. apply (L5SAR.apiece_ro L ar C HI LYa HIok _ _ LKq crq Awq Mq mdq fxq fx3 Rq pcW R3 wr M3v K HHq AMq MS3 MG3 FRZ3).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree Mq M3 AG3) as EM. subst M3.
  assert (INV3 : INV F Mq md3 LKq Awq crq kq 1).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART Mq Mq (fun _ => False) mdq md3 LKq crq Awq kq 1 INVq HH3 AM3 MRT3 (mem_grows_refl Mq)); [intros a0 []| intros a0 _ _; reflexivity]. }
  pose proof (csk_kept Rq R3 CSK (fun j Hj => Hj) KS3 QCS) as QCS3.
  pose proof LR3 as (G2 & _).
  apply (K_wr_call F fl LK2 M2 model2 G APART 1 kb wr (xhi + W) raW fx3 R3 Mq md3 LKq Awq crq kq NTB INV3 HBN ltac:(clear - HW; lia) KB0 RAW T1 G2 T11 QCS3).
  intros fx2 R2 Mx mdx LKx Awx crx kx INVx RP2 _. destruct (lregs_after R3 R2 LR3 QCS3 RP2) as [LR2 QCS2]. rewrite HW in INVx. exact (KX fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2).
Qed.

Lemma stepP8 (fxq : FPState) Rq Mq mdq LKq Awq crq kq : v <= 255 -> 2 = W ->
  INV F Mq mdq LKq Awq crq kq 1 -> lregs Rq sp F (PMSPA.o_v AD fb) v -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) -> getr Rq (reg 22) = Z_to_bv 64 (F + 32) ->
  (forall (fx2 : FPState) R2 Mx mdx LKx Awx crx kx, INV F Mx mdx LKx Awx crx kx W -> lregs R2 sp F (PMSPA.o_v AD fb) v -> (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xac1d0 Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xac1b8 Mq mdq) K.
Proof.
  intros HV HW INVq LRq QCS G22 KX. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq 1 INVq) as (SF & FFc & _ & OF & _ & _ & _ & _ & _ & _ & VFf & VSH). pose proof OF as (OR & _). pose proof INVq as ((HHq & AMq & _) & _).
  destruct (u_runP8 fxq Rq (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) v F fl ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia) ltac:(clear - VR; lia) ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia) LRq G22 SF FFc OF ltac:(clear - VR HV; lia))
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & LR3 & T22 & UQ3 & USH3).
  set (W3 := fun a0 => (sp - 128 + 36 <= a0 < sp - 128 + 36 + 1) \/ (F + 32 <= a0 < F + 32 + 8) \/ (F / 8 + 2147450884 <= a0 < F / 8 + 2147450884 + 1)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LKq crq Awq Mq mdq fxq fx3 Rq 0xac1b8 R3 PBIPC M3v W3 K HHq AMq MS3 MG3).
  { intros a0 Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; exact X'| intros X'; apply Hn; right; left; exact X'| intros X'; apply Hn; right; right; exact X']. }
  { intros a0 Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar _ _ 0 0 F 0 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - X' GF8. Lia.lia.
    - destruct Wa as [X'|[X'|X']]; unfold SB; clear - X' GF3 SLO SPT; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV F M3 md3 LKq Awq crq kq 1).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART Mq M3 W3 mdq md3 LKq crq Awq kq 1 INVq HH3 AM3 MRT3 MGM3); [| exact FR3].
    intros a0 [X'|[X'|X']]; [left; split; [clear - X'; lia| unfold PEBEK.ocell, PEBEK.SV11; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - X'; lia]
                          | right; left; clear - X'; lia | right; right; unfold SB; clear - X'; lia]. }
  pose proof (csk_kept Rq R3 CSK (fun j Hj => Hj) KS3 QCS) as QCS3.
  refine (K_pbi_call F fl LK2 M2 model2 G APART 1 (F + 32) (sp - 128 + 36) (xhi + W) 0xac1d0 fx3 R3 M3 md3 LKq Awq crq kq INV3 HBN ltac:(clear - HW; lia) ltac:(clear; lia) ltac:(clear; lia)
           ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) ltac:(clear; lia) ltac:(replace (F + 32) with ((F / 8 + 4) * 8) by (clear - GF8; lia); apply Z_mod_mult) _ _ T1 (proj1 LR3) T10 T11 QCS3 _).
  { apply (proj1 (L5A.u64_at_vis (ahid Awq mdq) M3 (F + 32) _ (L5A.avis_sub _ F 64 (F + 32) 8 VFf ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))). rewrite VIS3. exact UQ3. }
  { replace ((F + 32) / 8 + SBL) with (F / 8 + 2147450884) by (clear - GF8; Lia.lia).
    apply (proj1 (L5A.u8_at_vis (ahid Awq mdq) M3 (F / 8 + 2147450884) 0 (L5A.avis_sub _ (F / 8 + SB) 8 (F / 8 + 2147450884) 1 VSH ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
             ltac:(clear - GF1; lia) ltac:(clear - GF2; unfold SB; lia))). rewrite VIS3. exact USH3. }
  intros fx2 R2 Mx mdx LKx Awx crx kx INVx RP2 _. destruct (lregs_after R3 R2 LR3 QCS3 RP2) as [LR2 QCS2]. replace (1 + 1) with W in INVx by (clear - HW; lia).
  exact (KX fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2).
Qed.
End Frame.

Lemma stepD lo hi mk byo raD : runD lo hi mk byo raD -> lo <= v <= hi -> 32 <= byo <= 39 -> L5.ra_ok raD ->
  (forall F fl LK2 M2 model2
      (G : PMBUK.gctx L ar HI (PM.parser_own s ++ LBX) FF LK Aw sp 20480 (sp - 128) (sp - 8 * Z.of_nat (length PEBEK.SV11)) sp (PEBEK.ocell sp (Z.of_nat (length PEBEK.SV11))) (PEBEK.owns PEBEK.SV11 sp R) F fl 0 LK2 M2 model2 cr (PEBEK.EBX en k))
      (APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (PEBEK.EBX en k ++ (PM.parser_own s ++ LBX)) FF sp0 scr0 (a + i)) -> 0 < n ->
                 (a + n <= F \/ F + 64 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + 8 <= a) /\ (a + n <= fl \/ fl + 1 <= a))
      (fx2 : FPState) R2 Mx mdx LKx Awx crx kx,
      INV F Mx mdx LKx Awx crx kx 1 -> lregs R2 sp F (PMSPA.o_v AD fb) v -> (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)) ->
      (lo = 0 -> getr R2 (reg 22) = Z_to_bv 64 (F + 32)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 raD Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xac028 M model) K.
Proof.
  intros RD HV BYO RAD KX.
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp.
  destruct K_vis_entry as (SF0 & E2 & E10 & E1 & _ & OVR). cbv beta in SF0.
  destruct (u_runA fx R (mrestrict (ahid Aw model) M) sp ltac:(clear - SLO SHI SPT; lia) E2 SF0) as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T19 & T20 & T23 & OWN1).
  apply (K_start 0xac028 0xac094 fx1 R1 M1v MS1 MG1 FRZ1 OWN1 T1 T2 ltac:(apply KS1; inl) ltac:(clear; lia) ltac:(reflexivity)).
  intros F fl LK2 M2 model2 R2 G APART INV2 RP2 G10 ZSH.
  pose proof (K_g_facts F fl LK2 M2 model2 G APART) as GF. cbv beta in GF. destruct GF as (GF1 & GF2 & GF3 & _ & GF8 & _ & GL1 & GL2 & _).
  destruct (vis F fl LK2 M2 model2 G APART M2 model2 LK2 Aw cr k 0 INV2) as (SF2 & FF2 & OWN2 & OF2 & U8 & KR & K8 & _ & _ & _ & VFf2 & VSH2).
  pose proof OF2 as (OR & _).
  assert (FF2' : PEBEK.ffacts 128 sp F fl (mrestrict (ahid Aw model2) M2) true).
  { destruct FF2 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & X8). split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|]. split; [exact ZSH| exact X8]. }
  assert (R2c : forall j, In j L5SAR.cs_all -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
  destruct (RD fx1 R2 (mrestrict (ahid Aw model2) M2) sp (PMSPA.o_v AD fb) v (PESK.o_sink EE fb) F fl ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia) ltac:(clear - VR; lia) ltac:(clear - KR; lia) ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia)
             ltac:(rewrite (R2c 2%nat) by inl; exact T2) ltac:(rewrite (R2c 8%nat) by inl; exact T8) ltac:(rewrite (R2c 9%nat) by inl; exact T9) G10
             ltac:(rewrite (R2c 19%nat) by inl; rewrite T19, <- L5K.rl10; exact A10) ltac:(rewrite (R2c 20%nat) by inl; rewrite T20; exact A11) ltac:(rewrite (R2c 23%nat) by inl; exact T23)
             SF2 FF2' OF2 U8 KR K8 HV)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & U1 & U10 & U11 & LR3 & LR22).
  pose proof (conj LR3 LR22) as LR3full.
  pose proof INV2 as ((HH2 & AM2 & _) & _).
  set (W3 := fun a => (sp - 128 <= a < sp - 128 + 40) \/ (F <= a < F + 24) \/ (F / 8 + SBL <= a < F / 8 + SBL + 8)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 fx1 fx3 R2 0xac094 R3 PBPC M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; exact X'| intros X'; apply Hn; right; left; exact X'| intros X'; apply Hn; right; right; exact X']. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar _ _ 0 0 F 0 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - X' GF8. Lia.lia.
    - destruct Wa as [X'|[X'|X']]; unfold SB; clear - X' GF3 SLO SPT; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV F M3 md3 LK2 Aw cr k 0).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART M2 M3 W3 model2 md3 LK2 cr Aw k 0 INV2 HH3 AM3 MRT3 MGM3); [| exact FR3].
    intros a [X'|[X'|X']]; [left; split; [clear - X'; lia| unfold PEBEK.ocell, PEBEK.SV11; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - X'; lia]
                         | right; left; clear - X'; lia | right; right; unfold SB; clear - X'; lia]. }
  assert (QCS3 : forall j, In j CSK -> getr R3 (reg j) = getr R (reg j)).
  { intros j Hj. rewrite (KS3 j Hj). rewrite (R2c j (CSKall j Hj)). apply KS1. exact Hj. }
  pose proof W1 as HW.
  apply (K_pb_call F fl LK2 M2 model2 G APART 0 (sp - 128 + byo) (xhi + W) raD fx3 R3 M3 md3 LK2 Aw cr k INV3 HBN ltac:(clear - HW; lia) ltac:(clear - BYO; lia) ltac:(clear - BYO; lia) RAD U1 (proj1 LR3) U10 U11 QCS3).
  intros fx2 R2' Mx mdx LKx Awx crx kx INVx RP2' _. destruct (lregs_after F R3 R2' LR3 QCS3 RP2') as [LR2 QCS2].
  apply (KX F fl LK2 M2 model2 G APART fx2 R2' Mx mdx LKx Awx crx kx INVx LR2 QCS2).
  intros Hlo. rewrite (L5SAR.cs_of_preserved R3 R2' 22 RP2') by inl. exact (proj2 LR3full Hlo).
Qed.

Lemma main : srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xac028 M model) K.
Proof.
  pose proof W1 as HW.
  destruct (Z.le_gt_cases v 255) as [V8|V8'].
  { assert (HW2 : W = 2) by (unfold W, PECSPA.uint64_width; replace (v <=? 255) with true by (symmetry; apply Z.leb_le; exact V8); reflexivity).
    apply (stepD 0 255 85 35 0xac1b8 u_runD8); [clear - VR V8; lia| clear; lia| split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 G22.
    apply (stepP8 F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx V8 (eq_sym HW2) INVx LR2 QCS2 (G22 eq_refl)).
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (stepJ F fl LK2 M2 model2 G APART 0xac1d0 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ8 INV4 LR4 QCS4). }
  destruct (Z.le_gt_cases v 32767) as [V16|V16'].
  { assert (HW3 : W = 3).
    { unfold W, PECSPA.uint64_width. replace (v <=? 255) with false by (symmetry; apply Z.leb_gt; exact V8'). replace (v <=? 32767) with true by (symmetry; apply Z.leb_le; exact V16). reflexivity. }
    apply (stepD 256 32767 73 37 0xac210 u_runD16); [clear - V8' V16; lia| clear; lia| split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
    apply (stepW F fl LK2 M2 model2 G APART 0xac210 0xb3614 0xac220 256 32767 2 fx2 R2 Mx mdx LKx Awx crx kx u_runW16 NTB16); [clear - V8' V16; lia| clear; lia| clear - HW3; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (stepJ F fl LK2 M2 model2 G APART 0xac220 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ16 INV4 LR4 QCS4). }
  destruct (Z.le_gt_cases v 2147483647) as [V32|V32'].
  { assert (HW5 : W = 5).
    { unfold W, PECSPA.uint64_width. replace (v <=? 255) with false by (symmetry; apply Z.leb_gt; exact V8'). replace (v <=? 32767) with false by (symmetry; apply Z.leb_gt; exact V16').
      replace (v <=? 2147483647) with true by (symmetry; apply Z.leb_le; exact V32). reflexivity. }
    apply (stepD 32768 2147483647 108 38 0xac258 u_runD32); [clear - V16' V32; lia| clear; lia| split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
    apply (stepW F fl LK2 M2 model2 G APART 0xac258 0xb37f8 0xac264 32768 2147483647 4 fx2 R2 Mx mdx LKx Awx crx kx u_runW32 NTB32); [clear - V16' V32; lia| clear; lia| clear - HW5; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (tailE F fl LK2 M2 model2 G APART fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4). }
  assert (HW9 : W = 9).
  { unfold W, PECSPA.uint64_width. replace (v <=? 255) with false by (symmetry; apply Z.leb_gt; exact V8'). replace (v <=? 32767) with false by (symmetry; apply Z.leb_gt; exact V16').
    replace (v <=? 2147483647) with false by (symmetry; apply Z.leb_gt; exact V32'). reflexivity. }
  apply (stepD 2147483648 INT64_MAX 76 39 0xac170 u_runD64); [clear - V32' VR; lia| clear; lia| split; [clear; lia| reflexivity]|].
  intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
  apply (stepW F fl LK2 M2 model2 G APART 0xac170 0xb39f8 0xac17c 2147483648 INT64_MAX 8 fx2 R2 Mx mdx LKx Awx crx kx u_runW64 NTB64); [clear - V32' VR; lia| clear; lia| clear - HW9; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
  intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
  exact (stepJ F fl LK2 M2 model2 G APART 0xac17c fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ64 INV4 LR4 QCS4).
Qed.
End Call.

Theorem v_uint64_ok : PECSB.v_uint64_spec L ar HI P.
Proof.
  unfold PECSB.v_uint64_spec, PECSPA.v_uint64_spec, PECSPA.eslot_spec. cbn [pe_uint64 EE PeCLayoutB.EADDR_B].
  intros PMODE v fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 AV CPRE INCS POK MP NB HB CRED KONT.
  destruct AV as (VR & A11 & _). rewrite L5K.rl11 in A11. unfold UbjRef.INT64_MAX in VR |- *.
  destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad].
  assert (ESC : forall w, e_scalar w w (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad)
          = e_end_value (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + w) (xhi + w) xbad)) by reflexivity.
  rewrite ESC in HB, KONT. rewrite eev_hi in HB. cbn [s_hi] in HB.
  exact (main PMODE v fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
           HH AM K0 ENT FRM FRS FOK SP32 A10 VR A11 CPRE INCS MP HB CRED KONT).
Qed.
End WithHeap.
End PEBENCVU.
