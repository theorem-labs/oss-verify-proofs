(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5CoreSpecsAS8 L5StepARS8 L5CoreBRS8 L5ADetailHRS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PnStatics PmModelFactsA PmStep PeStepA PmParStep PmParKit PeASrcKit PeAParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeShZ PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrameA PeEncKit PeACReset1 PmAUarK PmAUar PeAEmbKit PeASnkAnn PeAEstkAnn PeSEncEnd PeAEncKitN PeAEncEndP1 PeAEncEndP2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_ab018_ab020 Ea0_code_abc94_abc9c Ea0_code_ab188_ab18c Ea0_code_abe04_abe08.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAENCE.
#[local] Transparent e_end_value.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).
Abbreviation SBL := 2147450880.
Abbreviation SM1 := 0x5e588.
Abbreviation PBPC := 0xaf02c.
Abbreviation MKPC := 0xae310.
Abbreviation SHRPC := 0xaeb80.

Abbreviation INV3 := 12297829382473034411.

Definition CSK : list nat := [3; 4]%nat.
Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.

Lemma v_mul_magic24 m : 0 <= m <= 2 ^ 60 -> v_mul (Z_to_bv 64 (24 * m / 8)) (Z_to_bv 64 INV3) = Z_to_bv 64 m.
Proof.
  intros Hm. unfold v_mul. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (24 * m / 8) with (3 * m) by lia. rewrite (Z.mod_small (3 * m)) by lia. rewrite (Z.mod_small INV3) by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (3 * m * INV3) with (m + (2 * m) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Definition runA (E0 SMRA : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp : Z),
    0 <= sp < 2 ^ 64 -> getr R (reg 2) = Z_to_bv 64 sp -> PEAEKN.sfacts 128 sp M ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 <= i < sp - 128 + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R E0 M) (mst fx' R' SM1 M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 SMRA /\ getr R' (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R' (reg 8) = Z_to_bv 64 sp /\ getr R' (reg 9) = Z_to_bv 64 (sp - 128)
      /\ getr R' (reg 19) = getr R (reg 12) /\ getr R' (reg 21) = getr R (reg 10) /\ getr R' (reg 25) = Z_to_bv 64 SBL
      /\ PEAEKN.owns PEAEKN.SV13 sp R M'.

Definition lregs (R : bvmap 5 word) (sp F ov oec : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R (reg 8) = Z_to_bv 64 sp /\ getr R (reg 9) = Z_to_bv 64 (sp - 128) /\ getr R (reg 18) = Z_to_bv 64 F
  /\ getr R (reg 19) = Z_to_bv 64 oec /\ getr R (reg 20) = Z_to_bv 64 (ov + 24) /\ getr R (reg 21) = Z_to_bv 64 ov /\ getr R (reg 22) = Z_to_bv 64 (ov + 32)
  /\ getr R (reg 23) = Z_to_bv 64 (F / 8 + SBL) /\ getr R (reg 24) = Z_to_bv 64 F /\ getr R (reg 25) = Z_to_bv 64 SBL
  /\ getr R (reg 26) = Z_to_bv 64 ((ov + 24) / 8 + SBL) /\ getr R (reg 27) = Z_to_bv 64 ((ov + 32) / 8 + SBL).

Definition dfacts (M : word -> option byte) (sp ov osk F fl eb ed d kd : Z) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5.writable RSEGS M ov 56 /\ ((sp - 128) + 128 <= ov \/ ov + 56 <= (sp - 128))
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 48) / 8 + SBL) 1
  /\ L5.u64_at RSEGS M (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0
  /\ L5.u32_at RSEGS M (ov + 48) d /\ 1 <= d <= 1024
  /\ L5.u64_at RSEGS M (ov + 24) eb /\ L5.u64_at RSEGS M (ov + 32) ed
  /\ 4096 <= eb <= 140737488355328 /\ 4120 <= ed <= 140737488355328 /\ ed mod 8 = 0 /\ eb mod 8 = 0 /\ 24 <= ed - eb <= 100000
  /\ L5.writable RSEGS M (ed - 24) 24 /\ (2147446784 + 17592186048512 <= ed - 24 \/ (ed - 24) + 24 <= 2147446784) /\ L5KA.zeros_at M ((ed - 24) / 8 + SBL) 3
  /\ ((ed - 24) + 24 <= (sp - 128) \/ (sp - 128) + 128 <= (ed - 24)) /\ ((ed - 24) + 24 <= ov \/ ov + 56 <= (ed - 24))
  /\ ((ed - 24) + 24 <= F \/ F + 128 <= (ed - 24)) /\ ((ed - 24) + 24 <= fl \/ fl + 1 <= (ed - 24))
  /\ ((ed - 24) / 8 + SBL + 3 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= (ed - 24) / 8 + SBL)
  /\ (ov + 56 <= F \/ F + 128 <= ov) /\ (ov + 56 <= fl \/ fl + 1 <= ov) /\ (ov / 8 + SBL + 7 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= ov / 8 + SBL)
  /\ L5.u32_at RSEGS M (ed - 24) kd.

Definition dpost (M' : word -> option byte) (sp ov F d E0 DSC : Z) : Prop :=
  L5.u32_at RSEGS M' (ov + 48) (d - 1) /\ L5.u64_at RSEGS M' (sp - 120) F /\ L5.u64_at RSEGS M' (F + 16) E0 /\ L5.u64_at RSEGS M' (F + 8) DSC /\ L5.u64_at RSEGS M' F 1102416563
  /\ L5.defined M' (F + 24) 104.

Definition runDi (E0 SMRA DSC MK kd PBRA : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec osk F fl eb ed d : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 -> 0 <= d < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - 128) -> getr R (reg 8) = Z_to_bv 64 sp -> getr R (reg 9) = Z_to_bv 64 (sp - 128) -> getr R (reg 10) = Z_to_bv 64 F ->
    getr R (reg 19) = Z_to_bv 64 oec -> getr R (reg 21) = Z_to_bv 64 ov -> getr R (reg 25) = Z_to_bv 64 SBL ->
    PEAEKN.sfacts 128 sp M -> PEAEKN.ffacts 128 sp F fl M true -> dfacts M sp ov osk F fl eb ed d kd ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 + 8 <= i < sp - 128 + 8 + 8) -> ~ (F <= i < F + 24) -> ~ (F / 8 + SBL <= i < F / 8 + SBL + 12) ->
            ~ (ov + 48 <= i < ov + 52) -> ~ (sp - 128 + 23 <= i < sp - 128 + 23 + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R SMRA M) (mst fx' R' PBPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 PBRA /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp - 105)
      /\ lregs R' sp F ov oec /\ L5.u8_at RSEGS M' (sp - 105) MK /\ dpost M' sp ov F d E0 DSC.

Definition crel (rel ln cn dd : Z) : Prop :=
  match rel with
  | 0 => 0 <= cn <= 16777215 /\ 1 <= ln - cn <= 16777216 /\ dd = 0
  | 1 => cn = ln + dd /\ 1 <= dd <= 18446744073692774399
  | _ => 18446744073692774400 <= cn <= 18446744073709551615 /\ dd = 0
  end.
Definition runDc (E0 SMRA DSC kd rel ecv MKRA : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec osk F fl eb ed d ln cn dd : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 -> 0 <= d < 2 ^ 64 ->
    0 <= ln < 2 ^ 64 -> 0 <= cn < 2 ^ 64 -> 0 <= dd < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - 128) -> getr R (reg 8) = Z_to_bv 64 sp -> getr R (reg 9) = Z_to_bv 64 (sp - 128) -> getr R (reg 10) = Z_to_bv 64 F ->
    getr R (reg 19) = Z_to_bv 64 oec -> getr R (reg 21) = Z_to_bv 64 ov -> getr R (reg 25) = Z_to_bv 64 SBL ->
    PEAEKN.sfacts 128 sp M -> PEAEKN.ffacts 128 sp F fl M true -> dfacts M sp ov osk F fl eb ed d kd ->
    L5.u64_at RSEGS M (ed - 16) ln -> 0 <= ln <= 16777216 -> L5.u64_at RSEGS M (ed - 8) cn -> crel rel ln cn dd ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 + 8 <= i < sp - 128 + 8 + 8) -> ~ (F <= i < F + 24) -> ~ (F / 8 + SBL <= i < F / 8 + SBL + 12) ->
            ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R SMRA M) (mst fx' R' MKPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 MKRA /\ getr R' (reg 10) = Z_to_bv 64 oec /\ getr R' (reg 11) = Z_to_bv 64 ecv
      /\ lregs R' sp F ov oec /\ dpost M' sp ov F d E0 DSC.

Definition runDeq (E0 SMRA DSC kd JE : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec osk F fl eb ed d ln : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 -> 0 <= d < 2 ^ 64 ->
    0 <= ln < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - 128) -> getr R (reg 8) = Z_to_bv 64 sp -> getr R (reg 9) = Z_to_bv 64 (sp - 128) -> getr R (reg 10) = Z_to_bv 64 F ->
    getr R (reg 19) = Z_to_bv 64 oec -> getr R (reg 21) = Z_to_bv 64 ov -> getr R (reg 25) = Z_to_bv 64 SBL ->
    PEAEKN.sfacts 128 sp M -> PEAEKN.ffacts 128 sp F fl M true -> dfacts M sp ov osk F fl eb ed d kd ->
    L5.u64_at RSEGS M (ed - 16) ln -> 0 <= ln <= 16777216 -> L5.u64_at RSEGS M (ed - 8) ln ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 + 8 <= i < sp - 128 + 8 + 8) -> ~ (F <= i < F + 24) -> ~ (F / 8 + SBL <= i < F / 8 + SBL + 12) ->
            ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R SMRA M) (mst fx' R' JE M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ lregs R' sp F ov oec /\ dpost M' sp ov F d E0 DSC.

Definition mfacts (M : word -> option byte) (sp ov F fl eb ed : Z) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5.writable RSEGS M ov 56 /\ ((sp - 128) + 128 <= ov \/ ov + 56 <= (sp - 128))
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 48) / 8 + SBL) 1
  /\ L5.u64_at RSEGS M (ov + 24) eb /\ L5.u64_at RSEGS M (ov + 32) ed
  /\ 4096 <= eb <= 140737488355328 /\ 4120 <= ed <= 140737488355328 /\ ed mod 8 = 0 /\ eb mod 8 = 0 /\ 24 <= ed - eb <= 100000
  /\ L5.writable RSEGS M (ed - 24) 24 /\ (2147446784 + 17592186048512 <= ed - 24 \/ (ed - 24) + 24 <= 2147446784) /\ L5KA.zeros_at M ((ed - 24) / 8 + SBL) 3
  /\ ((ed - 24) + 24 <= (sp - 128) \/ (sp - 128) + 128 <= (ed - 24)) /\ ((ed - 24) + 24 <= ov \/ ov + 56 <= (ed - 24))
  /\ ((ed - 24) + 24 <= F \/ F + 128 <= (ed - 24)) /\ ((ed - 24) + 24 <= fl \/ fl + 1 <= (ed - 24))
  /\ ((ed - 24) / 8 + SBL + 3 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= (ed - 24) / 8 + SBL)
  /\ (ov + 56 <= F \/ F + 128 <= ov) /\ (ov + 56 <= fl \/ fl + 1 <= ov) /\ (ov / 8 + SBL + 7 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= ov / 8 + SBL).

Definition runPQ (JPC SHRA : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec F fl eb ed m : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 ->
    lregs R sp F ov oec -> PEAEKN.sfacts 128 sp M -> L5.img_clear M 65536 1286144 -> PEAEKN.ffacts 128 sp F fl M false -> mfacts M sp ov F fl eb ed ->
    ed = eb + 24 * (m + 1) -> 0 <= m <= 4165 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (ov + 32 <= i < ov + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R JPC M) (mst fx' R' SHRPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 SHRA /\ getr R' (reg 10) = Z_to_bv 64 (ov + 24) /\ getr R' (reg 11) = Z_to_bv 64 (m + 1)
      /\ lregs R' sp F ov oec /\ L5.u64_at RSEGS M' (ov + 32) (ed - 24).

Definition runR0 (SHRA : Z) : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov oec F fl eb r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 ->
    lregs R sp F ov oec -> PEAEKN.sfacts 128 sp M -> PEAEKN.ffacts 128 sp F fl M false ->
    4096 <= ov <= 140737488355272 -> ov mod 8 = 0 -> (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) -> L5KA.zeros_at M (ov / 8 + SBL) 7 ->
    L5.writable RSEGS M ov 56 -> ((sp - 128) + 128 <= ov \/ ov + 56 <= (sp - 128)) ->
    L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 48) / 8 + SBL) 1 ->
    (ov + 56 <= F \/ F + 128 <= ov) -> (ov + 56 <= fl \/ fl + 1 <= ov) -> (ov / 8 + SBL + 7 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= ov / 8 + SBL) ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) eb -> 4096 <= eb <= 140737488355328 ->
    PEAEKN.owns PEAEKN.SV13 sp R0 M -> getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ PMAUK.Wret F fl 1 i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R SHRA M) (mst fx' R' r M')
      /\ L5.u8_at RSEGS M' fl 0 /\ regs_preserved R0 R'.

Definition runR1 (SHRA : Z) : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov oec F fl eb ed cn r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 -> 0 <= cn < 2 ^ 64 ->
    lregs R sp F ov oec -> PEAEKN.sfacts 128 sp M -> PEAEKN.ffacts 128 sp F fl M false ->
    4096 <= ov <= 140737488355272 -> ov mod 8 = 0 -> (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) -> L5KA.zeros_at M (ov / 8 + SBL) 7 ->
    L5.writable RSEGS M ov 56 -> ((sp - 128) + 128 <= ov \/ ov + 56 <= (sp - 128)) ->
    L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1 -> L5KA.zeros_at M ((ov + 48) / 8 + SBL) 1 ->
    (ov + 56 <= F \/ F + 128 <= ov) -> (ov + 56 <= fl \/ fl + 1 <= ov) -> (ov / 8 + SBL + 7 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= ov / 8 + SBL) ->
    L5.u64_at RSEGS M (ov + 24) eb -> 4096 <= eb <= 140737488355328 -> L5.u64_at RSEGS M (ov + 32) ed ->
    4120 <= ed <= 140737488355328 -> ed mod 8 = 0 -> 24 <= ed - eb <= 100000 -> L5.writable RSEGS M (ed - 8) 8 ->
    (2147446784 + 17592186048512 <= ed - 8 \/ (ed - 8) + 8 <= 2147446784) -> L5KA.zeros_at M ((ed - 8) / 8 + SBL) 1 ->
    ((ed - 8) + 8 <= (sp - 128) \/ (sp - 128) + 128 <= (ed - 8)) -> ((ed - 8) + 8 <= ov \/ ov + 56 <= (ed - 8)) ->
    ((ed - 8) + 8 <= F \/ F + 128 <= (ed - 8)) -> ((ed - 8) + 8 <= fl \/ fl + 1 <= (ed - 8)) -> ((ed - 8) / 8 + SBL + 1 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= (ed - 8) / 8 + SBL) ->
    L5.u64_at RSEGS M (ed - 8) cn ->
    PEAEKN.owns PEAEKN.SV13 sp R0 M -> getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ PMAUK.Wret F fl 1 i -> ~ (ed - 8 <= i < ed - 8 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R SHRA M) (mst fx' R' r M')
      /\ L5.u64_at RSEGS M' (ed - 8) ((cn + 1) mod 2 ^ 64) /\ L5.u8_at RSEGS M' fl 0 /\ regs_preserved R0 R'.

Definition runX (MKRA : Z) : Prop :=
  forall (fx : FPState) (R R2 R0 : bvmap 5 word) (M : word -> option byte) (sp ov oec F fl r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    lregs R sp F ov oec -> regs_preserved R R2 -> PEAEKN.sfacts 128 sp M -> PEAEKN.ffacts 128 sp F fl M false ->
    4096 <= ov <= 140737488355272 -> ov mod 8 = 0 ->
    (ov + 56 <= F \/ F + 128 <= ov) -> (ov + 56 <= fl \/ fl + 1 <= ov) -> (ov / 8 + SBL + 7 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= ov / 8 + SBL) ->
    PEAEKN.owns PEAEKN.SV13 sp R0 M -> getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ PMAUK.Wret F fl 1 i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R2 MKRA M) (mst fx' R' r M')
      /\ L5.u8_at RSEGS M' fl 0 /\ regs_preserved R0 R'.

Ltac gks KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEAENDP1.aligned; assumption | unfold PEAENDP2.aligned; assumption | apply wid | apply wrng | L5SAR.greg | L5SAR.gmem | lia]).
Ltac greg1 KS :=
  first [ assumption
        | lazymatch goal with |- getr ?R1 (reg ?n) = _ =>
            first [ lazymatch goal with H : getr R1 (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end
                  | rewrite (KS n) by inl; lazymatch goal with H : getr _ (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end ] end ].

Ltac midV R sp ov oec osk eb ed cn d ln F fl n ed2 dd r R0 :=
  constr:(fun j : nat => match j with 2%nat => sp | 10%nat => ov | 12%nat => oec | 38%nat => eb | 39%nat => ed | 41%nat => osk | 42%nat => cn | 43%nat => d | 46%nat => ln
     | 47%nat => F | 48%nat => fl | 50%nat => n | 51%nat => ed2 | 52%nat => dd | 64%nat => r
     | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9)) | 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19))
     | 69%nat => bv_unsigned (getr R0 (reg 20)) | 70%nat => bv_unsigned (getr R0 (reg 21)) | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23))
     | 73%nat => bv_unsigned (getr R0 (reg 24)) | 74%nat => bv_unsigned (getr R0 (reg 25)) | 75%nat => bv_unsigned (getr R0 (reg 26)) | 76%nat => bv_unsigned (getr R0 (reg 27))
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end).

Ltac runA_tac CONC :=
  intros fx R M sp Hsp G2 (K0 & K1 & K2 & K3 & K4 & K5);
  let P := fresh "P" in pose proof (CONC fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|]; split; [exact FRZ1|]; split; [exact MS1|];
  decompose [and] P; split; [gks KS|]; unfold PEAEKN.owns, PEAEKN.SV13; repeat split; first [greg1 KS | L5SAR.gmem].
Lemma u_runA_a : runA 0xaae90 0xaaf04. Proof. runA_tac PEAENDP1.aqNaA_conc. Qed.
Lemma u_runA_o : runA 0xabb0c 0xabb80. Proof. runA_tac PEAENDP2.aqNoA_conc. Qed.

Ltac runDi_tac CONC :=
  intros fx R M sp ov oec osk F fl eb ed d Hsp Hov Hoec Hosk HF Hfl Heb Hed Hd G2 G8 G9 G10 G19 G21 G25 (K0 & K1 & K2 & K3 & K4 & K5) FF0 DF;
  unfold PEAEKN.ffacts in FF0; decompose [and] FF0; unfold dfacts in DF; decompose [and] DF;
  let V := midV R sp ov oec osk eb ed 0 d 0 F fl 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2 N3 N4 N5; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia| clear - N4; lia| clear - N5; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs, dpost; repeat split; first [greg1 KS | assumption].
Lemma u_runDi_a1 : runDi 0xaae90 0xaaf04 83002 93 1 0xab040. Proof. runDi_tac PEAENDP1.aqNaDi1_conc. Qed.
Lemma u_runDi_a3 : runDi 0xaae90 0xaaf04 83002 93 3 0xab040. Proof. runDi_tac PEAENDP1.aqNaDi3_conc. Qed.
Lemma u_runDi_o1 : runDi 0xabb0c 0xabb80 75706 125 1 0xabcbc. Proof. runDi_tac PEAENDP2.aqNoDi1_conc. Qed.
Lemma u_runDi_o3 : runDi 0xabb0c 0xabb80 75706 125 3 0xabcbc. Proof. runDi_tac PEAENDP2.aqNoDi3_conc. Qed.

Ltac runDc_tac CONC :=
  intros fx R M sp ov oec osk F fl eb ed d ln cn dd Hsp Hov Hoec Hosk HF Hfl Heb Hed Hd Hln Hcn Hdd G2 G8 G9 G10 G19 G21 G25 (K0 & K1 & K2 & K3 & K4 & K5) FF0 DF UL LN UC REL;
  unfold PEAEKN.ffacts in FF0; decompose [and] FF0; unfold dfacts in DF; decompose [and] DF; cbn [crel] in REL; decompose [and] REL; try match goal with H : cn = _ |- _ => rewrite H in UC end;
  let V := midV R sp ov oec osk eb ed cn d ln F fl 0 0 dd 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2 N3 N4; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia| clear - N4; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs, dpost; repeat split; first [greg1 KS | assumption].
Lemma u_runDc_a00 : runDc 0xaae90 0xaaf04 83002 0 0 9 0xab108. Proof. runDc_tac PEAENDP1.aqNaDlt0_conc. Qed.
Lemma u_runDc_a01 : runDc 0xaae90 0xaaf04 83002 0 1 8 0xab108. Proof. runDc_tac PEAENDP1.aqNaDgt0_conc. Qed.
Lemma u_runDc_a02 : runDc 0xaae90 0xaaf04 83002 0 2 8 0xab108. Proof. runDc_tac PEAENDP1.aqNaDgth0_conc. Qed.
Lemma u_runDc_a20 : runDc 0xaae90 0xaaf04 83002 2 0 9 0xab108. Proof. runDc_tac PEAENDP1.aqNaDlt2_conc. Qed.
Lemma u_runDc_a21 : runDc 0xaae90 0xaaf04 83002 2 1 8 0xab108. Proof. runDc_tac PEAENDP1.aqNaDgt2_conc. Qed.
Lemma u_runDc_a22 : runDc 0xaae90 0xaaf04 83002 2 2 8 0xab108. Proof. runDc_tac PEAENDP1.aqNaDgth2_conc. Qed.
Lemma u_runDc_o00 : runDc 0xabb0c 0xabb80 75706 0 0 9 0xabd84. Proof. runDc_tac PEAENDP2.aqNoDlt0_conc. Qed.
Lemma u_runDc_o01 : runDc 0xabb0c 0xabb80 75706 0 1 8 0xabd84. Proof. runDc_tac PEAENDP2.aqNoDgt0_conc. Qed.
Lemma u_runDc_o02 : runDc 0xabb0c 0xabb80 75706 0 2 8 0xabd84. Proof. runDc_tac PEAENDP2.aqNoDgth0_conc. Qed.
Lemma u_runDc_o20 : runDc 0xabb0c 0xabb80 75706 2 0 9 0xabd84. Proof. runDc_tac PEAENDP2.aqNoDlt2_conc. Qed.
Lemma u_runDc_o21 : runDc 0xabb0c 0xabb80 75706 2 1 8 0xabd84. Proof. runDc_tac PEAENDP2.aqNoDgt2_conc. Qed.
Lemma u_runDc_o22 : runDc 0xabb0c 0xabb80 75706 2 2 8 0xabd84. Proof. runDc_tac PEAENDP2.aqNoDgth2_conc. Qed.

Ltac runDeq_tac CONC :=
  intros fx R M sp ov oec osk F fl eb ed d ln Hsp Hov Hoec Hosk HF Hfl Heb Hed Hd Hln G2 G8 G9 G10 G19 G21 G25 (K0 & K1 & K2 & K3 & K4 & K5) FF0 DF UL LN UC;
  unfold PEAEKN.ffacts in FF0; decompose [and] FF0; unfold dfacts in DF; decompose [and] DF;
  let V := midV R sp ov oec osk eb ed 0 d ln F fl 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2 N3 N4; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia| clear - N4; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs, dpost; repeat split; first [greg1 KS | assumption].
Lemma u_runDeq_a0 : runDeq 0xaae90 0xaaf04 83002 0 0xab040. Proof. runDeq_tac PEAENDP1.aqNaDeq0_conc. Qed.
Lemma u_runDeq_a2 : runDeq 0xaae90 0xaaf04 83002 2 0xab040. Proof. runDeq_tac PEAENDP1.aqNaDeq2_conc. Qed.
Lemma u_runDeq_o0 : runDeq 0xabb0c 0xabb80 75706 0 0xabcbc. Proof. runDeq_tac PEAENDP2.aqNoDeq0_conc. Qed.
Lemma u_runDeq_o2 : runDeq 0xabb0c 0xabb80 75706 2 0xabcbc. Proof. runDeq_tac PEAENDP2.aqNoDeq2_conc. Qed.

Lemma regs_end (R R0 R3 : bvmap 5 word) (sp : Z) :
  (forall j, In j CSK -> getr R3 (reg j) = getr R (reg j)) -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
  getr R0 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 2) = Z_to_bv 64 sp ->
  getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R3 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  getr R3 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) -> getr R3 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 23))) ->
  getr R3 (reg 24) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 24))) -> getr R3 (reg 25) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 25))) ->
  getr R3 (reg 26) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 26))) -> getr R3 (reg 27) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 27))) -> regs_preserved R0 R3.
Proof.
  intros KS3 QCS Rsp T2 T8 T9 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27. apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
  repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8; apply Z_to_bv_bv_unsigned | rewrite T9; apply Z_to_bv_bv_unsigned | rewrite T18; apply Z_to_bv_bv_unsigned
                                          | rewrite T19; apply Z_to_bv_bv_unsigned | rewrite T20; apply Z_to_bv_bv_unsigned | rewrite T21; apply Z_to_bv_bv_unsigned
                                          | rewrite T22; apply Z_to_bv_bv_unsigned | rewrite T23; apply Z_to_bv_bv_unsigned | rewrite T24; apply Z_to_bv_bv_unsigned
                                          | rewrite T25; apply Z_to_bv_bv_unsigned | rewrite T26; apply Z_to_bv_bv_unsigned | rewrite T27; apply Z_to_bv_bv_unsigned
                                          | rewrite (KS3 _) by inl; apply QCS; inl ] |]). destruct Hj.
Qed.

Lemma getr_upd_other10 (R : bvmap 5 word) (w : word) (j : nat) : j <> 10%nat -> (j < 32)%nat -> getr (regupd R 10%bv w) (reg j) = getr R (reg j).
Proof.
  intros Hj Hl. apply getr_other. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
  rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (10%bv : bv 5)) with 10 in E. rewrite Z.mod_small in E by lia. lia.
Qed.
Lemma getr_upd_other11 (R : bvmap 5 word) (w : word) (j : nat) : j <> 11%nat -> (j < 32)%nat -> getr (regupd R 11%bv w) (reg j) = getr R (reg j).
Proof.
  intros Hj Hl. apply getr_other. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
  rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (11%bv : bv 5)) with 11 in E. rewrite Z.mod_small in E by lia. lia.
Qed.

Ltac runPQ_tac CONCP CONCQ SRAIPC Wsr Fsr Dsr Wml Fml Dml :=
  intros fx R M sp ov oec F fl eb ed m Hsp Hov Hoec HF Hfl Heb Hed LR (K0 & K1 & K2 & K3 & K4 & K5) IMG FF0 MF Hedm Hm;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27);
  unfold PEAEKN.ffacts in FF0; decompose [and] FF0; unfold mfacts in MF; decompose [and] MF;

  let V := midV R sp ov oec 0 eb ed 0 0 0 F fl 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONCP fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & _ & AGW & _ & MS1 & KS & A10 & A11 & A12 & A13);
  let EM := fresh "EM" in assert (EM : M1 = M) by (apply functional_extensionality; intros a; apply AGW); rewrite EM in MS1; clear AGW EM;

  let MSR := fresh "MSR" in
  pose proof (PMARS1.srai_to fx1 R1 M SRAIPC Wsr _ _ _ Fsr eq_refl Dsr eq_refl ltac:(lia) ltac:(lia)) as MSR;
  let R1t := fresh "R1t" in set (R1t := regupd R1 10%bv (v_srai (getr R1 10%bv) (bv_unsigned (3%bv : bv 6)))) in MSR;
  let T10t := fresh "T10t" in
  assert (T10t : getr R1t (reg 10) = Z_to_bv 64 (24 * (m + 1) / 8))
    by (unfold R1t; rewrite <- L5K.rl10; rewrite (getr_same R1 10%bv _ ltac:(intros X; discriminate X)); rewrite L5K.rl10, A10; change (bv_unsigned (3%bv : bv 6)) with 3;
        replace (-1 * eb + ed) with (24 * (m + 1)) by (clear - Hedm; lia); rewrite PNAEK.v_srai3_small by (clear - Hm; lia); reflexivity);
  let TOt := fresh "TOt" in
  assert (TOt : forall j, j <> 10%nat -> (j < 32)%nat -> getr R1t (reg j) = getr R1 (reg j)) by (intros j Hj Hl; unfold R1t; apply getr_upd_other10; [exact Hj| exact Hl]);

  let MSM := fresh "MSM" in
  pose proof (PNAEK.mul_to fx1 R1t M (SRAIPC + 4) Wml _ _ _ Fml eq_refl Dml eq_refl ltac:(lia) ltac:(lia)) as MSM;
  let R1m := fresh "R1m" in set (R1m := regupd R1t 11%bv (v_mul (getr R1t 10%bv) (getr R1t 12%bv))) in MSM;
  let T11 := fresh "T11" in
  assert (T11 : getr R1m (reg 11) = Z_to_bv 64 (m + 1))
    by (unfold R1m; rewrite <- L5K.rl11; rewrite (getr_same R1t 11%bv _ ltac:(intros X; discriminate X)); rewrite L5K.rl10, T10t; rewrite L5K.rl12, (TOt 12%nat) by (clear; lia); rewrite A12;
        apply v_mul_magic24; clear - Hm; lia);
  let TOm := fresh "TOm" in
  assert (TOm : forall j, j <> 11%nat -> j <> 10%nat -> (j < 32)%nat -> getr R1m (reg j) = getr R1 (reg j))
    by (intros j Hj Hj' Hl; unfold R1m; rewrite getr_upd_other11; [apply TOt; [exact Hj'| exact Hl]| exact Hj| exact Hl]);

  let V2 := midV R1m sp ov oec 0 eb ed 0 0 0 F fl (m + 1) 0 0 0 R1m in
  let Q := fresh "Q" in pose proof (CONCQ fx1 R1m M V2) as Q; cbn beta iota in Q;
  L5SAR.feed Q ltac:(first [ exact T11
                           | rewrite (TOm _) by (clear; lia); first [ rewrite (KS _) by inl; assumption | assumption | rewrite A13; reflexivity ]
                           | assumption | unfold PEAENDP1.aligned; assumption | unfold PEAENDP2.aligned; assumption | apply wid | apply wrng
                           | L5SAR.gmem | lia ]);
  let KSq := fresh "KSq" in
  destruct Q as (fx2 & R2 & M2 & MG2 & _ & FRZ2 & MS2 & KSq & B1 & B10 & U32);
  exists fx2, R2, M2; split; [exact MG2|];
  split; [intros i Hi N; apply (FRZ2 i Hi); clear - N; lia|];
  split; [eapply msteps_trans; [exact MS1|]; eapply msteps_trans; [exact MSR|]; eapply msteps_trans; [exact MSM| exact MS2]|];
  split; [intros j Hj; rewrite (KSq j) by (cbn in Hj; decompose [or] Hj; try contradiction; subst; inl); rewrite (TOm j) by (cbn in Hj; decompose [or] Hj; try contradiction; subst; clear; lia);
          apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|];
  split; [exact B1|]; split; [exact B10|]; split; [rewrite (KSq 11%nat) by inl; exact T11|];
  split; [| replace (ed - 24) with (eb + 24 * (m + 1) - 24) by (clear - Hedm; lia); first [exact U32 | replace (eb + 24 * (m + 1) - 24) with (ed - 24) by (clear - Hedm; lia); exact U32]];
  unfold lregs; repeat split; (rewrite (KSq _) by inl; rewrite (TOm _) by (clear; lia); first [rewrite (KS _) by inl; assumption | assumption]).
Lemma u_runPQ_a : runPQ 0xab040 0xab07c. Proof. runPQ_tac PEAENDP1.aqNaP_conc PEAENDP1.aqNaQ_conc 0xab068 W_ab018 F_ab018 D_ab018 W_ab01c F_ab01c D_ab01c. Qed.
Lemma u_runPQ_o : runPQ 0xabcbc 0xabcf8. Proof. runPQ_tac PEAENDP2.aqNoP_conc PEAENDP2.aqNoQ_conc 0xabce4 W_abc94 F_abc94 D_abc94 W_abc98 F_abc98 D_abc98. Qed.

Ltac fin_tac RETPC Wr Fr Dr fx1 R1 M1 T1 Hr1 Hr2 MS1 :=
  let MSR := fresh "MSR" in
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 RETPC Wr _ Fr eq_refl Dr T1 ltac:(clear - Hr1; lia) Hr2) as MSR;
  exists fx1, R1, M1.
Ltac runR0_tac CONC RETPC Wr Fr Dr :=
  intros fx R R0 M sp ov oec F fl eb r Hsp Hov Hoec HF Hfl Heb LR (K0 & K1 & K2 & K3 & K4 & K5) FF0 O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 OF1 OF2 OF3 U24 U32 EB OWN0 Hra R0sp RA QCS;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27); unfold PEAEKN.ffacts in FF0; decompose [and] FF0;
  unfold PEAEKN.owns, PEAEKN.SV13 in OWN0; destruct OWN0 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104 & _); pose proof RA as (Hr1 & Hr2);
  rewrite Hra, L5.unsigned_lit in S8 by (clear - Hr1; lia);
  let V := midV R sp ov oec 0 eb eb 0 0 0 F fl 0 0 0 r R0 in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & FL0 & _);
  fin_tac RETPC Wr Fr Dr fx1 R1 M1 T1 Hr1 Hr2 MS1;
  split; [exact MG1|];
  split; [intros i Hi N; unfold PMAUK.Wret in N; change (ff_bytes 1) with 128 in N; change (128 / 8) with 16 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N; lia| clear - N; lia| clear - N; lia]|];
  split; [eapply msteps_trans; [exact MS1| eassumption]|]; split; [exact FL0|];
  apply (regs_end R R0 R1 sp); [gks KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23| exact T24| exact T25| exact T26| exact T27].
Lemma u_runR0_a : runR0 0xab07c. Proof. runR0_tac PEAENDP1.aqNaR0_conc 0xab1d8 W_ab188 F_ab188 D_ab188. Qed.
Lemma u_runR0_o : runR0 0xabcf8. Proof. runR0_tac PEAENDP2.aqNoR0_conc 0xabe54 W_abe04 F_abe04 D_abe04. Qed.

Ltac runR1_tac CONC CONCw RETPC Wr Fr Dr :=
  intros fx R R0 M sp ov oec F fl eb ed cn r Hsp Hov Hoec HF Hfl Heb Hed Hcn LR (K0 & K1 & K2 & K3 & K4 & K5) FF0 O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 OF1 OF2 OF3 U24 EB U32 ED1 ED8 LEN WR8 NSH ZC DJS DJO DJF DJL DJSH UC OWN0 Hra R0sp RA QCS;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27); unfold PEAEKN.ffacts in FF0; decompose [and] FF0;
  unfold PEAEKN.owns, PEAEKN.SV13 in OWN0; destruct OWN0 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104 & _); pose proof RA as (Hr1 & Hr2);
  rewrite Hra, L5.unsigned_lit in S8 by (clear - Hr1; lia);
  destruct (Z.eq_dec cn 18446744073709551615) as [CW|CNW];
  [ rewrite CW in UC;
    let V := midV R sp ov oec 0 eb 0 cn 0 0 F fl 0 ed 0 r R0 in
    let P := fresh "P" in pose proof (CONCw fx R M V) as P; cbn beta iota in P; feedP P;
    let KS := fresh "KS" in
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & FL0 & P);
    fin_tac RETPC Wr Fr Dr fx1 R1 M1 T1 Hr1 Hr2 MS1;
    split; [exact MG1|];
    split; [intros i Hi N N2; unfold PMAUK.Wret in N; change (ff_bytes 1) with 128 in N; change (128 / 8) with 16 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N2; lia| clear - N; lia| clear - N; lia| clear - N; lia]|];
    split; [eapply msteps_trans; [exact MS1| eassumption]|];
    split; [rewrite CW; change ((18446744073709551615 + 1) mod 2 ^ 64) with 0; decompose [and] P; L5SAR.gmem|]; split; [exact FL0|];
    apply (regs_end R R0 R1 sp); [gks KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23| exact T24| exact T25| exact T26| exact T27]
  | let V := midV R sp ov oec 0 eb 0 cn 0 0 F fl 0 ed 0 r R0 in
    let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
    let KS := fresh "KS" in
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & FL0 & P);
    fin_tac RETPC Wr Fr Dr fx1 R1 M1 T1 Hr1 Hr2 MS1;
    split; [exact MG1|];
    split; [intros i Hi N N2; unfold PMAUK.Wret in N; change (ff_bytes 1) with 128 in N; change (128 / 8) with 16 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N2; lia| clear - N; lia| clear - N; lia| clear - N; lia]|];
    split; [eapply msteps_trans; [exact MS1| eassumption]|];
    split; [rewrite Z.mod_small by (clear - Hcn CNW; lia); decompose [and] P; L5SAR.gmem|]; split; [exact FL0|];
    apply (regs_end R R0 R1 sp); [gks KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23| exact T24| exact T25| exact T26| exact T27] ].
Lemma u_runR1_a : runR1 0xab07c. Proof. runR1_tac PEAENDP1.aqNaR1_conc PEAENDP1.aqNaR1w_conc 0xab1d8 W_ab188 F_ab188 D_ab188. Qed.
Lemma u_runR1_o : runR1 0xabcf8. Proof. runR1_tac PEAENDP2.aqNoR1_conc PEAENDP2.aqNoR1w_conc 0xabe54 W_abe04 F_abe04 D_abe04. Qed.

Ltac runX_tac CONC RETPC Wr Fr Dr :=
  intros fx R R2 R0 M sp ov oec F fl r Hsp Hov Hoec HF Hfl LR RP2 (K0 & K1 & K2 & K3 & K4 & K5) FF0 O1 O2 OF1 OF2 OF3 OWN0 Hra R0sp RA QCS;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27); unfold PEAEKN.ffacts in FF0; decompose [and] FF0;
  unfold PEAEKN.owns, PEAEKN.SV13 in OWN0; destruct OWN0 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104 & _); pose proof RA as (Hr1 & Hr2);
  rewrite Hra, L5.unsigned_lit in S8 by (clear - Hr1; lia);

  let KP := fresh "KP" in pose proof (fun k (Hk : In k L5SAR.cs_all) => L5SAR.cs_of_preserved R R2 k RP2 Hk) as KP;
  let V := midV R2 sp ov oec 0 0 0 0 0 0 F fl 0 0 0 r R0 in
  let P := fresh "P" in pose proof (CONC fx R2 M V) as P; cbn beta iota in P;
  L5SAR.feed P ltac:(first [assumption | rewrite (KP _) by inl; assumption | unfold PEAENDP1.aligned; assumption | unfold PEAENDP2.aligned; assumption | apply wid | apply wrng | L5SAR.greg | L5SAR.gmem | lia]);
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & FL0 & _);
  fin_tac RETPC Wr Fr Dr fx1 R1 M1 T1 Hr1 Hr2 MS1;
  split; [exact MG1|];
  split; [intros i Hi N; unfold PMAUK.Wret in N; change (ff_bytes 1) with 128 in N; change (128 / 8) with 16 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N; lia| clear - N; lia| clear - N; lia]|];
  split; [eapply msteps_trans; [exact MS1| eassumption]|]; split; [exact FL0|];
  apply (regs_end R2 R0 R1 sp); [gks KS| intros j Hj; rewrite (KP j) by (cbn in Hj; decompose [or] Hj; try contradiction; subst; inl); apply QCS; exact Hj| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23| exact T24| exact T25| exact T26| exact T27].
Lemma u_runX_a : runX 0xab108. Proof. runX_tac PEAENDP1.aqNaX_conc 0xab1d8 W_ab188 F_ab188 D_ab188. Qed.
Lemma u_runX_o : runX 0xabd84. Proof. runX_tac PEAENDP2.aqNoX_conc 0xabe54 W_abe04 F_abe04 D_abe04. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma cons_of_ne {A} (l : list A) : l <> [] -> exists x l', l = x :: l'.
Proof. destruct l as [|x l']; [intros N; exfalso; exact (N eq_refl)| intros _; exists x, l'; reflexivity]. Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Hypothesis MKEC : PECSA.make_ec_spec L ar HI.
Hypothesis ESHR : PEAEKAN.ann_shrink_e_spec RSEGS AD L ar HI SHRPC.

Section Slot.

Variables (E0 SMRA PBRA MKRA JE SHRA DSC MK : Z).
Hypothesis RAS : L5.ra_ok PBRA /\ L5.ra_ok MKRA /\ L5.ra_ok SHRA /\ 0 <= SMRA < 2 ^ 64 /\ SMRA mod 2 = 0.
Hypothesis RUNA : runA E0 SMRA.
Hypothesis RDI : forall kd, kd = 1 \/ kd = 3 -> runDi E0 SMRA DSC MK kd PBRA.
Hypothesis RDC : forall kd rel, kd = 0 \/ kd = 2 -> 0 <= rel <= 2 -> runDc E0 SMRA DSC kd rel (if rel =? 0 then 9 else 8) MKRA.
Hypothesis RDEQ : forall kd, kd = 0 \/ kd = 2 -> runDeq E0 SMRA DSC kd JE.
Hypothesis RPQI : runPQ PBRA SHRA.
Hypothesis RPQE : runPQ JE SHRA.
Hypothesis RR0 : runR0 SHRA.
Hypothesis RR1 : runR1 SHRA.
Hypothesis RX : runX MKRA.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z).
Variables (xstk : list pstate) (xpos : Z) (xmore xdone xhalt : bool) (xdepth : Z) (xec : bool) (xestk : list eitem) (xedepth xlo xhi : Z) (xbad : bool).
Variables (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Let X : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad.
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 4.
Hypothesis FRM : PMSPA.ffroomA 4 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 (PMSPA.o_ec AD fb).
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis MP : PECSPA.mp_ence p X.
Hypothesis NBAD : s_bad (e_end X) = false.
Hypothesis HB : PESKA.spa_hb P (s_hi (e_end X)).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (e_end X) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Lemma HFR : 128 = 96 \/ 128 = 128. Proof. right; reflexivity. Qed.
Lemma HSV : PEAEKN.SV13 = PEAEKN.SV9 \/ PEAEKN.SV13 = PEAEKN.SV11 \/ PEAEKN.SV13 = PEAEKN.SV13. Proof. right; right; reflexivity. Qed.
Lemma HNF : 8 * Z.of_nat (length PEAEKN.SV13) <= 128. Proof. cbn. lia. Qed.
Lemma MPE : PECSPA.mp_enc p X. Proof. exact (proj1 MP). Qed.
Lemma CSK3 : In 3%nat CSK. Proof. inl. Qed.
Lemma CSK4 : In 4%nat CSK. Proof. inl. Qed.
Lemma CSKall j : In j CSK -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.

#[local] Abbreviation K_vis_entry := (PEAEKN.vis_entry L ar C HI LY HIok 128 PEAEKN.SV13 HFR R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK SP32 A10).
#[local] Abbreviation K_start := (PEAEKN.start L ar C HI P LY HIok 128 PEAEKN.SV13 HFR HSV fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 CPRE HNF).
#[local] Abbreviation K_vis_facts := (PEAEKN.vis_facts L ar C HI P LY HIok 128 PEAEKN.SV13 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 HNF).
#[local] Abbreviation K_vis_top := (PEAEKN.vis_facts_top L ar C HI P LY HIok 128 PEAEKN.SV13 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK HNF).
#[local] Abbreviation K_g_facts := (PEAEKN.g_facts L ar C HI LY HIok 128 PEAEKN.SV13 HSV R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK HNF).
#[local] Abbreviation K_depthw := (PEAEKN.inv_depthw L ar C HI P LY HIok 128 PEAEKN.SV13 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK HNF).
#[local] Abbreviation K_agree := (PEAEKN.inv_agree L ar C HI P LY HIok 128 PEAEKN.SV13 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK HNF).
#[local] Abbreviation K_pb := (PEAEKN.pb_call L ar C HI P LY HIok PO PB 128 PEAEKN.SV13 CSK HFR HSV CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 CPRE CRED HNF).
#[local] Abbreviation K_pop := (PEAEKN.pop_call L ar C HI P LY HIok ESHR 128 PEAEKN.SV13 CSK HFR HSV CSK3 CSK4 R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRS FOK SP32 CPRE INCS HNF).
#[local] Abbreviation INV := (PEAEKN.inv L ar HI P 128 PEAEKN.SV13 R M model LBX FF LK Aw cr sp fb xlo xhi s en k).

Lemma pre_facts : exists e0 rr, xestk = e0 :: rr /\ ei_ok e0 /\ Forall ei_ok rr /\ 1 <= xedepth <= MAX_DEPTH /\ PEC.en_stk en = rev (e0 :: rr) /\ PEC.en_depth en = xedepth /\ xbad = false /\ xlo <= xhi.
Proof.
  destruct MP as ((LOHI & BADX & FA & ED) & ED1). cbn [s_lo s_hi s_bad s_estk s_edepth X] in LOHI, BADX, FA, ED, ED1.
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (_ & _ & _ & _ & _ & Lestk & Ledepth & _). cbn [s_estk s_edepth X] in Lestk, Ledepth.
  destruct (cons_of_ne xestk) as (e0 & rr & HXS); [intros E; pose proof (PESENC.e_end_nil X ltac:(unfold X; cbn [s_estk]; exact E)) as BB; rewrite NBAD in BB; discriminate BB|].
  exists e0, rr. rewrite HXS in FA, Lestk. inversion FA as [|e0' rr' E0OK FArr]. subst e0' rr'.
  split; [exact HXS|]. split; [exact E0OK|]. split; [exact FArr|]. split; [clear - ED ED1; lia|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact BADX| exact LOHI].
Qed.

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI (PM.parser_own s ++ LBX) FF LK Aw sp 20480 (sp - 128) (sp - 8 * Z.of_nat (length PEAEKN.SV13)) sp (PEAEKN.ocell sp (Z.of_nat (length PEAEKN.SV13))) (PEAEKN.owns PEAEKN.SV13 sp R) F fl 1 LK2 M2 model2 cr (PEAEKN.EBX en k).
Hypothesis APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (PEAEKN.EBX en k ++ (PM.parser_own s ++ LBX)) FF sp0 scr0 (a + i)) -> 0 < n ->
    (a + n <= F \/ F + 128 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + 16 <= a) /\ (a + n <= fl \/ fl + 1 <= a).
#[local] Abbreviation K_fro NB XF KT := (PEAEKN.finish_ro L ar C HI P LY HIok 128 NB PEAEKN.SV13 HFR HSV R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS XF KT HNF F fl LK2 M2 model2 G APART).
#[local] Abbreviation K_fbu NB XF KT := (PEAEKN.finish_bump L ar C HI P LY HIok 128 NB PEAEKN.SV13 HFR HSV R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS XF KT HNF F fl LK2 M2 model2 G APART).
#[local] Abbreviation K_mk NB XF KT := (PEAEKN.mkec_finish L ar C HI P LY HIok MKEC 128 NB PEAEKN.SV13 CSK HFR HSV CSK3 CSK4 R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 CPRE INCS MPE XF KT HNF F fl LK2 M2 model2 G APART).

Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH; pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl4 in Rtp;
  pose proof (K_g_facts F fl LK2 M2 model2 G APART) as GF; cbv beta in GF; destruct GF as (GF1 & GF2 & GF3 & _ & GF8 & _ & GL1 & GL2 & _).

Lemma lregs_after R1 R2 : lregs R1 sp F (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) -> (forall j, In j CSK -> getr R1 (reg j) = getr R (reg j)) -> regs_preserved R1 R2 ->
  lregs R2 sp F (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) /\ (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)).
Proof.
  intros (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27) QCS RP. split.
  - unfold lregs. repeat split; first [ rewrite (L5SAR.cs_of_preserved R1 R2 2 RP) by inl; exact G2 | rewrite (L5SAR.cs_of_preserved R1 R2 8 RP) by inl; exact G8
      | rewrite (L5SAR.cs_of_preserved R1 R2 9 RP) by inl; exact G9 | rewrite (L5SAR.cs_of_preserved R1 R2 18 RP) by inl; exact G18 | rewrite (L5SAR.cs_of_preserved R1 R2 19 RP) by inl; exact G19
      | rewrite (L5SAR.cs_of_preserved R1 R2 20 RP) by inl; exact G20 | rewrite (L5SAR.cs_of_preserved R1 R2 21 RP) by inl; exact G21 | rewrite (L5SAR.cs_of_preserved R1 R2 22 RP) by inl; exact G22
      | rewrite (L5SAR.cs_of_preserved R1 R2 23 RP) by inl; exact G23 | rewrite (L5SAR.cs_of_preserved R1 R2 24 RP) by inl; exact G24 | rewrite (L5SAR.cs_of_preserved R1 R2 25 RP) by inl; exact G25
      | rewrite (L5SAR.cs_of_preserved R1 R2 26 RP) by inl; exact G26 | rewrite (L5SAR.cs_of_preserved R1 R2 27 RP) by inl; exact G27 ].
  - intros j Hj. rewrite (L5SAR.cs_of_preserved R1 R2 j RP (CSKall j Hj)). exact (QCS j Hj).
Qed.
Lemma csk_kept (R1 R2 : bvmap 5 word) : (forall j, In j CSK -> getr R2 (reg j) = getr R1 (reg j)) ->
  (forall j, In j CSK -> getr R1 (reg j) = getr R (reg j)) -> forall j, In j CSK -> getr R2 (reg j) = getr R (reg j).
Proof. intros KS3 Q j Hj. rewrite (KS3 j Hj). exact (Q j Hj). Qed.

Lemma vis Mq mdq LKq Awq crq kq a enq e1 rr : INV F Mq mdq LKq Awq crq kq a enq -> PEC.en_stk enq = rev (e1 :: rr) -> ei_ok e1 ->
  let MV := mrestrict (ahid Awq mdq) Mq in let eb := PEC.en_b enq in let ed := eb + 24 * (Z.of_nat (length rr) + 1) in
  PEAEKN.sfacts 128 sp MV /\ PEAEKN.ffacts 128 sp F fl MV false /\ PEAEKN.owns PEAEKN.SV13 sp R MV
  /\ mfacts MV sp (PMSPA.o_v AD fb) F fl eb ed
  /\ L5.u64_at RSEGS MV (PMSPA.o_v AD fb + 8) (PESK.o_sink EE fb) /\ 4096 <= PESK.o_sink EE fb <= 140737488355304 /\ (PESK.o_sink EE fb) mod 8 = 0
  /\ L5.u32_at RSEGS MV (PMSPA.o_v AD fb + 48) (PEC.en_depth enq)
  /\ L5.u32_at RSEGS MV (ed - 24) (ei_kind e1) /\ L5.u64_at RSEGS MV (ed - 16) (ei_len e1) /\ L5.u64_at RSEGS MV (ed - 8) (ei_cnt e1)
  /\ 0 <= eb <= 2 ^ 47 /\ 0 <= Z.of_nat (length rr) <= 4165
  /\ L5A.avis (ahid Awq mdq) F 128 /\ L5A.avis (ahid Awq mdq) (F / 8 + SB) 16 /\ L5A.avis (ahid Awq mdq) (PMSPA.o_v AD fb) 56 /\ L5.img_clear MV 65536 1286144.
Proof.
  intros INVq HSTK E1OK. entry_facts.
  pose proof (K_vis_facts F fl LK2 M2 model2 G APART Mq mdq LKq Awq crq kq a enq INVq) as VF. cbv beta in VF.
  destruct VF as (SF & FFc & OWN & OF & _ & VFf & VSH & _ & QVIS & _).
  pose proof OF as (OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8 & KR & K8 & KO & U24 & U32 & EB & AvF & AvS & AvL & AkF & AkS & AkL & U48).
  pose proof (K_vis_top F fl LK2 M2 model2 G APART Mq mdq LKq Awq crq kq a e1 rr enq INVq HSTK E1OK) as VT. cbv beta in VT.
  destruct VT as ((HLEN & EKP & EB1 & ED2 & ALend & ED3 & WR24 & EB6 & ZC & EDS & OVA & TCv & E1C & _ & BINe & EDC & EBC & EDF & EDSH & EDFL & ZC3 & TK & TL) & EDV).
  rewrite HLEN in U32.
  assert (D8 : forall j, (PMSPA.o_v AD fb + 8 * j) / 8 = PMSPA.o_v AD fb / 8 + j).
  { intros j. pose proof (Z.div_mod (PMSPA.o_v AD fb) 8 ltac:(clear; lia)) as E8. rewrite O8, Z.add_0_r in E8. rewrite E8 at 1.
    replace (8 * (PMSPA.o_v AD fb / 8) + 8 * j) with ((PMSPA.o_v AD fb / 8 + j) * 8) by (clear; lia). apply Z.div_mul. clear; lia. }
  assert (Z48 : L5KA.zeros_at (mrestrict (ahid Awq mdq) Mq) ((PMSPA.o_v AD fb + 48) / 8 + SBL) 1).
  { replace (PMSPA.o_v AD fb + 48) with (PMSPA.o_v AD fb + 8 * 6) by (clear; lia). rewrite D8. intros i Hi. replace (PMSPA.o_v AD fb / 8 + 6 + SBL + i) with (PMSPA.o_v AD fb / 8 + SBL + (6 + i)) by (clear; lia). apply Zov. clear - Hi; lia. }
  pose proof INVq as ((HHq & _) & _ & _ & EAq & _). pose proof EAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ELEN & _).
  assert (ECAP : PEC.ecap (PEC.en_k enq) <= 2048).
  { pose proof EAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EK & _). clear - EK EKP. unfold PEC.ecap. replace (PEC.en_k enq =? 0) with false by (symmetry; apply Z.eqb_neq; lia). change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; lia. }
  destruct (PEAEKN.keepf L ar C HI P LY HIok 128 PEAEKN.SV13 HFR HSV R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS Mq (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 INVq))))))))) as (_ & _ & _ & BASEq & _).
  split; [exact SF|]. split; [exact FFc|]. split; [exact OWN|].
  split. { unfold mfacts. repeat split; first [assumption | clear - OR; lia | clear - EB1 ED2 ED3; lia | clear - AvF O8 GF8; Lia.lia | clear - EDF ALend GF8; Lia.lia]. }
  split; [exact U8|]. split; [exact KR|]. split; [exact K8|]. split; [exact U48|]. split; [exact TK|]. split; [exact TL|]. split; [exact TCv|].
  split; [exact EB|]. split; [rewrite HLEN in ELEN; clear - ELEN ECAP; lia|].
  split; [exact VFf|]. split; [exact VSH|]. split; [exact QVIS|]. apply L5A.img_clear_mrestrict. exact (proj1 BASEq).
Qed.

Lemma d_piece (fx1 fx3 : FPState) R2 R3 (pc3 : Z) M3v :
  INV F M2 model2 LK2 Aw cr k 0 en ->
  msteps RSEGS (mst fx1 R2 SMRA (mrestrict (ahid Aw model2) M2)) (mst fx3 R3 pc3 M3v) -> mem_grows (mrestrict (ahid Aw model2) M2) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 + 8 <= i < sp - 128 + 8 + 8) -> ~ (F <= i < F + 24) -> ~ (F / 8 + SBL <= i < F / 8 + SBL + 12) ->
        ~ (PMSPA.o_v AD fb + 48 <= i < PMSPA.o_v AD fb + 52) -> ~ (sp - 128 + 23 <= i < sp - 128 + 23 + 1) -> M3v (Z_to_bv 64 i) = mrestrict (ahid Aw model2) M2 (Z_to_bv 64 i)) ->
  L5.u32_at RSEGS M3v (PMSPA.o_v AD fb + 48) (xedepth - 1) -> 1 <= xedepth <= MAX_DEPTH ->
  (forall M3 md3, INV F M3 md3 LK2 Aw cr k 0 (PEC.ENC (PEC.en_b en) (PEC.en_k en) (PEC.en_stk en) (xedepth - 1)) -> mrestrict (ahid Aw md3) M3 = M3v ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx3) R3 pc3 M3 md3) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx1) R2 SMRA M2 model2) K.
Proof.
  intros INV2 MS3 MG3 FRZ3 U48 HED KX. entry_facts.
  pose proof (K_vis_facts F fl LK2 M2 model2 G APART M2 model2 LK2 Aw cr k 0 en INV2) as VF. cbv beta in VF. destruct VF as (_ & _ & _ & OF & _ & _ & _ & _ & QVIS & _). pose proof OF as (OR & _).
  pose proof INV2 as ((HH2 & AM2 & _) & _). pose proof FOK as ((rs & Hfb) & Fal).
  set (ov := PMSPA.o_v AD fb) in *. assert (Eov : ov = fb + 496) by reflexivity.
  assert (O8 : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by (clear; lia); apply (PEAEKN.FB8 PEAEKN.SV13 FF fb FOK)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 ov 56 sp 20480 HH2 (PMKA.aobj_of_aobjA _ ov 56 (PMAUAR.aobjA_push FF ov 56 _ (PEAEKN.AOF PEAEKN.SV13 FF fb FOK ov 56 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))) O8) ltac:(clear; lia) ltac:(reflexivity)) as ((OI & _) & _).
  set (W3 := fun a => (sp - 128 + 8 <= a < sp - 128 + 8 + 8) \/ (F <= a < F + 24) \/ (F / 8 + SBL <= a < F / 8 + SBL + 12) \/ (ov + 48 <= a < ov + 52) \/ (sp - 128 + 23 <= a < sp - 128 + 23 + 1)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 fx1 fx3 R2 SMRA R3 pc3 M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; exact X'| intros X'; apply Hn; right; left; exact X'| intros X'; apply Hn; right; right; left; exact X'
                                | intros X'; apply Hn; right; right; right; left; exact X'| intros X'; apply Hn; right; right; right; right; exact X']. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|[X'|[X'|X']]]].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar _ _ 0 0 F 1 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 1 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128. unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - X' GF8. Lia.lia.
      + unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. split; [clear - X' Eov; lia| intros Y; clear - X' Y Eov; lia].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT; lia| intros Y; clear - Y; lia].
    - destruct Wa as [X'|[X'|[X'|[X'|X']]]]; unfold SB; clear - X' GF3 SLO SPT OI; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  apply (KX M3 md3); [| rewrite HID3; exact VIS3].
  apply (K_depthw F fl LK2 M2 model2 G APART M2 M3 W3 model2 md3 LK2 cr Aw k 0 en (xedepth - 1) INV2 HH3 AM3 MRT3 MGM3); [| exact FR3| | clear - HED; unfold MAX_DEPTH in *; lia].
  - intros a [X'|[X'|[X'|[X'|X']]]]; [left; split; [clear - X'; lia| unfold PEAEKN.ocell, PEAEKN.SV13; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - X'; lia]
                                   | right; left; clear - X'; lia | right; right; left; unfold SB; clear - X'; lia | right; right; right; exact X'
                                   | left; split; [clear - X'; lia| unfold PEAEKN.ocell, PEAEKN.SV13; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - X'; lia]].
  - assert (QVIS3 : L5A.avis (ahid Aw md3) ov 56) by (rewrite HID3; exact QVIS).
    apply (proj1 (L5A.u32_at_vis (ahid Aw md3) M3 (ov + 48) _ (L5A.avis_sub _ ov 56 (ov + 48) 4 QVIS3 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia))).
    rewrite HID3, VIS3. exact U48.
Qed.

Lemma stepR (NBv : Z) (rr : list eitem) (fx5 : FPState) R5 M5 md5 LK5 Aw5 cr5 k5 :
  INV F M5 md5 LK5 Aw5 cr5 k5 NBv (PEC.ENC (PEC.en_b en) (PEC.en_k en) (rev rr) (xedepth - 1)) -> Forall ei_ok rr -> 0 <= NBv <= 1 -> 4096 <= PEC.en_b en ->
  e_end X = ST xstk xpos xmore xdone xhalt xdepth xec (PESENC.ebump rr) (xedepth - 1) (xlo + NBv) (xhi + NBv) xbad ->
  lregs R5 sp F (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) -> (forall j, In j CSK -> getr R5 (reg j) = getr R (reg j)) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx5) R5 SHRA M5 md5) K.
Proof.
  intros INV5 FArr HNB EB4 HXF LR5 QCS5. entry_facts.
  set (en2 := PEC.ENC (PEC.en_b en) (PEC.en_k en) (rev rr) (xedepth - 1)) in *.
  pose proof (K_vis_facts F fl LK2 M2 model2 G APART M5 md5 LK5 Aw5 cr5 k5 NBv en2 INV5) as VF. cbv beta in VF.
  destruct VF as (SF & FFc & OWN & OF & _ & VFf & VSH & _ & QVIS & _).
  pose proof OF as (OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8 & KR & K8 & KO & U24 & U32 & EB & AvF & AvS & AvL & _).
  assert (D8 : forall j, (PMSPA.o_v AD fb + 8 * j) / 8 = PMSPA.o_v AD fb / 8 + j).
  { intros j. pose proof (Z.div_mod (PMSPA.o_v AD fb) 8 ltac:(clear; lia)) as E8. rewrite O8, Z.add_0_r in E8. rewrite E8 at 1.
    replace (8 * (PMSPA.o_v AD fb / 8) + 8 * j) with ((PMSPA.o_v AD fb / 8 + j) * 8) by (clear; lia). apply Z.div_mul. clear; lia. }
  assert (Z48 : L5KA.zeros_at (mrestrict (ahid Aw5 md5) M5) ((PMSPA.o_v AD fb + 48) / 8 + SBL) 1).
  { replace (PMSPA.o_v AD fb + 48) with (PMSPA.o_v AD fb + 8 * 6) by (clear; lia). rewrite D8. intros i Hi. replace (PMSPA.o_v AD fb / 8 + 6 + SBL + i) with (PMSPA.o_v AD fb / 8 + SBL + (6 + i)) by (clear; lia). apply Zov. clear - Hi; lia. }
  assert (OSH : PMSPA.o_v AD fb / 8 + SBL + 7 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= PMSPA.o_v AD fb / 8 + SBL) by (clear - AvF O8 GF8; Lia.lia).
  cbn [en2 PEC.en_b PEC.en_stk] in U24, U32, EB.
  destruct rr as [|e2 rr'].
  - cbn [rev length Z.of_nat Z.mul] in U32. rewrite Z.add_0_r in U32.
    destruct (RR0 fx5 R5 R (mrestrict (ahid Aw5 md5) M5) sp (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) F fl (PEC.en_b en) r ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia) ltac:(unfold PMSPA.o_ec; cbn [pa_off_ec PeCLayoutA.CADDR_A]; clear - OR; unfold PMSPA.o_v in OR; cbn [pa_off_v PeCLayoutA.CADDR_A] in OR; lia)
               ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia) ltac:(clear - EB; lia)
               LR5 SF FFc OR O8 OBIG Zov OWR ODJ Z8 Z24 Z32 Z48 AvF AvL OSH U24 U32 ltac:(clear - EB EB4; lia) OWN Rra Rsp RAok QCS5)
      as (fx6 & R6 & M6v & MG6 & FRZ6 & MS6 & FL6 & RP6).
    exact (K_fro NBv (e_end X) KONT SHRA fx5 R5 M5 md5 LK5 Aw5 cr5 k5 fx6 R6 M6v en2 (xedepth - 1) INV5 eq_refl eq_refl HXF MS6 MG6 FRZ6 FL6 RP6).
  - inversion FArr as [|e2' rr'' E2OK FArr']. subst e2' rr''.
    pose proof (vis M5 md5 LK5 Aw5 cr5 k5 NBv en2 e2 rr' INV5 eq_refl E2OK) as VT. cbv beta in VT. cbn [en2 PEC.en_b PEC.en_depth] in VT.
    destruct VT as (_ & _ & _ & MF & _ & _ & _ & _ & _ & _ & TC & _ & MR & _).
    set (ed := PEC.en_b en + 24 * (Z.of_nat (length rr') + 1)) in *.
    pose proof MF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U32' & _ & ED2 & ALend & _ & LEN & WR24 & EDBIG & ZC3 & EDS & EDO & EDF & EDL & EDSH & _).
    pose proof E2OK as (_ & E2C & _). unfold UbjRef.TWO64 in E2C.
    assert (ZC : L5KA.zeros_at (mrestrict (ahid Aw5 md5) M5) ((ed - 8) / 8 + SBL) 1).
    { intros i Hi. replace ((ed - 8) / 8 + SBL + i) with ((ed - 24) / 8 + SBL + (2 + i)) by (clear - ALend Hi; Lia.lia). apply ZC3. clear - Hi; lia. }
    destruct (RR1 fx5 R5 R (mrestrict (ahid Aw5 md5) M5) sp (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) F fl (PEC.en_b en) ed (ei_cnt e2) r ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia)
               ltac:(unfold PMSPA.o_ec; cbn [pa_off_ec PeCLayoutA.CADDR_A]; clear - OR; unfold PMSPA.o_v in OR; cbn [pa_off_v PeCLayoutA.CADDR_A] in OR; lia)
               ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia) ltac:(clear - EB; lia) ltac:(clear - ED2 LEN EB; lia) E2C
               LR5 SF FFc OR O8 OBIG Zov OWR ODJ Z8 Z24 Z32 Z48 AvF AvL OSH U24 ltac:(clear - EB4 LEN ED2; lia) U32'
               ltac:(clear - ED2 LEN EB; lia) ALend LEN ltac:(eapply L5.writable_sub; [exact WR24| clear; lia| clear; lia]) ltac:(clear - EDBIG; lia) ZC
               ltac:(clear - EDS; lia) ltac:(clear - EDO; lia) ltac:(clear - EDF; lia) ltac:(clear - EDL; lia) ltac:(clear - EDF ALend GF8; Lia.lia) TC OWN Rra Rsp RAok QCS5)
      as (fx6 & R6 & M6v & MG6 & FRZ6 & MS6 & CC6 & FL6 & RP6).
    exact (K_fbu NBv (e_end X) KONT SHRA fx5 R5 M5 md5 LK5 Aw5 cr5 k5 fx6 R6 M6v e2 rr' en2 (xedepth - 1) INV5 eq_refl E2OK eq_refl HXF MS6 MG6 FRZ6 CC6 FL6 RP6).
Qed.

Lemma stepPQ (JPC : Z) (RPQ : runPQ JPC SHRA) (NBv : Z) (e0 : eitem) (rr : list eitem) (fx4 : FPState) R4 M4 md4 LK4 Aw4 cr4 k4 :
  INV F M4 md4 LK4 Aw4 cr4 k4 NBv (PEC.ENC (PEC.en_b en) (PEC.en_k en) (PEC.en_stk en) (xedepth - 1)) ->
  PEC.en_stk en = rev (e0 :: rr) -> ei_ok e0 -> Forall ei_ok rr -> 0 <= NBv <= 1 -> 4096 <= PEC.en_b en ->
  e_end X = ST xstk xpos xmore xdone xhalt xdepth xec (PESENC.ebump rr) (xedepth - 1) (xlo + NBv) (xhi + NBv) xbad ->
  lregs R4 sp F (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) -> (forall j, In j CSK -> getr R4 (reg j) = getr R (reg j)) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx4) R4 JPC M4 md4) K.
Proof.
  intros INV4 HSTK E0OK FArr HNB EB4 HXF LR4 QCS4. entry_facts.
  set (en1 := PEC.ENC (PEC.en_b en) (PEC.en_k en) (PEC.en_stk en) (xedepth - 1)) in *.
  apply (K_pop F fl LK2 M2 model2 G APART JPC SHRA (fun R' => lregs R' sp F (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))) fx4 R4 M4 md4 LK4 Aw4 cr4 k4 NBv en1 e0 rr INV4
           ltac:(cbn [en1 PEC.en_stk]; exact HSTK) E0OK (proj1 (proj2 (proj2 RAS)))).
  -
    intros MV SF IMG WR16 OVSC FFc OWN OF TF.
    pose proof OF as (OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8 & KR & K8 & KO & U24 & U32 & EB & AvF & AvS & AvL & _). cbn [en1 PEC.en_b PEC.en_stk] in U24, U32, EB.
    destruct TF as (HLEN & EKP & EB1 & ED2 & ALend & ED3 & WR24 & EB6 & ZC & EDS & OVA & TCv & E1C & _ & BINe & EDC & EBC & EDF & EDSH & EDFL & ZC3 & TK & TL). cbn [en1 PEC.en_b PEC.en_k PEC.en_stk] in *.
    rewrite HLEN in U32. set (m := Z.of_nat (length rr)) in *. set (eb := PEC.en_b en) in *. set (ed := eb + 24 * (m + 1)) in *.
    assert (D8 : forall j, (PMSPA.o_v AD fb + 8 * j) / 8 = PMSPA.o_v AD fb / 8 + j).
    { intros j. pose proof (Z.div_mod (PMSPA.o_v AD fb) 8 ltac:(clear; lia)) as E8. rewrite O8, Z.add_0_r in E8. rewrite E8 at 1.
      replace (8 * (PMSPA.o_v AD fb / 8) + 8 * j) with ((PMSPA.o_v AD fb / 8 + j) * 8) by (clear; lia). apply Z.div_mul. clear; lia. }
    assert (Z48 : L5KA.zeros_at MV ((PMSPA.o_v AD fb + 48) / 8 + SBL) 1).
    { replace (PMSPA.o_v AD fb + 48) with (PMSPA.o_v AD fb + 8 * 6) by (clear; lia). rewrite D8. intros i Hi. replace (PMSPA.o_v AD fb / 8 + 6 + SBL + i) with (PMSPA.o_v AD fb / 8 + SBL + (6 + i)) by (clear; lia). apply Zov. clear - Hi; lia. }
    assert (M0 : 0 <= m <= 4165) by (unfold m; clear - ED3 HLEN; pose proof (Nat2Z.is_nonneg (length rr)); unfold m in *; lia).
    assert (MF : mfacts MV sp (PMSPA.o_v AD fb) F fl eb ed).
    { unfold mfacts. repeat split; first [assumption | clear - OR; lia | unfold ed; clear - EB1 ED2 ED3 M0; lia | clear - AvF O8 GF8; Lia.lia | clear - EDF ALend GF8; Lia.lia | unfold ed; assumption]. }
    destruct (RPQ fx4 R4 MV sp (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) F fl eb ed m ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia)
               ltac:(unfold PMSPA.o_ec; cbn [pa_off_ec PeCLayoutA.CADDR_A]; clear - OR; unfold PMSPA.o_v in OR; cbn [pa_off_v PeCLayoutA.CADDR_A] in OR; lia)
               ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia) ltac:(clear - EB; lia) ltac:(unfold ed; clear - ED2 EB1 M0; lia) LR4 SF IMG FFc MF eq_refl M0)
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & LR3 & U32').
    exists fx3, R3, M3v. split; [exact MS3|]. split; [exact MG3|]. split; [intros i Hi N1 N2; exact (FRZ3 i Hi N1)|].
    split; [unfold ed in U32'; replace (eb + 24 * (m + 1) - 24) with (eb + 24 * m) in U32' by (clear; lia); exact U32'|].
    assert (QCS3 : forall j, In j CSK -> getr R3 (reg j) = getr R (reg j)) by (intros j Hj; rewrite (KS3 j Hj); exact (QCS4 j Hj)).
    split; [exact T10|]. split; [exact T11|]. split; [exact T1|]. split; [exact (proj1 LR3)|]. split; [exact QCS3|]. split; [exact LR3| exact QCS3].
  - intros fx5 R3 R5 M5 md5 LK5 Aw5 INV5 [LR3 QCS3] RP35 AG5.
    destruct (lregs_after R3 R5 LR3 QCS3 RP35) as [LR5 QCS5].
    exact (stepR NBv rr fx5 R5 M5 md5 LK5 Aw5 cr4 k4 INV5 FArr HNB EB4 HXF LR5 QCS5).
Qed.
End Frame.
#[local] Abbreviation K_mkx NB XF KT := (PEAEKN.mkec_finish L ar C HI P LY HIok MKEC 128 NB PEAEKN.SV13 CSK HFR HSV CSK3 CSK4 R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 CPRE INCS MPE XF KT HNF).

Lemma main : srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R E0 M model) K.
Proof.
  destruct pre_facts as (e0 & rr & HXS & E0OK & FArr & ED & HSTK & HED & HBADX & LOHI).
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp.
  assert (XS' : s_estk X = e0 :: rr) by (unfold X; cbn [s_estk]; exact HXS).
  pose proof E0OK as (E0L & E0C & E0K). unfold UbjRef.TWO64 in E0C.
  destruct K_vis_entry as (SF0 & E2 & E10 & E1 & _ & OVR). cbv beta in SF0.
  destruct (RUNA fx R (mrestrict (ahid Aw model) M) sp ltac:(clear - SLO SHI SPT; lia) E2 SF0) as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T19 & T21 & T25 & OWN1).
  apply (K_start E0 SMRA fx1 R1 M1v MS1 MG1 FRZ1 OWN1 T1 T2 ltac:(apply KS1; inl) (proj1 (proj2 (proj2 (proj2 RAS)))) (proj2 (proj2 (proj2 (proj2 RAS))))).
  intros F fl LK2 M2 model2 R2 G APART INV2 RP2 G10 ZSH.
  pose proof (K_g_facts F fl LK2 M2 model2 G APART) as GF. cbv beta in GF. destruct GF as (GF1 & GF2 & GF3 & _ & GF8 & _ & GL1 & GL2 & _).
  destruct (vis F fl LK2 M2 model2 G APART M2 model2 LK2 Aw cr k 0 en e0 rr INV2 HSTK E0OK) as (SF2 & FF2 & OWN2 & MF2 & U8 & KR & K8 & U48 & TK & TL & TC & EBR & MR & VFf2 & VSH2 & QVIS2 & _).
  rewrite HED in U48.
  pose proof MF2 as (OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & Z48 & U24 & U32 & EB1 & ED2 & ALend & EAL & LEN & WR24 & EDBIG & ZC3 & EDS & EDO & EDF & EDL & EDSH & AvF & AvL & OSH).
  set (eb := PEC.en_b en) in *. set (ed := eb + 24 * (Z.of_nat (length rr) + 1)) in *.
  assert (FF2' : PEAEKN.ffacts 128 sp F fl (mrestrict (ahid Aw model2) M2) true).
  { destruct FF2 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & X8). split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|]. split; [exact ZSH| exact X8]. }
  assert (DF : dfacts (mrestrict (ahid Aw model2) M2) sp (PMSPA.o_v AD fb) (PESK.o_sink EE fb) F fl eb ed xedepth (ei_kind e0)).
  { unfold dfacts. repeat split; first [assumption | clear - OR KR EB1 ED2 LEN ED; unfold MAX_DEPTH in *; lia]. }
  assert (R2c : forall j, In j L5SAR.cs_all -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
  assert (Q2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (Q8 : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (Q9 : getr R2 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (Q19 : getr R2 (reg 19) = Z_to_bv 64 (PMSPA.o_ec AD fb)) by (rewrite (R2c 19%nat) by inl; rewrite T19; exact A12).
  assert (Q21 : getr R2 (reg 21) = Z_to_bv 64 (PMSPA.o_v AD fb)) by (rewrite (R2c 21%nat) by inl; rewrite T21, <- L5K.rl10; exact A10).
  assert (Q25 : getr R2 (reg 25) = Z_to_bv 64 SBL) by (rewrite (R2c 25%nat) by inl; exact T25).
  assert (QCS2 : forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)) by (intros j Hj; rewrite (R2c j (CSKall j Hj)); apply KS1; exact Hj).
  assert (HSP : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia). assert (HOV : 0 <= PMSPA.o_v AD fb < 2 ^ 64) by (clear - OR; lia).
  assert (HOEC : 0 <= PMSPA.o_ec AD fb < 2 ^ 64) by (unfold PMSPA.o_ec; cbn [pa_off_ec PeCLayoutA.CADDR_A]; clear - OR; unfold PMSPA.o_v in OR; cbn [pa_off_v PeCLayoutA.CADDR_A] in OR; lia).
  assert (HOSK : 0 <= PESK.o_sink EE fb < 2 ^ 64) by (clear - KR; lia). assert (HF : 0 <= F < 2 ^ 64) by (clear - GF1 GF2; lia). assert (HFL : 0 <= fl < 2 ^ 64) by (clear - GL1 GL2; lia).
  assert (HEB : 0 <= eb < 2 ^ 64) by (clear - EBR; lia). assert (HEDr : 0 <= ed < 2 ^ 64) by (clear - ED2 EB1 LEN; lia). assert (HD : 0 <= xedepth < 2 ^ 64) by (clear - ED; unfold MAX_DEPTH in *; lia).

  destruct (ei_indef e0) eqn:HIND.
  -
    assert (HKD : ei_kind e0 = 1 \/ ei_kind e0 = 3).
    { unfold ei_indef in HIND. destruct (Z.eqb_spec (ei_kind e0) 1) as [E|N]; [left; exact E|]. destruct (Z.eqb_spec (ei_kind e0) 3) as [E'|N']; [right; exact E'| discriminate HIND]. }
    pose proof (PESENC.e_end_indef X e0 rr XS' HIND) as EEQ. cbn [s_stk s_pos s_more s_done s_halt s_depth s_ec s_edepth s_lo s_hi s_bad X] in EEQ.
    pose proof HB as HB1. rewrite EEQ in HB1. cbn [s_hi] in HB1.
    destruct (RDI (ei_kind e0) HKD fx1 R2 (mrestrict (ahid Aw model2) M2) sp (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) (PESK.o_sink EE fb) F fl eb ed xedepth HSP HOV HOEC HOSK HF HFL HEB HEDr HD
               Q2 Q8 Q9 G10 Q19 Q21 Q25 SF2 FF2' DF)
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & U1 & U10 & U11 & LR3 & UB & DP).
    pose proof DP as (DD & _).
    apply (d_piece F fl LK2 M2 model2 G APART fx1 fx3 R2 R3 PBPC M3v INV2 MS3 MG3 FRZ3 DD ED).
    intros M3 md3 INV3 VIS3.
    assert (QCS3 : forall j, In j CSK -> getr R3 (reg j) = getr R (reg j)) by (intros j Hj; rewrite (KS3 j Hj); exact (QCS2 j Hj)).
    apply (K_pb F fl LK2 M2 model2 G APART 0 (sp - 105) (xhi + 1) PBRA fx3 R3 M3 md3 LK2 Aw cr k _ INV3 HB1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
             (proj1 RAS) U1 (proj1 LR3) U10 U11 QCS3).
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 RP34 _. destruct (lregs_after F R3 R4 LR3 QCS3 RP34) as [LR4 QCS4].
    exact (stepPQ F fl LK2 M2 model2 G APART PBRA RPQI 1 e0 rr fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 HSTK E0OK FArr ltac:(clear; lia) (proj1 EB1) EEQ LR4 QCS4).
  -
    assert (HKD : ei_kind e0 = 0 \/ ei_kind e0 = 2).
    { unfold ei_indef in HIND. destruct (Z.eqb_spec (ei_kind e0) 1) as [E|N]; [discriminate HIND|]. destruct (Z.eqb_spec (ei_kind e0) 3) as [E'|N']; [discriminate HIND|]. clear - E0K N N'. lia. }
    destruct (Z.lt_total (ei_cnt e0) (ei_len e0)) as [HLT|[HEQ|HGT]].
    +
      pose proof (PESENC.e_end_lt X e0 rr XS' HIND HLT) as EEQ. cbn [s_stk s_pos s_more s_done s_halt s_depth s_ec s_estk s_edepth s_lo s_hi s_bad X] in EEQ.
      destruct (RDC (ei_kind e0) 0 HKD ltac:(clear; lia) fx1 R2 (mrestrict (ahid Aw model2) M2) sp (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) (PESK.o_sink EE fb) F fl eb ed xedepth (ei_len e0) (ei_cnt e0) 0
                 HSP HOV HOEC HOSK HF HFL HEB HEDr HD ltac:(unfold MAX_ITEMS in *; clear - E0L; lia) ltac:(clear - E0C; lia) ltac:(clear; lia)
                 Q2 Q8 Q9 G10 Q19 Q21 Q25 SF2 FF2' DF TL ltac:(unfold MAX_ITEMS in *; clear - E0L; lia) TC ltac:(cbn [crel]; unfold MAX_ITEMS in *; clear - E0L E0C HLT; lia))
        as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & U1 & U10 & U11 & LR3 & DP).
      pose proof DP as (DD & _).
      apply (d_piece F fl LK2 M2 model2 G APART fx1 fx3 R2 R3 MKPC M3v INV2 MS3 MG3 ltac:(intros i Hi N1 N2 N3 N4 _; exact (FRZ3 i Hi N1 N2 N3 N4)) DD ED).
      intros M3 md3 INV3 VIS3.
      assert (QCS3 : forall j, In j CSK -> getr R3 (reg j) = getr R (reg j)) by (intros j Hj; rewrite (KS3 j Hj); exact (QCS2 j Hj)).
      cbn [Z.eqb] in U11.
      apply (K_mkx 0 (e_end X) KONT F fl LK2 M2 model2 G APART 9 MKRA fx3 R3 M3 md3 LK2 Aw cr k _ xestk (xedepth - 1) INV3
               ltac:(cbn [PEC.en_stk]; rewrite HXS; exact HSTK) eq_refl ltac:(rewrite EEQ, HXS, !Z.add_0_r; reflexivity) U10 U11 ltac:(clear; lia) U1 (proj1 (proj2 RAS)) (proj1 LR3) QCS3).
      intros fx2 R2' MV RP SFx FFx OWNx.
      destruct (RX fx2 R3 R2' R MV sp (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) F fl r HSP HOV HOEC HF HFL LR3 RP SFx FFx OR O8 AvF AvL OSH OWNx Rra Rsp RAok QCS3) as (fx6 & R6 & M6v & MG6 & FRZ6 & MS6 & FL6 & RP6).
      exists fx6, R6, M6v. split; [exact MS6|]. split; [exact MG6|]. split; [exact FRZ6|]. split; [exact FL6| exact RP6].
    +
      pose proof (PESENC.e_end_eq X e0 rr XS' HIND HEQ) as EEQ. cbn [s_stk s_pos s_more s_done s_halt s_depth s_ec s_edepth s_lo s_hi s_bad X] in EEQ.
      pose proof TC as TC'. rewrite HEQ in TC'.
      destruct (RDEQ (ei_kind e0) HKD fx1 R2 (mrestrict (ahid Aw model2) M2) sp (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) (PESK.o_sink EE fb) F fl eb ed xedepth (ei_len e0)
                 HSP HOV HOEC HOSK HF HFL HEB HEDr HD ltac:(unfold MAX_ITEMS in *; clear - E0L; lia)
                 Q2 Q8 Q9 G10 Q19 Q21 Q25 SF2 FF2' DF TL ltac:(unfold MAX_ITEMS in *; clear - E0L; lia) TC')
        as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & LR3 & DP).
      pose proof DP as (DD & _).
      apply (d_piece F fl LK2 M2 model2 G APART fx1 fx3 R2 R3 JE M3v INV2 MS3 MG3 ltac:(intros i Hi N1 N2 N3 N4 _; exact (FRZ3 i Hi N1 N2 N3 N4)) DD ED).
      intros M3 md3 INV3 VIS3.
      assert (QCS3 : forall j, In j CSK -> getr R3 (reg j) = getr R (reg j)) by (intros j Hj; rewrite (KS3 j Hj); exact (QCS2 j Hj)).
      exact (stepPQ F fl LK2 M2 model2 G APART JE RPQE 0 e0 rr fx3 R3 M3 md3 LK2 Aw cr k INV3 HSTK E0OK FArr ltac:(clear; lia) (proj1 EB1) ltac:(rewrite EEQ, !Z.add_0_r; reflexivity) LR3 QCS3).
    +
      pose proof (PESENC.e_end_gt X e0 rr XS' HIND ltac:(clear - HGT; lia)) as EEQ. cbn [s_stk s_pos s_more s_done s_halt s_depth s_ec s_estk s_edepth s_lo s_hi s_bad X] in EEQ.
      assert (RUN : exists rel dd, 1 <= rel <= 2 /\ 0 <= dd < 2 ^ 64 /\ crel rel (ei_len e0) (ei_cnt e0) dd).
      { destruct (Z_lt_le_dec (ei_cnt e0) 18446744073692774400) as [LO|HIc].
        - exists 1, (ei_cnt e0 - ei_len e0). cbn [crel]. unfold MAX_ITEMS in *. clear - E0L E0C HGT LO. lia.
        - exists 2, 0. cbn [crel]. clear - E0C HIc. lia. }
      destruct RUN as (rel & dd & Hrel & Hdd & CREL).
      destruct (RDC (ei_kind e0) rel HKD ltac:(clear - Hrel; lia) fx1 R2 (mrestrict (ahid Aw model2) M2) sp (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) (PESK.o_sink EE fb) F fl eb ed xedepth (ei_len e0) (ei_cnt e0) dd
                 HSP HOV HOEC HOSK HF HFL HEB HEDr HD ltac:(unfold MAX_ITEMS in *; clear - E0L; lia) ltac:(clear - E0C; lia) Hdd
                 Q2 Q8 Q9 G10 Q19 Q21 Q25 SF2 FF2' DF TL ltac:(unfold MAX_ITEMS in *; clear - E0L; lia) TC CREL)
        as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & U1 & U10 & U11 & LR3 & DP).
      pose proof DP as (DD & _).
      apply (d_piece F fl LK2 M2 model2 G APART fx1 fx3 R2 R3 MKPC M3v INV2 MS3 MG3 ltac:(intros i Hi N1 N2 N3 N4 _; exact (FRZ3 i Hi N1 N2 N3 N4)) DD ED).
      intros M3 md3 INV3 VIS3.
      assert (QCS3 : forall j, In j CSK -> getr R3 (reg j) = getr R (reg j)) by (intros j Hj; rewrite (KS3 j Hj); exact (QCS2 j Hj)).
      replace (if rel =? 0 then 9 else 8) with 8 in U11 by (destruct (Z.eqb_spec rel 0); [exfalso; clear - Hrel e1; lia| reflexivity]).
      apply (K_mkx 0 (e_end X) KONT F fl LK2 M2 model2 G APART 8 MKRA fx3 R3 M3 md3 LK2 Aw cr k _ xestk (xedepth - 1) INV3
               ltac:(cbn [PEC.en_stk]; rewrite HXS; exact HSTK) eq_refl ltac:(rewrite EEQ, HXS, !Z.add_0_r; reflexivity) U10 U11 ltac:(clear; lia) U1 (proj1 (proj2 RAS)) (proj1 LR3) QCS3).
      intros fx2 R2' MV RP SFx FFx OWNx.
      destruct (RX fx2 R3 R2' R MV sp (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb) F fl r HSP HOV HOEC HF HFL LR3 RP SFx FFx OR O8 AvF AvL OSH OWNx Rra Rsp RAok QCS3) as (fx6 & R6 & M6v & MG6 & FRZ6 & MS6 & FL6 & RP6).
      exists fx6, R6, M6v. split; [exact MS6|]. split; [exact MG6|]. split; [exact FRZ6|]. split; [exact FL6| exact RP6].
Qed.
End Call.
End Slot.

Local Ltac row E0 SMRA PBRA MKRA JE SHRA DSC MK uA uDi1 uDi3 uDc00 uDc01 uDc02 uDc20 uDc21 uDc22 uDeq0 uDeq2 uPQ uR0 uR1 uX :=
  intros PMODE a fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 A12 CPRE INCS POK MP NB HB CRED KONT;
  rewrite L5K.rl12 in A12; destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad];
  refine (main E0 SMRA PBRA MKRA JE SHRA DSC MK ltac:(unfold L5.ra_ok; clear; lia) uA _ _ _ uPQ uPQ uR0 uR1 uX PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
            HH AM K0 ENT FRM FRS FOK SP32 A10 A12 CPRE INCS MP NB HB CRED KONT);
  [ intros kd [-> | ->]; [exact uDi1| exact uDi3]
  | intros kd rel [-> | ->] Hrel;
    (destruct (Z.eq_dec rel 0) as [-> |N0]; [| destruct (Z.eq_dec rel 1) as [-> |N1]; [| replace rel with 2 by lia]]); cbn [Z.eqb];
    [exact uDc00| exact uDc01| exact uDc02| exact uDc20| exact uDc21| exact uDc22]
  | intros kd [-> | ->]; [exact uDeq0| exact uDeq2] ].

Theorem v_end_arr_ok : PECSA.v_end_arr_spec L ar HI P.
Proof.
  unfold PECSA.v_end_arr_spec, PECSPA.v_end_arr_spec, PECSPA.eslot_spec, PECSPA.args_t2. cbn [pe_end_arr EE PeCLayoutA.EADDR_A].
  row 0xaae90 0xaaf04 0xab040 0xab108 0xab040 0xab07c 83002 93 u_runA_a u_runDi_a1 u_runDi_a3 u_runDc_a00 u_runDc_a01 u_runDc_a02 u_runDc_a20 u_runDc_a21 u_runDc_a22 u_runDeq_a0 u_runDeq_a2 u_runPQ_a u_runR0_a u_runR1_a u_runX_a.
Qed.

Theorem v_end_obj_ok : PECSA.v_end_obj_spec L ar HI P.
Proof.
  unfold PECSA.v_end_obj_spec, PECSPA.v_end_obj_spec, PECSPA.eslot_spec, PECSPA.args_t2. cbn [pe_end_obj EE PeCLayoutA.EADDR_A].
  row 0xabb0c 0xabb80 0xabcbc 0xabd84 0xabcbc 0xabcf8 75706 125 u_runA_o u_runDi_o1 u_runDi_o3 u_runDc_o00 u_runDc_o01 u_runDc_o02 u_runDc_o20 u_runDc_o21 u_runDc_o22 u_runDeq_o0 u_runDeq_o2 u_runPQ_o u_runR0_o u_runR1_o u_runX_o.
Qed.
End WithHeap.

End PEAENCE.
