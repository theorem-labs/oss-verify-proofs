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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrameA PeEncKit PeBCReset1 PmBUarK PmBUar PeBPbIndSpec PeBEncNtbSpec PeBEncKit PeBEncKit1 PeBEncNtb PeBEncI64P.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_ac770_ac774.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENCVI.
#[local] Transparent e_end_value.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).
Abbreviation SBL := 2147450880.
Abbreviation SM1 := 0x5edb0.
Abbreviation PBIPC := 0xb2794.

Definition CSK : list nat := [3; 4; 26; 27]%nat.
Abbreviation PBPC := 0xb120c.
Abbreviation INT64_MAX := 9223372036854775807.
Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.

Definition TWO63 : Z := 9223372036854775808.
Definition TWO64 : Z := 18446744073709551616.
Definition runA : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp : Z),
    0 <= sp < 2 ^ 64 -> getr R (reg 2) = Z_to_bv 64 sp -> PEBEK1.sfacts 128 sp M ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 <= i < sp - 128 + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac3a0 M) (mst fx' R' SM1 M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 0xac40c /\ getr R' (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R' (reg 8) = Z_to_bv 64 sp /\ getr R' (reg 9) = Z_to_bv 64 (sp - 128)
      /\ getr R' (reg 19) = getr R (reg 10) /\ getr R' (reg 20) = getr R (reg 11) /\ getr R' (reg 24) = Z_to_bv 64 SBL
      /\ PEBEK1.owns PEBEK1.SV11 sp R M'.

Definition lregs (R : bvmap 5 word) (sp F ov v : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R (reg 8) = Z_to_bv 64 sp /\ getr R (reg 9) = Z_to_bv 64 (sp - 128) /\ getr R (reg 18) = Z_to_bv 64 F
  /\ getr R (reg 19) = Z_to_bv 64 ov /\ getr R (reg 20) = Z_to_bv 64 v /\ getr R (reg 21) = Z_to_bv 64 (ov + 8) /\ getr R (reg 23) = Z_to_bv 64 (F / 8 + SBL)
  /\ getr R (reg 24) = Z_to_bv 64 SBL /\ getr R (reg 25) = Z_to_bv 64 F.

Definition ovfacts (M : word -> option byte) (sp ov F fl : Z) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5.writable RSEGS M ov 56 /\ ((sp - 128) + 128 <= ov \/ ov + 56 <= (sp - 128))
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1
  /\ (ov + 56 <= F \/ F + 128 <= ov) /\ (ov + 56 <= fl \/ fl + 1 <= ov) /\ (ov / 8 + SBL + 7 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= ov / 8 + SBL).

Definition runD (lo hi raD s6v : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov v o F fl : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - 128) -> getr R (reg 8) = Z_to_bv 64 sp -> getr R (reg 9) = Z_to_bv 64 (sp - 128) -> getr R (reg 10) = Z_to_bv 64 F ->
    getr R (reg 19) = Z_to_bv 64 ov -> getr R (reg 20) = Z_to_bv 64 v -> getr R (reg 24) = Z_to_bv 64 SBL ->
    PEBEK1.sfacts 128 sp M -> PEBEK1.ffacts 128 sp F fl M true -> ovfacts M sp ov F fl ->
    L5.u64_at RSEGS M (ov + 8) o -> 4096 <= o <= 140737488355304 -> o mod 8 = 0 -> lo <= v <= hi ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 <= i < sp - 128 + 40) -> ~ (F <= i < F + 24) -> ~ (F / 8 + SBL <= i < F / 8 + SBL + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac40c M) (mst fx' R' PBPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 raD /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 11) = Z_to_bv 64 (sp - 128 + 39)
      /\ lregs R' sp F ov v /\ (s6v <> 0 -> getr R' (reg 22) = Z_to_bv 64 (F + s6v)).

Definition runP (pcP q shb raP lo hi : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov v F fl : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    lregs R sp F ov v -> getr R (reg 22) = Z_to_bv 64 (F + q) -> PEBEK1.sfacts 128 sp M -> PEBEK1.ffacts 128 sp F fl M false -> ovfacts M sp ov F fl -> lo <= v <= hi ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 + 39 <= i < sp - 128 + 39 + 1) -> ~ (F + q <= i < F + q + 8) -> ~ (F / 8 + SBL + shb <= i < F / 8 + SBL + shb + 1) ->
            M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pcP M) (mst fx' R' PBIPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 raP /\ getr R' (reg 10) = Z_to_bv 64 (F + q) /\ getr R' (reg 11) = Z_to_bv 64 (sp - 128 + 39)
      /\ lregs R' sp F ov v /\ getr R' (reg 22) = Z_to_bv 64 (F + q)
      /\ L5.u64_at RSEGS M' (F + q) (ov + 8) /\ L5.u8_at RSEGS M' (F / 8 + SBL + shb) 0.

Definition runW (pcW wr raW : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov v F : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= F < 2 ^ 64 ->
    lregs R sp F ov v -> PEBEK1.sfacts 128 sp M -> 4096 <= ov <= 140737488355272 -> ov mod 8 = 0 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pcW M) (mst fx' R' wr M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 raW /\ getr R' (reg 11) = Z_to_bv 64 (ov + 8) /\ lregs R' sp F ov v.

Definition runJ (pcJ shb : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov v F fl : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    lregs R sp F ov v -> PEBEK1.sfacts 128 sp M -> PEBEK1.ffacts 128 sp F fl M false -> ovfacts M sp ov F fl ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (F / 8 + SBL + shb <= i < F / 8 + SBL + shb + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pcJ M) (mst fx' R' 0xac68c M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ lregs R' sp F ov v.

Definition runE0 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov v F fl eb r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 ->
    lregs R sp F ov v -> PEBEK1.sfacts 128 sp M -> PEBEK1.ffacts 128 sp F fl M false -> ovfacts M sp ov F fl ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) eb -> 0 <= eb <= 140737488355328 ->
    PEBEK1.owns PEBEK1.SV11 sp R0 M -> getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ PMBUK.Wret F fl 1 i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac68c M) (mst fx' R' r M')
      /\ L5.u8_at RSEGS M' fl 0 /\ regs_preserved R0 R'.

Definition runE1 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov v F fl eb ed cn r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 -> 0 <= cn < 2 ^ 64 ->
    lregs R sp F ov v -> PEBEK1.sfacts 128 sp M -> PEBEK1.ffacts 128 sp F fl M false -> ovfacts M sp ov F fl ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) ed ->
    4096 <= eb -> 4120 <= ed <= 140737488355328 -> ed mod 8 = 0 -> 24 <= ed - eb <= 100000 -> L5.writable RSEGS M (ed - 24) 24 ->
    (2147446784 + 17592186048512 <= ed - 24 \/ (ed - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((ed - 8) / 8 + SBL) 1 ->
    ((ed - 24) + 24 <= (sp - 128) \/ (sp - 128) + 128 <= (ed - 24)) -> ((ed - 24) + 24 <= ov \/ ov + 56 <= (ed - 24)) ->
    ((ed - 24) + 24 <= F \/ F + 128 <= (ed - 24)) -> ((ed - 24) + 24 <= fl \/ fl + 1 <= (ed - 24)) -> ((ed - 24) / 8 + SBL + 3 <= F / 8 + SBL \/ F / 8 + SBL + 16 <= (ed - 24) / 8 + SBL) ->
    L5.u64_at RSEGS M (ed - 8) cn ->
    PEBEK1.owns PEBEK1.SV11 sp R0 M -> getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ PMBUK.Wret F fl 1 i -> ~ (ed - 8 <= i < ed - 8 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xac68c M) (mst fx' R' r M')
      /\ L5.u64_at RSEGS M' (ed - 8) ((cn + 1) mod 2 ^ 64) /\ L5.u8_at RSEGS M' fl 0 /\ regs_preserved R0 R'.

Ltac gks KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEBENCVIP.aligned; assumption | apply wid | apply wrng | L5SAR.greg | L5SAR.gmem | lia]).
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
  pose proof (PEBENCVIP.bviA_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|].
  decompose [and] P. split; [gks KS|]. unfold PEBEK1.owns, PEBEK1.SV11. repeat split; first [greg1 KS | L5SAR.gmem].
Qed.

Ltac runD_tac CONC :=
  intros fx R M sp ov v o F fl Hsp Hov Hv Ho HF Hfl G2 G8 G9 G10 G19 G20 G24 (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF UO OR1 OA HV;
  unfold PEBEK1.ffacts in FF0; decompose [and] FF0; unfold ovfacts in OVF; decompose [and] OVF;
  let V := midV R sp ov v o F fl 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs; repeat split; first [greg1 KS | intros Hs6; first [greg1 KS | exfalso; apply Hs6; reflexivity]].
Lemma u_runDp8 : runD 0 255 0xac58c 64. Proof. runD_tac PEBENCVIP.bviDp8_conc. Qed.
Lemma u_runDp16 : runD 256 32767 0xac65c 0. Proof. runD_tac PEBENCVIP.bviDp16_conc. Qed.
Lemma u_runDp32 : runD 32768 2147483647 0xac680 0. Proof. runD_tac PEBENCVIP.bviDp32_conc. Qed.
Lemma u_runDp64 : runD 2147483648 (TWO63 - 1) 0xac548 0. Proof. unfold runD, TWO63. runD_tac PEBENCVIP.bviDp64_conc. Qed.
Lemma u_runDn8 : runD (TWO64 - 128) (TWO64 - 1) 0xac5e4 32. Proof. unfold runD, TWO64. runD_tac PEBENCVIP.bviDn8_conc. Qed.
Lemma u_runDn16 : runD (TWO64 - 32768) (TWO64 - 129) 0xac65c 0. Proof. unfold runD, TWO64. runD_tac PEBENCVIP.bviDn16_conc. Qed.
Lemma u_runDn32 : runD (TWO64 - 2147483648) (TWO64 - 32769) 0xac680 0. Proof. unfold runD, TWO64. runD_tac PEBENCVIP.bviDn32_conc. Qed.
Lemma u_runDn64 : runD TWO63 (TWO64 - 2147483649) 0xac548 0. Proof. unfold runD, TWO63, TWO64. runD_tac PEBENCVIP.bviDn64_conc. Qed.

Ltac runP_tac CONC :=
  intros fx R M sp ov v F fl Hsp Hov Hv HF Hfl LR G22 (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF HV;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G24 & G25); unfold PEBEK1.ffacts in FF0; decompose [and] FF0; unfold ovfacts in OVF; decompose [and] OVF;
  let V := midV R sp ov v 0 F fl 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs; repeat split; first [greg1 KS | L5SAR.gmem].
Lemma u_runPp8 : runP 0xac58c 64 8 0xac5a4 0 255. Proof. runP_tac PEBENCVIP.bviPp8_conc. Qed.
Lemma u_runPn8 : runP 0xac5e4 32 4 0xac5fc (TWO64 - 128) (TWO64 - 1). Proof. unfold runP, TWO64. runP_tac PEBENCVIP.bviPn8_conc. Qed.

Ltac runW_tac CONC :=
  intros fx R M sp ov v F Hsp Hov Hv HF LR (K0 & K1 & K2 & K3 & K4 & K5) OR1 OA1;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G24 & G25);
  let V := midV R sp ov v 0 F 0 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|]; split; [intros i Hi; apply FRZ1; exact Hi|]; split; [exact MS1|];
  decompose [and] P; split; [gks KS|]; unfold lregs; repeat split; greg1 KS.
Lemma u_runW16 : runW 0xac65c 0xb3614 0xac668. Proof. runW_tac PEBENCVIP.bviW16_conc. Qed.
Lemma u_runW32 : runW 0xac680 0xb37f8 0xac68c. Proof. runW_tac PEBENCVIP.bviW32_conc. Qed.
Lemma u_runW64 : runW 0xac548 0xb39f8 0xac554. Proof. runW_tac PEBENCVIP.bviW64_conc. Qed.

Ltac runJ_tac CONC :=
  intros fx R M sp ov v F fl Hsp Hov Hv HF Hfl LR (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF;
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G24 & G25); unfold PEBEK1.ffacts in FF0; decompose [and] FF0; unfold ovfacts in OVF; decompose [and] OVF;
  let V := midV R sp ov v 0 F fl 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  let REST := fresh "REST" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & REST);
  first [ let P' := fresh "P'" in destruct REST as [KS P']; decompose [and] P' | rename REST into KS ];
  exists fx1, R1, M1; split; [exact MG1|]; split; [intros i Hi N1; apply FRZ1; first [exact Hi | clear - N1; lia]|]; split; [exact MS1|];
  split; [gks KS|]; unfold lregs; repeat split; greg1 KS.
Lemma u_runJp8 : runJ 0xac5a4 8. Proof. runJ_tac PEBENCVIP.bviJp8_conc. Qed.
Lemma u_runJn8 : runJ 0xac5fc 4. Proof. runJ_tac PEBENCVIP.bviJn8_conc. Qed.
Lemma u_runJ16 : runJ 0xac668 4. Proof. runJ_tac PEBENCVIP.bviJ16_conc. Qed.
Lemma u_runJ64 : runJ 0xac554 4. Proof. runJ_tac PEBENCVIP.bviJ64_conc. Qed.

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
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G24 & G25). unfold PEBEK1.ffacts in FF0. decompose [and] FF0. unfold ovfacts in OVF. decompose [and] OVF.
  unfold PEBEK1.owns, PEBEK1.SV11 in OWN0. destruct OWN0 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & _). pose proof RA as (Hr1 & Hr2).
  rewrite Hra, L5.unsigned_lit in S8 by (clear - Hr1; lia).
  let V := midV R sp ov v 0 F fl eb eb 0 r R0 in pose proof (PEBENCVIP.bviE0_conc fx R M V) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & FL0 & _).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac7c0 W_ac770 r F_ac770 eq_refl D_ac770 T1 ltac:(clear - Hr1; lia) Hr2) as MSR.
  exists fx1, R1, M1. split; [exact MG1|].
  split; [intros i Hi N; unfold PMBUK.Wret in N; change (ff_bytes 1) with 128 in N; change (128 / 8) with 16 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N; lia| clear - N; lia| clear - N; lia]|].
  split; [eapply msteps_trans; [exact MS1| exact MSR]|]. split; [exact FL0|].
  apply (regs_end R R0 R1 sp PEBENCVIP.KS_bviE0); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23| exact T24| exact T25].
Qed.

Lemma u_runE1 : runE1.
Proof.
  intros fx R R0 M sp ov v F fl eb ed cn r Hsp Hov Hv HF Hfl Heb Hed Hcn LR (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF U24 U32 EB1 ED1 ED8 LEN WR24 NSH ZC DJS DJO DJF DJL DJSH UC OWN0 Hra R0sp RA QCS.
  unfold lregs in LR; destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G24 & G25). unfold PEBEK1.ffacts in FF0. decompose [and] FF0. unfold ovfacts in OVF. decompose [and] OVF.
  unfold PEBEK1.owns, PEBEK1.SV11 in OWN0. destruct OWN0 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & _). pose proof RA as (Hr1 & Hr2).
  rewrite Hra, L5.unsigned_lit in S8 by (clear - Hr1; lia).
  destruct (Z.eq_dec cn 18446744073709551615) as [CW|CNW].
  - rewrite CW in UC.
    let V := midV R sp ov v 0 F fl eb ed cn r R0 in pose proof (PEBENCVIP.bviE1w_conc fx R M V) as P. cbn beta iota in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & FL0 & _ & _ & CC).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac7c0 W_ac770 r F_ac770 eq_refl D_ac770 T1 ltac:(clear - Hr1; lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|].
    split; [intros i Hi N N2; unfold PMBUK.Wret in N; change (ff_bytes 1) with 128 in N; change (128 / 8) with 16 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N2; lia| clear - N; lia| clear - N; lia| clear - N; lia]|].
    split; [eapply msteps_trans; [exact MS1| exact MSR]|]. split; [rewrite CW; change ((18446744073709551615 + 1) mod 2 ^ 64) with 0; exact CC|]. split; [exact FL0|].
    apply (regs_end R R0 R1 sp PEBENCVIP.KS_bviE1w); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23| exact T24| exact T25].
  - let V := midV R sp ov v 0 F fl eb ed cn r R0 in pose proof (PEBENCVIP.bviE1_conc fx R M V) as P. cbn beta iota in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & FL0 & _ & _ & CC).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xac7c0 W_ac770 r F_ac770 eq_refl D_ac770 T1 ltac:(clear - Hr1; lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|].
    split; [intros i Hi N N2; unfold PMBUK.Wret in N; change (ff_bytes 1) with 128 in N; change (128 / 8) with 16 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N2; lia| clear - N; lia| clear - N; lia| clear - N; lia]|].
    split; [eapply msteps_trans; [exact MS1| exact MSR]|]. split; [rewrite Z.mod_small by (clear - Hcn CNW; lia); exact CC|]. split; [exact FL0|].
    apply (regs_end R R0 R1 sp PEBENCVIP.KS_bviE1); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23| exact T24| exact T25].
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
Let W : Z := PECSPA.int64_width v.
Let u : Z := if 0 <=? v then v else v + TWO64.
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 4.
Hypothesis FRM : PMSPA.ffroomA 4 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis VR : - TWO63 <= v < TWO63.
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
Lemma HSV : PEBEK1.SV11 = PEBEK1.SV9 \/ PEBEK1.SV11 = PEBEK1.SV11. Proof. right; reflexivity. Qed.
Lemma W1 : 2 <= W <= 9. Proof. unfold W, PECSPA.int64_width, PECSPA.uint64_width. repeat destruct (_ <=? _); lia. Qed.
Lemma UR : 0 <= u < 2 ^ 64. Proof. unfold u, TWO63, TWO64 in *. destruct (Z.leb_spec 0 v) as [Hp|Hn]; [clear - VR Hp| clear - VR Hn]; lia. Qed.
Lemma A11u : getr R (reg 11) = Z_to_bv 64 u.
Proof. rewrite A11. unfold u, TWO64. destruct (Z.leb_spec 0 v) as [Hp|Hn]; [reflexivity|]. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (v + 18446744073709551616) with (v + 1 * 2 ^ 64) by (clear; lia). rewrite Z_mod_plus_full. reflexivity. Qed.
Lemma HNB : 0 <= W. Proof. pose proof W1. lia. Qed.
Lemma CSK3 : In 3%nat CSK. Proof. inl. Qed.
Lemma CSK4 : In 4%nat CSK. Proof. inl. Qed.
Lemma CSKall j : In j CSK -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.

Local Notation K_vis_entry := (PEBEK1.vis_entry L ar C HI LY HIok 128 HFR R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK SP32 A10).
Local Notation K_start := (PEBEK1.start L ar C HI P LY HIok 128 PEBEK1.SV11 HFR HSV fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 CPRE).
Local Notation K_vis_facts := (PEBEK1.vis_facts L ar C HI P LY HIok 128 PEBEK1.SV11 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32).
Local Notation K_g_facts := (PEBEK1.g_facts L ar C HI LY HIok 128 PEBEK1.SV11 HFR HSV R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK).
Local Notation K_inv_agree := (PEBEK1.inv_agree L ar C HI P LY HIok 128 PEBEK1.SV11 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK).
Local Notation K_pb_call := (PEBEK1.pb_call L ar C HI P LY HIok PO PB 128 PEBEK1.SV11 CSK HFR HSV CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 CPRE CRED).
Local Notation K_pbi_call := (PEBEK1.pbi_call L ar C HI P LY HIok PO PBI 128 PEBEK1.SV11 CSK HFR HSV CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 CPRE CRED).
Local Notation K_wr_call := (PEBEK1.wr_call L ar C HI P LY HIok 128 PEBEK1.SV11 CSK HFR HSV CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 CPRE CRED).
Local Notation INV := (PEBEK1.inv L ar HI P 128 PEBEK1.SV11 R M model LBX FF LK Aw cr sp fb xlo xhi s en k).

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMBUK.gctx L ar HI (PM.parser_own s ++ LBX) FF LK Aw sp 20480 (sp - 128) (sp - 8 * Z.of_nat (length PEBEK1.SV11)) sp (PEBEK1.ocell sp (Z.of_nat (length PEBEK1.SV11))) (PEBEK1.owns PEBEK1.SV11 sp R) F fl 1 LK2 M2 model2 cr (PEBEK1.EBX en k).
Hypothesis APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (PEBEK1.EBX en k ++ (PM.parser_own s ++ LBX)) FF sp0 scr0 (a + i)) -> 0 < n ->
    (a + n <= F \/ F + 128 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + 16 <= a) /\ (a + n <= fl \/ fl + 1 <= a).

Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH; pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl4 in Rtp;
  pose proof (K_g_facts F fl LK2 M2 model2 G APART) as GF; cbv beta in GF; destruct GF as (GF1 & GF2 & GF3 & _ & GF8 & _ & GL1 & GL2 & _).

Lemma lregs_after R1 R2 : lregs R1 sp F (PMSPA.o_v AD fb) u -> (forall j, In j CSK -> getr R1 (reg j) = getr R (reg j)) -> regs_preserved R1 R2 ->
  lregs R2 sp F (PMSPA.o_v AD fb) u /\ (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)).
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
  PEBEK1.sfacts 128 sp MV /\ PEBEK1.ffacts 128 sp F fl MV false /\ PEBEK1.owns PEBEK1.SV11 sp R MV /\ ovfacts MV sp (PMSPA.o_v AD fb) F fl
  /\ L5.u64_at RSEGS MV (PMSPA.o_v AD fb + 8) (PESK.o_sink EE fb) /\ 4096 <= PESK.o_sink EE fb <= 140737488355304 /\ (PESK.o_sink EE fb) mod 8 = 0
  /\ L5.u64_at RSEGS MV (PMSPA.o_v AD fb + 24) (PEC.en_b en) /\ L5.u64_at RSEGS MV (PMSPA.o_v AD fb + 32) (PEC.en_b en + 24 * Z.of_nat (length (PEC.en_stk en))) /\ 0 <= PEC.en_b en <= 2 ^ 47
  /\ L5A.avis (ahid Awq mdq) F 128 /\ L5A.avis (ahid Awq mdq) (F / 8 + SB) 16.
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
  INV F Mq mdq LKq Awq crq kq W -> lregs Rq sp F (PMSPA.o_v AD fb) u -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xac68c Mq mdq) K.
Proof.
  intros INVq LRq QCS. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq W INVq) as (SF4 & FF4 & OWN4 & OF4 & _ & _ & _ & U24 & U32 & EB & _).
  pose proof OF4 as (OR4 & _).
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (_ & _ & _ & _ & _ & Lestk & _). cbn [s_estk X] in Lestk.
  unfold PMSPA.cfg.
  destruct xestk as [|e1 rr] eqn:HXS.
  - rewrite Lestk in U32. cbn [rev length Z.of_nat Z.mul] in U32. rewrite Z.add_0_r in U32.
    destruct (u_runE0 fxq Rq R (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) u F fl (PEC.en_b en) r ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR4; lia) UR ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia) ltac:(clear - EB; lia)
               LRq SF4 FF4 OF4 U24 U32 ltac:(clear - EB; lia) OWN4 Rra Rsp RAok QCS)
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & FL5 & RP5).
    exact (PEBEK1.finish_ro L ar C HI P LY HIok 128 W PEBEK1.SV11 HFR HSV R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec [] xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS KONT
             F fl LK2 M2 model2 G APART 0xac68c fxq Rq Mq mdq LKq Awq crq kq fx5 R5 M5v INVq eq_refl MS5 MG5 FRZ5 FL5 RP5).
  - pose proof (PEBEK1.vis_facts_top L ar C HI P LY HIok 128 PEBEK1.SV11 HFR HSV R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE MP
                  F fl LK2 M2 model2 G APART Mq mdq LKq Awq crq kq W e1 rr INVq eq_refl) as VT. cbv beta in VT.
    destruct VT as (HLEN & EKP & EB1 & ED2 & ALend & ED3 & WR24 & EB6 & ZC & EDS & OVA & TCv & E1C & E1OK & BINe & EDC & EBC & EDF & EDSH & EDFL & EDV).
    rewrite HLEN in U32. set (ed := PEC.en_b en + 24 * (Z.of_nat (length rr) + 1)) in *.
    destruct (u_runE1 fxq Rq R (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) u F fl (PEC.en_b en) ed (ei_cnt e1) r ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR4; lia) UR ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia)
               ltac:(clear - EB; lia) ltac:(clear - EB1 ED2 ED3; lia) E1C LRq SF4 FF4 OF4 U24 U32
               EB1 ltac:(clear - EB1 ED2 ED3; lia) ALend ED3 WR24 EB6 ZC EDS OVA EDF EDFL ltac:(clear - EDF ALend GF8; Lia.lia) TCv OWN4 Rra Rsp RAok QCS)
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & CC5 & FL5 & RP5).
    exact (PEBEK1.finish_bump L ar C HI P LY HIok 128 W PEBEK1.SV11 HFR HSV R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS MP KONT
             F fl LK2 M2 model2 G APART 0xac68c fxq Rq Mq mdq LKq Awq crq kq fx5 R5 M5v e1 rr INVq eq_refl MS5 MG5 FRZ5 CC5 FL5 RP5).
Qed.

Lemma stepJ pcJ shb (fxq : FPState) Rq Mq mdq LKq Awq crq kq : runJ pcJ shb -> (shb = 4 \/ shb = 8) ->
  INV F Mq mdq LKq Awq crq kq W -> lregs Rq sp F (PMSPA.o_v AD fb) u -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcJ Mq mdq) K.
Proof.
  intros RJ HSHB INVq LRq QCS. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq W INVq) as (SF & FFc & _ & OF & _ & _ & _ & _ & _ & _ & VFf & VSH).
  pose proof OF as (OR & _). pose proof INVq as ((HHq & AMq & _) & _).
  destruct (RJ fxq Rq (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) u F fl ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia) UR ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia) LRq SF FFc OF)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & LR3).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LKq crq Awq Mq mdq fxq fx3 Rq pcJ R3 0xac68c M3v (fun a0 => F / 8 + SBL + shb <= a0 < F / 8 + SBL + shb + 1) K HHq AMq MS3 MG3).
  { intros a0 Ha Hn. apply FRZ3; [exact Ha| exact Hn]. }
  { intros a0 Ha Wa. split.
    - apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 1 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128. unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - Wa GF8 HSHB. Lia.lia.
    - clear - Wa GF3 HSHB; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV F M3 md3 LKq Awq crq kq W).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART Mq M3 (fun a0 => F / 8 + SBL + shb <= a0 < F / 8 + SBL + shb + 1) mdq md3 LKq crq Awq kq W INVq HH3 AM3 MRT3 MGM3); [| exact FR3].
    intros a0 X'. right; right. unfold SB. clear - X' HSHB; lia. }
  apply (tailE fx3 R3 M3 md3 LKq Awq crq kq INV3 LR3). exact (csk_kept Rq R3 CSK (fun j Hj => Hj) KS3 QCS).
Qed.

Lemma stepW pcW wr raW kb (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  runW pcW wr raW -> PENTBB.ntb_specB RSEGS AD L ar HI wr kb P -> 0 <= kb -> 1 + kb = W -> L5.ra_ok raW ->
  INV F Mq mdq LKq Awq crq kq 1 -> lregs Rq sp F (PMSPA.o_v AD fb) u -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) ->
  (forall (fx2 : FPState) R2 Mx mdx LKx Awx crx kx, INV F Mx mdx LKx Awx crx kx W -> lregs R2 sp F (PMSPA.o_v AD fb) u -> (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 raW Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcW Mq mdq) K.
Proof.
  intros RW NTB KB0 HW RAW INVq LRq QCS KX. entry_facts.
  destruct (vis Mq mdq LKq Awq crq kq 1 INVq) as (SF & FFc & _ & OF & _). pose proof OF as (OR & O8 & _). pose proof INVq as ((HHq & AMq & _) & _).
  destruct (RW fxq Rq (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) u F ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia) UR ltac:(clear - GF1 GF2; lia) LRq SF OR O8)
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

Lemma stepP pcP q shb raP lo hi (fxq : FPState) Rq Mq mdq LKq Awq crq kq : runP pcP q shb raP lo hi -> lo <= u <= hi -> 2 = W ->
  ((q = 64 /\ shb = 8) \/ (q = 32 /\ shb = 4)) -> L5.ra_ok raP ->
  INV F Mq mdq LKq Awq crq kq 1 -> lregs Rq sp F (PMSPA.o_v AD fb) u -> (forall j, In j CSK -> getr Rq (reg j) = getr R (reg j)) -> getr Rq (reg 22) = Z_to_bv 64 (F + q) ->
  (forall (fx2 : FPState) R2 Mx mdx LKx Awx crx kx, INV F Mx mdx LKx Awx crx kx W -> lregs R2 sp F (PMSPA.o_v AD fb) u -> (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 raP Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcP Mq mdq) K.
Proof.
  intros RP HV HW HQ RAP INVq LRq QCS G22 KX. entry_facts.
  assert (HQ8 : q = 8 * shb) by (clear - HQ; lia). assert (HQR : 32 <= q <= 64) by (clear - HQ; lia).
  destruct (vis Mq mdq LKq Awq crq kq 1 INVq) as (SF & FFc & _ & OF & _ & _ & _ & _ & _ & _ & VFf & VSH). pose proof OF as (OR & _). pose proof INVq as ((HHq & AMq & _) & _).
  destruct (RP fxq Rq (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) u F fl ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia) UR ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia) LRq G22 SF FFc OF HV)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & LR3 & T22 & UQ3 & USH3).
  set (W3 := fun a0 => (sp - 128 + 39 <= a0 < sp - 128 + 39 + 1) \/ (F + q <= a0 < F + q + 8) \/ (F / 8 + SBL + shb <= a0 < F / 8 + SBL + shb + 1)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LKq crq Awq Mq mdq fxq fx3 Rq pcP R3 PBIPC M3v W3 K HHq AMq MS3 MG3).
  { intros a0 Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; exact X'| intros X'; apply Hn; right; left; exact X'| intros X'; apply Hn; right; right; exact X']. }
  { intros a0 Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar _ _ 0 0 F 1 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - X' HQR; lia].
      + apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 1 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128. unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - X' GF8 HQ. Lia.lia.
    - destruct Wa as [X'|[X'|X']]; unfold SB; clear - X' GF3 SLO SPT HQ; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV F M3 md3 LKq Awq crq kq 1).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART Mq M3 W3 mdq md3 LKq crq Awq kq 1 INVq HH3 AM3 MRT3 MGM3); [| exact FR3].
    intros a0 [X'|[X'|X']]; [left; split; [clear - X'; lia| unfold PEBEK1.ocell, PEBEK1.SV11; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - X'; lia]
                          | right; left; clear - X' HQR; lia | right; right; unfold SB; clear - X' HQ; lia]. }
  pose proof (csk_kept Rq R3 CSK (fun j Hj => Hj) KS3 QCS) as QCS3.
  refine (K_pbi_call F fl LK2 M2 model2 G APART 1 (F + q) (sp - 128 + 39) (xhi + W) raP fx3 R3 M3 md3 LKq Awq crq kq INV3 HBN ltac:(clear - HW; lia) ltac:(clear; lia) ltac:(clear; lia)
           RAP ltac:(clear - HQR; lia) ltac:(clear - HQR; lia) ltac:(replace (F + q) with ((F / 8 + shb) * 8) by (clear - GF8 HQ8; lia); apply Z_mod_mult) _ _ T1 (proj1 LR3) T10 T11 QCS3 _).
  { apply (proj1 (L5A.u64_at_vis (ahid Awq mdq) M3 (F + q) _ (L5A.avis_sub _ F 128 (F + q) 8 VFf ltac:(clear - HQR; lia) ltac:(clear - HQR; lia)) ltac:(clear - GF1 HQR; lia) ltac:(clear - GF2 HQR; lia))). rewrite VIS3. exact UQ3. }
  { replace ((F + q) / 8 + SBL) with (F / 8 + SBL + shb) by (clear - GF8 HQ8 HQR; Lia.lia).
    apply (proj1 (L5A.u8_at_vis (ahid Awq mdq) M3 (F / 8 + SBL + shb) 0 (L5A.avis_sub _ (F / 8 + SB) 16 (F / 8 + SBL + shb) 1 VSH ltac:(unfold SB; clear - HQ; lia) ltac:(unfold SB; clear - HQ; lia))
             ltac:(clear - GF1 HQ; lia) ltac:(clear - GF2 HQ; unfold SB; lia))). rewrite VIS3. exact USH3. }
  intros fx2 R2 Mx mdx LKx Awx crx kx INVx RP2 _. destruct (lregs_after R3 R2 LR3 QCS3 RP2) as [LR2 QCS2]. replace (1 + 1) with W in INVx by (clear - HW; lia).
  exact (KX fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2).
Qed.
End Frame.

Lemma stepD lo hi raD s6v : runD lo hi raD s6v -> lo <= u <= hi -> L5.ra_ok raD ->
  (forall F fl LK2 M2 model2
      (G : PMBUK.gctx L ar HI (PM.parser_own s ++ LBX) FF LK Aw sp 20480 (sp - 128) (sp - 8 * Z.of_nat (length PEBEK1.SV11)) sp (PEBEK1.ocell sp (Z.of_nat (length PEBEK1.SV11))) (PEBEK1.owns PEBEK1.SV11 sp R) F fl 1 LK2 M2 model2 cr (PEBEK1.EBX en k))
      (APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (PEBEK1.EBX en k ++ (PM.parser_own s ++ LBX)) FF sp0 scr0 (a + i)) -> 0 < n ->
                 (a + n <= F \/ F + 128 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + 16 <= a) /\ (a + n <= fl \/ fl + 1 <= a))
      (fx2 : FPState) R2 Mx mdx LKx Awx crx kx,
      INV F Mx mdx LKx Awx crx kx 1 -> lregs R2 sp F (PMSPA.o_v AD fb) u -> (forall j, In j CSK -> getr R2 (reg j) = getr R (reg j)) ->
      (s6v <> 0 -> getr R2 (reg 22) = Z_to_bv 64 (F + s6v)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 raD Mx mdx) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xac3a0 M model) K.
Proof.
  intros RD HV RAD KX.
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp.
  destruct K_vis_entry as (SF0 & E2 & E10 & E1 & _ & OVR). cbv beta in SF0.
  destruct (u_runA fx R (mrestrict (ahid Aw model) M) sp ltac:(clear - SLO SHI SPT; lia) E2 SF0) as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T19 & T20 & T24 & OWN1).
  apply (K_start 0xac3a0 0xac40c fx1 R1 M1v MS1 MG1 FRZ1 OWN1 T1 T2 ltac:(apply KS1; inl) ltac:(clear; lia) ltac:(reflexivity)).
  intros F fl LK2 M2 model2 R2 G APART INV2 RP2 G10 ZSH.
  pose proof (K_g_facts F fl LK2 M2 model2 G APART) as GF. cbv beta in GF. destruct GF as (GF1 & GF2 & GF3 & _ & GF8 & _ & GL1 & GL2 & _).
  destruct (vis F fl LK2 M2 model2 G APART M2 model2 LK2 Aw cr k 0 INV2) as (SF2 & FF2 & OWN2 & OF2 & U8 & KR & K8 & _ & _ & _ & VFf2 & VSH2).
  pose proof OF2 as (OR & _).
  assert (FF2' : PEBEK1.ffacts 128 sp F fl (mrestrict (ahid Aw model2) M2) true).
  { destruct FF2 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & X8). split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|]. split; [exact ZSH| exact X8]. }
  assert (R2c : forall j, In j L5SAR.cs_all -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
  destruct (RD fx1 R2 (mrestrict (ahid Aw model2) M2) sp (PMSPA.o_v AD fb) u (PESK.o_sink EE fb) F fl ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia) UR ltac:(clear - KR; lia) ltac:(clear - GF1 GF2; lia) ltac:(clear - GL1 GL2; lia)
             ltac:(rewrite (R2c 2%nat) by inl; exact T2) ltac:(rewrite (R2c 8%nat) by inl; exact T8) ltac:(rewrite (R2c 9%nat) by inl; exact T9) G10
             ltac:(rewrite (R2c 19%nat) by inl; rewrite T19, <- L5K.rl10; exact A10) ltac:(rewrite (R2c 20%nat) by inl; rewrite T20; exact A11u) ltac:(rewrite (R2c 24%nat) by inl; exact T24)
             SF2 FF2' OF2 U8 KR K8 HV)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & U1 & U10 & U11 & LR3 & LR22).
  pose proof (conj LR3 LR22) as LR3full.
  pose proof INV2 as ((HH2 & AM2 & _) & _).
  set (W3 := fun a => (sp - 128 <= a < sp - 128 + 40) \/ (F <= a < F + 24) \/ (F / 8 + SBL <= a < F / 8 + SBL + 12)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 fx1 fx3 R2 0xac40c R3 PBPC M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; exact X'| intros X'; apply Hn; right; left; exact X'| intros X'; apply Hn; right; right; exact X']. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar _ _ 0 0 F 1 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 1 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128. unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - X' GF8. Lia.lia.
    - destruct Wa as [X'|[X'|X']]; unfold SB; clear - X' GF3 SLO SPT; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV F M3 md3 LK2 Aw cr k 0).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART M2 M3 W3 model2 md3 LK2 cr Aw k 0 INV2 HH3 AM3 MRT3 MGM3); [| exact FR3].
    intros a [X'|[X'|X']]; [left; split; [clear - X'; lia| unfold PEBEK1.ocell, PEBEK1.SV11; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - X'; lia]
                         | right; left; clear - X'; lia | right; right; unfold SB; clear - X'; lia]. }
  assert (QCS3 : forall j, In j CSK -> getr R3 (reg j) = getr R (reg j)).
  { intros j Hj. rewrite (KS3 j Hj). rewrite (R2c j (CSKall j Hj)). apply KS1. exact Hj. }
  pose proof W1 as HW.
  apply (K_pb_call F fl LK2 M2 model2 G APART 0 (sp - 128 + 39) (xhi + W) raD fx3 R3 M3 md3 LK2 Aw cr k INV3 HBN ltac:(clear - HW; lia) ltac:(clear; lia) ltac:(clear; lia) RAD U1 (proj1 LR3) U10 U11 QCS3).
  intros fx2 R2' Mx mdx LKx Awx crx kx INVx RP2' _. destruct (lregs_after F R3 R2' LR3 QCS3 RP2') as [LR2 QCS2].
  apply (KX F fl LK2 M2 model2 G APART fx2 R2' Mx mdx LKx Awx crx kx INVx LR2 QCS2).
  intros Hlo. rewrite (L5SAR.cs_of_preserved R3 R2' 22 RP2') by inl. exact (proj2 LR3full Hlo).
Qed.

Lemma main : srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xac3a0 M model) K.
Proof.
  pose proof W1 as HW. pose proof UR as UR0.
  assert (PLW : ((0 <= u <= 255 /\ W = 2) \/ (256 <= u <= 32767 /\ W = 3) \/ (32768 <= u <= 2147483647 /\ W = 5) \/ (2147483648 <= u <= TWO63 - 1 /\ W = 9))
             \/ ((TWO64 - 128 <= u <= TWO64 - 1 /\ W = 2) \/ (TWO64 - 32768 <= u <= TWO64 - 129 /\ W = 3)
             \/ (TWO64 - 2147483648 <= u <= TWO64 - 32769 /\ W = 5) \/ (TWO63 <= u <= TWO64 - 2147483649 /\ W = 9))).
  { unfold W, u, PECSPA.int64_width, PECSPA.uint64_width, TWO63, TWO64 in *. destruct (Z.leb_spec 0 v) as [P0|N0].
    - left. destruct (Z.leb_spec v 255) as [L1|L1]; [left; split; [clear - P0 L1; lia|reflexivity]|]. destruct (Z.leb_spec v 32767) as [L2|L2]; [right; left; split; [clear - L1 L2; lia|reflexivity]|].
      destruct (Z.leb_spec v 2147483647) as [L3|L3]; [right; right; left; split; [clear - L2 L3; lia|reflexivity]| right; right; right; split; [clear - VR L3; lia|reflexivity]].
    - right. destruct (Z.leb_spec (-128) v) as [L1|L1]; [left; split; [clear - N0 L1; lia|reflexivity]|]. destruct (Z.leb_spec (-32768) v) as [L2|L2]; [right; left; split; [clear - L1 L2; lia|reflexivity]|].
      destruct (Z.leb_spec (-2147483648) v) as [L3|L3]; [right; right; left; split; [clear - L2 L3; lia|reflexivity]| right; right; right; split; [clear - VR L3 N0; lia|reflexivity]]. }
  destruct PLW as [[[V8 HW2]|[[V16 HW3]|[[V32 HW5]|[V64 HW9]]]]|[[V8 HW2]|[[V16 HW3]|[[V32 HW5]|[V64 HW9]]]]].
  - apply (stepD 0 255 0xac58c 64 u_runDp8 V8); [split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 G22.
    apply (stepP F fl LK2 M2 model2 G APART 0xac58c 64 8 0xac5a4 0 255 fx2 R2 Mx mdx LKx Awx crx kx u_runPp8 V8 (eq_sym HW2) ltac:(left; split; reflexivity) ltac:(split; [clear; lia| reflexivity]) INVx LR2 QCS2 (G22 ltac:(clear; lia))).
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (stepJ F fl LK2 M2 model2 G APART 0xac5a4 8 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJp8 ltac:(right; reflexivity) INV4 LR4 QCS4).
  - apply (stepD 256 32767 0xac65c 0 u_runDp16 V16); [split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
    apply (stepW F fl LK2 M2 model2 G APART 0xac65c 0xb3614 0xac668 2 fx2 R2 Mx mdx LKx Awx crx kx u_runW16 NTB16); [clear; lia| clear - HW3; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (stepJ F fl LK2 M2 model2 G APART 0xac668 4 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ16 ltac:(left; reflexivity) INV4 LR4 QCS4).
  - apply (stepD 32768 2147483647 0xac680 0 u_runDp32 V32); [split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
    apply (stepW F fl LK2 M2 model2 G APART 0xac680 0xb37f8 0xac68c 4 fx2 R2 Mx mdx LKx Awx crx kx u_runW32 NTB32); [clear; lia| clear - HW5; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (tailE F fl LK2 M2 model2 G APART fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4).
  - apply (stepD 2147483648 (TWO63 - 1) 0xac548 0 u_runDp64 V64); [split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
    apply (stepW F fl LK2 M2 model2 G APART 0xac548 0xb39f8 0xac554 8 fx2 R2 Mx mdx LKx Awx crx kx u_runW64 NTB64); [clear; lia| clear - HW9; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (stepJ F fl LK2 M2 model2 G APART 0xac554 4 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ64 ltac:(left; reflexivity) INV4 LR4 QCS4).
  - apply (stepD (TWO64 - 128) (TWO64 - 1) 0xac5e4 32 u_runDn8 V8); [split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 G22.
    apply (stepP F fl LK2 M2 model2 G APART 0xac5e4 32 4 0xac5fc (TWO64 - 128) (TWO64 - 1) fx2 R2 Mx mdx LKx Awx crx kx u_runPn8 V8 (eq_sym HW2) ltac:(right; split; reflexivity) ltac:(split; [clear; lia| reflexivity]) INVx LR2 QCS2 (G22 ltac:(clear; lia))).
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (stepJ F fl LK2 M2 model2 G APART 0xac5fc 4 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJn8 ltac:(left; reflexivity) INV4 LR4 QCS4).
  - apply (stepD (TWO64 - 32768) (TWO64 - 129) 0xac65c 0 u_runDn16 V16); [split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
    apply (stepW F fl LK2 M2 model2 G APART 0xac65c 0xb3614 0xac668 2 fx2 R2 Mx mdx LKx Awx crx kx u_runW16 NTB16); [clear; lia| clear - HW3; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (stepJ F fl LK2 M2 model2 G APART 0xac668 4 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ16 ltac:(left; reflexivity) INV4 LR4 QCS4).
  - apply (stepD (TWO64 - 2147483648) (TWO64 - 32769) 0xac680 0 u_runDn32 V32); [split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
    apply (stepW F fl LK2 M2 model2 G APART 0xac680 0xb37f8 0xac68c 4 fx2 R2 Mx mdx LKx Awx crx kx u_runW32 NTB32); [clear; lia| clear - HW5; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (tailE F fl LK2 M2 model2 G APART fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4).
  - apply (stepD TWO63 (TWO64 - 2147483649) 0xac548 0 u_runDn64 V64); [split; [clear; lia| reflexivity]|].
    intros F fl LK2 M2 model2 G APART fx2 R2 Mx mdx LKx Awx crx kx INVx LR2 QCS2 _.
    apply (stepW F fl LK2 M2 model2 G APART 0xac548 0xb39f8 0xac554 8 fx2 R2 Mx mdx LKx Awx crx kx u_runW64 NTB64); [clear; lia| clear - HW9; lia| split; [clear; lia| reflexivity]| exact INVx| exact LR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 LR4 QCS4.
    exact (stepJ F fl LK2 M2 model2 G APART 0xac554 4 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ64 ltac:(left; reflexivity) INV4 LR4 QCS4).
Qed.
End Call.

Theorem v_int64_ok : PECSB.v_int64_spec L ar HI P.
Proof.
  unfold PECSB.v_int64_spec, PECSPA.v_int64_spec, PECSPA.eslot_spec. cbn [pe_int64 EE PeCLayoutB.EADDR_B].
  intros PMODE v fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 AV CPRE INCS POK MP NB HB CRED KONT.
  destruct AV as (VR & A11 & _). rewrite L5K.rl11 in A11.
  assert (VR' : - TWO63 <= v < TWO63) by (unfold TWO63; clear - VR; lia).
  destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad].
  assert (ESC : forall w, e_scalar w w (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad)
          = e_end_value (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + w) (xhi + w) xbad)) by reflexivity.
  rewrite ESC in HB, KONT. rewrite eev_hi in HB. cbn [s_hi] in HB.
  exact (main PMODE v fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
           HH AM K0 ENT FRM FRS FOK SP32 A10 VR' A11 CPRE INCS MP HB CRED KONT).
Qed.
End WithHeap.
End PEBENCVI.
