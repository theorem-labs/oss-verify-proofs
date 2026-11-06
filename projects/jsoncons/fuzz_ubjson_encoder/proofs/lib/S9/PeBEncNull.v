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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrameA PeEncKit PeBCReset1 PmBUarK PmBUar PeBPbIndSpec PeBEncNtbSpec PeBEncKit PeBEncNullP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_ad744_ad748.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENCN.
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

Definition CSK : list nat := [3; 4; 24; 25; 26; 27]%nat.
Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.

Definition runA : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp : Z),
    0 <= sp < 2 ^ 64 -> getr R (reg 2) = Z_to_bv 64 sp -> PEBEK.sfacts 96 sp M ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp - 96 + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad588 M) (mst fx' R' SM0 M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 0xad5e8 /\ getr R' (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R' (reg 8) = Z_to_bv 64 sp /\ getr R' (reg 9) = Z_to_bv 64 (sp - 96)
      /\ getr R' (reg 19) = getr R (reg 10) /\ getr R' (reg 20) = Z_to_bv 64 SBL
      /\ PEBEK.owns PEBEK.SV9 sp R M'.

Definition lregs (R : bvmap 5 word) (sp F ov : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R (reg 8) = Z_to_bv 64 sp /\ getr R (reg 9) = Z_to_bv 64 (sp - 96) /\ getr R (reg 18) = Z_to_bv 64 F
  /\ getr R (reg 19) = Z_to_bv 64 ov /\ getr R (reg 20) = Z_to_bv 64 SBL /\ getr R (reg 21) = Z_to_bv 64 F /\ getr R (reg 22) = Z_to_bv 64 (F / 8 + SBL).

Definition runB : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov F fl : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - 96) -> getr R (reg 8) = Z_to_bv 64 sp -> getr R (reg 9) = Z_to_bv 64 (sp - 96) -> getr R (reg 10) = Z_to_bv 64 F ->
    getr R (reg 19) = Z_to_bv 64 ov -> getr R (reg 20) = Z_to_bv 64 SBL ->
    PEBEK.sfacts 96 sp M -> PEBEK.ffacts 96 sp F fl M true -> 4096 <= ov <= 140737488355272 -> ov mod 8 = 0 ->
    (ov + 56 <= F \/ F + 64 <= ov) -> (ov + 56 <= fl \/ fl + 1 <= ov) -> (ov / 8 + SBL + 7 <= F / 8 + SBL \/ F / 8 + SBL + 8 <= ov / 8 + SBL) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp - 96 + 24) -> ~ (F <= i < F + 24) -> ~ (F + 32 <= i < F + 32 + 8) -> ~ (F / 8 + SBL <= i < F / 8 + SBL + 8) ->
            M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad5e8 M) (mst fx' R' PBIPC M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 0xad694 /\ getr R' (reg 10) = Z_to_bv 64 (F + 32) /\ getr R' (reg 11) = Z_to_bv 64 (sp - 96 + 23)
      /\ lregs R' sp F ov
      /\ L5.u64_at RSEGS M' (F + 32) (ov + 8) /\ L5.u8_at RSEGS M' (F / 8 + 2147450884) 0.

Definition ovfacts (M : word -> option byte) (sp ov F fl eb ed : Z) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5.writable RSEGS M ov 56 /\ ((sp - 96) + 96 <= ov \/ ov + 56 <= (sp - 96))
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1
  /\ (ov + 56 <= F \/ F + 64 <= ov) /\ (ov + 56 <= fl \/ fl + 1 <= ov) /\ (ov / 8 + SBL + 7 <= F / 8 + SBL \/ F / 8 + SBL + 8 <= ov / 8 + SBL)
  /\ L5.u64_at RSEGS M (ov + 24) eb /\ L5.u64_at RSEGS M (ov + 32) ed /\ 0 <= eb /\ ed <= 140737488355328.

Definition runE0 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov F fl eb r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 ->
    lregs R sp F ov -> PEBEK.sfacts 96 sp M -> PEBEK.ffacts 96 sp F fl M false -> ovfacts M sp ov F fl eb eb ->
    PEBEK.owns PEBEK.SV9 sp R0 M -> getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ PMBUK.Wret F fl 0 i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad694 M) (mst fx' R' r M')
      /\ L5.u8_at RSEGS M' fl 0 /\ regs_preserved R0 R'.

Definition runE1 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov F fl eb ed cn r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 -> 0 <= cn < 2 ^ 64 ->
    lregs R sp F ov -> PEBEK.sfacts 96 sp M -> PEBEK.ffacts 96 sp F fl M false -> ovfacts M sp ov F fl eb ed ->
    4096 <= eb -> 4120 <= ed -> ed mod 8 = 0 -> 24 <= ed - eb <= 100000 -> L5.writable RSEGS M (ed - 24) 24 ->
    (2147446784 + 17592186048512 <= ed - 24 \/ (ed - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((ed - 8) / 8 + SBL) 1 ->
    ((ed - 24) + 24 <= (sp - 96) \/ (sp - 96) + 96 <= (ed - 24)) -> ((ed - 24) + 24 <= ov \/ ov + 56 <= (ed - 24)) ->
    ((ed - 24) + 24 <= F \/ F + 64 <= (ed - 24)) -> ((ed - 24) + 24 <= fl \/ fl + 1 <= (ed - 24)) -> ((ed - 24) / 8 + SBL + 3 <= F / 8 + SBL \/ F / 8 + SBL + 8 <= (ed - 24) / 8 + SBL) ->
    L5.u64_at RSEGS M (ed - 8) cn ->
    PEBEK.owns PEBEK.SV9 sp R0 M -> getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ PMBUK.Wret F fl 0 i -> ~ (ed - 8 <= i < ed - 8 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xad694 M) (mst fx' R' r M')
      /\ L5.u64_at RSEGS M' (ed - 8) ((cn + 1) mod 2 ^ 64) /\ L5.u8_at RSEGS M' fl 0 /\ regs_preserved R0 R'.

Ltac gks KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEBENCNP.aligned; assumption | apply wid | apply wrng | L5SAR.greg | L5SAR.gmem | lia]).
Ltac greg1 KS :=
  first [ assumption
        | lazymatch goal with |- getr ?R1 (reg ?n) = _ =>
            first [ lazymatch goal with H : getr R1 (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end
                  | rewrite (KS n) by inl; lazymatch goal with H : getr _ (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end ] end ].

Lemma null_runA : runA.
Proof.
  intros fx R M sp Hsp G2 (K0 & K1 & K2 & K3 & K4 & K5).
  pose proof (PEBENCNP.bvnA_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|].
  decompose [and] P. split; [gks KS|]. unfold PEBEK.owns, PEBEK.SV9. repeat split; first [greg1 KS | L5SAR.gmem].
Qed.

Lemma null_runB : runB.
Proof.
  intros fx R M sp ov F fl Hsp Hov HF Hfl G2 G8 G9 G10 G19 G20 (K0 & K1 & K2 & K3 & K4 & K5) FF0 OR O8 D1 D2 D3. unfold PEBEK.ffacts in FF0. decompose [and] FF0.
  pose proof (PEBENCNP.bvnB_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 47%nat => F | 48%nat => fl
                                  | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P).
  exists fx1, R1, M1. split; [exact MG1|].
  split; [intros i Hi N1 N2 N3 N4; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia| clear - N3; lia| clear - N4; lia]|].
  split; [exact MS1|]. decompose [and] P. split; [gks KS|]. unfold lregs. repeat split; greg1 KS.
Qed.

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

Ltac tailV R R0 sp ov F fl eb ed cn r :=
  constr:(fun j : nat => match j with 2%nat => sp | 10%nat => ov | 38%nat => eb | 39%nat => ed | 42%nat => cn | 47%nat => F | 48%nat => fl | 64%nat => r
     | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9)) | 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19))
     | 69%nat => bv_unsigned (getr R0 (reg 20)) | 70%nat => bv_unsigned (getr R0 (reg 21)) | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23))
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end).

Lemma null_runE0 : runE0.
Proof.
  intros fx R R0 M sp ov F fl eb r Hsp Hov HF Hfl Heb LR (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF OWN0 Hra R0sp RA QCS.
  unfold lregs in LR. destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22). unfold PEBEK.ffacts in FF0. decompose [and] FF0. unfold ovfacts in OVF. decompose [and] OVF.
  unfold PEBEK.owns, PEBEK.SV9 in OWN0. destruct OWN0 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & _). pose proof RA as (Hr1 & Hr2).
  rewrite Hra, L5.unsigned_lit in S8 by (clear - Hr1; lia).
  let V := tailV R R0 sp ov F fl eb eb 0 r in pose proof (PEBENCNP.bvnE0_conc fx R M V) as P. cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & FL0 & _).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xad794 W_ad744 r F_ad744 eq_refl D_ad744 T1 ltac:(clear - Hr1; lia) Hr2) as MSR.
  exists fx1, R1, M1. split; [exact MG1|].
  split; [intros i Hi N; unfold PMBUK.Wret in N; change (ff_bytes 0) with 64 in N; change (64 / 8) with 8 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N; lia| clear - N; lia| clear - N; lia]|].
  split; [eapply msteps_trans; [exact MS1| exact MSR]|]. split; [exact FL0|].
  apply (regs_end R R0 R1 sp PEBENCNP.KS_bvnE0); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23].
Qed.

Lemma null_runE1 : runE1.
Proof.
  intros fx R R0 M sp ov F fl eb ed cn r Hsp Hov HF Hfl Heb Hed Hcn LR (K0 & K1 & K2 & K3 & K4 & K5) FF0 OVF EB1 ED1 ED8 LEN WR24 NSH ZC DJS DJO DJF DJL DJSH UC OWN0 Hra R0sp RA QCS.
  unfold lregs in LR. destruct LR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22). unfold PEBEK.ffacts in FF0. decompose [and] FF0. unfold ovfacts in OVF. decompose [and] OVF.
  unfold PEBEK.owns, PEBEK.SV9 in OWN0. destruct OWN0 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & _). pose proof RA as (Hr1 & Hr2).
  rewrite Hra, L5.unsigned_lit in S8 by (clear - Hr1; lia).
  destruct (Z.eq_dec cn 18446744073709551615) as [CW|CNW].
  - rewrite CW in UC.
    let V := tailV R R0 sp ov F fl eb ed cn r in pose proof (PEBENCNP.bvnE1w_conc fx R M V) as P. cbn beta iota in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & FL0 & _ & CC).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xad794 W_ad744 r F_ad744 eq_refl D_ad744 T1 ltac:(clear - Hr1; lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|].
    split; [intros i Hi N N2; unfold PMBUK.Wret in N; change (ff_bytes 0) with 64 in N; change (64 / 8) with 8 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N2; lia| clear - N; lia| clear - N; lia| clear - N; lia]|].
    split; [eapply msteps_trans; [exact MS1| exact MSR]|]. split; [rewrite CW; change ((18446744073709551615 + 1) mod 2 ^ 64) with 0; exact CC|]. split; [exact FL0|].
    apply (regs_end R R0 R1 sp PEBENCNP.KS_bvnE1w); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23].
  - let V := tailV R R0 sp ov F fl eb ed cn r in pose proof (PEBENCNP.bvnE1_conc fx R M V) as P. cbn beta iota in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & _ & _ & _ & T18 & T19 & T20 & T21 & T22 & T23 & FL0 & _ & CC).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xad794 W_ad744 r F_ad744 eq_refl D_ad744 T1 ltac:(clear - Hr1; lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|].
    split; [intros i Hi N N2; unfold PMBUK.Wret in N; change (ff_bytes 0) with 64 in N; change (64 / 8) with 8 in N; unfold SB in N; apply FRZ1; [exact Hi| clear - N2; lia| clear - N; lia| clear - N; lia| clear - N; lia]|].
    split; [eapply msteps_trans; [exact MS1| exact MSR]|]. split; [rewrite Z.mod_small by (clear - Hcn CNW; lia); exact CC|]. split; [exact FL0|].
    apply (regs_end R R0 R1 sp PEBENCNP.KS_bvnE1); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20| exact T21| exact T22| exact T23].
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
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_enc p X.
Hypothesis HBN : PESKA.spa_hb P (xhi + 1).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (e_end_value (XS 1)) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Lemma HFR : 96 = 96 \/ 96 = 128. Proof. left; reflexivity. Qed.
Lemma HSV : PEBEK.SV9 = PEBEK.SV9 \/ PEBEK.SV9 = PEBEK.SV11. Proof. left; reflexivity. Qed.
Lemma HNB : 0 <= 1. Proof. clear; lia. Qed.
Lemma CSK3 : In 3%nat CSK. Proof. inl. Qed.
Lemma CSK4 : In 4%nat CSK. Proof. inl. Qed.
Lemma CSKall j : In j CSK -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.

Local Notation K_vis_entry := (PEBEK.vis_entry L ar C HI LY HIok 96 HFR R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK SP32 A10).
Local Notation K_start := (PEBEK.start L ar C HI P LY HIok 96 PEBEK.SV9 HFR HSV fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 CPRE).
Local Notation K_vis_facts := (PEBEK.vis_facts L ar C HI P LY HIok 96 PEBEK.SV9 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32).
Local Notation K_g_facts := (PEBEK.g_facts L ar C HI LY HIok 96 PEBEK.SV9 HFR HSV R M model LBX FF LK Aw cr sp r fb s en k HH ENT FOK).
Local Notation K_inv_agree := (PEBEK.inv_agree L ar C HI P LY HIok 96 PEBEK.SV9 HFR HSV R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK).
Local Notation K_pbi_call := (PEBEK.pbi_call L ar C HI P LY HIok PO PBI 96 PEBEK.SV9 CSK HFR HSV CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 CPRE CRED).
Local Notation K_finish_ro := (PEBEK.finish_ro L ar C HI P LY HIok 96 1 PEBEK.SV9 HFR HSV R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS KONT).
Local Notation K_finish_bump := (PEBEK.finish_bump L ar C HI P LY HIok 96 1 PEBEK.SV9 HFR HSV R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS MP KONT).
Local Notation K_vis_facts_top := (PEBEK.vis_facts_top L ar C HI P LY HIok 96 PEBEK.SV9 HFR HSV R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE MP).
Local Notation INV := (PEBEK.inv L ar HI P 96 PEBEK.SV9 R M model LBX FF LK Aw cr sp fb xlo xhi s en k).

Lemma csk_after (R1 R2 : bvmap 5 word) : (forall j, In j CSK -> getr R1 (reg j) = getr R (reg j)) -> regs_preserved R1 R2 -> forall j, In j CSK -> getr R2 (reg j) = getr R (reg j).
Proof. intros Q RP j Hj. rewrite (L5SAR.cs_of_preserved R1 R2 j RP (CSKall j Hj)). exact (Q j Hj). Qed.

Theorem null_core : srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xad588 M model) K.
Proof.
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp.
  destruct K_vis_entry as (SF0 & E2 & E10 & E1 & _ & OVR). cbv beta in SF0.
  destruct (null_runA fx R (mrestrict (ahid Aw model) M) sp ltac:(clear - SLO SHI SPT; lia) E2 SF0) as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T19 & T20 & OWN1).
  apply (K_start 0xad588 0xad5e8 fx1 R1 M1v MS1 MG1 FRZ1 OWN1 T1 T2 ltac:(apply KS1; inl) ltac:(clear; lia) ltac:(reflexivity)).
  intros F fl LK2 M2 model2 R2 G APART INV2 RP2 G10 ZSH.

  pose proof (K_vis_facts F fl LK2 M2 model2 G APART M2 model2 LK2 Aw cr k 0 INV2) as VF2. cbv beta in VF2.
  destruct VF2 as (SF2 & FF2 & OWN2 & OF2 & VS2 & VFf2 & VSH2 & VFL2 & VOV2 & VOK2).
  pose proof OF2 as (OR & O8 & OBIG & _ & _ & _ & _ & _ & _ & U8 & KR & K8 & KO & _ & _ & _ & AvF & AvS & AvL & _).
  pose proof FF2 as (GF1 & _ & _ & _ & _ & _ & _ & _ & GL1 & _).
  assert (FF2' : PEBEK.ffacts 96 sp F fl (mrestrict (ahid Aw model2) M2) true).
  { destruct FF2 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & X8). split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|]. split; [exact ZSH| exact X8]. }
  pose proof (K_g_facts F fl LK2 M2 model2 G APART) as GF. cbv beta in GF. destruct GF as (_ & GF2 & GF3 & _ & GF8 & _).
  assert (R2c : forall j, In j L5SAR.cs_all -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
  destruct (null_runB fx1 R2 (mrestrict (ahid Aw model2) M2) sp (PMSPA.o_v AD fb) F fl ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR; lia) ltac:(clear - GF1; lia) ltac:(clear - GL1; lia)
             ltac:(rewrite (R2c 2%nat) by inl; exact T2) ltac:(rewrite (R2c 8%nat) by inl; exact T8) ltac:(rewrite (R2c 9%nat) by inl; exact T9) G10
             ltac:(rewrite (R2c 19%nat) by inl; rewrite T19, <- L5K.rl10; exact A10) ltac:(rewrite (R2c 20%nat) by inl; exact T20) SF2 FF2' ltac:(clear - OR; lia) O8 AvF AvL ltac:(clear - AvF O8 GF8; Lia.lia))
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & U1 & U10 & U11 & LR3 & UQ3 & USH3).
  pose proof INV2 as ((HH2 & AM2 & _) & _).
  set (W3 := fun a => (sp - 96 <= a < sp - 96 + 24) \/ ((F <= a < F + 24) \/ (F + 32 <= a < F + 32 + 8)) \/ (F / 8 + SBL <= a < F / 8 + SBL + 8)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 fx1 fx3 R2 0xad5e8 R3 PBIPC M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; exact X'| intros X'; apply Hn; right; left; left; exact X'| intros X'; apply Hn; right; left; right; exact X'| intros X'; apply Hn; right; right; exact X']. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar _ _ 0 0 F 0 (sp - 96 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar _ _ 0 0 F 0 (sp - 96 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
        unfold in_shadow_of, HeapIfaceA.S. unfold SB. clear - X' GF8. Lia.lia.
    - destruct Wa as [X'|[X'|X']]; unfold SB; clear - X' GF3 SLO SPT; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV F M3 md3 LK2 Aw cr k 0).
  { apply (K_inv_agree F fl LK2 M2 model2 G APART M2 M3 W3 model2 md3 LK2 cr Aw k 0 INV2 HH3 AM3 MRT3 MGM3); [| exact FR3].
    intros a [X'|[X'|X']]; [left; split; [clear - X'; lia| unfold PEBEK.ocell, PEBEK.SV9; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - X'; lia]
                         | right; left; clear - X'; lia | right; right; unfold SB; clear - X'; lia]. }
  refine (K_pbi_call F fl LK2 M2 model2 G APART 0 (F + 32) (sp - 96 + 23) (xhi + 1) 0xad694 fx3 R3 M3 md3 LK2 Aw cr k INV3 HBN ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
           ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) ltac:(clear; lia) ltac:(replace (F + 32) with ((F / 8 + 4) * 8) by (clear - GF8; lia); apply Z_mod_mult) _ _ U1 (proj1 LR3) U10 U11 _ _).
  { apply (proj1 (L5A.u64_at_vis (ahid Aw model2) M3 (F + 32) _ (L5A.avis_sub _ F 64 (F + 32) 8 VFf2 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))). rewrite VIS3. exact UQ3. }
  { replace ((F + 32) / 8 + SBL) with (F / 8 + 2147450884) by (clear - GF8; Lia.lia).
    apply (proj1 (L5A.u8_at_vis (ahid Aw model2) M3 (F / 8 + 2147450884) 0 (L5A.avis_sub _ (F / 8 + SB) 8 (F / 8 + 2147450884) 1 VSH2 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
             ltac:(clear - GF1; lia) ltac:(clear - GF2; unfold SB; lia))). rewrite VIS3. exact USH3. }
  { intros j Hj. rewrite (KS3 j) by (revert Hj; unfold CSK; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl).
    rewrite (R2c j (CSKall j Hj)). apply KS1. exact Hj. }

  intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 RP4 AG4.
  pose proof (K_vis_facts F fl LK2 M2 model2 G APART M4 md4 LK4 Aw4 cr4 k4 1 INV4) as VF4. cbv beta in VF4.
  destruct VF4 as (SF4 & FF4 & OWN4 & OF4 & _).
  pose proof OF4 as (OR4 & O84 & OBIG4 & Zov4 & OWR4 & ODJ4 & Z84 & Z244 & Z324 & U84 & _ & _ & _ & U24 & U32 & EB & AvF4 & AvS4 & AvL4 & _).
  pose proof FF4 as (_ & _ & _ & _ & _ & _ & _ & _ & GL14 & _).
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (_ & _ & _ & _ & _ & Lestk & _). cbn [s_estk X] in Lestk.
  assert (LR4 : lregs R4 sp F (PMSPA.o_v AD fb)).
  { destruct LR3 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y22). unfold lregs.
    repeat split; first [ rewrite (L5SAR.cs_of_preserved R3 R4 2 RP4) by inl; exact Y2 | rewrite (L5SAR.cs_of_preserved R3 R4 8 RP4) by inl; exact Y8
                        | rewrite (L5SAR.cs_of_preserved R3 R4 9 RP4) by inl; exact Y9 | rewrite (L5SAR.cs_of_preserved R3 R4 18 RP4) by inl; exact Y18
                        | rewrite (L5SAR.cs_of_preserved R3 R4 19 RP4) by inl; exact Y19 | rewrite (L5SAR.cs_of_preserved R3 R4 20 RP4) by inl; exact Y20
                        | rewrite (L5SAR.cs_of_preserved R3 R4 21 RP4) by inl; exact Y21 | rewrite (L5SAR.cs_of_preserved R3 R4 22 RP4) by inl; exact Y22 ]. }
  assert (QCS4 : forall j, In j CSK -> getr R4 (reg j) = getr R (reg j)).
  { apply (csk_after R3 R4); [| exact RP4]. intros j Hj. rewrite (KS3 j) by (revert Hj; unfold CSK; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl).
    rewrite (R2c j (CSKall j Hj)). apply KS1. exact Hj. }
  unfold PMSPA.cfg.
  destruct xestk as [|e1 rr] eqn:HXS.
  - rewrite Lestk in U32. cbn [rev length Z.of_nat Z.mul] in U32. rewrite Z.add_0_r in U32.
    destruct (null_runE0 fx4 R4 R (mrestrict (ahid Aw4 md4) M4) sp (PMSPA.o_v AD fb) F fl (PEC.en_b en) r ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR4; lia) ltac:(clear - GF1; lia) ltac:(clear - GL14; lia) ltac:(clear - EB; lia)
               LR4 SF4 FF4 ltac:(unfold ovfacts; repeat split; first [assumption | clear - OR4; lia | clear - EB; lia | clear - AvF4 O84 GF8; Lia.lia]) OWN4 Rra Rsp RAok QCS4)
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & FL5 & RP5).
    exact (PEBEK.finish_ro L ar C HI P LY HIok 96 1 PEBEK.SV9 HFR HSV R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec [] xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS KONT F fl LK2 M2 model2 G APART 0xad694 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 fx5 R5 M5v INV4 eq_refl MS5 MG5 FRZ5 FL5 RP5).
  - pose proof (PEBEK.vis_facts_top L ar C HI P LY HIok 96 PEBEK.SV9 HFR HSV R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE MP F fl LK2 M2 model2 G APART M4 md4 LK4 Aw4 cr4 k4 1 e1 rr INV4 eq_refl) as VT. cbv beta in VT.
    destruct VT as (HLEN & EKP & EB1 & ED2 & ALend & ED3 & WR24 & EB6 & ZC & EDS & OVA & TCv & E1C & E1OK & BINe & EDC & EBC & EDF & EDSH & EDFL & EDV).
    rewrite HLEN in U32. set (ed := PEC.en_b en + 24 * (Z.of_nat (length rr) + 1)) in *.
    destruct (null_runE1 fx4 R4 R (mrestrict (ahid Aw4 md4) M4) sp (PMSPA.o_v AD fb) F fl (PEC.en_b en) ed (ei_cnt e1) r ltac:(clear - SLO SHI SPT; lia) ltac:(clear - OR4; lia) ltac:(clear - GF1; lia) ltac:(clear - GL14; lia)
               ltac:(clear - EB; lia) ltac:(clear - EB1 ED2 ED3; lia) E1C LR4 SF4 FF4 ltac:(unfold ovfacts; repeat split; first [assumption | clear - OR4; lia | clear - EB EB1; lia | clear - ED2; lia | clear - AvF4 O84 GF8; Lia.lia])
               EB1 ltac:(clear - EB1 ED3; lia) ALend ED3 WR24 EB6 ZC EDS OVA EDF EDFL ltac:(clear - EDF ALend GF8; Lia.lia) TCv OWN4 Rra Rsp RAok QCS4)
      as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & CC5 & FL5 & RP5).
    exact (PEBEK.finish_bump L ar C HI P LY HIok 96 1 PEBEK.SV9 HFR HSV R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e HH ENT FOK CPRE INCS MP KONT F fl LK2 M2 model2 G APART 0xad694 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 fx5 R5 M5v e1 rr INV4 eq_refl MS5 MG5 FRZ5 CC5 FL5 RP5).
Qed.
End Call.

Theorem v_null_ok : PECSB.v_null_spec L ar HI P.
Proof.
  unfold PECSB.v_null_spec, PECSPA.v_null_spec, PECSPA.eslot_spec. cbn [pe_null EE PeCLayoutB.EADDR_B].
  intros PMODE [] fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 _ CPRE INCS POK MP NB HB CRED KONT.
  destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad].
  assert (ESC : e_scalar 1 1 (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad)
          = e_end_value (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + 1) (xhi + 1) xbad)) by reflexivity.
  rewrite ESC in HB, KONT. rewrite eev_hi in HB. cbn [s_hi] in HB.
  exact (null_core PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
           HH AM K0 ENT FRM FRS FOK SP32 A10 CPRE INCS MP HB CRED KONT).
Qed.
End WithHeap.
End PEBENCN.
