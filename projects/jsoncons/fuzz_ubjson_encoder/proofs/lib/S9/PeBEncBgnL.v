(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5CoreSpecsAB0S9 L5StepARB0S9 L5CoreBRB0S9 L5ADetailHRB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PnStatics PmModelFactsA PmStep PeStepAB0 PmParStep PmParKit PeBSrcKit PeBParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeShZ PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrameA PeEncKit PeBCReset1 PeCEPushSpecsA PeBEmbKitJ PeBEncKitG PeBEncBgnP1 PeBEncBgnP2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_ad338_ad33c Eb0_code_aca64_aca68 Eb0_code_aba40_aba44 Eb0_code_acc50_acc54.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENCBL.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).
Abbreviation SBL := 2147450880.
Abbreviation ECONE := 0xb4078.
Abbreviation ESLOW := 0xb417c.
Abbreviation ECONQ := 0xb04f4.
Abbreviation ESLOQ := 0xb0648.
Abbreviation PBPC := 0xb120c.
Abbreviation MKPC := 0xafda8.
Abbreviation PLPC := 0xafe84.

Definition CSKb : list nat := [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.

Lemma u64_same_bytes (M1 M2 : word -> option byte) a v :
  L5.defined M1 a 8 -> L5.defined M2 a 8 -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M2 a v ->
  forall i, 0 <= i < 8 -> M2 (Z_to_bv 64 (a + i)) = M1 (Z_to_bv 64 (a + i)).
Proof.
  intros D1 D2 U1 U2 i Hi. unfold L5.u64_at in U1, U2. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (PMBEK.rdn_nth RSEGS M2 8 a _ U2 (Z.to_nat i) ltac:(lia) ltac:(apply D2; lia)).
  rewrite (PMBEK.rdn_nth RSEGS M1 8 a _ U1 (Z.to_nat i) ltac:(lia) ltac:(apply D1; lia)). reflexivity.
Qed.

Lemma z1_of_z7 (M : word -> option byte) ov c : L5KA.zeros_at M (ov / 8 + SBL) 7 -> ov mod 8 = 0 -> 0 <= c <= 48 -> c mod 8 = 0 -> L5KA.zeros_at M ((ov + c) / 8 + SBL) 1.
Proof. intros Z7 O8 Hc C8 i Hi. replace ((ov + c) / 8 + SBL + i) with (ov / 8 + SBL + (c / 8 + i)) by lia. apply Z7. lia. Qed.

Definition sfacts (FR sp : Z) (M : word -> option byte) : Prop :=
  L5.img_clear M 1273856 1306624 /\ L5.u64_at RSEGS M 1335544 SBL /\ L5.u32_at RSEGS M 1335552 1
  /\ 140735332487168 + 20480 <= sp <= 140737488355328 /\ sp mod 16 = 0 /\ L5.writable RSEGS M (sp - FR) FR.
Definition efacts (FR sp ov osk : Z) (M : word -> option byte) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5.writable RSEGS M ov 56 /\ ((sp - FR) + FR <= ov \/ ov + 56 <= (sp - FR))
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 16) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 40) / 8 + SBL) 1
  /\ L5KA.zeros_at M ((ov + 48) / 8 + SBL) 1
  /\ L5.u64_at RSEGS M (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0 /\ L5.u32_at RSEGS M (ov + 16) MAX_DEPTH.

Definition lregs (R : bvmap 5 word) (sp ov : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 80) /\ getr R (reg 8) = Z_to_bv 64 ov /\ getr R (reg 9) = Z_to_bv 64 (ov + 32) /\ getr R (reg 18) = Z_to_bv 64 SBL
  /\ getr R (reg 19) = Z_to_bv 64 ((ov + 32) / 8 + SBL).
Definition lregs2 (R : bvmap 5 word) (sp ov : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 80) /\ getr R (reg 8) = Z_to_bv 64 ov /\ getr R (reg 9) = Z_to_bv 64 (ov + 8) /\ getr R (reg 18) = Z_to_bv 64 ((ov + 8) / 8 + SBL)
  /\ getr R (reg 19) = Z_to_bv 64 ((ov + 32) / 8 + SBL).

Definition saved (M : word -> option byte) (R : bvmap 5 word) (sp r : Z) : Prop :=
  L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R (reg 20))) /\ L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M (sp - 8) r.

Definition runAc (E0 ECRA KD : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk d r e c n : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= d < 2 ^ 64 -> 0 <= r < 2 ^ 64 -> 0 <= e < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= n <= 16777216 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 ov -> getr R (reg 1) = Z_to_bv 64 r -> getr R (reg 11) = Z_to_bv 64 n ->
    sfacts 80 sp M -> efacts 80 sp ov osk M -> L5.u32_at RSEGS M (ov + 48) d -> 0 <= d <= 1023 ->
    L5.u64_at RSEGS M (ov + 32) e -> L5.u64_at RSEGS M (ov + 40) c -> 4096 <= e <= 140737488355304 -> e mod 8 = 0 -> 4096 <= c <= 140737488355328 -> c mod 8 = 0 -> e < c ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R E0 M) (mst fx' R' ECONQ M')
      /\ (forall j, In j CSKb -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 ECRA /\ lregs R' sp ov /\ getr R' (reg 10) = Z_to_bv 64 (ov + 24) /\ getr R' (reg 11) = Z_to_bv 64 (sp - 68) /\ getr R' (reg 12) = Z_to_bv 64 (sp - 64)
      /\ getr R' (reg 20) = Z_to_bv 64 e
      /\ L5.u32_at RSEGS M' (sp - 68) KD /\ L5.u32_at RSEGS M' (ov + 48) (d + 1) /\ L5.u64_at RSEGS M' (sp - 64) n /\ saved M' R sp r.

Definition runAs (E0 JOIN KD : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk d r e n : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= d < 2 ^ 64 -> 0 <= r < 2 ^ 64 -> 0 <= e < 2 ^ 64 -> 0 <= n <= 16777216 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 ov -> getr R (reg 1) = Z_to_bv 64 r -> getr R (reg 11) = Z_to_bv 64 n ->
    sfacts 80 sp M -> efacts 80 sp ov osk M -> L5.u32_at RSEGS M (ov + 48) d -> 0 <= d <= 1023 ->
    L5.u64_at RSEGS M (ov + 32) e -> L5.u64_at RSEGS M (ov + 40) e -> 0 <= e <= 140737488355328 -> e mod 8 = 0 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R E0 M) (mst fx' R' ESLOQ M')
      /\ (forall j, In j CSKb -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 JOIN /\ lregs R' sp ov /\ getr R' (reg 10) = Z_to_bv 64 (ov + 24) /\ getr R' (reg 11) = Z_to_bv 64 (sp - 68) /\ getr R' (reg 12) = Z_to_bv 64 (sp - 64)
      /\ getr R' (reg 20) = Z_to_bv 64 e
      /\ L5.u32_at RSEGS M' (sp - 68) KD /\ L5.u32_at RSEGS M' (ov + 48) (d + 1) /\ L5.u64_at RSEGS M' (sp - 64) n /\ saved M' R sp r.

Definition runE (E0 MKRA : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk oec r n : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= r < 2 ^ 64 -> 0 <= n <= 16777216 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 ov -> getr R (reg 14) = Z_to_bv 64 oec -> getr R (reg 1) = Z_to_bv 64 r -> getr R (reg 11) = Z_to_bv 64 n ->
    sfacts 80 sp M -> efacts 80 sp ov osk M -> L5.u32_at RSEGS M (ov + 48) 1024 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (ov + 48 <= i < ov + 52) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R E0 M) (mst fx' R' MKPC M')
      /\ (forall j, In j CSKb -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 MKRA /\ getr R' (reg 2) = Z_to_bv 64 (sp - 80) /\ getr R' (reg 8) = Z_to_bv 64 ov /\ getr R' (reg 18) = Z_to_bv 64 SBL
      /\ getr R' (reg 10) = Z_to_bv 64 oec /\ getr R' (reg 11) = Z_to_bv 64 11
      /\ L5.u32_at RSEGS M' (ov + 48) 1025 /\ L5.u64_at RSEGS M' (sp - 64) n /\ saved M' R sp r.

Definition runPj (ECRA JOIN : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp e : Z),
    0 <= sp < 2 ^ 64 -> 0 <= e < 2 ^ 64 -> getr R (reg 2) = Z_to_bv 64 (sp - 80) -> getr R (reg 20) = Z_to_bv 64 e -> 4096 <= e <= 140737488355304 -> e mod 8 = 0 ->
    sfacts 80 sp M ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R ECRA M) (mst fx' R' JOIN M')
      /\ (forall j, In j CSKb -> getr R' (reg j) = getr R (reg j)) /\ (forall j, In j [2; 8; 9; 18; 19]%nat -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 10) = Z_to_bv 64 (e + 24).

Definition runP (JOIN PBRA MK : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk it : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= it < 2 ^ 64 ->
    lregs R sp ov -> getr R (reg 10) = Z_to_bv 64 (it + 24) -> 4096 <= it <= 140737488355304 -> it mod 8 = 0 -> sfacts 80 sp M -> efacts 80 sp ov osk M ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (ov + 32 <= i < ov + 32 + 8) -> ~ (sp - 50 <= i < sp - 50 + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R JOIN M) (mst fx' R' PBPC M')
      /\ (forall j, In j CSKb -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 PBRA /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp - 50)
      /\ lregs2 R' sp ov /\ L5.u8_at RSEGS M' (sp - 50) MK /\ L5.u64_at RSEGS M' (ov + 32) (it + 24).

Definition runP2 (RA2 PBRA2 : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 ->
    lregs2 R sp ov -> sfacts 80 sp M -> efacts 80 sp ov osk M ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 49 <= i < sp - 49 + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R RA2 M) (mst fx' R' PBPC M')
      /\ (forall j, In j CSKb -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 PBRA2 /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp - 49)
      /\ lregs2 R' sp ov /\ L5.u8_at RSEGS M' (sp - 49) 35.

Definition runL (RA3 PLRA : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk n : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= n <= 16777216 ->
    lregs2 R sp ov -> sfacts 80 sp M -> efacts 80 sp ov osk M -> L5.u64_at RSEGS M (sp - 64) n ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R RA3 M) (mst fx' R' PLPC M')
      /\ (forall j, In j CSKb -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 PLRA /\ getr R' (reg 10) = Z_to_bv 64 ov /\ getr R' (reg 11) = Z_to_bv 64 n
      /\ lregs2 R' sp ov.

Definition runR (RPC : Z) : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp r : Z),
    0 <= sp < 2 ^ 64 -> getr R (reg 2) = Z_to_bv 64 (sp - 80) -> sfacts 80 sp M -> saved M R0 sp r ->
    getr R0 (reg 1) = Z_to_bv 64 r -> getr R0 (reg 2) = Z_to_bv 64 sp -> L5.ra_ok r -> (forall j, In j CSKb -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R RPC M) (mst fx' R' r M')
      /\ getr R' (reg 10) = Z_to_bv 64 1 /\ regs_preserved R0 R'.

Ltac gks KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEBBGNP1.aligned; assumption | unfold PEBBGNP2.aligned; assumption | apply wid | apply wrng | L5SAR.greg | L5SAR.gmem | lia]).
Ltac greg1 KS :=
  first [ assumption
        | lazymatch goal with |- getr ?R1 (reg ?n) = _ =>
            first [ lazymatch goal with H : getr R1 (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end
                  | rewrite (KS n) by inl; lazymatch goal with H : getr _ (reg n) = _ |- _ => rewrite H; first [reflexivity | f_equal; lia] end ] end ].

Ltac midV R sp ov n oec osk d r e c it R0 :=
  constr:(fun j : nat => match j with 2%nat => sp | 10%nat => ov | 11%nat => n | 13%nat => oec | 14%nat => oec | 41%nat => osk | 43%nat => d | 44%nat => e | 45%nat => c | 46%nat => it | 64%nat => r
     | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9)) | 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19))
     | 69%nat => bv_unsigned (getr R0 (reg 20))
     | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end).

Ltac fin_tac KS Hr G1 :=
  repeat split; first [greg1 KS | assumption | rewrite G1, L5.unsigned_lit by (clear - Hr; lia); assumption
                      | lazymatch goal with |- L5.u64_at _ _ _ ?r => lazymatch goal with H : L5.u64_at _ _ (?sp - 8) _ |- _ => rewrite G1, (L5.unsigned_lit r) in H by (clear - Hr; lia); exact H end end ].
Ltac runAc_tac CONC :=
  intros fx R M sp ov osk d r e c n Hsp Hov Hosk Hd Hr He Hc Hn G2 G10 G1 G11 SF EF U48 HD U32 U40 RE E8 RC C8 LT;
  unfold sfacts in SF; decompose [and] SF; unfold efacts in EF; decompose [and] EF;
  let V := midV R sp ov n 0 osk d r e c 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P;
  rewrite G10 in P; rewrite !(L5.unsigned_lit ov) in P by (clear - Hov; lia); rewrite G11 in P; rewrite !(L5.unsigned_lit n) in P by (clear - Hn; lia);
  feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs, saved; fin_tac KS Hr G1.
Lemma u_runAc_l : runAc 0xab900 0xab9c4 2. Proof. runAc_tac PEBBGNP2.bqBlAc_conc. Qed.
Lemma u_runAc_m : runAc 0xacb14 0xacbd4 0. Proof. runAc_tac PEBBGNP2.bqBmAc_conc. Qed.
Ltac runAs_tac CONC :=
  intros fx R M sp ov osk d r e n Hsp Hov Hosk Hd Hr He Hn G2 G10 G1 G11 SF EF U48 HD U32 U40 RE E8;
  unfold sfacts in SF; decompose [and] SF; unfold efacts in EF; decompose [and] EF;
  let V := midV R sp ov n 0 osk d r e e 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P;
  rewrite G10 in P; rewrite !(L5.unsigned_lit ov) in P by (clear - Hov; lia); rewrite G11 in P; rewrite !(L5.unsigned_lit n) in P by (clear - Hn; lia);
  feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs, saved; fin_tac KS Hr G1.
Lemma u_runAs_l : runAs 0xab900 0xab9e4 2. Proof. runAs_tac PEBBGNP2.bqBlAs_conc. Qed.
Lemma u_runAs_m : runAs 0xacb14 0xacbf4 0. Proof. runAs_tac PEBBGNP2.bqBmAs_conc. Qed.

Ltac runE_tac CONC :=
  intros fx R M sp ov osk oec r n Hsp Hov Hosk Hoec Hr Hn G2 G10 G14 G1 G11 SF EF U48;
  unfold sfacts in SF; decompose [and] SF; unfold efacts in EF; decompose [and] EF;
  let V := midV R sp ov n oec osk 1024 r 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P;
  rewrite G10 in P; rewrite !(L5.unsigned_lit ov) in P by (clear - Hov; lia); rewrite G11 in P; rewrite !(L5.unsigned_lit n) in P by (clear - Hn; lia);
  feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia]|];
  split; [exact MS1|]; rewrite G14 in P; decompose [and] P; split; [gks KS|]; unfold saved; fin_tac KS Hr G1.
Lemma u_runE_l : runE 0xab900 0xabaa0. Proof. runE_tac PEBBGNP2.bqBlE_conc. Qed.
Lemma u_runE_m : runE 0xacb14 0xaccb0. Proof. runE_tac PEBBGNP2.bqBmE_conc. Qed.

Ltac runPj_tac CONC :=
  intros fx R M sp e Hsp He G2 G20 RE E8 SF;
  unfold sfacts in SF; decompose [and] SF;
  let V := midV R sp 0 0 0 0 0 0 e 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi; apply FRZ1; exact Hi|];
  split; [exact MS1|]; split; [gks KS|]; split; [gks KS| exact P].
Lemma u_runPj_l : runPj 0xab9c4 0xab9e4. Proof. runPj_tac PEBBGNP2.bqBlPj_conc. Qed.
Lemma u_runPj_m : runPj 0xacbd4 0xacbf4. Proof. runPj_tac PEBBGNP2.bqBmPj_conc. Qed.

Ltac runP_tac CONC :=
  intros fx R M sp ov osk it Hsp Hov Hosk Hit (G2 & G8 & G9 & G18 & G19) G10 RI I8 SF EF;
  unfold sfacts in SF; decompose [and] SF; unfold efacts in EF; decompose [and] EF;
  let V := midV R sp ov 0 0 osk 0 0 0 0 it R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| clear - N1; lia| clear - N2; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs2; repeat split; first [greg1 KS | assumption].
Lemma u_runP_l : runP 0xab9e4 0xaba3c 91. Proof. runP_tac PEBBGNP2.bqBlP_conc. Qed.
Lemma u_runP_m : runP 0xacbf4 0xacc4c 123. Proof. runP_tac PEBBGNP2.bqBmP_conc. Qed.
Ltac runP2_tac CONC :=
  intros fx R M sp ov osk Hsp Hov Hosk (G2 & G8 & G9 & G18 & G19) SF EF;
  unfold sfacts in SF; decompose [and] SF; unfold efacts in EF; decompose [and] EF;
  let V := midV R sp ov 0 0 osk 0 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi N1; apply FRZ1; [exact Hi| clear - N1; lia]|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs2; repeat split; first [greg1 KS | assumption].
Lemma u_runP2_l : runP2 0xaba3c 0xaba64. Proof. runP2_tac PEBBGNP2.bqBlP2_conc. Qed.
Lemma u_runP2_m : runP2 0xacc4c 0xacc74. Proof. runP2_tac PEBBGNP2.bqBmP2_conc. Qed.
Ltac runL_tac CONC :=
  intros fx R M sp ov osk n Hsp Hov Hosk Hn (G2 & G8 & G9 & G18 & G19) SF EF U64n;
  unfold sfacts in SF; decompose [and] SF; unfold efacts in EF; decompose [and] EF;
  let V := midV R sp ov n 0 osk 0 0 0 0 0 R in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & P);
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi; apply FRZ1; exact Hi|];
  split; [exact MS1|]; decompose [and] P; split; [gks KS|]; unfold lregs2; repeat split; first [greg1 KS | assumption].
Lemma u_runL_l : runL 0xaba64 0xaba70. Proof. runL_tac PEBBGNP2.bqBlL_conc. Qed.
Lemma u_runL_m : runL 0xacc74 0xacc80. Proof. runL_tac PEBBGNP2.bqBmL_conc. Qed.

Lemma regs_end (R R0 R3 : bvmap 5 word) (sp : Z) :
  (forall j, In j CSKb -> getr R3 (reg j) = getr R (reg j)) -> (forall j, In j CSKb -> getr R (reg j) = getr R0 (reg j)) ->
  getr R0 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 1) = getr R0 (reg 1) ->
  getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> regs_preserved R0 R3.
Proof.
  intros KS3 QCS Rsp T2 T1 T8 T9 T18 T19 T20. apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
  repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8; apply Z_to_bv_bv_unsigned | rewrite T9; apply Z_to_bv_bv_unsigned
                                          | rewrite T18; apply Z_to_bv_bv_unsigned | rewrite T19; apply Z_to_bv_bv_unsigned | rewrite T20; apply Z_to_bv_bv_unsigned
                                          | rewrite (KS3 _) by inl; apply QCS; inl ] |]). destruct Hj.
Qed.

Ltac runR_tac CONC RET Wr Fr Dr :=
  intros fx R R0 M sp r Hsp G2 SF (S48 & S40 & S32 & S24 & S16 & S8) Hra R0sp RA QCS;
  unfold sfacts in SF; decompose [and] SF; pose proof RA as (Hr1 & Hr2);
  let V := midV R sp 0 0 0 0 0 r 0 0 0 R0 in
  let P := fresh "P" in pose proof (CONC fx R M V) as P; cbn beta iota in P; feedP P;
  let KS := fresh "KS" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS & T1 & T2 & T8 & T9 & T10 & T18 & T19 & T20);
  let MSR := fresh "MSR" in
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 RET Wr _ Fr eq_refl Dr T1 ltac:(clear - Hr1; lia) Hr2) as MSR;
  exists fx1, R1, M1; split; [exact MG1|];
  split; [intros i Hi; apply FRZ1; exact Hi|];
  split; [eapply msteps_trans; [exact MS1| exact MSR]|]; split; [exact T10|];
  apply (regs_end R R0 R1 sp); [gks KS| exact QCS| exact R0sp| exact T2| rewrite T1, Hra; reflexivity| exact T8| exact T9| exact T18| exact T19| exact T20].
Lemma u_runR_l : runR 0xaba70. Proof. runR_tac PEBBGNP2.bqBlR_conc 0xaba90 W_aba40 F_aba40 D_aba40. Qed.
Lemma u_runR_m : runR 0xacc80. Proof. runR_tac PEBBGNP2.bqBmR_conc 0xacca0 W_acc50 F_acc50 D_acc50. Qed.
Lemma u_runX_l : runR 0xabaa0. Proof. runR_tac PEBBGNP2.bqBlX_conc 0xaba90 W_aba40 F_aba40 D_aba40. Qed.
Lemma u_runX_m : runR 0xaccb0. Proof. runR_tac PEBBGNP2.bqBmX_conc 0xacca0 W_acc50 F_acc50 D_acc50. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMB.ly_as0 L C LY.
Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Hypothesis MKEC : PECSB.make_ec_spec L ar HI.
Hypothesis PUTL : PECSB.put_length_spec L ar HI P.
Hypothesis ECK : PECEPX.econe_kl_spec RSEGS AD EE L ar HI.
Hypothesis ESK : PECEPX.eslow_kl_spec RSEGS AD EE L ar HI.

Section Slot.
Variables (E0 ECRA JOIN PBRA PBRA2 PLRA MKRA KD MK : Z).
Hypothesis RAS : L5.ra_ok ECRA /\ L5.ra_ok JOIN /\ L5.ra_ok PBRA /\ L5.ra_ok PBRA2 /\ L5.ra_ok PLRA /\ L5.ra_ok MKRA.
Hypothesis HKD : 0 <= KD <= 3.
Hypothesis HMK : 0 <= MK <= 255.
Hypothesis RUNAC : runAc E0 ECRA KD.
Hypothesis RUNAS : runAs E0 JOIN KD.
Hypothesis RUNE : runE E0 MKRA.
Hypothesis RUNPJ : runPj ECRA JOIN.
Hypothesis RUNP : runP JOIN PBRA MK.
Hypothesis RUNP2 : runP2 PBRA PBRA2.
Hypothesis RUNL : runL PBRA2 PLRA.
Hypothesis RUNR : runR PLRA.
Hypothesis RUNX : runR MKRA.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z).
Variable (n : Z).
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
Hypothesis HN : 0 <= n <= UbjRef.MAX_ITEMS.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 n.
Hypothesis A14 : getr R (reg 14) = Z_to_bv 64 (PMSPA.o_ec AD fb).
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_encb p X.
Hypothesis NBAD : s_bad (e_begin_len KD n X) = false.
Hypothesis HB : PESKA.spa_hb P (s_hi (e_begin_len KD n X)).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (e_begin_len KD n X) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Definition FC (Mx : word -> option byte) : Prop := saved Mx R sp r /\ L5.u64_at RSEGS Mx (sp - 64) n.
Lemma FC_frame M1 M2 : (forall a, sp - 80 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros AG ((C48 & C40 & C32 & C24 & C16 & C8) & UN). pose proof ENT as (_ & _ & _ & _ & _ & ASTK & _). change (PMSPA.pm_scr 4) with 20480 in ASTK. pose proof ASTK as (_ & SLO & SHI & SPT & _).
  assert (SV : forall a0 w, sp - 80 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; clear - Hi H1 H2; lia| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC, saved. repeat split; (apply SV; [clear; lia| clear; lia| assumption]).
Qed.

Lemma FC_but M1 M2 lo hi : sp - 56 <= lo -> hi <= sp - 48 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros Hlo Hhi AG ((C48 & C40 & C32 & C24 & C16 & C8) & UN). pose proof ENT as (_ & _ & _ & _ & _ & ASTK & _). change (PMSPA.pm_scr 4) with 20480 in ASTK. pose proof ASTK as (_ & SLO & SHI & SPT & _).
  assert (SV : forall a0 w, sp - 80 <= a0 -> a0 + 8 <= sp -> (a0 + 8 <= lo \/ hi <= a0) -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 H3 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; [clear - Hi H1 H2 SLO SHI SPT; lia| clear - Hi H3; lia]| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC, saved. repeat split; (apply SV; [clear; lia| clear; lia| clear - Hlo Hhi; lia| assumption]).
Qed.
Lemma HFR : 80 = 32 \/ 80 = 64 \/ 80 = 80 \/ 80 = 96. Proof. right; right; left; reflexivity. Qed.
Lemma HNB : 0 <= 2 + pl_size n. Proof. pose proof (pl_size_pos n). lia. Qed.
Lemma CSK3 : In 3%nat CSKb. Proof. inl. Qed.
Lemma CSK4 : In 4%nat CSKb. Proof. inl. Qed.
Lemma CSKall j : In j CSKb -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.
Lemma MPE : PECSPA.mp_enc p X. Proof. exact (proj1 MP). Qed.

Lemma pre_facts : Forall ei_ok xestk /\ 0 <= xedepth <= MAX_DEPTH /\ Z.of_nat (length xestk) <= MAX_DEPTH /\ PEC.en_stk en = rev xestk /\ PEC.en_depth en = xedepth /\ xbad = false /\ xlo <= xhi.
Proof.
  destruct MP as ((LOHI & BADX & FA & ED) & ELEN). cbn [s_lo s_hi s_bad s_estk s_edepth X] in LOHI, BADX, FA, ED, ELEN.
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (_ & _ & _ & _ & _ & Lestk & Ledepth & _). cbn [s_estk s_edepth X] in Lestk, Ledepth.
  split; [exact FA|]. split; [exact ED|]. split; [exact ELEN|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact BADX| exact LOHI].
Qed.

Lemma XF_err : xedepth = MAX_DEPTH -> e_begin_len KD n X = ST xstk xpos xmore xdone xhalt xdepth true xestk (xedepth + 1) (xlo + 0) (xhi + 0) xbad.
Proof.
  intros E. unfold e_begin_len. cbv zeta. cbn [s_edepth w_edepth X]. replace (MAX_DEPTH <? xedepth + 1) with true by (symmetry; apply Z.ltb_lt; rewrite E; unfold MAX_DEPTH; clear; lia).
  unfold X, w_ec, w_edepth. cbn [s_stk s_pos s_more s_done s_halt s_depth s_ec s_estk s_edepth s_lo s_hi s_bad]. rewrite !Z.add_0_r. reflexivity.
Qed.
Lemma XF_ok : xedepth + 1 <= MAX_DEPTH -> e_begin_len KD n X = ST xstk xpos xmore xdone xhalt xdepth xec (EI KD n 0 :: xestk) (xedepth + 1) (xlo + (2 + pl_size n)) (xhi + (2 + pl_size n)) xbad.
Proof.
  intros E. unfold e_begin_len. cbv zeta. cbn [s_edepth w_edepth X]. replace (MAX_DEPTH <? xedepth + 1) with false by (symmetry; apply Z.ltb_ge; exact E).
  unfold e_put_length. replace (INT64_MAX <? n) with false by (symmetry; apply Z.ltb_ge; unfold INT64_MAX; clear - HN; unfold MAX_ITEMS in HN; lia).
  unfold X, w_out, w_estk, w_edepth. cbn [s_stk s_pos s_more s_done s_halt s_depth s_ec s_estk s_edepth s_lo s_hi s_bad]. f_equal; clear; lia.
Qed.

#[local] Abbreviation K_pl := (PEBEKG.pl_call L ar C HI P LY HIok PUTL 80 CSKb HFR CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 FC FC_frame CPRE INCS POK CRED).
#[local] Abbreviation K_vis_entry := (PEBEKG.vis_entry L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 A10 CPRE).
#[local] Abbreviation K_startw := (PEBEKG.inv_startw L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 FC CPRE).
#[local] Abbreviation K_vis := (PEBEKG.vis_facts L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC).
#[local] Abbreviation K_frame := (PEBEKG.inv_frame L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC).
#[local] Abbreviation K_econe := (PEBEKG.econe_call L ar C HI P LY HIok 80 CSKb HFR CSK3 CSK4 R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRS FOK SP32 FC FC_frame CPRE INCS).
#[local] Abbreviation K_eslow := (PEBEKG.eslow_call L ar C HI P LY HIok PO 80 CSKb HFR CSK3 CSK4 R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRS FOK SP32 FC FC_frame (e_begin_len KD n X) CPRE INCS CRED KONT).
#[local] Abbreviation K_pb := (PEBEKG.pb_call L ar C HI P LY HIok PO PB 80 CSKb HFR CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb xlo xhi s en k HH K0 ENT FRM FRS FOK SP32 FC FC_frame CRED).
#[local] Abbreviation K_mkec := (PEBEKG.mkec_call L ar C HI P LY HIok MKEC 80 CSKb HFR CSK3 CSK4 R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH K0 ENT FRM FRS FOK SP32 FC FC_frame (e_begin_len KD n X) CPRE INCS MPE KONT).
#[local] Abbreviation K_fro := (PEBEKG.finish_ro L ar C HI P LY HIok 80 HFR R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK FC (e_begin_len KD n X) CPRE INCS KONT).
#[local] Abbreviation K_ferr := (PEBEKG.finish_err L ar C HI P LY HIok 80 HFR R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK FC (e_begin_len KD n X) CPRE INCS KONT).
#[local] Abbreviation INV := (PEBEKG.inv L ar HI P M model LBX FF LK Aw cr sp fb xlo xhi s en k FC).

Local Ltac entry0 :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH; pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp;
  pose proof FOK as ((rs & Hfb) & Fal);
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _);
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6); cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6; change (ff_bytes 5) with 2048 in F1, F2, F3, F4, F5, F6;
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP; unfold FS_BYTES in F1, F2, F3, F4, F5, F6, FSAPP, FSCEIL, FSIMG; rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.

Lemma join_tail (fxq : FPState) Rq Mq mdq LKq Awq crq kq bq cq (it : Z) :
  xedepth + 1 <= MAX_DEPTH -> PEC.en_stk en = rev xestk -> Forall ei_ok xestk -> xbad = false -> xlo <= xhi -> 0 <= xedepth ->
  INV Mq mdq LKq Awq crq kq 0 (PEC.ENC bq cq (rev xestk ++ [EI KD n 0]) (xedepth + 1)) ->
  lregs Rq sp (PMSPA.o_v AD fb) -> (forall j, In j CSKb -> getr Rq (reg j) = getr R (reg j)) ->
  getr Rq (reg 10) = Z_to_bv 64 (it + 24) -> 4096 <= it <= 140737488355304 -> it mod 8 = 0 -> bq + 24 * (Z.of_nat (length xestk) + 1) = it + 24 ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq JOIN Mq mdq) K.
Proof.
  intros DOK HSTK FA HBADX LOHI ED0 INVq LRq QCSq A10q ITR IT8 HIT. entry0. pose proof (pl_size_pos n) as PLS.
  assert (HN24 : 0 <= n <= 16777216) by (clear - HN; unfold MAX_ITEMS in HN; lia).
  set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  assert (Eov : ov = fb + 496) by reflexivity.
  assert (AOV : PMSPA.aobjA FF ov 56) by (apply (PEBEKG.AOF FF fb FOK); clear - Eov; lia).
  set (en2 := PEC.ENC bq cq (rev xestk ++ [EI KD n 0]) (xedepth + 1)) in *.
  pose proof (K_vis Mq mdq LKq Awq crq kq 0 en2 INVq) as VFq. cbv beta in VFq.
  destruct VFq as (ICq & CSBq & CUARq & SPR & A16' & SWRq & OR & O8 & OBIG & Zovq & OWRq & ODJ & Z8q & Z16q & Z48q & U8q & KR & K8 & KO & U16q & U48q & _ & RBq & FCq).
  set (Hq := ahid Awq mdq) in *. set (MVq := mrestrict Hq Mq) in *.
  assert (SP0 : 0 <= sp < 2 ^ 64) by (clear - SPR; lia). assert (OVR : 0 <= ov < 2 ^ 64) by (clear - OR; lia). assert (OKR : 0 <= osk < 2 ^ 64) by (clear - KR; lia).
  assert (SFq : sfacts 80 sp MVq) by (split; [exact ICq|]; split; [exact CSBq|]; split; [exact CUARq|]; split; [exact SPR|]; split; [exact A16'| exact SWRq]).
  assert (EFq : efacts 80 sp ov osk MVq) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zovq|]; split; [exact OWRq|]; split; [exact ODJ|]; split; [exact Z8q|]; split; [exact Z16q|];
    split; [exact (z1_of_z7 MVq ov 32 Zovq O8 ltac:(clear; lia) eq_refl)|]; split; [exact (z1_of_z7 MVq ov 40 Zovq O8 ltac:(clear; lia) eq_refl)|]; split; [exact Z48q|];
    split; [exact U8q|]; split; [exact KR|]; split; [exact K8| exact U16q]).
  pose proof INVq as (_ & _ & _ & _ & AMq & _ & _ & HHq & EAq & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq ov 56 sp 20480 HHq (PMKB.aobj_of_aobjA FF ov 56 AOV O8) ltac:(clear; lia) ltac:(reflexivity)) as ((_ & _ & _ & _ & _) & _ & QDEFq & QVISq & _).
  pose proof EAq as (_ & _ & _ & _ & EV32q & _ & _ & EDEFq & _). cbn [PEC.en_b PEC.en_stk en2] in EV32q. change PEC.ESZ with 24 in EV32q.
  rewrite length_app, length_rev, Nat2Z.inj_add in EV32q. change (Z.of_nat (length [EI KD n 0])) with 1 in EV32q. rewrite HIT in EV32q.
  destruct (RUNP fxq Rq MVq sp ov osk it SP0 OVR OKR ltac:(clear - ITR; lia) LRq A10q ITR IT8 SFq EFq) as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & LR3 & UB & UE3).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq fxq fx3 Rq JOIN R3 PBPC M3v (fun a0 => (ov + 32 <= a0 < ov + 32 + 8) \/ (sp - 50 <= a0 < sp - 50 + 1)) K HHq AMq MS3 MG3).
  { intros a0 Ha0 Hn. apply FRZ3; [exact Ha0| intros Y; apply Hn; left; exact Y| intros Y; apply Hn; right; exact Y]. }
  { intros a0 Ha0 [Wa|Wa].
    - split; [| clear - Wa Eov F1 F2 F6 FSIMG; lia]. unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|].
      cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. split; [clear - Wa Eov; lia| intros Y; clear - Wa Y Eov; lia].
    - split; [| clear - Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia]. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict Hq M3 = M3v) in VIS3.

  assert (UE3r : L5.u64_at RSEGS M3 (ov + 32) (it + 24)).
  { rewrite <- VIS3 in UE3. exact (proj1 (L5A.u64_at_vis Hq M3 (ov + 32) _ (L5A.avis_sub Hq ov 56 (ov + 32) 8 QVISq ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia)) UE3). }
  assert (BYTES : forall i, 0 <= i < 8 -> M3 (Z_to_bv 64 (ov + 32 + i)) = Mq (Z_to_bv 64 (ov + 32 + i))).
  { apply (u64_same_bytes Mq M3 (ov + 32) (it + 24)); [| | exact EV32q| exact UE3r].
    - intros i Hi. replace (ov + 32 + i) with (ov + (32 + i)) by (clear; lia). apply EDEFq. clear - Hi; lia.
    - apply (L5.defined_grows Mq M3 _ _ MGM3). intros i Hi. replace (ov + 32 + i) with (ov + (32 + i)) by (clear; lia). apply EDEFq. clear - Hi; lia. }
  assert (FR3' : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 50 <= i < sp - 50 + 1) -> M3 (Z_to_bv 64 i) = Mq (Z_to_bv 64 i)).
  { intros i Hi Ni. destruct (L5SAR.rng_dec i (ov + 32) (ov + 40)) as [IW|NW].
    - replace i with (ov + 32 + (i - (ov + 32))) by (clear; lia). apply BYTES. clear - IW; lia.
    - apply FR3; [exact Hi| intros [Y|Y]; [clear - Y NW; lia| exact (Ni Y)]]. }
  pose proof (K_frame Mq M3 mdq md3 LKq Awq crq kq 0 (sp - 50) (sp - 50 + 1) en2 INVq ltac:(clear; lia) ltac:(clear; lia) MGM3 FR3' (FC_but Mq M3 (sp - 50) (sp - 50 + 1) ltac:(clear; lia) ltac:(clear; lia) FR3' FCq) HH3 AM3 MRT3) as INV3.
  assert (QCS3 : forall j, In j CSKb -> getr R3 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (KS3 jj Hjj); exact (QCSq jj Hjj)).

  pose proof HB as HBF. rewrite (XF_ok DOK) in HBF. cbn [s_hi] in HBF.
  apply (K_pb 0 (sp - 50) (xhi + (2 + pl_size n)) PBRA fx3 R3 M3 md3 LKq Awq crq kq en2 INV3 HBF ltac:(clear - PLS; lia) ltac:(clear; lia) ltac:(clear; lia) (proj1 (proj2 (proj2 RAS))) T1 (proj1 LR3) T10 T11 QCS3).
  intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 RP34.

  pose proof (K_vis M4 md4 LK4 Aw4 cr4 k4 (0 + 1) en2 INV4) as VF4. cbv beta in VF4.
  destruct VF4 as (IC4 & CSB4 & CUAR4 & _ & _ & SWR4 & _ & _ & _ & Zov4 & OWR4 & _ & Z84 & Z164 & Z484 & U84 & _ & _ & _ & U164 & U484 & _ & RB4 & FC4).
  set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  assert (SF4 : sfacts 80 sp MV4) by (split; [exact IC4|]; split; [exact CSB4|]; split; [exact CUAR4|]; split; [exact SPR|]; split; [exact A16'| exact SWR4]).
  assert (EF4 : efacts 80 sp ov osk MV4) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov4|]; split; [exact OWR4|]; split; [exact ODJ|]; split; [exact Z84|]; split; [exact Z164|];
    split; [exact (z1_of_z7 MV4 ov 32 Zov4 O8 ltac:(clear; lia) eq_refl)|]; split; [exact (z1_of_z7 MV4 ov 40 Zov4 O8 ltac:(clear; lia) eq_refl)|]; split; [exact Z484|];
    split; [exact U84|]; split; [exact KR|]; split; [exact K8| exact U164]).
  pose proof (fun jj Hjj => L5SAR.cs_of_preserved R3 R4 jj RP34 Hjj) as Rc4.
  assert (LR4 : lregs2 R4 sp ov).
  { destruct LR3 as (I2 & I8 & I9 & I18 & I19). split; [rewrite (Rc4 2%nat) by inl; exact I2|]. split; [rewrite (Rc4 8%nat) by inl; exact I8|]. split; [rewrite (Rc4 9%nat) by inl; exact I9|].
    split; [rewrite (Rc4 18%nat) by inl; exact I18| rewrite (Rc4 19%nat) by inl; exact I19]. }
  assert (QCS4 : forall j, In j CSKb -> getr R4 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (Rc4 jj (CSKall jj Hjj)); exact (QCS3 jj Hjj)).
  destruct (RUNP2 fx4 R4 MV4 sp ov osk SP0 OVR OKR LR4 SF4 EF4) as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & KS5 & V1 & V10 & V11 & LR5 & VB).
  pose proof INV4 as (_ & _ & _ & _ & AM4 & _ & _ & HH4 & _).
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK4 cr4 Aw4 M4 md4 fx4 fx5 R4 PBRA R5 PBPC M5v (fun a0 => sp - 49 <= a0 < sp - 49 + 1) K HH4 AM4 MS5 MG5).
  { intros a0 Ha0 Hn. apply FRZ5; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split; [| clear - Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia]. }
  intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
  pose proof (K_frame M4 M5 md4 md5 LK4 Aw4 cr4 k4 1 (sp - 49) (sp - 49 + 1) en2 INV4 ltac:(clear; lia) ltac:(clear; lia) MGM5 FR5 (FC_but M4 M5 (sp - 49) (sp - 49 + 1) ltac:(clear; lia) ltac:(clear; lia) FR5 FC4) HH5 AM5 MRT5) as INV5.
  assert (QCS5 : forall j, In j CSKb -> getr R5 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (KS5 jj Hjj); exact (QCS4 jj Hjj)).
  apply (K_pb 1 (sp - 49) (xhi + (2 + pl_size n)) PBRA2 fx5 R5 M5 md5 LK4 Aw4 cr4 k4 en2 INV5 HBF ltac:(clear - PLS; lia) ltac:(clear; lia) ltac:(clear; lia) (proj1 (proj2 (proj2 (proj2 RAS)))) V1 (proj1 LR5) V10 V11 QCS5).
  intros fx6 R6 M6 md6 LK6 Aw6 cr6 k6 INV6 RP56.

  pose proof (K_vis M6 md6 LK6 Aw6 cr6 k6 (1 + 1) en2 INV6) as VF6. cbv beta in VF6.
  destruct VF6 as (IC6 & CSB6 & CUAR6 & _ & _ & SWR6 & _ & _ & _ & Zov6 & OWR6 & _ & Z86 & Z166 & Z486 & U86 & _ & _ & _ & U166 & U486 & _ & RB6 & FC6).
  set (H6 := ahid Aw6 md6) in *. set (MV6 := mrestrict H6 M6) in *.
  assert (SF6 : sfacts 80 sp MV6) by (split; [exact IC6|]; split; [exact CSB6|]; split; [exact CUAR6|]; split; [exact SPR|]; split; [exact A16'| exact SWR6]).
  assert (EF6 : efacts 80 sp ov osk MV6) by (split; [exact OR|]; split; [exact O8|]; split; [exact OBIG|]; split; [exact Zov6|]; split; [exact OWR6|]; split; [exact ODJ|]; split; [exact Z86|]; split; [exact Z166|];
    split; [exact (z1_of_z7 MV6 ov 32 Zov6 O8 ltac:(clear; lia) eq_refl)|]; split; [exact (z1_of_z7 MV6 ov 40 Zov6 O8 ltac:(clear; lia) eq_refl)|]; split; [exact Z486|];
    split; [exact U86|]; split; [exact KR|]; split; [exact K8| exact U166]).
  pose proof (fun jj Hjj => L5SAR.cs_of_preserved R5 R6 jj RP56 Hjj) as Rc6.
  assert (LR6 : lregs2 R6 sp ov).
  { destruct LR5 as (I2 & I8 & I9 & I18 & I19). split; [rewrite (Rc6 2%nat) by inl; exact I2|]. split; [rewrite (Rc6 8%nat) by inl; exact I8|]. split; [rewrite (Rc6 9%nat) by inl; exact I9|].
    split; [rewrite (Rc6 18%nat) by inl; exact I18| rewrite (Rc6 19%nat) by inl; exact I19]. }
  assert (QCS6 : forall j, In j CSKb -> getr R6 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (Rc6 jj (CSKall jj Hjj)); exact (QCS5 jj Hjj)).
  destruct FC6 as (_ & UN6).
  destruct (RUNL fx6 R6 MV6 sp ov osk n SP0 OVR OKR HN24 LR6 SF6 EF6 (RB6 (sp - 64) n ltac:(clear; lia) ltac:(clear; lia) UN6)) as (fx7 & R7 & M7v & MG7 & FRZ7 & MS7 & KS7 & W1 & W10 & W11 & LR7).
  pose proof INV6 as (_ & _ & _ & _ & AM6 & _ & _ & HH6 & _).
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK6 cr6 Aw6 M6 md6 fx6 fx7 R6 PBRA2 R7 PLPC M7v K HH6 AM6 MS7 MG7 FRZ7).
  intros M7 md7 HH7 AM7 MRT7 HID7 VIS7 MGM7 AG7. pose proof (L5SAR.mem_eq_of_agree M6 M7 AG7) as EM7. subst M7.
  pose proof (K_frame M6 M6 md6 md7 LK6 Aw6 cr6 k6 (1 + 1) sp sp en2 INV6 ltac:(clear; lia) ltac:(clear; lia) ltac:(intros w Dw; exact Dw) ltac:(intros i _ _; reflexivity) (proj1 INV6) HH7 AM7 MRT7) as INV7.
  assert (QCS7 : forall j, In j CSKb -> getr R7 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (KS7 jj Hjj); exact (QCS6 jj Hjj)).
  assert (MPX : PECSPA.mp_enc p (ST xstk xpos xmore xdone xhalt xdepth xec (EI KD n 0 :: xestk) (xedepth + 1) (xlo + (1 + 1)) (xhi + (1 + 1)) xbad)).
  { unfold PECSPA.mp_enc. cbn [s_lo s_hi s_bad s_estk s_edepth]. split; [clear - LOHI; lia|]. split; [exact HBADX|]. split; [| clear - ED0 DOK; unfold MAX_DEPTH in *; lia].
    constructor; [| exact FA]. unfold ei_ok. cbn [ei_len ei_cnt ei_kind]. unfold TWO64. clear - HN HKD. lia. }
  apply (K_pl (1 + 1) PLRA n (EI KD n 0 :: xestk) (xedepth + 1) fx7 R7 M6 md7 LK6 Aw6 cr6 k6 en2 INV7 ltac:(cbn [PEC.en_stk rev en2]; reflexivity) ltac:(reflexivity) MPX
           ltac:(replace (xhi + (1 + 1) + pl_size n) with (xhi + (2 + pl_size n)) by (clear; lia); exact HBF) ltac:(unfold INT64_MAX; clear - HN24; lia) (proj1 (proj2 (proj2 (proj2 (proj2 RAS))))) W1 (proj1 LR7) W10 W11 QCS7).
  intros fx8 R8 M8 md8 LK8 Aw8 cr8 k8 INV8 RP78.

  pose proof (K_vis M8 md8 LK8 Aw8 cr8 k8 (1 + 1 + pl_size n) en2 INV8) as VF8. cbv beta in VF8.
  destruct VF8 as (IC8 & CSB8 & CUAR8 & _ & _ & SWR8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB8 & FC8).
  set (H8 := ahid Aw8 md8) in *. set (MV8 := mrestrict H8 M8) in *.
  assert (SF8 : sfacts 80 sp MV8) by (split; [exact IC8|]; split; [exact CSB8|]; split; [exact CUAR8|]; split; [exact SPR|]; split; [exact A16'| exact SWR8]).
  pose proof (fun jj Hjj => L5SAR.cs_of_preserved R7 R8 jj RP78 Hjj) as Rc8.
  assert (G28 : getr R8 (reg 2) = Z_to_bv 64 (sp - 80)) by (rewrite (Rc8 2%nat) by inl; exact (proj1 LR7)).
  assert (QCS8 : forall j, In j CSKb -> getr R8 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (Rc8 jj (CSKall jj Hjj)); exact (QCS7 jj Hjj)).
  destruct FC8 as ((C48 & C40 & C32 & C24 & C16 & C8) & _).
  destruct (RUNR fx8 R8 R MV8 sp r SP0 G28 SF8
               (conj (RB8 (sp - 48) _ ltac:(clear; lia) ltac:(clear; lia) C48) (conj (RB8 (sp - 40) _ ltac:(clear; lia) ltac:(clear; lia) C40) (conj (RB8 (sp - 32) _ ltac:(clear; lia) ltac:(clear; lia) C32)
               (conj (RB8 (sp - 24) _ ltac:(clear; lia) ltac:(clear; lia) C24) (conj (RB8 (sp - 16) _ ltac:(clear; lia) ltac:(clear; lia) C16) (RB8 (sp - 8) r ltac:(clear; lia) ltac:(clear; lia) C8))))))
               Rra Rsp RAok ltac:(intros jj Hjj; exact (QCS8 jj Hjj))) as (fx9 & R9 & M9v & MG9 & FRZ9 & MS9 & T109 & RP9).
  exact (K_fro (1 + 1 + pl_size n) PLRA fx8 R8 M8 md8 LK8 Aw8 cr8 k8 fx9 R9 M9v en2 (EI KD n 0 :: xestk) (xedepth + 1) INV8 ltac:(cbn [PEC.en_stk rev en2]; reflexivity) ltac:(reflexivity)
           ltac:(rewrite (XF_ok DOK); f_equal; clear; lia) MS9 MG9 FRZ9 RP9).
Qed.

Lemma main : srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R E0 M model) K.
Proof.
  destruct pre_facts as (FA & ED & ELEN & HSTK & HED & HBADX & LOHI). entry0.
  assert (HN24 : 0 <= n <= 16777216) by (clear - HN; unfold MAX_ITEMS in HN; lia).
  destruct K_vis_entry as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z16 & Z48 & U8v & KR & K8 & KO & U16 & U48 & HDEP & G2 & G10 & G1 & RAr & RB).
  cbv beta in RB. set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *. set (oec := PMSPA.o_ec AD fb) in *.
  assert (Eov : ov = fb + 496) by reflexivity. assert (Eoec : oec = fb + 1120) by reflexivity.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & _).
  assert (AOV : PMSPA.aobjA FF ov 56) by (apply (PEBEKG.AOF FF fb FOK); clear - Eov; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 20480 HH (PMKB.aobj_of_aobjA FF ov 56 AOV O8) ltac:(clear; lia) ltac:(reflexivity)) as ((Q1 & Q2' & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & _).
  assert (SP0 : 0 <= sp < 2 ^ 64) by (clear - SPR; lia). assert (OVR : 0 <= ov < 2 ^ 64) by (clear - OR; lia). assert (OKR : 0 <= osk < 2 ^ 64) by (clear - KR; lia).
  assert (OECR : 0 <= oec < 2 ^ 64) by (clear - OR Eov Eoec; lia). assert (RR : 0 <= r < 2 ^ 64) by (clear - Hr1; lia).
  assert (SF : sfacts 80 sp MV) by (split; [exact IC0|]; split; [exact CSBv|]; split; [exact CUARv|]; split; [exact SPR|]; split; [exact A16'| exact SWR]).
  assert (EF : efacts 80 sp ov osk MV).
  { split; [exact OR|]. split; [exact O8|]. split; [exact OBIG|]. split; [exact Zov|]. split; [exact OWR|]. split; [exact ODJ|]. split; [exact Z8|]. split; [exact Z16|].
    split; [exact (z1_of_z7 MV ov 32 Zov O8 ltac:(clear; lia) eq_refl)|]. split; [exact (z1_of_z7 MV ov 40 Zov O8 ltac:(clear; lia) eq_refl)|]. split; [exact Z48|].
    split; [exact U8v|]. split; [exact KR|]. split; [exact K8| exact U16]. }
  rewrite HDEP in U48.
  unfold PMSPA.cfg.
  destruct (Z_le_gt_dec xedepth 1023) as [DOK|DERR].
  -
    assert (DOK' : xedepth + 1 <= MAX_DEPTH) by (clear - DOK; unfold MAX_DEPTH; lia).

    pose proof CPRE as (_ & _ & EA0 & _).
    pose proof EA0 as (_ & _ & _ & _ & EV32 & EV40 & _ & _ & _ & EK12 & ELENC & _ & EKB & EBLK & _).
    change PEC.ESZ with 24 in EV32, EV40, ELENC, EBLK. rewrite HSTK, length_rev in EV32, ELENC, EBLK.
    set (len := Z.of_nat (length xestk)) in *. set (bb := PEC.en_b en) in *. set (kk := PEC.en_k en) in *.
    assert (U32v : L5.u64_at RSEGS MV (ov + 32) (bb + 24 * len)).
    { exact (proj2 (L5A.u64_at_vis H M (ov + 32) _ (L5A.avis_sub H ov 56 (ov + 32) 8 QVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia)) EV32). }
    assert (U40v : L5.u64_at RSEGS MV (ov + 40) (bb + 24 * PEC.ecap kk)).
    { exact (proj2 (L5A.u64_at_vis H M (ov + 40) _ (L5A.avis_sub H ov 56 (ov + 40) 8 QVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia)) EV40). }

    assert (BLK : 0 < kk -> 4096 <= bb /\ bb + 24 * PEC.ecap kk <= 2 ^ 47 /\ bb mod 8 = 0).
    { intros KP. destruct (EBLK KP) as (B8 & _ & BRNG & _). destruct BRNG as (B4096 & _).
      assert (IN : In (bb, PEC.ESZ * PEC.ecap kk) (PEC.owned s en k ++ LBX)).
      { apply in_or_app. left. unfold PEC.owned. apply in_or_app. right. apply in_or_app. left. unfold PEC.enc_own. fold kk. fold bb.
        replace (kk =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KP; lia). left. reflexivity. }
      pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH _ IN) as [B0 B47]. cbn [fst snd] in B0, B47. change PEC.ESZ with 24 in B47.
      split; [exact B4096|]. split; [exact B47| exact B8]. }
    assert (HC0 : 0 <= PEC.ecap kk) by (unfold PEC.ecap; destruct (kk =? 0); [clear; lia| apply Z.pow_nonneg; clear; lia]).
    assert (LEN0 : 0 <= len) by (subst len; clear; lia).
    destruct (Z_lt_le_dec len (PEC.ecap kk)) as [ROOM|FULL].
    +
      assert (KP : 0 < kk).
      { destruct (Z.eq_dec kk 0) as [E0z|NE]; [| clear - NE EK12; subst kk; lia]. exfalso. unfold PEC.ecap in ROOM. rewrite E0z in ROOM. cbn in ROOM. clear - ROOM LEN0. lia. }
      destruct (BLK KP) as (B4096 & B47 & B8).
      destruct (RUNAC fx R MV sp ov osk xedepth r (bb + 24 * len) (bb + 24 * PEC.ecap kk) n SP0 OVR OKR ltac:(clear - ED; unfold MAX_DEPTH in ED; lia) RR
                 ltac:(clear - B4096 B47 ROOM LEN0 HC0; lia) ltac:(clear - B4096 B47 HC0; lia) HN24 G2 G10 G1 A11 SF EF U48 ltac:(clear - ED DOK; lia) U32v U40v
                 ltac:(clear - B4096 B47 ROOM LEN0 HC0; lia) ltac:(clear - B8; lia) ltac:(clear - B4096 B47 HC0; lia) ltac:(clear - B8; lia) ltac:(clear - ROOM; lia))
        as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & LR1 & T10 & T11 & T12 & T20 & UKD & UD1 & UN1 & SV1).
      apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R E0 R1 ECONQ M1v (fun a0 => (sp - 80 <= a0 < sp - 80 + 80) \/ (ov + 48 <= a0 < ov + 52)) K HH AM MS1 MG1).
      { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| intros Y; apply Hn; left; exact Y| intros Y; apply Hn; right; exact Y]. }
      { intros a0 Ha0 [Wa|Wa].
        - split; [| clear - Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
        - split; [| clear - Wa Eov F1 F2 F6 FSIMG; lia]. unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|].
          cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. split; [clear - Wa Eov; lia| intros Y; clear - Wa Y Eov; lia]. }
      intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
      assert (FCM1 : FC M1).
      { rewrite <- VIS1 in SV1, UN1. destruct SV1 as (C48 & C40 & C32 & C24 & C16 & C8). unfold FC, saved.
        repeat split; (apply RB; [clear; lia| clear; lia| assumption]). }
      assert (UD1' : L5.u32_at RSEGS M1 (ov + 48) (xedepth + 1)).
      { rewrite <- VIS1 in UD1. exact (proj1 (L5A.u32_at_vis H M1 (ov + 48) _ (L5A.avis_sub H ov 56 (ov + 48) 4 QVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia)) UD1). }
      pose proof (K_startw M1 md1 (xedepth + 1) MGM1 ltac:(intros i Hi N1 N2; apply FR1; [exact Hi| intros [Y|Y]; [exact (N1 Y)| exact (N2 Y)]]) FCM1 HH1 AM1 MRT1 UD1' ltac:(clear - ED DOK; unfold MAX_DEPTH in *; lia)) as INV1.
      assert (QCS1 : forall j, In j CSKb -> getr R1 (reg j) = getr R (reg j)) by (intros jj Hjj; exact (KS1 jj Hjj)).

      pose proof ECK as ECX. unfold PECEPX.econe_kl_spec in ECX.
      assert (UKD' : L5.u32_at RSEGS M1 (sp - 68) KD).
      { rewrite <- VIS1 in UKD. exact (proj1 (L5A.u32_at_vis H M1 (sp - 68) KD (VIS (sp - 68) 4 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia)) UKD). }
      pose proof INV1 as (_ & ASTK1 & SZ1 & _).
      apply (K_econe ECONQ 0 ECRA (PECEPA.ecells_kl RSEGS ar) (EI KD n 0) fx1 R1 M1 md1 LK Aw cr k _ ECX INV1
               ltac:(cbn [PEC.en_stk PEC.en_k]; rewrite HSTK, length_rev; exact ROOM) (proj1 RAS) T1 (proj1 LR1) T10 QCS1).
      { pose proof FCM1 as (_ & UN'). exists (sp - 68), (sp - 64), KD, n. split; [exact T11|]. split; [exact T12|]. split; [clear - A16; Lia.lia|]. split; [clear - A16; Lia.lia|].
        split. { unfold PMSPA.accA, aacc. intros a Ha. left. apply (PESHZ.bat0_of_shadow_zero M1 (sp - 20480) 2560 a SZ1); [apply (PEBEKG.SPd8 sp SP32); reflexivity| clear - Ha; lia| clear - Ha; lia]. }
        split. { unfold PMSPA.accA, aacc. intros a Ha. left. apply (PESHZ.bat0_of_shadow_zero M1 (sp - 20480) 2560 a SZ1); [apply (PEBEKG.SPd8 sp SP32); reflexivity| clear - Ha; lia| clear - Ha; lia]. }
        split. { split; [right; clear - SHI SPT; lia| clear - ODJ; lia]. }
        split. { split; [right; clear - SHI SPT; lia| clear - ODJ; lia]. }
        split; [apply (PESHZ.bat0_of_shadow_zero M1 (sp - 20480) 2560 (sp - 68) SZ1); [apply (PEBEKG.SPd8 sp SP32); reflexivity| clear; lia| clear; lia]|].
        split; [apply (PESHZ.bat0_of_shadow_zero M1 (sp - 20480) 2560 (sp - 64) SZ1); [apply (PEBEKG.SPd8 sp SP32); reflexivity| clear; lia| clear; lia]|].
        split; [exact UKD'|]. split; [exact UN'|]. split; [exact HKD|]. split; [exact HN| reflexivity]. }
      intros fx2 R2 M2 md2 LK2 Aw2 INV2 RP12. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in INV2. rewrite HSTK in INV2.

      pose proof (K_vis M2 md2 LK2 Aw2 cr k 0 _ INV2) as VF2. cbv beta in VF2.
      destruct VF2 as (IC2 & CSB2 & CUAR2 & _ & _ & SWR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FC2).
      set (H2 := ahid Aw2 md2) in *. set (MV2 := mrestrict H2 M2) in *.
      assert (SF2 : sfacts 80 sp MV2) by (split; [exact IC2|]; split; [exact CSB2|]; split; [exact CUAR2|]; split; [exact SPR|]; split; [exact A16'| exact SWR2]).
      pose proof (fun jj Hjj => L5SAR.cs_of_preserved R1 R2 jj RP12 Hjj) as Rc.
      destruct LR1 as (I2 & I8 & I9 & I18 & I19).
      assert (LR2 : lregs R2 sp ov).
      { split; [rewrite (Rc 2%nat) by inl; exact I2|]. split; [rewrite (Rc 8%nat) by inl; exact I8|]. split; [rewrite (Rc 9%nat) by inl; exact I9|].
        split; [rewrite (Rc 18%nat) by inl; exact I18| rewrite (Rc 19%nat) by inl; exact I19]. }
      assert (G20 : getr R2 (reg 20) = Z_to_bv 64 (bb + 24 * len)) by (rewrite (Rc 20%nat) by inl; exact T20).
      assert (QCS2 : forall j, In j CSKb -> getr R2 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (Rc jj (CSKall jj Hjj)); exact (QCS1 jj Hjj)).
      destruct (RUNPJ fx2 R2 MV2 sp (bb + 24 * len) SP0 ltac:(clear - B4096 B47 ROOM LEN0 HC0; lia) (proj1 LR2) G20 ltac:(clear - B4096 B47 ROOM LEN0 HC0; lia) ltac:(clear - B8; lia) SF2)
        as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & KS3' & T103).
      pose proof INV2 as (_ & _ & _ & _ & AM2 & _ & _ & HH2 & _).
      apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK2 cr Aw2 M2 md2 fx2 fx3 R2 ECRA R3 JOIN M3v (fun _ => False) K HH2 AM2 MS3 MG3).
      { intros a0 Ha0 _. apply FRZ3. exact Ha0. }
      { intros a0 Ha0 Wa. destruct Wa. }
      intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
      assert (FR3' : forall i, 0 <= i < 2 ^ 64 -> ~ (sp <= i < sp) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i)) by (intros i Hi _; apply FR3; [exact Hi| intros Y; exact Y]).
      pose proof (K_frame M2 M3 md2 md3 LK2 Aw2 cr k 0 sp sp _ INV2 ltac:(clear; lia) ltac:(clear; lia) MGM3 FR3' (FC_frame M2 M3 ltac:(intros a0 Ha0; apply FR3; [clear - Ha0 SLO SHI SPT; lia| intros Y; exact Y]) FC2) HH3 AM3 MRT3) as INV3.
      assert (LR3 : lregs R3 sp ov).
      { destruct LR2 as (J2 & J8 & J9 & J18 & J19). split; [rewrite (KS3' 2%nat) by inl; exact J2|]. split; [rewrite (KS3' 8%nat) by inl; exact J8|]. split; [rewrite (KS3' 9%nat) by inl; exact J9|].
        split; [rewrite (KS3' 18%nat) by inl; exact J18| rewrite (KS3' 19%nat) by inl; exact J19]. }
      assert (QCS3 : forall j, In j CSKb -> getr R3 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (KS3 jj Hjj); exact (QCS2 jj Hjj)).
      exact (join_tail fx3 R3 M3 md3 LK2 Aw2 cr k bb kk (bb + 24 * len) DOK' HSTK FA HBADX LOHI (proj1 ED) INV3 LR3 QCS3 T103 ltac:(clear - B4096 B47 ROOM LEN0 HC0; lia) ltac:(clear - B8; lia) ltac:(clear; lia)).
    +
      assert (LEQ : len = PEC.ecap kk) by (clear - FULL ELENC; lia).
      assert (EB : 0 <= bb + 24 * len <= 140737488355328 /\ (bb + 24 * len) mod 8 = 0).
      { destruct (Z.eq_dec kk 0) as [K0z|Knz].
        - pose proof (EKB K0z) as B0z. fold bb in B0z. rewrite LEQ. unfold PEC.ecap. rewrite K0z, B0z. cbn. clear; lia.
        - destruct (BLK ltac:(clear - Knz EK12; subst kk; lia)) as (B4096 & B47 & B8). rewrite LEQ. split; [clear - B4096 B47 HC0; lia| clear - B8; lia]. }
      destruct EB as (EB1 & EB8).
      rewrite <- LEQ in U40v.
      destruct (RUNAS fx R MV sp ov osk xedepth r (bb + 24 * len) n SP0 OVR OKR ltac:(clear - ED; unfold MAX_DEPTH in ED; lia) RR ltac:(clear - EB1; lia) HN24
                 G2 G10 G1 A11 SF EF U48 ltac:(clear - ED DOK; lia) U32v U40v EB1 EB8)
        as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & LR1 & T10 & T11 & T12 & T20 & UKD & UD1 & UN1 & SV1).
      apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R E0 R1 ESLOQ M1v (fun a0 => (sp - 80 <= a0 < sp - 80 + 80) \/ (ov + 48 <= a0 < ov + 52)) K HH AM MS1 MG1).
      { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| intros Y; apply Hn; left; exact Y| intros Y; apply Hn; right; exact Y]. }
      { intros a0 Ha0 [Wa|Wa].
        - split; [| clear - Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
        - split; [| clear - Wa Eov F1 F2 F6 FSIMG; lia]. unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|].
          cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. split; [clear - Wa Eov; lia| intros Y; clear - Wa Y Eov; lia]. }
      intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
      assert (FCM1 : FC M1).
      { rewrite <- VIS1 in SV1, UN1. destruct SV1 as (C48 & C40 & C32 & C24 & C16 & C8). unfold FC, saved.
        repeat split; (apply RB; [clear; lia| clear; lia| assumption]). }
      assert (UD1' : L5.u32_at RSEGS M1 (ov + 48) (xedepth + 1)).
      { rewrite <- VIS1 in UD1. exact (proj1 (L5A.u32_at_vis H M1 (ov + 48) _ (L5A.avis_sub H ov 56 (ov + 48) 4 QVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia)) UD1). }
      pose proof (K_startw M1 md1 (xedepth + 1) MGM1 ltac:(intros i Hi N1 N2; apply FR1; [exact Hi| intros [Y|Y]; [exact (N1 Y)| exact (N2 Y)]]) FCM1 HH1 AM1 MRT1 UD1' ltac:(clear - ED DOK; unfold MAX_DEPTH in *; lia)) as INV1.
      assert (QCS1 : forall j, In j CSKb -> getr R1 (reg j) = getr R (reg j)) by (intros jj Hjj; exact (KS1 jj Hjj)).

      pose proof ESK as ESX. unfold PECEPX.eslow_kl_spec in ESX.
      assert (UKD' : L5.u32_at RSEGS M1 (sp - 68) KD).
      { rewrite <- VIS1 in UKD. exact (proj1 (L5A.u32_at_vis H M1 (sp - 68) KD (VIS (sp - 68) 4 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia)) UKD). }
      pose proof INV1 as (_ & ASTK1 & SZ1 & _).
      apply (K_eslow ESLOQ 0 JOIN (PECEPA.ecells_kl RSEGS ar) (EI KD n 0) fx1 R1 M1 md1 LK Aw cr k _ ESX INV1
               ltac:(cbn [PEC.en_stk PEC.en_k]; rewrite HSTK, length_rev; exact LEQ) ltac:(cbn [PEC.en_stk]; rewrite HSTK, length_rev; exact ELEN) (proj1 (proj2 RAS)) T1 (proj1 LR1) T10 QCS1).
      { pose proof FCM1 as (_ & UN'). exists (sp - 68), (sp - 64), KD, n. split; [exact T11|]. split; [exact T12|]. split; [clear - A16; Lia.lia|]. split; [clear - A16; Lia.lia|].
        split. { unfold PMSPA.accA, aacc. intros a Ha. left. apply (PESHZ.bat0_of_shadow_zero M1 (sp - 20480) 2560 a SZ1); [apply (PEBEKG.SPd8 sp SP32); reflexivity| clear - Ha; lia| clear - Ha; lia]. }
        split. { unfold PMSPA.accA, aacc. intros a Ha. left. apply (PESHZ.bat0_of_shadow_zero M1 (sp - 20480) 2560 a SZ1); [apply (PEBEKG.SPd8 sp SP32); reflexivity| clear - Ha; lia| clear - Ha; lia]. }
        split. { split; [right; clear - SHI SPT; lia| clear - ODJ; lia]. }
        split. { split; [right; clear - SHI SPT; lia| clear - ODJ; lia]. }
        split; [apply (PESHZ.bat0_of_shadow_zero M1 (sp - 20480) 2560 (sp - 68) SZ1); [apply (PEBEKG.SPd8 sp SP32); reflexivity| clear; lia| clear; lia]|].
        split; [apply (PESHZ.bat0_of_shadow_zero M1 (sp - 20480) 2560 (sp - 64) SZ1); [apply (PEBEKG.SPd8 sp SP32); reflexivity| clear; lia| clear; lia]|].
        split; [exact UKD'|]. split; [exact UN'|]. split; [exact HKD|]. split; [exact HN| reflexivity]. }
      intros fx2 R2 M2 md2 LK2 Aw2 B INV2 RP12 RA10. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in INV2, RA10. rewrite HSTK in INV2. rewrite HSTK, length_rev in RA10.
      change PEC.ESZ with 24 in RA10. fold len in RA10.

      pose proof INV2 as (_ & _ & _ & _ & _ & _ & _ & HH2 & EA2 & _).
      pose proof EA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ELEN2 & _ & _ & EBLK2 & _). cbn [PEC.en_b PEC.en_k PEC.en_stk] in ELEN2, EBLK2. change PEC.ESZ with 24 in ELEN2, EBLK2.
      rewrite length_app, length_rev, Nat2Z.inj_add in ELEN2. change (Z.of_nat (length [EI KD n 0])) with 1 in ELEN2. fold len in ELEN2. fold kk in ELEN2. fold kk in EBLK2.
      assert (KP2 : 0 < kk + 1) by (clear - EK12; lia).
      destruct (EBLK2 KP2) as (B8n & _ & BRNGn & _). destruct BRNGn as (B4096n & _).
      assert (INn : In (B, PEC.ESZ * PEC.ecap (kk + 1)) (PEC.owned s (PEC.ENC B (kk + 1) (rev xestk ++ [EI KD n 0]) (xedepth + 1)) k ++ LBX)).
      { apply in_or_app. left. unfold PEC.owned. apply in_or_app. right. apply in_or_app. left. unfold PEC.enc_own. cbn [PEC.en_k PEC.en_b].
        replace (kk + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KP2; lia). left. reflexivity. }
      pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH2 _ INn) as [Bn0 Bn47]. cbn [fst snd] in Bn0, Bn47. change PEC.ESZ with 24 in Bn47.
      exact (join_tail fx2 R2 M2 md2 LK2 Aw2 _ k B (kk + 1) (B + 24 * len) DOK' HSTK FA HBADX LOHI (proj1 ED) INV2 ltac:(destruct LR1 as (I2 & I8 & I9 & I18 & I19); pose proof (fun jj Hjj => L5SAR.cs_of_preserved R1 R2 jj RP12 Hjj) as Rc;
                    split; [rewrite (Rc 2%nat) by inl; exact I2|]; split; [rewrite (Rc 8%nat) by inl; exact I8|]; split; [rewrite (Rc 9%nat) by inl; exact I9|];
                    split; [rewrite (Rc 18%nat) by inl; exact I18| rewrite (Rc 19%nat) by inl; exact I19])
               ltac:(intros jj Hjj; rewrite (L5SAR.cs_of_preserved R1 R2 jj RP12 (CSKall jj Hjj)); exact (QCS1 jj Hjj))
               ltac:(rewrite RA10; f_equal; clear; lia) ltac:(clear - B4096n Bn47 ELEN2 LEN0 HC0; lia) ltac:(clear - B8n; lia) ltac:(clear; lia)).
  -
    assert (D1024 : xedepth = 1024) by (clear - ED DERR; unfold MAX_DEPTH in ED; lia). rewrite D1024 in U48.
    destruct (RUNE fx R MV sp ov osk oec r n SP0 OVR OKR OECR RR HN24 G2 G10 A14 G1 A11 SF EF U48)
      as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T18 & T10 & T11 & UD1 & UN1 & SV1).
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R E0 R1 MKPC M1v (fun a0 => (sp - 80 <= a0 < sp - 80 + 80) \/ (ov + 48 <= a0 < ov + 52)) K HH AM MS1 MG1).
    { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| intros Y; apply Hn; left; exact Y| intros Y; apply Hn; right; exact Y]. }
    { intros a0 Ha0 [Wa|Wa].
      - split; [| clear - Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
      - split; [| clear - Wa Eov F1 F2 F6 FSIMG; lia]. unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|].
        cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. split; [clear - Wa Eov; lia| intros Y; clear - Wa Y Eov; lia]. }
    intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
    assert (FCM1 : FC M1).
    { rewrite <- VIS1 in SV1, UN1. destruct SV1 as (C48 & C40 & C32 & C24 & C16 & C8). unfold FC, saved.
      repeat split; (apply RB; [clear; lia| clear; lia| assumption]). }
    assert (UD1' : L5.u32_at RSEGS M1 (ov + 48) 1025).
    { rewrite <- VIS1 in UD1. exact (proj1 (L5A.u32_at_vis H M1 (ov + 48) _ (L5A.avis_sub H ov 56 (ov + 48) 4 QVIS ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia)) UD1). }
    pose proof (K_startw M1 md1 1025 MGM1 ltac:(intros i Hi N1 N2; apply FR1; [exact Hi| intros [Y|Y]; [exact (N1 Y)| exact (N2 Y)]]) FCM1 HH1 AM1 MRT1 UD1' ltac:(unfold MAX_DEPTH; clear; lia)) as INV1.
    assert (QCS1 : forall j, In j CSKb -> getr R1 (reg j) = getr R (reg j)) by (intros jj Hjj; exact (KS1 jj Hjj)).
    apply (K_mkec 0 MKRA 11 fx1 R1 M1 md1 LK Aw cr k _ INV1 (proj2 (proj2 (proj2 (proj2 (proj2 RAS))))) ltac:(clear; lia) T1 T2 T10 T11 QCS1).
    intros fx2 R2 M2 md2 LK2 Aw2 INV2 RP12.

    pose proof (PEBEKG.vis_facts_e L ar C HI P LY HIok 80 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC M2 md2 LK2 Aw2 cr k 0 _ 11 INV2) as VF2. cbv beta in VF2.
    destruct VF2 as (IC2 & CSB2 & CUAR2 & _ & _ & SWR2 & RB2 & FC2).
    set (H2 := ahid Aw2 md2) in *. set (MV2 := mrestrict H2 M2) in *.
    assert (SF2 : sfacts 80 sp MV2) by (split; [exact IC2|]; split; [exact CSB2|]; split; [exact CUAR2|]; split; [exact SPR|]; split; [exact A16'| exact SWR2]).
    pose proof (fun jj Hjj => L5SAR.cs_of_preserved R1 R2 jj RP12 Hjj) as Rc.
    assert (G2' : getr R2 (reg 2) = Z_to_bv 64 (sp - 80)) by (rewrite (Rc 2%nat) by inl; exact T2).
    assert (QCS2 : forall j, In j CSKb -> getr R2 (reg j) = getr R (reg j)) by (intros jj Hjj; rewrite (Rc jj (CSKall jj Hjj)); exact (QCS1 jj Hjj)).
    destruct FC2 as ((C48 & C40 & C32 & C24 & C16 & C8) & _).
    destruct (RUNX fx2 R2 R MV2 sp r SP0 G2' SF2
                 (conj (RB2 (sp - 48) _ ltac:(clear; lia) ltac:(clear; lia) C48) (conj (RB2 (sp - 40) _ ltac:(clear; lia) ltac:(clear; lia) C40) (conj (RB2 (sp - 32) _ ltac:(clear; lia) ltac:(clear; lia) C32)
                 (conj (RB2 (sp - 24) _ ltac:(clear; lia) ltac:(clear; lia) C24) (conj (RB2 (sp - 16) _ ltac:(clear; lia) ltac:(clear; lia) C16) (RB2 (sp - 8) r ltac:(clear; lia) ltac:(clear; lia) C8))))))
                 Rra Rsp RAok ltac:(intros jj Hjj; exact (QCS2 jj Hjj))) as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & T105 & RP5).
    exact (K_ferr 0 MKRA fx2 R2 M2 md2 LK2 Aw2 cr k fx5 R5 M5v (PEC.ENC (PEC.en_b en) (PEC.en_k en) (PEC.en_stk en) 1025) 11 xestk (xedepth + 1) INV2 ltac:(clear; lia)
             ltac:(cbn [PEC.en_stk]; exact HSTK) ltac:(cbn [PEC.en_depth]; rewrite D1024; reflexivity) (XF_err ltac:(rewrite D1024; reflexivity)) MS5 MG5 FRZ5 RP5).
Qed.
End Call.
End Slot.

Local Ltac row E0 ECRA JOIN PBRA PBRA2 PLRA MKRA KD MK uAc uAs uE uPj uP uP2 uL uR uX :=
  intros PMODE n fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 (HN & A11 & A14) CPRE INCS POK MP NB HB CRED KONT;
  rewrite L5K.rl11 in A11; rewrite L5K.rl14 in A14; destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad];
  refine (main E0 ECRA JOIN PBRA PBRA2 PLRA MKRA KD MK ltac:(unfold L5.ra_ok; clear; lia) ltac:(clear; lia) uAc uAs uE uPj uP uP2 uL uR uX PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p n
            xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 HN A11 A14 CPRE INCS POK MP HB CRED KONT).

Theorem v_begin_arr_len_ok : PECSB.v_begin_arr_len_spec L ar HI P.
Proof.
  unfold PECSB.v_begin_arr_len_spec, PECSPA.v_begin_arr_len_spec, PECSPA.eslot_spec, PECSPA.args_len. cbn [pe_begin_arr_len EE PeCLayoutB.EADDR_B].
  row 0xab900 0xab9c4 0xab9e4 0xaba3c 0xaba64 0xaba70 0xabaa0 2 91 u_runAc_l u_runAs_l u_runE_l u_runPj_l u_runP_l u_runP2_l u_runL_l u_runR_l u_runX_l.
Qed.

Theorem v_begin_obj_len_ok : PECSB.v_begin_obj_len_spec L ar HI P.
Proof.
  unfold PECSB.v_begin_obj_len_spec, PECSPA.v_begin_obj_len_spec, PECSPA.eslot_spec, PECSPA.args_len. cbn [pe_begin_obj_len EE PeCLayoutB.EADDR_B].
  row 0xacb14 0xacbd4 0xacbf4 0xacc4c 0xacc74 0xacc80 0xaccb0 0 123 u_runAc_m u_runAs_m u_runE_m u_runPj_m u_runP_m u_runP2_m u_runL_m u_runR_m u_runX_m.
Qed.
End WithHeap.
End PEBENCBL.
