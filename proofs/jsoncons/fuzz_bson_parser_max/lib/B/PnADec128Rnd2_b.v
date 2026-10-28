(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare AxSymExec3 L5Defs L5Kn L5KnA L5Core L5CoreKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModelFacts
     PnDecFacts PnDecBv PnMemW PnSDec128Rnd2 PnADec128Bv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128Defs_b PnADec128P3_b PnADec128P4_b PnADec128Rnd_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADRN2.
Import PNADRN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Abbreviation rdig := PNSDRN2.rdig.

Section Call.
Variables (R0 : bvmap 5 word) (S F : Z).
Hypothesis FS : 140735332487296 <= S <= 140737488355328.
Hypothesis F32 : S mod 32 = 0.
Hypothesis FF1 : 4096 <= F <= 140737488354816.
Hypothesis FF32 : F mod 32 = 0.
Hypothesis FFSH : 2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784.
Hypothesis FFS : S - 256 + 256 <= F \/ F + 512 <= S - 256.
Hypothesis FFI : 65536 + 6840320 <= F \/ F + 512 <= 65536.
Abbreviation cell := (PNADD.cell F).
Definition VV (k : Z) (i : nat) : Z :=
  match i with 2%nat => S | 40%nat => k | 50%nat => F | _ => 0 end.
Local Ltac fsc := first [ assumption | (hnf; assumption) | match goal with |- getr _ _ = Z_to_bv 64 ?z => match goal with H : getr _ _ = Z_to_bv 64 ?y |- _ => replace z with y by lia; exact H end end | lia ].
Local Ltac rg R1 KS1 :=
  first [ assumption | (hnf; assumption)
        | (rewrite KS1 by inl; first [ assumption | match goal with H : getr _ (reg ?j) = Z_to_bv 64 ?y |- getr _ (reg ?j) = Z_to_bv 64 ?z => replace z with y by lia; exact H end ])
        | match goal with H : getr R1 (reg ?j) = Z_to_bv 64 ?y |- getr R1 (reg ?j) = Z_to_bv 64 ?z => replace z with y by lia; exact H end ].

Lemma ext4_zero E j v (lo : nat) : AX2.ev E j = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  1 <= bv_unsigned (AX2.edenot E (AX2.EAlu ALU_SLTU (AX2.EAlu ALU_SUB (AX2.EExt true lo 4 (AX2.EVar j)) (AX2.ELit 0)) (AX2.ELit 1))) <= 1 ->
  (v / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ 32 = 0.
Proof.
  intros Ej Hv H. apply (proj1 (proj1 (PNADBV.test_iff E _))) in H.
  cbn [AX2.edenot] in H. rewrite Ej in H. unfold AX2.ext_val, AX2.ext_Z in H. rewrite (PNDBV.u_lit v Hv) in H.
  change (8 * Z.of_nat 4) with 32 in H. change (8 * N.of_nat 4)%N with 32%N in H.
  pose proof (Z.mod_pos_bound (v / 2 ^ (8 * Z.of_nat lo)) (2 ^ 32) ltac:(clear; lia)) as Hu. revert H Hu.
  generalize ((v / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ 32) as u. intros u H Hu.
  rewrite Z_to_bv_unsigned in H. unfold bv_swrap, bv_wrap in H.
  change (bv_modulus 32) with (2 ^ 32) in H. change (bv_half_modulus 32) with (2 ^ 31) in H. change (bv_modulus 64) with (2 ^ 64) in H.
  destruct (Z_lt_le_dec u (2 ^ 31)) as [LT|GE].
  - rewrite (Z.mod_small (u + 2 ^ 31)) in H by lia. replace (u + 2 ^ 31 - 2 ^ 31) with u in H by lia. rewrite Z.mod_small in H by lia. exact H.
  - exfalso. replace ((u + 2 ^ 31) mod 2 ^ 32) with (u + 2 ^ 31 - 2 ^ 32) in H by (apply (Z.mod_unique_pos _ _ 1); lia).
    replace ((u + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) mod 2 ^ 64) with (u - 2 ^ 32 + 2 ^ 64) in H by (apply (Z.mod_unique_pos _ _ (-1)); lia). lia.
Qed.
Lemma word_zero v : 0 <= v < 2 ^ 64 -> v mod 2 ^ 32 = 0 -> (v / 2 ^ 32) mod 2 ^ 32 = 0 -> v = 0.
Proof.
  intros Hv L H. pose proof (Z.div_mod v (2 ^ 32) ltac:(clear; lia)) as E.
  assert (Q : 0 <= v / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small in H by exact Q. lia.
Qed.

Lemma headfork fx R M k W :
  PNADRN.RRa R0 S F R k -> 0 <= k <= 3 -> 0 <= W < 2 ^ 113 -> L5.writable RSEGS M (S - 256) 256 ->
  L5.u64_at RSEGS M (S - 136) (PNSDRN2.p0 W + 2 ^ 32 * PNSDRN2.p1 W) -> L5.u64_at RSEGS M (S - 128) (PNSDRN2.p2 W + 2 ^ 32 * PNSDRN2.p3 W) ->
  exists fx' R' M' (pc' : Z), msteps RSEGS (st fx R 0xb4164 M) (st fx' R' pc' M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 120 <= a < S - 104) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ PNADRN.RRb R0 S F R' k /\ getr R' (reg 24) = Z_to_bv 64 k
    /\ ((pc' = 0xb4248 /\ W = 0 /\ getr R' (reg 18) = Z_to_bv 64 (F + 32) /\ getr R' (reg 12) = Z_to_bv 64 0
         /\ L5.u64_at RSEGS M' (S - 120) 0 /\ L5.u64_at RSEGS M' (S - 112) 0)
        \/ (pc' = 0xb41c8 /\ getr R' (reg 10) = Z_to_bv 64 (S - 120) /\ getr R' (reg 18) = Z_to_bv 64 (F + 28 + 36 * k)
            /\ getr R' (reg 21) = Z_to_bv 64 0
            /\ L5.u32_at RSEGS M' (S - 120) (PNSDRN2.p0 W) /\ L5.u32_at RSEGS M' (S - 116) (PNSDRN2.p1 W)
            /\ L5.u32_at RSEGS M' (S - 112) (PNSDRN2.p2 W) /\ L5.u32_at RSEGS M' (S - 108) (PNSDRN2.p3 W))).
Proof.
  intros RRk Hk HW WR C136 C128.
  destruct (PNSDRN2.parts_val W HW) as (EW & B0 & B1 & B2 & B3).
  assert (X41 : exists w41, w41 = PNSDRN2.p0 W + 2 ^ 32 * PNSDRN2.p1 W) by (eexists; reflexivity). destruct X41 as (w41 & Ew41).
  assert (X42 : exists w42, w42 = PNSDRN2.p2 W + 2 ^ 32 * PNSDRN2.p3 W) by (eexists; reflexivity). destruct X42 as (w42 & Ew42).
  rewrite <- Ew41 in C136. rewrite <- Ew42 in C128.
  assert (H41 : 0 <= w41 < 2 ^ 64) by (rewrite Ew41; lia).
  assert (H42 : 0 <= w42 < 2 ^ 64) by (rewrite Ew42; lia).
  pose proof RRk as (G2 & G3 & G4 & G8 & G9 & G10 & G18 & G19 & G20 & G22 & G23 & G25 & G26 & G27).
  (let T := type of (PNADP3.adkRH_conc fx R M (fun i => match i with 41%nat => w41 | 42%nat => w42 | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP3.adkRH_conc fx R M (fun i => match i with 41%nat => w41 | 42%nat => w42 | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & MS1 & KS1 & A7 & A10 & A11 & A12 & A24 & A28 & A30 & D112 & D120).
  assert (E136 : L5.u64_at RSEGS M1 (S - 136) w41) by (apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FZ1; lia| lia| lia| exact C136]).
  pose proof (L5.writable_grows RSEGS _ _ _ _ MG1 WR) as WR1.
  assert (E128 : L5.u64_at RSEGS M1 (S - 128) w42) by (apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FZ1; lia| lia| lia| exact C128]).
  (let T := type of (PNADP3.adkRF_conc fx1 R1 M1 (fun i => match i with 41%nat => w41 | 42%nat => w42 | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP3.adkRF_conc fx1 R1 M1 (fun i => match i with 41%nat => w41 | 42%nat => w42 | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [ fsc | (rewrite KS1 by inl; fsc) | (match goal with H : getr ?R (reg ?j) = _ |- getr ?R (reg ?j) = _ => rewrite H; reflexivity end) ])).
  destruct P as (fx2 & R2 & M2 & MG2 & _ & FZ2 & [ (MS2 & KS2 & B10 & B11 & C1 & C2 & C3 & C4)
     | [ (MS2 & KS2 & B10 & B11 & B18 & B21 & B28 & B30 & B31 & _ & _ & _ & _)
     | [ (MS2 & KS2 & B10 & B11 & B18 & B21 & B28 & B30 & B31 & _ & _ & _)
     | [ (MS2 & KS2 & B10 & B18 & B21 & B28 & B30 & B31 & _ & _)
     | (MS2 & KS2 & B10 & B18 & B21 & B28 & B30 & B31 & _) ] ] ] ]);
    (assert (EM : M2 = M1) by (apply L5SAR.mem_eq_of_agree; exact FZ2)); subst M2.
  { assert (Z41 : w41 = 0).
    { apply word_zero; [exact H41| |].
      - pose proof (PNADBV.w_zero _ _ C1) as L41. cbn [AX2.edenot AX2.ev] in L41. rewrite (PNDBV.u_lit w41 H41) in L41. exact L41.
      - assert (X : (w41 / 2 ^ (8 * Z.of_nat 4)) mod 2 ^ 32 = 0) by (eapply (ext4_zero _ 41%nat w41 4%nat); [| exact H41| exact C4]; reflexivity).
        change (8 * Z.of_nat 4) with 32 in X. exact X. }
    assert (Z42 : w42 = 0).
    { apply word_zero; [exact H42| |].
      - assert (L42 : (w42 / 2 ^ (8 * Z.of_nat 0)) mod 2 ^ 32 = 0) by (eapply (ext4_zero _ 42%nat w42 0%nat); [| exact H42| exact C3]; reflexivity).
        change (8 * Z.of_nat 0) with 0 in L42. rewrite Z.pow_0_r, Z.div_1_r in L42. exact L42.
      - assert (X : (w42 / 2 ^ (8 * Z.of_nat 4)) mod 2 ^ 32 = 0) by (eapply (ext4_zero _ 42%nat w42 4%nat); [| exact H42| exact C2]; reflexivity).
        change (8 * Z.of_nat 4) with 32 in X. exact X. }
    exists fx2, R2, M1, 0xb4248. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|].
    split; [intros a Ha Hn; apply FZ1; [exact Ha| clear - Hn; lia]|].
    split; [unfold PNADRN.RRb; repeat split; first [ (rewrite KS2 by inl; rewrite KS1 by inl; assumption) | (rewrite KS2 by inl; assumption) ]|].
    split; [rewrite KS2 by inl; exact A24|].
    left. split; [reflexivity|]. split; [rewrite EW; clear - Z41 Z42 Ew41 Ew42 B0 B1 B2 B3; lia|].
    split; [rewrite KS2 by inl; rewrite KS1 by inl; exact G18|].
    split; [rewrite KS2 by inl; rewrite A12, Z42; reflexivity|].
    split; [rewrite <- Z41; exact D120| rewrite <- Z42; exact D112]. }
  all: exists fx2, R2, M1, 0xb41c8; split; [eapply msteps_trans; [exact MS1| exact MS2]|]; split; [exact MG1|];
    (split; [intros a Ha Hn; apply FZ1; [exact Ha| clear - Hn; lia]|]);
    (split; [unfold PNADRN.RRb; repeat split; first [ (rewrite KS2 by inl; rewrite KS1 by inl; assumption) | (rewrite KS2 by inl; assumption) ]|]);
    (split; [rewrite KS2 by inl; exact A24|]);
    right; (split; [reflexivity|]); (split; [exact B10|]); (split; [rewrite B18; f_equal; clear; lia|]); (split; [exact B21|]);
    pose proof (PNMW.u32_of_u64_lo RSEGS M1 (S - 120) w41 ltac:(lia) ltac:(lia) H41 D120) as U0;
    pose proof (PNMW.u32_of_u64_hi RSEGS M1 (S - 120) w41 ltac:(lia) ltac:(lia) H41 D120) as U1;
    pose proof (PNMW.u32_of_u64_lo RSEGS M1 (S - 112) w42 ltac:(lia) ltac:(lia) H42 D112) as U2;
    pose proof (PNMW.u32_of_u64_hi RSEGS M1 (S - 112) w42 ltac:(lia) ltac:(lia) H42 D112) as U3;
    replace (S - 120 + 4) with (S - 116) in U1 by (clear; lia); replace (S - 112 + 4) with (S - 108) in U3 by (clear; lia);
    rewrite Ew41 in U0, U1; rewrite Ew42 in U2, U3;
    rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_small in U0 by lia; rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_small in U2 by lia;
    rewrite Z.mul_comm, Z.div_add, Z.div_small, Z.add_0_l in U1 by lia; rewrite Z.mul_comm, Z.div_add, Z.div_small, Z.add_0_l in U3 by lia;
    (split; [exact U0|]); (split; [exact U1|]); (split; [exact U2| exact U3]).
Qed.

Lemma tail0 fx R M k D :
  PNADRN.RRb R0 S F R k -> getr R (reg 18) = Z_to_bv 64 (F + 32) -> getr R (reg 24) = Z_to_bv 64 k -> getr R (reg 12) = Z_to_bv 64 D ->
  0 <= k <= 3 -> 0 <= D < 2 ^ 64 -> L5.writable RSEGS M (S - 256) 256 ->
  exists fx' R', msteps RSEGS (st fx R 0xb4248 M) (st fx' R' 0x77c94 M)
    /\ PNADRN.RRb R0 S F R' k /\ getr R' (reg 18) = Z_to_bv 64 (F + 32) /\ getr R' (reg 24) = Z_to_bv 64 k
    /\ getr R' (reg 1) = Z_to_bv 64 0xb4258 /\ getr R' (reg 10) = Z_to_bv 64 (S - 136) /\ getr R' (reg 11) = Z_to_bv 64 (S - 120)
    /\ getr R' (reg 12) = Z_to_bv 64 16.
Proof.
  intros RRk G18 G24 G12 Hk HD WR.
  pose proof RRk as (G2 & G3 & G4 & G8 & G9 & G19 & G20 & G22 & G23 & G25 & G26 & G27).
  (let T := type of (PNADP3.adkRT0_conc fx R M (fun i => match i with 42%nat => D | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP3.adkRT0_conc fx R M (fun i => match i with 42%nat => D | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & MS1 & KS1 & A1 & A10 & A11 & A12).
  assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1.
  exists fx1, R1. split; [exact MS1|].
  split; [unfold PNADRN.RRb; repeat split; rg R1 KS1|].
  repeat split; rg R1 KS1.
Qed.

Lemma tail0r fx R M k :
  PNADRN.RRb R0 S F R k -> getr R (reg 18) = Z_to_bv 64 (F + 32) -> getr R (reg 24) = Z_to_bv 64 k ->
  0 <= k <= 3 -> L5.writable RSEGS M (S - 256) 256 -> L5.u64_at RSEGS M (S - 168) (F + 32) ->
  exists fx' R' (pc' : Z), msteps RSEGS (st fx R 0xb4258 M) (st fx' R' pc' M)
    /\ ((k = 0 /\ pc' = 0xb4268 /\ PNADRN.RRo R0 S F R') \/ (1 <= k /\ pc' = 0xb4164 /\ PNADRN.RRa R0 S F R' (k - 1))).
Proof.
  intros RRk G18 G24 Hk WR C168.
  pose proof RRk as (G2 & G3 & G4 & G8 & G9 & G19 & G20 & G22 & G23 & G25 & G26 & G27).
  (let T := type of (PNADP3.adkRT0r_conc fx R M (VV k)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP3.adkRT0r_conc fx R M (VV k)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [(MS1 & KS1 & A10 & A14 & A19 & A26 & A28 & A29 & A30 & A31 & CND)|(MS1 & KS1 & A10 & A14 & A19 & A26 & A28 & A29 & A30 & A31 & CND)]);
    (assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1)); subst M1;
    rewrite Z.sub_0_r, Z.mod_small in CND by (clear - Hk; lia).
  - exists fx1, R1, 0xb4268. split; [exact MS1|]. left. split; [clear - CND Hk; lia|]. split; [reflexivity|].
    unfold PNADRN.RRo; repeat split; rg R1 KS1.
  - exists fx1, R1, 0xb4164. split; [exact MS1|]. right. split; [exact CND|]. split; [reflexivity|].
    unfold PNADRN.RRa; repeat split; rg R1 KS1.
Qed.

(* [comment removed for export] *)
Lemma reload fx R M k rr :
  PNADRN.RRb R0 S F R k -> getr R (reg 18) = Z_to_bv 64 (F + 28 + 36 * k) -> getr R (reg 21) = Z_to_bv 64 rr -> getr R (reg 24) = Z_to_bv 64 k ->
  0 <= k <= 3 -> 0 <= rr < 1000000000 -> L5.writable RSEGS M (S - 256) 256 ->
  exists fx' R' (pc' : Z), msteps RSEGS (st fx R 0xb4204 M) (st fx' R' pc' M)
    /\ PNADRN.RRb R0 S F R' k /\ getr R' (reg 18) = Z_to_bv 64 (F + 28 + 36 * k) /\ getr R' (reg 21) = Z_to_bv 64 rr
    /\ getr R' (reg 24) = Z_to_bv 64 k
    /\ ((pc' = 0xb4230 /\ rr = 0) \/ (pc' = 0xb420c /\ 1 <= rr /\ getr R' (reg 10) = Z_to_bv 64 (F + 64 + 36 * k))).
Proof.
  intros RRk G18 G21 G24 Hk Hrr WR.
  pose proof RRk as (G2 & G3 & G4 & G8 & G9 & G19 & G20 & G22 & G23 & G25 & G26 & G27).
  (let T := type of (PNADP3.adkRMr_conc fx R M (fun i => match i with 48%nat => rr | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP3.adkRMr_conc fx R M (fun i => match i with 48%nat => rr | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [(MS1 & KS1 & A28 & A29 & CND)|(MS1 & KS1 & A10 & A24 & A28 & A29 & CND)]);
    (assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1)); subst M1;
    rewrite Z.sub_0_r, Z.mod_small in CND by (clear - Hrr; lia).
  - exists fx1, R1, 0xb4230. split; [exact MS1|].
    split; [unfold PNADRN.RRb; repeat split; rg R1 KS1|].
    split; [rg R1 KS1|]. split; [rg R1 KS1|]. split; [rg R1 KS1|]. left. split; [reflexivity| clear - CND Hrr; lia].
  - exists fx1, R1, 0xb420c. split; [exact MS1|].
    split; [unfold PNADRN.RRb; repeat split; rg R1 KS1|].
    split; [rg R1 KS1|]. split; [rg R1 KS1|]. split; [rg R1 KS1|]. right. split; [reflexivity|]. split; [exact CND| rg R1 KS1].
Qed.

Local Ltac cget D k m j rr Hrr :=
  lazymatch type of D with L5.u32_at _ ?Mx ?a _ =>
    replace a with (F + 32 + 4 * (9 * k + m)) in D by (clear; lia);
    rewrite !PNSDRN2.Qz_fold in D; rewrite ?PNSDRN2.Dz_fold in D; rewrite ?(PNSDRN2.Qz_rr rr) in D; rewrite ?PNSDRN2.QzQn in D;
    first [ rewrite (PNSDRN2.rdS rr j m Hrr eq_refl) in D | rewrite (PNSDRN2.rd0 rr Hrr) in D | rewrite (PNSDRN2.rd8 rr Hrr) in D ];
    lazymatch type of D with L5.u32_at _ _ _ ?v => change (PNADD.cell F Mx (9 * k + m) v) in D end end.

(* [comment removed for export] *)
Definition digits_stmt (k : Z) : Prop :=
  forall fx R M rr, PNADRN.RRb R0 S F R k -> getr R (reg 10) = Z_to_bv 64 (F + 64 + 36 * k) -> getr R (reg 18) = Z_to_bv 64 (F + 28 + 36 * k) ->
    getr R (reg 21) = Z_to_bv 64 rr -> getr R (reg 24) = Z_to_bv 64 k -> 1 <= rr < 1000000000 ->
    L5.writable RSEGS M (S - 256) 256 -> L5.writable RSEGS M F 512 ->
    exists fx' R' M', msteps RSEGS (st fx R 0xb420c M) (st fx' R' 0xb4230 M') /\ mem_grows M M'
      /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 + 36 * k <= a < F + 32 + 36 * k + 36) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
      /\ PNADRN.RRb R0 S F R' k /\ getr R' (reg 18) = Z_to_bv 64 (F + 28 + 36 * k) /\ getr R' (reg 21) = Z_to_bv 64 0
      /\ getr R' (reg 24) = Z_to_bv 64 k
      /\ (forall m, 0 <= m <= 8 -> PNADD.cell F M' (9 * k + m) (PNSDRN2.rdig rr m)).

Local Ltac dig_tac CONC kk :=
  intros fx R M rr RRk G10 G18 G21 G24 Hrr WR WF;
  assert (Hrr' : 0 <= rr < 1000000000) by (clear - Hrr; lia);
  pose proof RRk as (G2 & G3 & G4 & G8 & G9 & G19 & G20 & G22 & G23 & G25 & G26 & G27);
  let P := fresh "P" in
  pose proof (CONC fx R M (fun i => match i with 48%nat => rr | _ => VV kk i end)) as P; cbn beta iota delta [VV] in P;
  L5SAR.feed P ltac:(fsc);
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & MS1 & KS1 & A1 & A10 & A11 & A12 & A21 & A24 & A25 & A31 & D0' & D1' & D2' & D3' & D4' & D5' & D6' & D7' & D8');
  cget D0' kk 0 8%nat rr Hrr'; cget D1' kk 1 7%nat rr Hrr'; cget D2' kk 2 6%nat rr Hrr'; cget D3' kk 3 5%nat rr Hrr'; cget D4' kk 4 4%nat rr Hrr';
  cget D5' kk 5 3%nat rr Hrr'; cget D6' kk 6 2%nat rr Hrr'; cget D7' kk 7 1%nat rr Hrr'; cget D8' kk 8 0%nat rr Hrr';
  exists fx1, R1, M1; split; [exact MS1|]; split; [exact MG1|];
  split; [intros a Ha Hn; apply (FZ1 a Ha); intros Y; apply Hn; lia|];
  split; [unfold PNADRN.RRb; repeat split; rg R1 KS1|];
  split; [rg R1 KS1|]; split; [rg R1 KS1|]; split; [rg R1 KS1|];
  apply PNSDRN2.nine9; assumption.
Lemma digits0 : digits_stmt 0. Proof. unfold digits_stmt. dig_tac PNADP4.adkRD0_conc 0. Qed.
Lemma digits1 : digits_stmt 1. Proof. unfold digits_stmt. dig_tac PNADP4.adkRD1_conc 1. Qed.
Lemma digits2 : digits_stmt 2. Proof. unfold digits_stmt. dig_tac PNADP4.adkRD2_conc 2. Qed.
Lemma digits3 : digits_stmt 3. Proof. unfold digits_stmt. dig_tac PNADP4.adkRD3_conc 3. Qed.
Lemma digits k : 0 <= k <= 3 -> digits_stmt k.
Proof.
  intros Hk. assert (HK : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by (clear - Hk; lia).
  destruct HK as [-> |[-> |[-> | ->]]]; [exact digits0| exact digits1| exact digits2| exact digits3].
Qed.

(* [comment removed for export] *)
Lemma tail fx R M k rr :
  PNADRN.RRb R0 S F R k -> getr R (reg 18) = Z_to_bv 64 (F + 28 + 36 * k) -> getr R (reg 21) = Z_to_bv 64 rr -> getr R (reg 24) = Z_to_bv 64 k ->
  0 <= k <= 3 -> 0 <= rr < 2 ^ 64 -> L5.writable RSEGS M (S - 256) 256 -> L5.u64_at RSEGS M (S - 168) (F + 32) ->
  exists fx' R' (pc' : Z), msteps RSEGS (st fx R 0xb4230 M) (st fx' R' pc' M)
    /\ ((k = 0 /\ pc' = 0xb4268 /\ PNADRN.RRo R0 S F R') \/ (1 <= k /\ pc' = 0xb4164 /\ PNADRN.RRa R0 S F R' (k - 1))).
Proof.
  intros RRk G18 G21 G24 Hk Hrr WR C168.
  pose proof RRk as (G2 & G3 & G4 & G8 & G9 & G19 & G20 & G22 & G23 & G25 & G26 & G27).
  (let T := type of (PNADP3.adkRT_conc fx R M (fun i => match i with 48%nat => rr | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP3.adkRT_conc fx R M (fun i => match i with 48%nat => rr | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [(MS1 & KS1 & A10 & A14 & A18 & A19 & A26 & A28 & A30 & A31 & CND)|(MS1 & KS1 & A10 & A14 & A18 & A19 & A26 & A28 & A30 & A31 & CND)]);
    (assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1)); subst M1;
    rewrite Z.sub_0_r, Z.mod_small in CND by (clear - Hk; lia).
  - exists fx1, R1, 0xb4268. split; [exact MS1|]. left. split; [clear - CND Hk; lia|]. split; [reflexivity|].
    unfold PNADRN.RRo; repeat split; rg R1 KS1.
  - exists fx1, R1, 0xb4164. split; [exact MS1|]. right. split; [exact CND|]. split; [reflexivity|].
    unfold PNADRN.RRa; repeat split; rg R1 KS1.
Qed.

End Call.
End PNADRN2.
