(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare L5Defs L5Kn L5KnA L5Core L5CoreKit L5DefsA L5StepAR PmModelFacts
     PnDecFacts PnSDec128Rnd2 PnADec128Defs PnADec128P3 PnADec128P4 PnADec128Rnd.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADRN2.
Import PNADRN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Abbreviation rdig := PNSDRN2.rdig.

Section Call.
Variables (R0 : bvmap 5 word) (S F first sigma E1 : Z).
Hypothesis FS : 140735332487296 <= S <= 140737488355328.
Hypothesis F32 : S mod 32 = 0.
Hypothesis FF1 : 4096 <= F <= 140737488354816.
Hypothesis FF32 : F mod 32 = 0.
Hypothesis FFSH : 2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784.
Hypothesis FFS : S - 128 + 128 <= F \/ F + 512 <= S - 128.
Hypothesis FFI : 65536 + 6832128 <= F \/ F + 512 <= 65536.
Hypothesis Ffirst : 4096 <= first <= 140737488355280.
Hypothesis Fsig : 0 <= sigma <= 1.
Hypothesis FE1 : 0 <= E1 < 2 ^ 64.
Abbreviation RR := (RRa R0 S F first sigma E1).
Abbreviation cell := (PNADD.cell F).
Definition VV (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => first | 38%nat => first + sigma | 50%nat => F | 59%nat => E1 | _ => 0 end.

Local Ltac cget D k m j rr Hrr :=
  lazymatch type of D with L5.u32_at _ ?Mx ?a _ =>
    replace a with (F + 32 + 4 * (9 * k + m)) in D by (clear; lia);
    rewrite !PNSDRN2.Qz_fold in D; rewrite ?PNSDRN2.Dz_fold in D; rewrite ?(PNSDRN2.Qz_rr rr) in D; rewrite ?PNSDRN2.QzQn in D;
    first [ rewrite (PNSDRN2.rdS rr j m Hrr eq_refl) in D | rewrite (PNSDRN2.rd0 rr Hrr) in D | rewrite (PNSDRN2.rd8 rr Hrr) in D ];
    lazymatch type of D with L5.u32_at _ _ _ ?v => change (PNADD.cell F Mx (9 * k + m) v) in D end end.

(* [comment removed for export] *)
Definition digits_stmt (k : Z) : Prop :=
  forall fx R M rr D0 D1, RR R k -> getr R (reg 7) = Z_to_bv 64 k -> getr R (reg 24) = Z_to_bv 64 (F + 64 + 36 * k) -> getr R (reg 30) = Z_to_bv 64 (F + 28 + 36 * k) ->
    getr R (reg 31) = Z_to_bv 64 rr -> getr R (reg 28) = Z_to_bv 64 D0 -> getr R (reg 29) = Z_to_bv 64 D1 -> 0 <= D0 < 2 ^ 64 -> 0 <= D1 < 2 ^ 64 ->
    1 <= rr < 1000000000 -> L5.writable RSEGS M (S - 128) 128 -> L5.writable RSEGS M F 512 ->
    exists fx' R' M', msteps RSEGS (st fx R 0xb2aa0 M) (st fx' R' 0xb2ac4 M') /\ mem_grows M M'
      /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 + 36 * k <= a < F + 32 + 36 * k + 36) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
      /\ RR R' k /\ getr R' (reg 7) = Z_to_bv 64 k /\ getr R' (reg 28) = Z_to_bv 64 D0 /\ getr R' (reg 29) = Z_to_bv 64 D1
      /\ (forall m, 0 <= m <= 8 -> cell M' (9 * k + m) (rdig rr m)).

Local Ltac dig_tac CONC KSL kk :=
  intros fx R M rr D0 D1 RRk G7 G24 G30 G31 G28 G29 HD0 HD1 Hrr WR WF;
  assert (Hrr' : 0 <= rr < 1000000000) by (clear - Hrr; lia);
  pose proof RRk as (G2 & G3 & G4 & G5 & G6 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G26 & G27);
  let P := fresh "P" in
  pose proof (CONC fx R M (fun i => match i with 47%nat => D0 | 48%nat => rr | 49%nat => D1 | _ => VV i end)) as P; cbn beta iota delta [VV] in P;
  L5SAR.feed P ltac:(first [ assumption | (hnf; assumption) | match goal with |- getr _ _ = Z_to_bv 64 ?z => match goal with H : getr _ _ = Z_to_bv 64 ?y |- _ => replace z with y by lia; exact H end end | lia ]);
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & MS1 & KS1 & A1 & A24 & A25 & A31 & D0' & D1' & D2' & D3' & D4' & D5' & D6' & D7' & D8');
  cget D0' kk 0 8%nat rr Hrr'; cget D1' kk 1 7%nat rr Hrr'; cget D2' kk 2 6%nat rr Hrr'; cget D3' kk 3 5%nat rr Hrr'; cget D4' kk 4 4%nat rr Hrr';
  cget D5' kk 5 3%nat rr Hrr'; cget D6' kk 6 2%nat rr Hrr'; cget D7' kk 7 1%nat rr Hrr'; cget D8' kk 8 0%nat rr Hrr';
  exists fx1, R1, M1; split; [exact MS1|]; split; [exact MG1|];
  split; [intros a Ha Hn; apply (FZ1 a Ha); intros Y; apply Hn; lia|];
  split; [apply (RRa_keep R0 S F first sigma E1 R R1 kk RRk); intros j Hj; apply KS1; revert j Hj; apply (L5K.incl_b RRL KSL); vm_compute; reflexivity|];
  split; [rewrite (KS1 7%nat) by inl; exact G7|];
  split; [rewrite (KS1 28%nat) by inl; exact G28|];
  split; [rewrite (KS1 29%nat) by inl; exact G29|];
  apply PNSDRN2.nine9; assumption.

Lemma digits0 : digits_stmt 0. Proof. unfold digits_stmt. dig_tac PNADP4.adkRD0_conc PNADP4.KS_adkRD0 0. Qed.
Lemma digits1 : digits_stmt 1. Proof. unfold digits_stmt. dig_tac PNADP4.adkRD1_conc PNADP4.KS_adkRD1 1. Qed.
Lemma digits2 : digits_stmt 2. Proof. unfold digits_stmt. dig_tac PNADP4.adkRD2_conc PNADP4.KS_adkRD2 2. Qed.
Lemma digits3 : digits_stmt 3. Proof. unfold digits_stmt. dig_tac PNADP4.adkRD3_conc PNADP4.KS_adkRD3 3. Qed.
Lemma digits k : 0 <= k <= 3 -> digits_stmt k.
Proof.
  intros Hk. assert (HK : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by (clear - Hk; lia).
  destruct HK as [-> |[-> |[-> | ->]]]; [exact digits0| exact digits1| exact digits2| exact digits3].
Qed.

Local Ltac fsc := first [ assumption | (hnf; assumption) | match goal with |- getr _ _ = Z_to_bv 64 ?z => match goal with H : getr _ _ = Z_to_bv 64 ?y |- _ => replace z with y by lia; exact H end end | lia ].
Lemma RRL_sub (KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) RRL = true -> forall j, In j RRL -> In j KS.
Proof. intros H. exact (L5K.incl_b RRL KS H). Qed.

(* [comment removed for export] *)
Lemma reload fx R M k rr D0 D1 :
  RR R k -> getr R (reg 7) = Z_to_bv 64 k -> getr R (reg 28) = Z_to_bv 64 (S - 104) -> getr R (reg 30) = Z_to_bv 64 (F + 28 + 36 * k) -> getr R (reg 31) = Z_to_bv 64 rr ->
  0 <= k <= 3 -> 0 <= rr < 1000000000 -> 0 <= D0 < 2 ^ 64 -> 0 <= D1 < 2 ^ 64 -> L5.writable RSEGS M (S - 128) 128 ->
  L5.u64_at RSEGS M (S - 120) D0 -> L5.u64_at RSEGS M (S - 112) D1 ->
  exists fx' R' (pc' : Z), msteps RSEGS (st fx R 0xb2a90 M) (st fx' R' pc' M)
    /\ RR R' k /\ getr R' (reg 7) = Z_to_bv 64 k /\ getr R' (reg 28) = Z_to_bv 64 D0 /\ getr R' (reg 29) = Z_to_bv 64 D1
    /\ getr R' (reg 30) = Z_to_bv 64 (F + 28 + 36 * k) /\ getr R' (reg 31) = Z_to_bv 64 rr
    /\ ((pc' = 0xb2ac4 /\ rr = 0) \/ (pc' = 0xb2aa0 /\ 1 <= rr /\ getr R' (reg 24) = Z_to_bv 64 (F + 64 + 36 * k))).
Proof.
  intros RRk G7 G28 G30 G31 Hk Hrr HD0 HD1 WR C0 C1.
  pose proof RRk as (G2 & G3 & G4 & G5 & G6 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G26 & G27).
  (let T := type of (PNADP3.adkRM_conc fx R M (fun i => match i with 40%nat => k | 47%nat => D0 | 48%nat => rr | 49%nat => D1 | _ => VV i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP3.adkRM_conc fx R M (fun i => match i with 40%nat => k | 47%nat => D0 | 48%nat => rr | 49%nat => D1 | _ => VV i end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [(MS1 & KS1 & A28 & A29 & CND)|(MS1 & KS1 & A24 & A28 & A29 & CND)]);
    (assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1)); subst M1;
    rewrite Z.sub_0_r, Z.mod_small in CND by (clear - Hrr; lia).
  - exists fx1, R1, 0xb2ac4. split; [exact MS1|].
    split; [apply (RRa_keep R0 S F first sigma E1 R R1 k RRk); intros j Hj; apply KS1; revert j Hj; apply RRL_sub; vm_compute; reflexivity|].
    split; [rewrite (KS1 7%nat) by inl; exact G7|]. split; [exact A28|]. split; [exact A29|].
    split; [rewrite (KS1 30%nat) by inl; exact G30|]. split; [rewrite (KS1 31%nat) by inl; exact G31|]. left. split; [reflexivity| clear - CND Hrr; lia].
  - exists fx1, R1, 0xb2aa0. split; [exact MS1|].
    split; [apply (RRa_keep R0 S F first sigma E1 R R1 k RRk); intros j Hj; apply KS1; revert j Hj; apply RRL_sub; vm_compute; reflexivity|].
    split; [rewrite (KS1 7%nat) by inl; exact G7|]. split; [exact A28|]. split; [exact A29|].
    split; [rewrite (KS1 30%nat) by inl; exact G30|]. split; [rewrite (KS1 31%nat) by inl; exact G31|]. right. split; [reflexivity|]. split; [exact CND|].
    rewrite A24. f_equal. clear; lia.
Qed.

(* [comment removed for export] *)
Definition RRT : list nat := [2; 3; 4; 5; 6; 8; 9; 11; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 26; 27]%nat.
Lemma RR_next R R' k a10 a14 : RR R k -> (forall j, In j RRT -> getr R' (reg j) = getr R (reg j)) ->
  getr R' (reg 10) = Z_to_bv 64 a10 -> a10 = 3 - (k - 1) -> getr R' (reg 14) = Z_to_bv 64 a14 -> a14 = F + 64 + 36 * (k - 1) -> RR R' (k - 1).
Proof.
  intros H KS E10 -> E14 ->. unfold RRa in *.
  destruct H as (G2 & G3 & G4 & G5 & G6 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G26 & G27).
  repeat split; first [ exact E10 | exact E14 | (rewrite KS by (unfold RRT; cbn [In]; tauto); assumption) ].
Qed.
Lemma tail fx R M k D0 D1 :
  RR R k -> getr R (reg 7) = Z_to_bv 64 k -> getr R (reg 28) = Z_to_bv 64 D0 -> getr R (reg 29) = Z_to_bv 64 D1 ->
  0 <= k <= 3 -> 0 <= D0 < 2 ^ 64 -> L5.writable RSEGS M (S - 128) 128 ->
  exists fx' R' (pc' : Z), msteps RSEGS (st fx R 0xb2ac4 M) (st fx' R' pc' M)
    /\ RR R' (k - 1) /\ getr R' (reg 28) = Z_to_bv 64 (D0 / 4294967296) /\ getr R' (reg 30) = Z_to_bv 64 D0 /\ getr R' (reg 29) = Z_to_bv 64 D1
    /\ getr R' (reg 31) = Z_to_bv 64 (k - 1)
    /\ ((pc' = 0xb2af8 /\ k = 0) \/ (pc' = 0xb2a14 /\ 1 <= k)).
Proof.
  intros RRk G7 G28 G29 Hk HD0 WR.
  pose proof RRk as (G2 & G3 & G4 & G5 & G6 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G26 & G27).
  (let T := type of (PNADP3.adkRT_conc fx R M (fun i => match i with 40%nat => k | 47%nat => D0 | _ => VV i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP3.adkRT_conc fx R M (fun i => match i with 40%nat => k | 47%nat => D0 | _ => VV i end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [(MS1 & KS1 & A10 & A14 & A28 & A30 & A31 & CND)|(MS1 & KS1 & A10 & A14 & A28 & A30 & A31 & CND)]);
    (assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1)); subst M1;
    rewrite Z.sub_0_r, Z.mod_small in CND by (clear - Hk; lia).
  - exists fx1, R1, 0xb2af8. split; [exact MS1|].
    split; [eapply (RR_next R R1 k); [exact RRk| intros j Hj; apply KS1; revert j Hj; apply (L5K.incl_b RRT); vm_compute; reflexivity| exact A10| clear; lia| exact A14| clear; lia]|].
    split; [exact A28|]. split; [exact A30|]. split; [rewrite (KS1 29%nat) by inl; exact G29|]. split; [exact A31|]. left. split; [reflexivity| clear - CND Hk; lia].
  - exists fx1, R1, 0xb2a14. split; [exact MS1|].
    split; [eapply (RR_next R R1 k); [exact RRk| intros j Hj; apply KS1; revert j Hj; apply (L5K.incl_b RRT); vm_compute; reflexivity| exact A10| clear; lia| exact A14| clear; lia]|].
    split; [exact A28|]. split; [exact A30|]. split; [rewrite (KS1 29%nat) by inl; exact G29|]. split; [exact A31|]. right. split; [reflexivity| exact CND].
Qed.

End Call.
End PNADRN2.
