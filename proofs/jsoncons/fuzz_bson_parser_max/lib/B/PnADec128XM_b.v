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
     PnDecFacts PnDecBv PnMemW PnSDec128Rnd2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128Defs_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnADec128Bv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128P7_b PnADec128Rnd_b PnADec128Mid_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADXM.
Import PNADRN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

(* [comment removed for export] *)
Definition KB : list nat := [2; 3; 4; 8; 9; 19; 23; 26; 27]%nat.
Definition keeps (R R' : bvmap 5 word) : Prop := forall j, In j KB -> getr R' (reg j) = getr R (reg j).
Lemma keeps_of (KS : list nat) R R' : forallb (fun k => existsb (Nat.eqb k) KS) KB = true -> (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) -> keeps R R'.
Proof. intros H K j Hj. apply K. revert j Hj. exact (L5K.incl_b KB KS H). Qed.
Lemma keeps_trans R1 R2 R3 : keeps R1 R2 -> keeps R2 R3 -> keeps R1 R3.
Proof. intros A B j Hj. rewrite (B j Hj). exact (A j Hj). Qed.
(* [comment removed for export] *)
Definition RF (R0 : bvmap 5 word) (S F : Z) (R : bvmap 5 word) : Prop :=
  PNADD.RBA R0 S F R /\ getr R (reg 19) = Z_to_bv 64 PNADD.SBv.
Lemma RF_keeps R0 S F R R' : RF R0 S F R -> keeps R R' -> RF R0 S F R'.
Proof.
  intros ((G2 & G3 & G4 & G8 & G9 & G23 & G26 & G27) & G19) K. unfold RF, PNADD.RBA.
  rewrite !(K 2%nat), !(K 3%nat), !(K 4%nat), !(K 8%nat), !(K 9%nat), !(K 19%nat), !(K 23%nat), !(K 26%nat), !(K 27%nat) by (unfold KB; cbn [In]; tauto).
  repeat split; assumption.
Qed.

Section Call.
Variables (R0 : bvmap 5 word) (S F first sigma : Z).
Hypothesis FS : 140735332487296 <= S <= 140737488355328.
Hypothesis F32 : S mod 32 = 0.
Hypothesis FF1 : 4096 <= F <= 140737488354816.
Hypothesis FF32 : F mod 32 = 0.
Hypothesis FFSH : 2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784.
Hypothesis FFS : S - 256 + 256 <= F \/ F + 512 <= S - 256.
Hypothesis FFI : 65536 + 6840320 <= F \/ F + 512 <= 65536.
Hypothesis Ffirst : 4096 <= first <= 140737488355280.
Hypothesis Ff8 : first mod 8 = 0.
Hypothesis FfSH : 2147446784 + 17592186048512 <= first \/ first + 48 <= 2147446784.
Hypothesis FfS : S - 256 + 256 <= first \/ first + 48 <= S - 256.
Hypothesis FfI : 65536 + 6840320 <= first \/ first + 48 <= 65536.
Hypothesis Fsig : 0 <= sigma <= 1.
Abbreviation RFr := (RF R0 S F).
Definition VV (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => first | 44%nat => sigma | 50%nat => F | _ => 0 end.
Local Ltac fsc := first [ assumption | (hnf; assumption) | match goal with |- getr _ _ = Z_to_bv 64 ?z => match goal with H : getr _ _ = Z_to_bv 64 ?y |- _ => replace z with y by lia; exact H end end | lia ].
Local Ltac kp KS := (let j := fresh "j" in let Hj := fresh "Hj" in unfold keeps; intros j Hj; apply KS; revert j Hj; apply (L5K.incl_b KB); vm_compute; reflexivity).
Local Ltac openRF H := destruct H as ((?G2 & ?G3 & ?G4 & ?G8 & ?G9 & ?G23 & ?G26 & ?G27) & ?G19); unfold PNADD.SH, PNADD.SBv in *.

(* [comment removed for export] *)
Lemma fork fx R M hi lo :
  RFr R -> getr R (reg 18) = Z_to_bv 64 (F + 32) -> getr R (reg 20) = Z_to_bv 64 first -> getr R (reg 30) = Z_to_bv 64 (first + sigma) ->
  getr R (reg 11) = Z_to_bv 64 hi -> getr R (reg 10) = Z_to_bv 64 lo -> getr R (reg 13) = Z_to_bv 64 (hi / 4294967296) ->
  0 <= hi < 2 ^ 64 -> 0 <= lo < 2 ^ 64 -> L5.writable RSEGS M (S - 256) 256 ->
  exists fx' R' (pc' : Z), msteps RSEGS (st fx R 0xb4994 M) (st fx' R' pc' M) /\ keeps R R'
    /\ getr R' (reg 18) = Z_to_bv 64 (F + 32) /\ getr R' (reg 20) = Z_to_bv 64 first /\ getr R' (reg 30) = Z_to_bv 64 (first + sigma)
    /\ getr R' (reg 11) = Z_to_bv 64 hi /\ getr R' (reg 10) = Z_to_bv 64 lo /\ getr R' (reg 13) = Z_to_bv 64 (hi / 4294967296)
    /\ (pc' = 0xb49d8 \/ pc' = 0xb49ac \/ pc' = 0xb4a04).
Proof.
  intros RFR G18 G20 G30 G11 G10 G13 Hhi Hlo WR. openRF RFR.
  assert (H39 : 0 <= hi / 4294967296 <= 4294967295) by (split; [apply Z.div_pos; clear - Hhi; lia| apply Z.lt_succ_r; apply Z.div_lt_upper_bound; clear - Hhi; lia]).
  (let T := type of (PNADP7.adkX1_conc fx R M (fun j => match j with 35%nat => lo | 36%nat => hi | 39%nat => hi / 4294967296 | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP7.adkX1_conc fx R M (fun j => match j with 35%nat => lo | 36%nat => hi | 39%nat => hi / 4294967296 | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [(MS1 & KS1 & _)|[(MS1 & KS1 & _)|(MS1 & KS1 & _)]]);
    (assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1)); subst M1.
  - exists fx1, R1, 0xb49d8. split; [exact MS1|]. split; [kp KS1|].
    split; [rewrite (KS1 18%nat) by inl; exact G18|]. split; [rewrite (KS1 20%nat) by inl; exact G20|]. split; [rewrite (KS1 30%nat) by inl; exact G30|].
    split; [rewrite (KS1 11%nat) by inl; exact G11|]. split; [rewrite (KS1 10%nat) by inl; exact G10|]. split; [rewrite (KS1 13%nat) by inl; exact G13|]. left. reflexivity.
  - exists fx1, R1, 0xb49ac. split; [exact MS1|]. split; [kp KS1|].
    split; [rewrite (KS1 18%nat) by inl; exact G18|]. split; [rewrite (KS1 20%nat) by inl; exact G20|]. split; [rewrite (KS1 30%nat) by inl; exact G30|].
    split; [rewrite (KS1 11%nat) by inl; exact G11|]. split; [rewrite (KS1 10%nat) by inl; exact G10|]. split; [rewrite (KS1 13%nat) by inl; exact G13|]. right; left. reflexivity.
  - exists fx1, R1, 0xb4a04. split; [exact MS1|]. split; [kp KS1|].
    split; [rewrite (KS1 18%nat) by inl; exact G18|]. split; [rewrite (KS1 20%nat) by inl; exact G20|]. split; [rewrite (KS1 30%nat) by inl; exact G30|].
    split; [rewrite (KS1 11%nat) by inl; exact G11|]. split; [rewrite (KS1 10%nat) by inl; exact G10|]. split; [rewrite (KS1 13%nat) by inl; exact G13|]. right; right. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma inf_call fx R M :
  RFr R -> getr R (reg 18) = Z_to_bv 64 (F + 32) -> getr R (reg 20) = Z_to_bv 64 first -> getr R (reg 30) = Z_to_bv 64 (first + sigma) ->
  L5.writable RSEGS M (S - 256) 256 -> L5.u8_at RSEGS M 6759112 16 -> L5.u64_at RSEGS M (S - 176) (first + 42) ->
  exists fx' R', msteps RSEGS (st fx R 0xb49ac M) (st fx' R' 0x77c94 M) /\ keeps R R'
    /\ getr R' (reg 1) = Z_to_bv 64 739916 /\ getr R' (reg 10) = Z_to_bv 64 (first + sigma) /\ getr R' (reg 11) = Z_to_bv 64 6759113
    /\ getr R' (reg 12) = Z_to_bv 64 8 /\ getr R' (reg 18) = Z_to_bv 64 6759112 /\ getr R' (reg 20) = Z_to_bv 64 (first + sigma).
Proof.
  intros RFR G18 G20 G30 WR C0 C176. openRF RFR.
  (let T := type of (PNADP7.adkXI_conc fx R M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP7.adkXI_conc fx R M VV) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & MS1 & KS1 & A1 & A10 & A11 & A12 & A18 & A20 & _).
  assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1.
  exists fx1, R1. split; [exact MS1|]. split; [kp KS1|].
  split; [exact A1|]. split; [exact A10|]. split; [exact A11|]. split; [exact A12|]. split; [exact A18| exact A20].
Qed.

(* [comment removed for export] *)
Lemma sh_buf (M : mem) q : L5KA.zeros_at M (first / 8 + 2147450880) 6 -> first <= q < first + 48 -> L5KA.zeros_at M (q / 8 + 2147450880) 1.
Proof.
  intros Z Hq. pose proof (Z.div_mod first 8 ltac:(clear; lia)) as E8. rewrite Ff8, Z.add_0_r in E8.
  assert (Q1 : first / 8 <= q / 8) by (apply Z.div_le_mono; clear - Hq; lia).
  assert (Q2 : q / 8 < first / 8 + 6) by (apply Z.div_lt_upper_bound; clear - Hq E8; lia).
  apply (L5KA.zeros_at_sub M _ _ _ _ Z); clear - Q1 Q2; lia.
Qed.

(* [comment removed for export] *)
Definition tail_stmt (pc0 : Z) (r : nat) (b : Z) : Prop :=
  forall fx R M q, RFr R -> getr R (reg r) = Z_to_bv 64 b -> getr R (reg 24) = Z_to_bv 64 q -> first <= q <= first + 40 -> b <= q ->
    L5.writable RSEGS M (S - 256) 256 -> L5.writable RSEGS M first 42 -> L5KA.zeros_at M (first / 8 + 2147450880) 6 ->
    exists fx' R' M', msteps RSEGS (st fx R pc0 M) (st fx' R' 0xb46b0 M') /\ mem_grows M M'
      /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 1) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
      /\ PNADD.stE R0 S F q 0 R'.
Local Ltac tail_tac CONC :=
  intros fx R M q RFR G Gq Hq HB WR WF ZF; pose proof RFR as RFR'; openRF RFR;
  pose proof (sh_buf M q ZF ltac:(clear - Hq; lia)) as ZQ;
  pose proof (L5.writable_sub RSEGS M first 42 q 1 WF ltac:(clear - Hq; lia) ltac:(clear - Hq; lia)) as WQ;
  lazymatch type of G with getr _ _ = Z_to_bv 64 ?v => assert (HBm : v mod 2 ^ 64 <= q) by (rewrite Z.mod_small by lia; exact HB) end;
  let P := fresh "P" in
  pose proof (CONC fx R M (fun j => match j with 52%nat => q | _ => VV j end)) as P; cbn beta iota delta [VV] in P;
  L5SAR.feed P ltac:(fsc);
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & MS1 & KS1 & _ & _ & A24 & A25 & _);
  exists fx1, R1, M1; split; [exact MS1|]; split; [exact MG1|];
  split; [intros a Ha Hn; apply (FZ1 a Ha); intros Y; apply Hn; clear - Y; lia|];
  unfold PNADD.stE; split; [exact (proj1 (RF_keeps R0 S F R R1 RFR' ltac:(kp KS1)))|];
  split; [exact A24| exact A25].
Lemma inf_store : tail_stmt 0xb4a90 20%nat (first + sigma). Proof. unfold tail_stmt. tail_tac PNADP7.adkXT_conc. Qed.
Lemma nan_store : tail_stmt 0xb4ad0 21%nat first. Proof. unfold tail_stmt. tail_tac PNADP7.adkXU_conc. Qed.

(* [comment removed for export] *)
Lemma inf_tail fx R M :
  RFr R -> getr R (reg 18) = Z_to_bv 64 6759112 -> getr R (reg 20) = Z_to_bv 64 (first + sigma) ->
  L5.writable RSEGS M (S - 256) 256 -> L5.u8_at RSEGS M 6759112 16 -> L5.writable RSEGS M first 42 -> L5KA.zeros_at M (first / 8 + 2147450880) 6 ->
  exists fx' R' M', msteps RSEGS (st fx R 0xb4a4c M) (st fx' R' 0xb46b0 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (first + sigma + 8 <= a < first + sigma + 8 + 1) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ PNADD.stE R0 S F (first + sigma + 8) 0 R'.
Proof.
  intros RFR G18 G20 WR C0 WF ZF. pose proof RFR as RFR'. openRF RFR.
  (let T := type of (PNADP7.adkXJ_conc fx R M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP7.adkXJ_conc fx R M VV) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & MS1 & KS1 & _ & _ & _ & A24).
  assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1.
  assert (B20 : getr R1 (reg 20) = Z_to_bv 64 (first + sigma)) by (rewrite (KS1 20%nat) by inl; exact G20).
  destruct (inf_store fx1 R1 M (first + sigma + 8) (RF_keeps R0 S F R R1 RFR' ltac:(kp KS1)) B20 A24 ltac:(clear - Fsig; lia) ltac:(clear; lia) WR WF ZF) as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & SE).
  exists fx2, R2, M2. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG2|]. split; [exact FZ2| exact SE].
Qed.

(* [comment removed for export] *)
Lemma nan_call fx R M :
  RFr R -> getr R (reg 18) = Z_to_bv 64 (F + 32) -> getr R (reg 20) = Z_to_bv 64 first -> getr R (reg 30) = Z_to_bv 64 (first + sigma) ->
  L5.writable RSEGS M (S - 256) 256 -> L5.u8_at RSEGS M 6759144 6 -> L5.u64_at RSEGS M (S - 176) (first + 42) ->
  exists fx' R', msteps RSEGS (st fx R 0xb49d8 M) (st fx' R' 0x77c94 M) /\ keeps R R'
    /\ getr R' (reg 1) = Z_to_bv 64 739956 /\ getr R' (reg 10) = Z_to_bv 64 first /\ getr R' (reg 11) = Z_to_bv 64 6759145
    /\ getr R' (reg 12) = Z_to_bv 64 3 /\ getr R' (reg 18) = Z_to_bv 64 6759144 /\ getr R' (reg 20) = Z_to_bv 64 first /\ getr R' (reg 21) = Z_to_bv 64 first.
Proof.
  intros RFR G18 G20 G30 WR C0 C176. openRF RFR.
  (let T := type of (PNADP7.adkXN_conc fx R M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP7.adkXN_conc fx R M VV) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & MS1 & KS1 & A1 & A10 & A11 & A12 & A18 & A21).
  assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1.
  exists fx1, R1. split; [exact MS1|]. split; [kp KS1|].
  split; [exact A1|]. split; [exact A10|]. split; [exact A11|]. split; [exact A12|]. split; [exact A18|].
  split; [rewrite (KS1 20%nat) by inl; exact G20| exact A21].
Qed.
Lemma nan_tail fx R M :
  RFr R -> getr R (reg 18) = Z_to_bv 64 6759144 -> getr R (reg 20) = Z_to_bv 64 first -> getr R (reg 21) = Z_to_bv 64 first ->
  L5.writable RSEGS M (S - 256) 256 -> L5.u8_at RSEGS M 6759144 6 -> L5.writable RSEGS M first 42 -> L5KA.zeros_at M (first / 8 + 2147450880) 6 ->
  exists fx' R' M', msteps RSEGS (st fx R 0xb4a74 M) (st fx' R' 0xb46b0 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (first + 3 <= a < first + 3 + 1) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ PNADD.stE R0 S F (first + 3) 0 R'.
Proof.
  intros RFR G18 G20 G21 WR C0 WF ZF. pose proof RFR as RFR'. openRF RFR.
  (let T := type of (PNADP7.adkXO_conc fx R M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP7.adkXO_conc fx R M VV) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & MS1 & KS1 & _ & _ & A21 & A24).
  assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1.
  destruct (nan_store fx1 R1 M (first + 3) (RF_keeps R0 S F R R1 RFR' ltac:(kp KS1)) A21 A24 ltac:(clear; lia) ltac:(clear; lia) WR WF ZF) as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & SE).
  exists fx2, R2, M2. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG2|]. split; [exact FZ2| exact SE].
Qed.

(* [comment removed for export] *)
Lemma msb8 hi : ((131072 * hi) mod 2 ^ 64 / 9223372036854775808 + 8) mod 2 ^ 64 <= 7 -> False.
Proof.
  intros H. pose proof (Z.mod_pos_bound (131072 * hi) (2 ^ 64) ltac:(clear; lia)) as B.
  assert (Q : 0 <= (131072 * hi) mod 2 ^ 64 / 9223372036854775808 <= 1) by (split; [apply Z.div_pos; clear - B; lia| apply Z.lt_succ_r; apply Z.div_lt_upper_bound; clear - B; lia]).
  rewrite Z.mod_small in H by (clear - Q; lia). clear - H Q. lia.
Qed.
Lemma noncanon fx R M hi lo :
  RFr R -> getr R (reg 18) = Z_to_bv 64 (F + 32) -> getr R (reg 20) = Z_to_bv 64 first -> getr R (reg 30) = Z_to_bv 64 (first + sigma) ->
  getr R (reg 11) = Z_to_bv 64 hi -> getr R (reg 10) = Z_to_bv 64 lo -> getr R (reg 13) = Z_to_bv 64 (hi / 4294967296) ->
  0 <= hi < 2 ^ 64 -> 0 <= lo < 2 ^ 64 -> L5.writable RSEGS M (S - 256) 256 -> L5.writable RSEGS M F 512 -> L5.img_clear M 65536 1282048 ->
  exists fx' R' M', msteps RSEGS (st fx R 0xb4a04 M) (st fx' R' 0xb4294 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 240 <= a < S - 176 \/ S - 168 <= a < S - 160 \/ S - 136 <= a < S - 120 \/ F + 32 <= a < F + 36) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ PNADD.stP R0 S F first sigma (Z.land (hi / 4294967296 / 32768) 16383) 0 1 R' /\ PNADD.cell F M' 0 0.
Proof.
  intros RFR G18 G20 G30 G11 G10 G13 Hhi Hlo WR WF IC. pose proof RFR as RFR'. openRF RFR.
  assert (H39 : 0 <= hi / 4294967296 <= 4294967295) by (split; [apply Z.div_pos; clear - Hhi; lia| apply Z.lt_succ_r; apply Z.div_lt_upper_bound; clear - Hhi; lia]).
  set (E1 := hi / 4294967296 / 32768).
  assert (FE1 : 0 <= E1 < 2 ^ 64) by (subst E1; split; [apply Z.div_pos; clear - H39; lia| apply Z.div_lt_upper_bound; clear - H39; lia]).
  (let T := type of (PNADP7.adkXC_conc fx R M (fun j => match j with 35%nat => lo | 36%nat => hi | 39%nat => hi / 4294967296 | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP7.adkXC_conc fx R M (fun j => match j with 35%nat => lo | 36%nat => hi | 39%nat => hi / 4294967296 | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [(MS1 & KS1 & A5 & _ & _ & _ & _ & _ & _ & A17 & _)
     |[(MS1 & KS1 & A5 & _ & _ & _ & _ & _ & _ & _ & A17 & _)
     |[(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C7 & _)
     |[(MS1 & KS1 & A5 & _ & _ & _ & _ & _ & _ & _ & A17 & _)
     |[(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C7 & _)
     |[(MS1 & KS1 & A5 & _ & _ & _ & _ & _ & _ & A17 & _)
     |(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C7 & _)]]]]]]);
    try (exfalso; exact (msb8 hi C7));
    (assert (B17 : getr R1 (reg 17) = Z_to_bv 64 E1) by exact A17);
    (assert (SZ : PNADD.stZ R0 S F first sigma (Z.land E1 16383) R1)
      by (pose proof (RF_keeps R0 S F R R1 RFR' ltac:(kp KS1)) as (RBA1 & B19); unfold PNADD.stZ, PNADD.RBO;
          split; [split; [exact RBA1|]; split; [exact B19|]; split; [rewrite (KS1 20%nat) by inl; exact G20| rewrite (KS1 30%nat) by inl; exact G30]|];
          split; [rewrite (KS1 18%nat) by inl; exact G18|]; split; [rewrite B17, (PNSDRN2.bvu_small E1 FE1); reflexivity| exact A5]));
    (pose proof (L5.writable_grows RSEGS _ _ _ _ MG1 WR) as WR1; pose proof (L5.writable_grows RSEGS _ _ _ _ MG1 WF) as WF1);
    (pose proof (PNADMID.iszero R0 S F first sigma E1) as IZ; L5SAR.feed IZ ltac:(first [assumption | lia]); specialize (IZ 0 ltac:(clear; lia));
     destruct (IZ fx1 R1 M1 (Z.land E1 16383) SZ B17 WR1 WF1) as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & SP & CZ);
     exists fx2, R2, M2; split; [eapply msteps_trans; [exact MS1| exact MS2]|]; split; [eapply mem_grows_trans; [exact MG1| exact MG2]|];
     split; [intros a Ha Hn; rewrite (FZ2 a Ha) by (clear - Hn; lia); apply FZ1; [exact Ha| clear - Hn; lia ..]|]; split; [exact SP| exact CZ]).
Qed.

End Call.
End PNADXM.
