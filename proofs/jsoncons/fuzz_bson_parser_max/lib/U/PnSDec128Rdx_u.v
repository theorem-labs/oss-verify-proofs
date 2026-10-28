(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk L5Defs L5Core L5CoreKit
     AxSymExec3. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSDec128Defs_u PnSDec128XP_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSDRDX.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

(* [comment removed for export] *)
Lemma slt_small (ev : nat -> word) (bl : nat -> list byte) a b :
  0 <= a < 2 ^ 62 -> 0 <= b < 2 ^ 62 -> ev 70%nat = Z_to_bv 64 a -> ev 59%nat = Z_to_bv 64 b ->
  bv_unsigned (AX2.edenot (AX2.Env ev bl) (AX2.EAlu Instr.ALU_SLT (AX2.EVar 70) (AX2.EVar 59))) = (if Z.ltb a b then 1 else 0).
Proof.
  intros Ha Hb Ea Eb. cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div]. rewrite Ea, Eb. unfold bv_lts. rewrite !Z_to_bv_signed.
  unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
  rewrite (Z.mod_small (a + 2 ^ 63)) by (clear -Ha; lia). rewrite (Z.mod_small (b + 2 ^ 63)) by (clear -Hb; lia).
  replace (a + 2 ^ 63 - 2 ^ 63) with a by (clear; lia). replace (b + 2 ^ 63 - 2 ^ 63) with b by (clear; lia).
  destruct (Z.ltb a b); reflexivity.
Qed.
Lemma to_bv_of_unsigned (b : bv 64) z : bv_unsigned b = z -> b = Z_to_bv 64 z.
Proof. intros <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* [comment removed for export] *)
Lemma subw_val sd rd : 0 <= rd <= sd -> sd <= 36 ->
  ((((4294967296 * sd) mod 2 ^ 64) + ((18446744069414584320 * rd) mod 2 ^ 64)) mod 2 ^ 64) / 4294967296 = sd - rd.
Proof.
  intros H1 H2. rewrite <- Zplus_mod. replace (4294967296 * sd + 18446744069414584320 * rd) with (4294967296 * (sd - rd) + rd * 2 ^ 64) by (clear; lia).
  rewrite Z.mod_add by (clear; lia). rewrite Z.mod_small by (clear -H1 H2; lia). rewrite Z.mul_comm, Z.div_mul by (clear; lia). reflexivity.
Qed.
Lemma land3_0 a : 0 <= a -> a mod 4 = 0 -> Z.land a 3 = 0.
Proof. intros Ha Hm. change 3 with (Z.ones 2). rewrite Z.land_ones by (clear; lia). exact Hm. Qed.
Local Ltac bvc := apply bv_eq; vm_compute; reflexivity.

Section Rdx.
Variables (R0 : bvmap 5 word) (S first sigma e r : Z).
Let u8 := bv_unsigned (getr R0 (reg 8)).
Let u9 := bv_unsigned (getr R0 (reg 9)).
Let u18 := bv_unsigned (getr R0 (reg 18)).
Let u19 := bv_unsigned (getr R0 (reg 19)).
Let u20 := bv_unsigned (getr R0 (reg 20)).
Let u21 := bv_unsigned (getr R0 (reg 21)).
Let u22 := bv_unsigned (getr R0 (reg 22)).
Let u23 := bv_unsigned (getr R0 (reg 23)).
Hypothesis FS : 140735332483312 <= S <= 140737488355328.
Hypothesis F16 : S mod 16 = 0.
Hypothesis Ffirst : 4096 <= first <= 140737488355286.
Hypothesis Fdj : S - 256 + 256 <= first \/ first + 42 <= S - 256.
Hypothesis Fimg : first + 42 <= 65536 \/ 962560 <= first.      (* [comment removed for export] *)
Hypothesis Fsig : 0 <= sigma <= 1.
Hypothesis Fe : 0 <= e <= 16383.
Hypothesis Fr : 0 <= r < 2 ^ 47.

Abbreviation MI := (PNSDD.MI R0 S first r).
Definition VV (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => first | 38%nat => sigma | 50%nat => e
  | 60%nat => r | 61%nat => u8 | 62%nat => u9 | 63%nat => u18 | 64%nat => u19 | 65%nat => u20 | 66%nat => u21 | 67%nat => u22 | 68%nat => u23 | _ => 0 end.
(* [comment removed for export] *)
Definition QR (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 256) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4) /\ getr R (reg 8) = Z_to_bv 64 (first + 42)
  /\ getr R (reg 24) = getr R0 (reg 24) /\ getr R (reg 25) = getr R0 (reg 25) /\ getr R (reg 26) = getr R0 (reg 26) /\ getr R (reg 27) = getr R0 (reg 27).

Lemma ufacts : 0 <= u8 < 2 ^ 64 /\ 0 <= u9 < 2 ^ 64 /\ 0 <= u18 < 2 ^ 64 /\ 0 <= u19 < 2 ^ 64 /\ 0 <= u20 < 2 ^ 64 /\ 0 <= u21 < 2 ^ 64
  /\ 0 <= u22 < 2 ^ 64 /\ 0 <= u23 < 2 ^ 64.
Proof.
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 8))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 9))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 18))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 19))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 20))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 21))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 22))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 23))).
  unfold bv_modulus in *. subst u8 u9 u18 u19 u20 u21 u22 u23. repeat split; lia.
Qed.
Lemma ptr_land z : 0 <= z <= 36 -> Z.land (bv_unsigned (Z_to_bv 64 (S - 216 + 4 * z))) 3 = 0.
Proof. intros Hz. rewrite L5.unsigned_lit by (clear -FS Hz; lia). apply land3_0; [clear -FS Hz; lia|]. clear -F16 FS. Lia.lia. Qed.

(* [comment removed for export] *)
Lemma MI_out M M' : MI M -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (first + 0 <= a < first + 0 + 42) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> MI M'.
Proof.
  intros (W1 & W2 & IC & SV) MG FZ. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W1)|]. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W2)|].
  split. { apply (PMKP.clear_agree M M' 65536 754672); [|exact IC]. intros i Hi. apply FZ; clear -Hi FS Ffirst Fimg; lia. }
  destruct SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply FZ; clear -Hi FS Fdj; lia| clear -FS; lia| clear -FS; lia| eassumption]).
Qed.
Lemma out_trans (M1 M2 M3 : word -> option byte) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ (first + 0 <= a < first + 0 + 42) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (first + 0 <= a < first + 0 + 42) -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (first + 0 <= a < first + 0 + 42) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
Proof. intros A B a Ha N. rewrite (B a Ha N). apply A; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma frac_loop (m : nat) : forall fx R M j off boff cnt sd,
  QR R -> getr R (reg 10) = Z_to_bv 64 (S - 216 + boff) -> getr R (reg 12) = Z_to_bv 64 (j + 1) -> getr R (reg 13) = Z_to_bv 64 (first + off + j) ->
  getr R (reg 14) = Z_to_bv 64 0 -> getr R (reg 15) = Z_to_bv 64 cnt -> getr R (reg 16) = Z_to_bv 64 (-5) ->
  MI M -> L5.defined M (S - 216) 144 ->
  1 <= sd <= 36 -> 1 <= cnt <= 36 -> 0 <= j < cnt -> cnt - j <= Z.of_nat m -> 2 <= off -> off + j <= 41 -> 0 <= boff -> boff + 4 * (cnt - 1 - j) <= 140 ->
  exists fx' R' M' n, msteps RSEGS (st fx R 0x39048 M) (st fx' R' 0x38f6c M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (first + 0 <= a < first + 0 + 42) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ MI M' /\ QR R' /\ getr R' (reg 19) = Z_to_bv 64 (first + off + n) /\ j < n <= cnt /\ off + n <= 42.
Proof.
  induction m as [|m IH]; intros fx R M j off boff cnt sd (G2 & G3 & G4 & G8 & G24 & G25 & G26 & G27) G10 G12 G13 G14 G15 G16 MIM DEF Hsd Hcnt Hj Hm Hoff Hoj Hb0 Hb1;
    [exfalso; clear -Hj Hm; lia|].
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  (let T := type of (PNSDXP.dkXL2a_conc fx R M (fun i => match i with 55%nat => sd | 57%nat => off | 58%nat => boff | 71%nat => cnt | 72%nat => j | _ => VV i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDXP.dkXL2a_conc fx R M (fun i => match i with 55%nat => sd | 57%nat => off | 58%nat => boff | 71%nat => cnt | 72%nat => j | _ => VV i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A19).
  assert (MI1 : MI M1) by exact (MI_out M M1 MIM MG1 FZ1).
  pose proof MI1 as (WRf1 & WR11 & IC1 & SV1). pose proof SV1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  (let T := type of (PNSDXP.dkXL2b_conc fx1 R1 M1 (fun i => match i with 55%nat => sd | 57%nat => off | 58%nat => boff | 71%nat => cnt | 72%nat => j | _ => VV i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDXP.dkXL2b_conc fx1 R1 M1 (fun i => match i with 55%nat => sd | 57%nat => off | 58%nat => boff | 71%nat => cnt | 72%nat => j | _ => VV i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS1 _) by PMK.inl; PMK.sc | rewrite A19; f_equal; clear; lia])).
  destruct P as (fx2 & R2 & M2 & MG2 & FW2 & FZ2 & [ (MS2 & KS2 & B10 & B12 & B13 & CLT & CJ) | [ (MS2 & KS2 & B10 & B12 & B13 & CGE & CJ) | (MS2 & KS2 & CEXIT) ] ]);
    assert (EM : M2 = M1) by (apply functional_extensionality; exact FW2); subst M2.
  - (* [comment removed for export] *)
    rewrite Z.mod_small in CJ by (clear -Hj Hcnt; lia).
    assert (Hoj1 : off + (j + 1) <= 41).
    { revert CLT. rewrite (Z.mod_small (first + off)) by (clear -Ffirst Hoff Hoj Hj; lia). rewrite (Z.mod_small (first + off + j)) by (clear -Ffirst Hoff Hoj Hj; lia).
      rewrite (Z.mod_small (first + off + j + 1)) by (clear -Ffirst Hoff Hoj Hj; lia). rewrite (Z.mod_small (first + 42)) by (clear -Ffirst; lia). clear -Hoj. intros CLT. lia. }
    destruct (IH fx2 R2 M1 (j + 1) off (boff + 4) cnt sd) as (fx' & R' & M' & n & MS & MG & FZ & MI' & QR' & E19 & Hn & Hon).
    { unfold QR. rewrite !(KS2 _) by PMK.inl. rewrite !(KS1 _) by PMK.inl. repeat apply conj; assumption. }
    { rewrite B10; f_equal; clear; lia. } { rewrite B12; f_equal; clear; lia. } { rewrite B13; f_equal; clear; lia. }
    { rewrite (KS2 _), (KS1 _) by PMK.inl. exact G14. } { rewrite (KS2 _), (KS1 _) by PMK.inl. exact G15. } { rewrite (KS2 _), (KS1 _) by PMK.inl. exact G16. }
    { exact MI1. } { exact (L5.defined_grows M M1 _ _ MG1 DEF). } { exact Hsd. } { exact Hcnt. } { clear -Hj CJ; lia. } { clear -Hm; lia. } { exact Hoff. } { exact Hoj1. }
    { clear -Hb0; lia. } { clear -Hb1 CJ Hj; lia. }
    exists fx', R', M', n. split; [eapply msteps_trans; [exact MS1|]; eapply msteps_trans; [exact MS2| exact MS]|]. split; [exact (mem_grows_trans _ _ _ MG1 MG)|].
    split; [exact (out_trans M M1 M' FZ1 FZ)|]. split; [exact MI'|]. split; [exact QR'|]. split; [exact E19|]. clear -Hn Hon Hj. split; lia.
  - (* [comment removed for export] *)
    rewrite Z.mod_small in CJ by (clear -Hj Hcnt; lia).
    exists fx2, R2, M1, (j + 1). split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FZ1|]. split; [exact MI1|].
    split. { unfold QR. rewrite !(KS2 _) by PMK.inl. rewrite !(KS1 _) by PMK.inl. repeat apply conj; assumption. }
    split; [rewrite (KS2 _) by PMK.inl; rewrite A19; f_equal; clear; lia|]. clear -Hj CJ Hoj Hcnt. split; lia.
  - (* [comment removed for export] *)
    rewrite Z.mod_small in CEXIT by (clear -Hj Hcnt; lia).
    exists fx2, R2, M1, (j + 1). split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FZ1|]. split; [exact MI1|].
    split. { unfold QR. rewrite !(KS2 _) by PMK.inl. rewrite !(KS1 _) by PMK.inl. repeat apply conj; assumption. }
    split; [rewrite (KS2 _) by PMK.inl; rewrite A19; f_equal; clear; lia|]. clear -Hj CEXIT Hoj Hcnt. split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma int_loop (m : nat) : forall fx R M i off boff rd sd,
  QR R -> getr R (reg 5) = Z_to_bv 64 (-5) -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (first + off) -> getr R (reg 9) = Z_to_bv 64 (first + off) ->
  getr R (reg 11) = Z_to_bv 64 rd -> getr R (reg 12) = Z_to_bv 64 sd -> getr R (reg 13) = Z_to_bv 64 (S - 216 + boff) -> getr R (reg 14) = Z_to_bv 64 (S - 216 + boff) ->
  getr R (reg 16) = Z_to_bv 64 0 -> getr R (reg 17) = Z_to_bv 64 i ->
  MI M -> L5.defined M (S - 216) 144 ->
  1 <= sd <= 36 -> 1 <= rd <= 35 -> 1 <= i <= rd -> rd - i < Z.of_nat m -> 0 <= off -> off + (rd - i) <= 35 -> 0 <= boff -> boff + 4 * (rd - i) <= 140 ->
  exists fx' R' M', msteps RSEGS (st fx R 0x38e68 M) (st fx' R' 0x38fc4 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (first + 0 <= a < first + 0 + 42) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ MI M' /\ QR R' /\ getr R' (reg 11) = Z_to_bv 64 rd /\ getr R' (reg 12) = Z_to_bv 64 sd
    /\ getr R' (reg 10) = Z_to_bv 64 (S - 216 + boff + 4 * (rd - i + 1)) /\ getr R' (reg 14) = Z_to_bv 64 (S - 216 + boff + 4 * (rd - i + 1))
    /\ getr R' (reg 15) = Z_to_bv 64 (first + off + (rd - i + 1)).
Proof.
  induction m as [|m IH]; intros fx R M i off boff rd sd (G2 & G3 & G4 & G8 & G24 & G25 & G26 & G27) G5 G6 G7 G9 G11 G12 G13 G14 G16 G17 MIM DEF Hsd Hrd Hi Hm Hoff Hoi Hb0 Hb1;
    [exfalso; clear -Hi Hm; lia|].
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  (let T := type of (PNSDXP.dkXL1a_conc fx R M (fun k => match k with 55%nat => sd | 57%nat => off | 58%nat => boff | 59%nat => rd | 70%nat => i | _ => VV k end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDXP.dkXL1a_conc fx R M (fun k => match k with 55%nat => sd | 57%nat => off | 58%nat => boff | 59%nat => rd | 70%nat => i | _ => VV k end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A7 & A10 & A14 & A15).
  assert (MI1 : MI M1) by exact (MI_out M M1 MIM MG1 FZ1).
  pose proof MI1 as (WRf1 & WR11 & IC1 & SV1). pose proof SV1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  (let T := type of (PNSDXP.dkXL1b_conc fx1 R1 M1 (fun k => match k with 55%nat => sd | 57%nat => off + 1 | 58%nat => boff + 4 | 59%nat => rd | 70%nat => i | _ => VV k end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDXP.dkXL1b_conc fx1 R1 M1 (fun k => match k with 55%nat => sd | 57%nat => off + 1 | 58%nat => boff + 4 | 59%nat => rd | 70%nat => i | _ => VV k end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS1 _) by PMK.inl; PMK.sc | rewrite A10; f_equal; clear; lia | rewrite A15; f_equal; clear; lia])).
  destruct P as (fx2 & R2 & M2 & MG2 & FW2 & FZ2 & [ (MS2 & KS2 & B9 & B13 & B17 & CLT) | (MS2 & KS2 & CGE) ]);
    assert (EM : M2 = M1) by (apply functional_extensionality; exact FW2); subst M2;
    [rewrite (slt_small _ _ i rd) in CLT by (first [reflexivity | clear -Hi Hrd; lia]) | rewrite (slt_small _ _ i rd) in CGE by (first [reflexivity | clear -Hi Hrd; lia])].
  - (* [comment removed for export] *)
    destruct (Z.ltb_spec i rd) as [X|X]; [| exfalso; clear -CLT; lia].
    destruct (IH fx2 R2 M1 (i + 1) (off + 1) (boff + 4) rd sd) as (fx' & R' & M' & MS & MG & FZ & MI' & QR' & E11 & E12 & E10 & E14 & E15).
    { unfold QR. rewrite !(KS2 _) by PMK.inl. rewrite !(KS1 _) by PMK.inl. repeat apply conj; assumption. }
    { rewrite (KS2 _), (KS1 _) by PMK.inl. exact G5. } { rewrite (KS2 _), (KS1 _) by PMK.inl. exact G6. }
    { rewrite (KS2 _) by PMK.inl. rewrite A7; f_equal; clear; lia. } { rewrite B9; f_equal; clear; lia. }
    { rewrite (KS2 _), (KS1 _) by PMK.inl. exact G11. } { rewrite (KS2 _), (KS1 _) by PMK.inl. exact G12. }
    { rewrite B13; f_equal; clear; lia. } { rewrite (KS2 _) by PMK.inl. rewrite A14; f_equal; clear; lia. }
    { rewrite (KS2 _), (KS1 _) by PMK.inl. exact G16. } { rewrite B17; f_equal; clear; lia. }
    { exact MI1. } { exact (L5.defined_grows M M1 _ _ MG1 DEF). } { exact Hsd. } { exact Hrd. } { clear -Hi X; lia. } { clear -Hm; lia. } { clear -Hoff; lia. } { clear -Hoi X; lia. }
    { clear -Hb0; lia. } { clear -Hb1 X; lia. }
    exists fx', R', M'. split; [eapply msteps_trans; [exact MS1|]; eapply msteps_trans; [exact MS2| exact MS]|]. split; [exact (mem_grows_trans _ _ _ MG1 MG)|].
    split; [exact (out_trans M M1 M' FZ1 FZ)|]. split; [exact MI'|]. split; [exact QR'|]. split; [exact E11|]. split; [exact E12|].
    split; [rewrite E10; f_equal; clear; lia|]. split; [rewrite E14; f_equal; clear; lia| rewrite E15; f_equal; clear; lia].
  - (* [comment removed for export] *)
    destruct (Z.ltb_spec i rd) as [X|X]; [exfalso; clear -CGE; lia|]. assert (Ei : i = rd) by (clear -X Hi; lia).
    exists fx2, R2, M1. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FZ1|]. split; [exact MI1|].
    split. { unfold QR. rewrite !(KS2 _) by PMK.inl. rewrite !(KS1 _) by PMK.inl. repeat apply conj; assumption. }
    split; [rewrite (KS2 _), (KS1 _) by PMK.inl; exact G11|]. split; [rewrite (KS2 _), (KS1 _) by PMK.inl; exact G12|].
    split; [rewrite (KS2 _) by PMK.inl; rewrite A10; f_equal; clear -Ei; lia|].
    split; [rewrite (KS2 _) by PMK.inl; rewrite A14; f_equal; clear -Ei; lia| rewrite (KS2 _) by PMK.inl; rewrite A15; f_equal; clear -Ei; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac npos P MIM G13 Z13 :=
  PMK.feed P ltac:(first [PMK.sc | eauto 1]);   (* [comment removed for export] *)
  let fx1 := fresh "fx1" in let R1 := fresh "R1" in let M1 := fresh "M1" in
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A5 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & _);
  exists fx1, R1, M1; split; [exact MS1|]; split; [exact MG1|]; split; [exact FZ1|]; split; [exact (MI_out _ M1 MIM MG1 FZ1)|];
  split; [unfold QR; rewrite !(KS1 _) by PMK.inl; repeat apply conj; assumption|];
  split; [rewrite A10; exact G13|]; split; [exact A12|]; split; [rewrite A13; f_equal; clear; lia|];
  split; [apply to_bv_of_unsigned; rewrite A14; exact Z13|]; split; [exact A15| rewrite A16; bvc].

Lemma nonpos fx R M k z sd :
  0 <= k <= 5 -> 0 <= z -> z + sd <= 36 ->
  QR R -> getr R (reg 9) = Z_to_bv 64 (first + sigma) -> getr R (reg 11) = Z_to_bv 64 (- k) -> getr R (reg 12) = Z_to_bv 64 sd ->
  getr R (reg 13) = Z_to_bv 64 (S - 216 + 4 * z) ->
  MI M -> 1 <= sd <= 36 ->
  exists fx' R' M', msteps RSEGS (st fx R 0x38e48 M) (st fx' R' 0x39048 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (first + 0 <= a < first + 0 + 42) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ MI M' /\ QR R' /\ getr R' (reg 10) = Z_to_bv 64 (S - 216 + 4 * z) /\ getr R' (reg 12) = Z_to_bv 64 1
    /\ getr R' (reg 13) = Z_to_bv 64 (first + (sigma + k + 2)) /\ getr R' (reg 14) = Z_to_bv 64 0 /\ getr R' (reg 15) = Z_to_bv 64 sd
    /\ getr R' (reg 16) = Z_to_bv 64 (-5).
Proof.
  intros Hk Hz Hzs (G2 & G3 & G4 & G8 & G24 & G25 & G26 & G27) G9 G11 G12 G13 MIM Hsd.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (Z13 : Z.land (bv_unsigned (getr R (reg 13))) 3 = 0) by (rewrite G13; apply ptr_land; clear -Hz Hzs Hsd; lia).
  assert (CASES : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by (clear -Hk; lia).
  destruct CASES as [-> |[-> |[-> |[-> |[-> | ->]]]]]; cbn [Z.opp] in G11.
  - (let T := type of (PNSDXP.dkXN0_conc fx R M (fun j => match j with 55%nat => sd | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDXP.dkXN0_conc fx R M (fun j => match j with 55%nat => sd | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
    destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A5 & A10 & A12 & A13 & A14 & A15 & A16 & A17 & _).
    exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [exact FZ1|]. split; [exact (MI_out M M1 MIM MG1 FZ1)|].
    split. { unfold QR. rewrite !(KS1 _) by PMK.inl. repeat apply conj; assumption. }
    split; [rewrite A10; exact G13|]. split; [exact A12|]. split; [rewrite A13; f_equal; clear; lia|].
    split; [apply to_bv_of_unsigned; rewrite A14; exact Z13|]. split; [exact A15| rewrite A16; bvc].
  - pose proof (PNSDXP.dkXN1_conc fx R M (fun j => match j with 55%nat => sd | _ => VV j end)) as P. cbn beta iota delta [VV] in P. npos P MIM G13 Z13.
  - pose proof (PNSDXP.dkXN2_conc fx R M (fun j => match j with 55%nat => sd | _ => VV j end)) as P. cbn beta iota delta [VV] in P. npos P MIM G13 Z13.
  - pose proof (PNSDXP.dkXN3_conc fx R M (fun j => match j with 55%nat => sd | _ => VV j end)) as P. cbn beta iota delta [VV] in P. npos P MIM G13 Z13.
  - pose proof (PNSDXP.dkXN4_conc fx R M (fun j => match j with 55%nat => sd | _ => VV j end)) as P. cbn beta iota delta [VV] in P. npos P MIM G13 Z13.
  - pose proof (PNSDXP.dkXN5_conc fx R M (fun j => match j with 55%nat => sd | _ => VV j end)) as P. cbn beta iota delta [VV] in P. npos P MIM G13 Z13.
Qed.

(* [comment removed for export] *)
Theorem radix fx R M z sd :
  PNSDD.stQ R0 S first sigma e z sd R -> MI M -> L5.defined M (S - 216) 144 ->
  0 <= z -> 1 <= sd -> z + sd <= 36 -> e <= 6175 -> 6171 <= sd + e ->
  exists fx' R' M' ptr, msteps RSEGS (st fx R 0x38e44 M) (st fx' R' 0x38f6c M') /\ mem_grows M M' /\ PNSDD.agree_but (PNSDD.in_out first) M M'
    /\ PNSDD.stE R0 S ptr R' /\ first <= ptr <= first + 42 /\ MI M'.
Proof.
  intros ((X2 & X3 & X4 & X8 & X9 & X24 & X25 & X26 & X27) & X15 & X13 & X12) MIM DEF Hz Hsd Hzs He1 He2.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  set (rd := sd + e - 6176). assert (Hrd : -5 <= rd <= sd - 1) by (subst rd; clear -He1 He2; lia).
  assert (FINI : forall fx5 R5 M5 off n, msteps RSEGS (st fx R 0x38e44 M) (st fx5 R5 0x38f6c M5) ->
            mem_grows M M5 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (first + 0 <= a < first + 0 + 42) -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> MI M5 ->
            QR R5 -> getr R5 (reg 19) = Z_to_bv 64 (first + off + n) -> 2 <= off -> 1 <= n <= 36 -> off + n <= 42 ->
            exists fx' R' M' ptr, msteps RSEGS (st fx R 0x38e44 M) (st fx' R' 0x38f6c M') /\ mem_grows M M' /\ PNSDD.agree_but (PNSDD.in_out first) M M'
              /\ PNSDD.stE R0 S ptr R' /\ first <= ptr <= first + 42 /\ MI M').
  { intros fx5 R5 M5 off n MS5 MG5 FZ5 MI5 (Q2 & Q3 & Q4 & Q8 & Q24 & Q25 & Q26 & Q27) E19 Hoff Hn Hon.
    exists fx5, R5, M5, (first + off + n). split; [exact MS5|]. split; [exact MG5|].
    split; [intros a Ha N; apply FZ5; [exact Ha| unfold PNSDD.in_out in N; clear -N; intros X; apply N; lia]|].
    split. { unfold PNSDD.stE. repeat apply conj; assumption. }
    split; [clear -Hoff Hn Hon; lia| exact MI5]. }
  (* [comment removed for export] *)
  (let T := type of (PNSDXP.dkXA_conc fx R M (fun j => match j with 55%nat => sd | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDXP.dkXA_conc fx R M (fun j => match j with 55%nat => sd | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A11); assert (EM : M1 = M) by (apply functional_extensionality; exact FW1); subst M1.
  assert (A11' : getr R1 (reg 11) = Z_to_bv 64 rd) by (rewrite A11; f_equal; subst rd; clear; lia).
  destruct (Z_lt_le_dec 0 rd) as [POS|NPOS].
  - (* [comment removed for export] *)
    (let T := type of (PNSDXP.dkXP_conc fx1 R1 M (fun j => match j with 55%nat => sd | 59%nat => rd | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDXP.dkXP_conc fx1 R1 M (fun j => match j with 55%nat => sd | 59%nat => rd | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS1 _) by PMK.inl; PMK.sc])).
    destruct P as (fx2 & R2 & M2 & MG2 & FW2 & FZ2 & MS2 & KS2 & A5 & A6 & A7 & A14 & A16 & A17); assert (EM : M2 = M) by (apply functional_extensionality; exact FW2); subst M2.
    assert (KK : forall k, In k [2; 3; 4; 8; 9; 12; 13; 24; 25; 26; 27]%nat -> getr R2 (reg k) = getr R (reg k)).
    { intros k Hk. rewrite (KS2 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). apply KS1. revert Hk; clear; intros Hk; cbn in Hk |- *; tauto. }
    assert (Z13 : Z.land (bv_unsigned (getr R1 (reg 13))) 3 = 0) by (rewrite (KS1 _) by PMK.inl; rewrite X13; apply ptr_land; clear -Hz Hzs Hsd; lia).
    destruct (int_loop (Datatypes.S (Z.to_nat rd)) fx2 R2 M 1 sigma (4 * z) rd sd
                ltac:(unfold QR; repeat apply conj; rewrite (KK _) by PMK.inl; assumption)
                ltac:(rewrite A5; bvc) A6 A7 ltac:(rewrite (KK _) by PMK.inl; exact X9) ltac:(rewrite (KS2 _) by PMK.inl; exact A11')
                ltac:(rewrite (KK _) by PMK.inl; exact X12) ltac:(rewrite (KK _) by PMK.inl; exact X13) ltac:(rewrite A14, (KS1 _) by PMK.inl; exact X13)
                ltac:(apply to_bv_of_unsigned; rewrite A16; exact Z13) A17
                MIM DEF ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia)
                ltac:(rewrite Nat2Z.inj_succ, Z2Nat.id by (clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia); clear; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia))
      as (fx3 & R3 & M3 & MS3 & MG3 & FZ3 & MI3 & QR3 & E11 & E12 & E10 & E14 & E15).
    pose proof MI3 as (WRf3 & WR13 & IC3 & SV3). pose proof SV3 as (Q1 & Q2' & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    pose proof QR3 as (Y2 & Y3 & Y4 & Y8 & Y24 & Y25 & Y26 & Y27).
    (let T := type of (PNSDXP.dkXD_conc fx3 R3 M3 (fun j => match j with 55%nat => sd | 57%nat => sigma + rd | 58%nat => 4 * z + 4 * rd | 59%nat => rd | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDXP.dkXD_conc fx3 R3 M3 (fun j => match j with 55%nat => sd | 57%nat => sigma + rd | 58%nat => 4 * z + 4 * rd | 59%nat => rd | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite E10; f_equal; clear; lia | rewrite E14; f_equal; clear; lia | rewrite E15; f_equal; clear; lia])).
    destruct P as (fx4 & R4 & M4 & MG4 & FW4 & FZ4 & [ (MS4 & KS4 & _ & _ & _ & _ & _ & _ & _ & CEQ & _) | (MS4 & KS4 & B5 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & CNE & DOT) ]).
    { exfalso. clear -CEQ Hrd POS Hsd Hzs Hz. rewrite Z.mod_small in CEQ by Lia.lia. Lia.lia. }
    apply to_bv_of_unsigned in B15. rewrite (subw_val sd rd) in B15 by (clear -Hrd POS Hsd Hzs Hz; lia).
    assert (MI4 : MI M4) by exact (MI_out M3 M4 MI3 MG4 FZ4).
    destruct  (frac_loop (Datatypes.S (Z.to_nat (sd - rd))) fx4 R4 M4 0 (sigma + rd + 1) (4 * z + 4 * rd) (sd - rd) sd
                ltac:(unfold QR; repeat apply conj; rewrite (KS4 _) by PMK.inl; assumption)
                ltac:(rewrite (KS4 _) by PMK.inl; rewrite E10; f_equal; clear; lia) ltac:(rewrite B12; f_equal; clear; lia) ltac:(rewrite B13; f_equal; clear; lia)
                ltac:(apply to_bv_of_unsigned; rewrite B14; apply land3_0; clear -Hz POS Hrd; Lia.lia) B15 ltac:(rewrite B16; bvc)
                MI4 (L5.defined_grows M M4 _ _ (mem_grows_trans _ _ _ MG3 MG4) DEF) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia)
                ltac:(rewrite Nat2Z.inj_succ, Z2Nat.id by (clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia); clear; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd POS Hsd Hzs Hz Fsig; Lia.lia))
      as (fx5 & R5 & M5 & n & MS5 & MG5 & FZ5 & MI5 & QR5 & E19' & Hn & Hon).
    apply (FINI fx5 R5 M5 (sigma + rd + 1) n); [| exact (mem_grows_trans _ _ _ MG3 (mem_grows_trans _ _ _ MG4 MG5))| | exact MI5| exact QR5| exact E19'| clear -Fsig POS; Lia.lia| clear -Hn Hrd POS Hsd Hzs Hz; Lia.lia| exact Hon].
    + eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3|]. eapply msteps_trans; [exact MS4| exact MS5].
    + exact (out_trans M M4 M5 (out_trans M M3 M4 FZ3 FZ4) FZ5).
  - (* [comment removed for export] *)
    destruct (nonpos fx1 R1 M (- rd) z sd ltac:(clear -Hrd NPOS Hsd Hzs Hz Fsig; Lia.lia) Hz Hzs
                ltac:(unfold QR; repeat apply conj; rewrite (KS1 _) by PMK.inl; assumption)
                ltac:(rewrite (KS1 _) by PMK.inl; exact X9) ltac:(rewrite A11'; f_equal; clear; lia)
                ltac:(rewrite (KS1 _) by PMK.inl; exact X12) ltac:(rewrite (KS1 _) by PMK.inl; exact X13) MIM ltac:(clear -Hsd Hzs Hz; Lia.lia))
      as (fx3 & R3 & M3 & MS3 & MG3 & FZ3 & MI3 & QR3 & E10 & E12 & E13 & E14 & E15 & E16).
    destruct (frac_loop (Datatypes.S (Z.to_nat sd)) fx3 R3 M3 0 (sigma + (- rd) + 2) (4 * z) sd sd QR3
                E10 ltac:(rewrite E12; f_equal; clear; lia) ltac:(rewrite E13; f_equal; clear; lia) E14 E15 E16
                MI3 (L5.defined_grows M M3 _ _ MG3 DEF) ltac:(clear -Hrd NPOS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd NPOS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd NPOS Hsd Hzs Hz Fsig; Lia.lia)
                ltac:(rewrite Nat2Z.inj_succ, Z2Nat.id by (clear -Hrd NPOS Hsd Hzs Hz Fsig; Lia.lia); clear; Lia.lia) ltac:(clear -Hrd NPOS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd NPOS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd NPOS Hsd Hzs Hz Fsig; Lia.lia) ltac:(clear -Hrd NPOS Hsd Hzs Hz Fsig; Lia.lia))
      as (fx5 & R5 & M5 & n & MS5 & MG5 & FZ5 & MI5 & QR5 & E19' & Hn & Hon).
    apply (FINI fx5 R5 M5 (sigma + (- rd) + 2) n); [| exact (mem_grows_trans _ _ _ MG3 MG5)| | exact MI5| exact QR5| exact E19'| clear -Fsig Hrd NPOS; Lia.lia| clear -Hn Hsd Hzs Hz; Lia.lia| exact Hon].
    + eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS3| exact MS5].
    + exact (out_trans M M3 M5 FZ3 FZ5).
Qed.

End Rdx.
End PNSDRDX.
