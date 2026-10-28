(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BgWords BgSqrCorrect.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp BnKaraX BnKaraMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_cmp_words W_mul_normal BnCalls W_mul_recursive.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_add_words WU_sub_words WU_cmp_words BnCallsU.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU2 Require Import WU_sqr_words WU_sqr_normal SqrCalls.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW2 Require Import SqrKaraX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 1079624 => 1
  | 1079628 => 1
  | 1079632 => 1
  | 1079636 => 1
  | 1079640 => 1
  | 1079644 => 2
  | 1079648 => 1
  | 1079652 => 1
  | 1079656 => 1
  | 1079660 => 2
  | 1079720 => 1
  | 1079724 => 1
  | 1079728 => 2
  | 1079732 => 2
  | 1079748 => 2
  | 1079752 => 2
  | 1079772 => 2
  | 1079800 => 2
  | 1079844 => 2
  | 1079852 => 2
  | 1079856 => 2
  | 1079904 => 2
  | 1079948 => 2
  | 1079952 => 1
  | 1079956 => 2
  | 1079996 => 2
  | 1080016 => 2
  | 1080024 => 1
  | 1080028 => 2
  | 1080052 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition bn_sqr_recursive_entry := 0x107810%Z.

Definition srec_stack (CSL : Z) (k : nat) : Z := (112 * Z.of_nat k + CSL)%Z.

Definition sqr_rec_spec_at (CSL : Z) (k : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a R T : list Z) (lo : Z),
    limbs a -> limbs R -> limbs T ->
    (k <= 26)%nat ->
    length a = Nat.pow 2 k -> length R = (2 * Nat.pow 2 k)%nat -> (sqr_scratch k <= length T)%nat ->
    bv_unsigned a2 = Z.of_nat (Nat.pow 2 k) ->
    limbs_at bgusegs m (bv_unsigned a1) a -> limbs_at bgusegs m (bv_unsigned a0) R -> limbs_at bgusegs m (bv_unsigned a3) T ->
    wr_at bgusegs m (bv_unsigned a0) (8 * Z.of_nat (length R)) -> wr_at bgusegs m (bv_unsigned a3) (8 * Z.of_nat (length T)) ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0)%Z ->
    (bv_unsigned a3 + 8 * Z.of_nat (length T) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a3)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a3 \/ bv_unsigned a3 + 8 * Z.of_nat (length T) <= bv_unsigned a0)%Z ->
    stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - srec_stack CSL k)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned sp - srec_stack CSL k \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a3 + 8 * Z.of_nat (length T) <= bv_unsigned sp - srec_stack CSL k \/ bv_unsigned sp <= bv_unsigned a3)%Z ->
    (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - srec_stack CSL k \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    mem_inv bgusegs m ->
    ub_ptr_ok 1 (bv_unsigned a0) -> ub_ptr_ok 1 (bv_unsigned a1) -> ub_ptr_ok 1 (bv_unsigned a3) ->
    evt bgusegs (kr_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (bv_unsigned a0) (Z.of_nat (length R)) (bv_unsigned a3) (Z.of_nat (length T)) (srec_stack CSL k)
                 (fst (sqr_recursive k a R T)) (snd (sqr_recursive k a R T)) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x107810) fc None m (seg_rom bgusegs)).

Section CallWrap.
  Variable POST : machine_state -> Prop.
  Variables (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo SPz RET : Z).
  Hypothesis ESP : bv_unsigned wsp = SPz.
  Hypothesis ERET : ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET.
  Hypothesis STK : stk bgusegs m lo SPz.
  Hypothesis MI0 : mem_inv bgusegs m.

  Lemma call_sqr_rec : forall (CSL : Z) (k : nat) (a R T : list Z) (RP AP TQ : Z),
    sqr_rec_spec_at CSL k ->
    limbs a -> limbs R -> limbs T -> (k <= 26)%nat ->
    length a = Nat.pow 2 k -> length R = (2 * Nat.pow 2 k)%nat -> (sqr_scratch k <= length T)%nat ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = Z.of_nat (Nat.pow 2 k) -> bv_unsigned w3 = TQ ->
    limbs_at bgusegs m AP a -> limbs_at bgusegs m RP R -> limbs_at bgusegs m TQ T ->
    wr_at bgusegs m RP (8 * Z.of_nat (length R)) -> wr_at bgusegs m TQ (8 * Z.of_nat (length T)) ->
    (RP + 8 * Z.of_nat (length R) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= AP \/ AP + 8 * Z.of_nat (length a) <= TQ)%Z ->
    (RP + 8 * Z.of_nat (length R) <= TQ \/ TQ + 8 * Z.of_nat (length T) <= RP)%Z ->
    (lo <= SPz - srec_stack CSL k)%Z ->
    (RP + 8 * Z.of_nat (length R) <= SPz - srec_stack CSL k \/ SPz <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= SPz - srec_stack CSL k \/ SPz <= TQ)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - srec_stack CSL k \/ SPz <= AP)%Z ->
    ub_ptr_ok 1 RP -> ub_ptr_ok 1 AP -> ub_ptr_ok 1 TQ ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length R)); (TQ, TQ + 8 * Z.of_nat (length T)); (SPz - srec_stack CSL k, SPz)]%Z m m2 ->
       wmono bgusegs m m2 -> mem_inv bgusegs m2 ->
       limbs_at bgusegs m2 RP (fst (sqr_recursive k a R T)) -> limbs_at bgusegs m2 TQ (snd (sqr_recursive k a R T)) ->
       stk bgusegs m2 lo SPz ->
       evt bgusegs POST
         (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
             F (Z_to_bv 64 RET) fc None m2 (seg_rom bgusegs))) ->
    evt bgusegs POST
      (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x107810) fc None m (seg_rom bgusegs)).
  Proof using ESP ERET STK MI0.
    intros CSL k a R T RP AP TQ SPEC LA LR LT Hk HLA HLR HLT E0 E1 E2 E3 RA RR RT WR WT DRA DTA DRT LO SEPR SEPT SEPA UR UA UT K.
    subst RP AP TQ SPz.
    eapply evt_cut; [ eapply SPEC with (a := a) (R := R) (T := T) (lo := lo); eassumption | ].
    intros ms' PO. unfold kr_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & HT & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  Lemma call_cmp_words : forall (a b : list Z) (AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2 ^ 31)%Z ->
    bv_unsigned w0 = AP -> bv_unsigned w1 = BP -> bv_unsigned w2 = Z.of_nat (length a) ->
    limbs_at bgusegs m AP a -> limbs_at bgusegs m BP b ->
    (lo <= SPz - 16)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= BP)%Z ->
    ub_ptr_ok (Z.of_nat (length a)) AP -> ub_ptr_ok (Z.of_nat (length a)) BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(SPz - 16, SPz)]%Z m m2 -> wmono bgusegs m m2 -> mem_inv bgusegs m2 -> stk bgusegs m2 lo SPz ->
       evt bgusegs POST
         (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 (cmp_words a b)) v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
             F (Z_to_bv 64 RET) fc None m2 (seg_rom bgusegs))) ->
    evt bgusegs POST
      (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xff514) fc None m (seg_rom bgusegs)).
  Proof using ESP ERET STK MI0.
    intros a b AP BP LA LB LEN N31 E0 E1 E2 RA RB LO SEPA SEPB UA UB K.
    subst AP BP SPz.
    eapply evt_cut; [ eapply bn_cmp_words_uspec with (a := a) (b := b) (lo := lo); try eassumption; rewrite LEN; eassumption | ].
    intros ms' PO. unfold ro_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.
End CallWrap.

Definition sqr_pre (CSL : Z) (k' n la nT : nat) (SK rp tq ap SP lo : Z) : Prop :=
  n = Nat.pow 2 k' /\ (3 <= k' <= 25)%nat /\ (8 <= n)%nat /\ (Z.of_nat n <= 33554432)%Z /\
  la = (2 * n)%nat /\ (4 * n + sqr_scratch k' <= nT)%nat /\ SK = srec_stack CSL k' /\
  (rp + 8 * Z.of_nat (4 * n) <= ap \/ ap + 8 * Z.of_nat la <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat la <= tq)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= tq \/ tq + 8 * Z.of_nat nT <= rp)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= SP - 112 - SK \/ SP <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= SP - 112 - SK \/ SP <= tq)%Z /\
  (ap + 8 * Z.of_nat la <= SP - 112 - SK \/ SP <= ap)%Z /\
  (lo <= SP - 112 - SK)%Z /\ (0 <= lo)%Z /\ (256 <= CSL)%Z.

Section Kara.
  Variable CSL : Z.
  Variable k' : nat.
  Hypothesis IH : sqr_rec_spec_at CSL k'.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : list Z) (lo : Z) (n nT : nat) (SK : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation tq := (bv_unsigned a3).
  Notation SP := (bv_unsigned sp).
  Notation N := (Z.of_nat n).
  Hypothesis PRE : sqr_pre CSL k' n (length a) nT SK (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned sp) lo.
  Hypothesis LA : limbs a.
  Hypothesis A2 : bv_unsigned a2 = (2 * N)%Z.
  Hypothesis UR : ub_ptr_ok 1 (bv_unsigned a0).
  Hypothesis UA : ub_ptr_ok 1 (bv_unsigned a1).
  Hypothesis UT : ub_ptr_ok 1 (bv_unsigned a3).
  Variable RES : list Z * list Z.

  Lemma Hn : n = Nat.pow 2 k'. Proof. apply PRE. Qed.
  Lemma Hk' : (3 <= k' <= 25)%nat. Proof. apply PRE. Qed.
  Lemma Hn8 : (8 <= n)%nat. Proof. apply PRE. Qed.
  Lemma HnB : (N <= 33554432)%Z. Proof. apply PRE. Qed.
  Lemma HLA : length a = (2 * n)%nat. Proof. apply PRE. Qed.
  Lemma HnT : (4 * n + sqr_scratch k' <= nT)%nat. Proof. apply PRE. Qed.
  Lemma HSK : SK = srec_stack CSL k'. Proof. apply PRE. Qed.
  Lemma DRA : (rp + 8 * Z.of_nat (4 * n) <= ap \/ ap + 8 * Z.of_nat (length a) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma DTA : (tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat (length a) <= tq)%Z. Proof. apply PRE. Qed.
  Lemma DRT : (rp + 8 * Z.of_nat (4 * n) <= tq \/ tq + 8 * Z.of_nat nT <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPR : (rp + 8 * Z.of_nat (4 * n) <= SP - 112 - SK \/ SP <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPT : (tq + 8 * Z.of_nat nT <= SP - 112 - SK \/ SP <= tq)%Z. Proof. apply PRE. Qed.
  Lemma SEPA : (ap + 8 * Z.of_nat (length a) <= SP - 112 - SK \/ SP <= ap)%Z. Proof. apply PRE. Qed.
  Lemma LO : (lo <= SP - 112 - SK)%Z. Proof. apply PRE. Qed.
  Lemma LO0 : (0 <= lo)%Z. Proof. apply PRE. Qed.
  Lemma HCSL : (256 <= CSL)%Z. Proof. apply PRE. Qed.
  Lemma SK0 : (0 <= SK)%Z. Proof. rewrite HSK. unfold srec_stack. pose proof HCSL. lia. Qed.
  Lemma SK_ge : (256 <= SK /\ CSL <= SK)%Z. Proof. rewrite HSK. unfold srec_stack. pose proof HCSL. lia. Qed.
  Lemma FS0 : (0 <= 112)%Z. Proof. lia. Qed.
  Lemma FBE : (SP + -112 = SP - 112)%Z. Proof. reflexivity. Qed.
  Lemma ESP112 : bv_unsigned (Z_to_bv 64 (SP + -112)) = (SP + -112)%Z.
  Proof.
    apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R.
    pose proof LO. pose proof LO0. pose proof SK0. lia.
  Qed.
  Lemma pow_n : Nat.pow 2 k' = n. Proof. symmetry. exact Hn. Qed.
  Lemma sqr_scratch_tail : (sqr_scratch k' <= nT - 4 * n)%nat. Proof. pose proof HnT. lia. Qed.

  Notation POST := (kr_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                      (bv_unsigned a0) (Z.of_nat (4 * n)) (bv_unsigned a3) (Z.of_nat nT) (112 + SK)%Z (fst RES) (snd RES) lo m).
  Notation KBK := (KB bgusegs m (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a (4 * n)%nat nT
                      112%Z SK (bv_unsigned sp + -112)%Z).
  Notation KUPD := (KB_upd bgusegs m (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a (4 * n)%nat nT
                      112%Z SK (bv_unsigned sp + -112)%Z FS0 FBE SK0 DRA DRA DTA DTA DRT SEPR SEPT SEPA SEPA).
  Notation KFRAME := (KB_frame bgusegs m (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a (4 * n)%nat nT
                      112%Z SK (bv_unsigned sp + -112)%Z FS0 FBE SK0 SEPR SEPT SEPA SEPA).
  Notation KSTORE := (KB_storeR bgusegs m (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a (4 * n)%nat nT
                      112%Z SK (bv_unsigned sp + -112)%Z FS0 FBE SK0 DRA DRA DRT SEPR).
  Notation KAFTER L := (L bgusegs m (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a (4 * n)%nat nT
                      112%Z SK (bv_unsigned sp + -112)%Z FS0 FBE SK0 DRA DRA DTA DTA DRT SEPR SEPT SEPA SEPA).
  Notation KACC L := (L bgusegs m (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a (4 * n)%nat nT
                      112%Z SK (bv_unsigned sp + -112)%Z).

  Notation FCELLS jb := [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             a2 (Z_to_bv 64 (Z.of_nat n)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  Lemma geom : (8 <= N <= 33554432 /\ 0 <= lo /\ lo <= SP - 112 - SK /\ 256 <= SK /\ CSL <= SK /\ 256 <= CSL /\
                Z.of_nat (4 * n + sqr_scratch k') <= Z.of_nat nT /\ Z.of_nat (length a) = 2 * N)%Z.
  Proof.
    pose proof Hn8. pose proof HnB. pose proof LO. pose proof LO0. pose proof SK_ge. pose proof HnT. pose proof HLA. pose proof HCSL. lia.
  Qed.

  Lemma ubs : (0 < rp /\ rp mod 8 = 0 /\ 0 < ap /\ ap mod 8 = 0 /\ 0 < tq /\ tq mod 8 = 0)%Z.
  Proof. pose proof (UR ltac:(lia)). pose proof (UA ltac:(lia)). pose proof (UT ltac:(lia)). tauto. Qed.

  Ltac kubp G := unfold ub_ptr_ok; intros _; let UB := fresh "UB" in pose proof ubs as UB;
    split; [ clear - UB G; lia | clear - UB; Z.div_mod_to_equations; lia ].

  Lemma B_epi : forall jb m1 R T x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T -> RES = (R, T) ->
    evt bgusegs POST (ST 0x107b10 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM) E.
    do 15 zstep.
    assert (LO1 : (lo <= SP + -112)%Z) by (pose proof LO; pose proof SK0; lia).
    release_frame FR ST (bv_unsigned sp).
    subst RES. cbn [fst snd].
    assert (MU' : munch [(rp, rp + 8 * Z.of_nat (4 * n)); (tq, tq + 8 * Z.of_nat nT); (SP - (112 + SK), SP)]%Z m m1).
    { unfold KWfin in MU. replace (SP - (112 + SK))%Z with (SP - 112 - SK)%Z by (clear; lia). exact MU. }
    finish.
  Qed.

  Ltac kb_store SOK0 I2 :=
    lazymatch type of SOK0 with
    | store_ok _ ?m2 ?a0' _ = true =>
        let ad := cur_mem_addr in
        let SOK := fresh "SOK" in
        assert (SOK : store_ok bgusegs m2 ad 8 = true) by (replace ad with a0' by (unfold wa; f_equal; lia); exact SOK0);
        replace a0' with ad in I2 by (unfold wa; f_equal; lia);
        zstep; clear SOK SOK0;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => let m' := fresh "m" in gen_mem mm m' end
    end.

  Lemma B_loop : forall (l pre : list Z) jb m1 T x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 (pre ++ l) T -> cu_fit l -> RES = (pre ++ carry_up l, T) -> (1 <= length pre)%nat ->
    evt bgusegs POST (ST 0x107af4 m1 x1 x5 x6 x7 (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre) - 8)) (Z_to_bv 64 (-9)) x11
                       x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction l as [|x l' IHl]; intros until x31; intros I FIT E LP.
    { exfalso. unfold cu_fit in FIT. cbn [lval length] in FIT. rewrite Bp_0 in FIT. clear - FIT. lia. }
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (cu_fit_cons (x :: l') (proj2 (limbs_app_inv _ _ LR)) FIT) as (x' & l'' & Ecs & Hx & Hl' & Hfit').
    injection Ecs as <- <-.
    assert (Hi : (length pre < 4 * n)%nat) by (rewrite length_app in ER; cbn [length] in ER; clear - ER; lia).
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(pose proof Hn8; lia) ltac:(pose proof HnT; pose proof Hn8; lia)) as (BR0 & BR1 & _).
    assert (BP : (0 <= rp + 8 * Z.of_nat (length pre) - 8 /\ rp + 8 * Z.of_nat (length pre) + 8 <= 18446744073709551616)%Z) by (clear - BR0 BR1 Hi LP; lia).
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    ub1 ub_kind.
    ld_hd HR2.
    zstep. zstep.
    setreg 11%Z (Z_to_bv 64 (addw x 1)) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE (FCELLS jb) m1 (pre ++ x :: l') T (length pre) (addw x 1) eq_refl I Hi (addw_limb _ _)) as (SOK0 & I2).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI MU WM BR0 BR1.
    kb_store SOK0 I2.
    zstep.
    rewrite upd_app_mid in I2.
    pose proof (addw_limb x 1) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K; zify_cond K.
    - setreg 9%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x 1])) - 8)) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      eapply IHl; [exact I2 | apply Hfit'; exact K | | rewrite length_app; cbn [length]; clear; lia].
      rewrite E. cbn [carry_up]. rewrite K. cbn [Z.eqb]. rewrite <- app_assoc. reflexivity.
    - eapply B_epi; [exact I2|].
      rewrite E. cbn [carry_up]. destruct (Z.eqb_spec (addw x 1) 0) as [E0|_]; [contradiction|]. rewrite <- app_assoc. reflexivity.
  Qed.

  Ltac ret_even := apply ret_pc_even; [lia | reflexivity].
  Ltac ulit := first [ reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; lia); lia | lia ].

  Lemma B_fin : forall jb m1 R T c12 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T -> kc3_ok RES n R T c12 -> (-1 <= c12 <= 2)%Z ->
    evt bgusegs POST (ST 0x107a98 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (18446744073709551615 - rp))
                         (Z_to_bv 64 (tq + 8 * Z.of_nat (2 * n))) (Z_to_bv 64 c12) x23 (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n)))
                         (Z_to_bv 64 (8 * N)) (Z_to_bv 64 (16 * N)) (Z_to_bv 64 (18446744073709551615 - tq)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK Hc12.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ n (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    pose proof (zr_word a0) as R0. pose proof (zr_word a3) as R3. unfold inr64 in R0, R3.
    do 5 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply ucall_add_words with (a := slice R n (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -112)%Z)
                               (RP := (rp + 8 * N)%Z) (AP := (rp + 8 * N)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP112 | ret_even | exact ST | exact MI | exact LRa | exact LTb | rewrite ERa, ETb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa, A2; clear; lia
      | exact HRa | exact HTb | rewrite ERa; exact WRa
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D3 G; lia
      | kubp G | kubp G | kubp G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LTb ltac:(rewrite ERa, ETb; reflexivity)) as SP3.
    unfold kc3_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R n (2 * n)) (slice T (2 * n) (2 * n))) as [sg3 cy3]. cbn [fst snd] in *.
    destruct SP3 as (Ls3 & Es3 & Hc3 & _). rewrite ERa in Es3. destruct OK as (ERES & Hc & FIT).
    pose proof (KAFTER KB_after_R (FCELLS jb) m1 m2 R T n sg3 _ 80%Z eq_refl I MUc ltac:(rewrite ERa, Es3; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls3 ltac:(rewrite Es3; clear; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa WRa HTb LTb ETb MUc WMc HS I D1 D2 D3.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    zstep. rewrite (bn_swrap32_small (cy3 + 0)) by (clear - Hc3; lia). rewrite (Z.add_0_r cy3).
    zstep. rewrite (bn_swrap32_mod c12 0) by (clear - Hc12; lia). rewrite (Z.add_0_r c12).
    zstep.
    zstep. rewrite (bn_swrap32_mod c12 cy3) by (clear - Hc12 Hc3; lia).
    ub.
    zstep. first [ rewrite (bn_swrap32_small (c12 + cy3 + 0)) by (clear - Hc12 Hc3; lia) | rewrite (bn_swrap32_mod (c12 + cy3) 0) by (clear - Hc12 Hc3; lia) ]. rewrite (Z.add_0_r (c12 + cy3)).
    zstep. if_cases K; zify_cond K.
    { eapply B_epi; [exact I2|]. rewrite ERES. rewrite K. reflexivity. }
    specialize (FIT K). destruct (Z.eqb_spec (c12 + cy3) 0) as [E0|_]; [contradiction|].
    zstep. rewrite A2, (bn_swrap32_small (N + 2 * N)) by (clear - G; lia).
    zstep.
    remember (splice R n sg3) as R' eqn:ER'. pose proof ER as ERl.
    assert (Lpre : length (firstn (n + 2 * n) R') = (n + 2 * n)%nat) by (rewrite length_firstn; clear - ER; lia).
    destruct (skipn (n + 2 * n) R') as [|x l'] eqn:Esk.
    { exfalso. pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. clear - HH ER G. lia. }
    assert (ERpl : R' = firstn (n + 2 * n) R' ++ x :: l') by (rewrite <- Esk; symmetry; apply firstn_skipn).
    remember (firstn (n + 2 * n) R') as pre eqn:Epre.
    rewrite ERpl in I2, HR, LR. clear ERpl.
    pose proof (limbs_cons_lit x l' (proj2 (limbs_app_inv _ _ LR))) as (Hx & Ll').
    pose proof (KACC KB_bounds _ _ _ _ I2 ltac:(clear - G; lia) ltac:(clear - G; lia)) as (BR0 & BR1 & _).
    assert (Hi : (length pre < 4 * n)%nat) by (rewrite Lpre; clear - G; lia).
    rewrite ?Z.mod_small by (clear - G; lia). rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
    destruct ubs as (NZR & AR8 & NZA & AA8 & NZT & AT8).
    ub. zstep.
    setreg 9%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre))) ltac:(f_equal; rewrite Lpre; clear; lia).
    ub.
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    ld_hd HR2.
    zstep.
    setreg 10%Z (Z_to_bv 64 (addw x (c12 + cy3))) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE (FCELLS jb) m2 (pre ++ x :: l') T (length pre) (addw x (c12 + cy3)) eq_refl I2 Hi (addw_limb _ _)) as (SOK0 & I3).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI MU WM I2 MIc STc.
    kb_store SOK0 I3. rewrite upd_app_mid in I3.
    pose proof (addw_limb x (c12 + cy3)) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K2; zify_cond K2.
    - eapply B_epi; [exact I3|]. rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx).
      destruct (Z.ltb_spec (addw x (c12 + cy3)) x) as [HH|_]; [exfalso; clear - HH K2; lia|]. rewrite <- app_assoc. reflexivity.
    - zstep.
      setreg 9%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x (c12 + cy3)])) - 8)) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      assert (TST : (addw x (c12 + cy3) <? x) = true) by (apply Z.ltb_lt; clear - K2; lia).
      eapply B_loop; [exact I3 | | | rewrite length_app; cbn [length]; clear; lia].
      + eapply (add_carry_fit x l' (c12 + cy3)); [rewrite BW_lit; exact Hx | exact Ll' | rewrite BW_lit; clear - Hc; lia | | exact TST].
        replace (S (length l')) with n; [exact FIT|].
        pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. rewrite HH, ERl. clear. lia.
      + rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx). rewrite TST. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma B_sub : forall jb m1 R T c1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T -> kc2_ok RES n true R T c1 -> (0 <= c1 <= 1)%Z ->
    evt bgusegs POST (ST 0x107a60 m1 x1 x5 x6 x7 a0 (Z_to_bv 64 c1) x11 x12 x13 x14 x15 x16 x17 a3 x21 (Z_to_bv 64 (ap + 8 * N))
                         (Z_to_bv 64 (16 * N)) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 (8 * N)) (Z_to_bv 64 (16 * N))
                         (Z_to_bv 64 (18446744073709551615 - tq)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    pose proof (zr_word a0) as R0. pose proof (zr_word a3) as R3. unfold inr64 in R0, R3.
    ub.
    zstep. setreg 21%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (2 * n))) ltac:(f_equal; clear; lia).
    zstep. rewrite (bn_swrap32_small (c1 + 0)) by (clear - Hc1; lia). rewrite (Z.add_0_r c1).
    do 5 zstep.
    pose proof SEPT as D3.
    eapply ucall_sub_words with (a := slice T 0 (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -112)%Z)
                               (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP112 | ret_even | exact ST | exact MI | exact LTa | exact LTb | rewrite ETa, ETb; reflexivity
      | rewrite ETa; clear - G; lia | ulit | ulit | ulit | rewrite ETa, A2; clear; lia
      | exact HTa | exact HTb | rewrite ETa; exact WTb
      | unfold alias_ok; rewrite ETa; clear; lia | unfold alias_ok; left; reflexivity
      | clear - G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia
      | kubp G | kubp G | kubp G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (sub_words_spec _ _ LTa LTb ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (sub_words (slice T 0 (2 * n)) (slice T (2 * n) (2 * n))) as [sg2 bw]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hbw & _). rewrite ETa in Es2.
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T (2 * n)%nat sg2 _ 80%Z eq_refl I MUc ltac:(rewrite ETa, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep. rewrite (bn_swrap32_small (bw + 0)) by (clear - Hbw; lia). rewrite (Z.add_0_r bw).
    zstep.
    zstep. first [ rewrite (bn_swrap32_small (c1 - bw)) by (clear - Hc1 Hbw; lia) | rewrite (bn_swrap32_mod (c1 - bw) 0) by (clear - Hc1 Hbw; lia) | idtac ].
    ub1 ub_kind.
    ub1 ub_kind. setreg 20%Z (Z_to_bv 64 (18446744073709551615 - rp)) ltac:(f_equal; symmetry; apply zb_lxor_ones; clear - R0; lia).
    ub1 ub_kind.
    eapply B_fin; [exact I2 | exact OK | clear - Hc1 Hbw; lia].
  Qed.

  Lemma B_add1 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T -> kc_ok RES n true R T ->
    evt bgusegs POST (ST 0x107a4c m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 (Z_to_bv 64 (rp + 8 * Z.of_nat (2 * n))) (Z_to_bv 64 (ap + 8 * N))
                         (Z_to_bv 64 (16 * N)) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 (8 * N)) (Z_to_bv 64 (16 * N))
                         (Z_to_bv 64 (18446744073709551615 - tq)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & _).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear; lia)) as (HRb & LRb & ERb & _).
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (_ & _ & _ & WTa).
    pose proof (zr_word a0) as R0. pose proof (zr_word a3) as R3. unfold inr64 in R0, R3.
    do 5 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply ucall_add_words with (a := slice R 0 (2 * n)) (b := slice R (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -112)%Z)
                               (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (rp + 8 * Z.of_nat 0)%Z) (BP := (rp + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP112 | ret_even | exact ST | exact MI | exact LRa | exact LRb | rewrite ERa, ERb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa, A2; clear; lia
      | exact HRa | exact HRb | rewrite ERa; exact WTa
      | unfold alias_ok; rewrite ERa; clear - D1 G; lia | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D3 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia
      | kubp G | kubp G | kubp G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LRb ltac:(rewrite ERa, ERb; reflexivity)) as SP1.
    unfold kc_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R 0 (2 * n)) (slice R (2 * n) (2 * n))) as [sg1 cy1]. cbn [fst snd] in *.
    destruct SP1 as (Ls1 & Es1 & Hc1 & _). rewrite ERa in Es1.
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T 0%nat sg1 _ 80%Z eq_refl I MUc ltac:(rewrite ERa, Es1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls1 ltac:(rewrite Es1; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa HRb LRb ERb WTa MUc WMc HS I D1 D2 D3.
    eapply B_sub; [exact I2 | exact OK | exact Hc1].
  Qed.

  Notation a_lo := (firstn n a).
  Notation a_hi := (slice a n n).

  Lemma B_gen : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    sgen2_ok RES k' n a R T ->
    evt bgusegs POST (ST 0x107a10 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 a1 (Z_to_bv 64 (ap + 8 * N)) (Z_to_bv 64 (16 * N))
                         (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 (8 * N)) (Z_to_bv 64 (16 * N)) (Z_to_bv 64 (18446744073709551615 - tq))
                         x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl.
    assert (Lal : length a_lo = n) by (rewrite length_firstn; clear - G; lia).
    pose proof sqr_scratch_tail as HSC.
    pose proof (zr_word a0) as R0. pose proof (zr_word a3) as R3. unfold inr64 in R0, R3. pose proof ubs as UB.
    do 5 zstep.
    pose proof DRA as D1. pose proof DTA as D3. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof Hk' as HK.
    eapply call_sqr_rec with (CSL := CSL) (k := k') (a := a_lo) (R := slice R 0 (2 * n)) (T := skipn (4 * n) T)
                             (lo := lo) (SPz := (SP + -112)%Z)
                             (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP112 | ret_even | exact ST | exact MI | exact IH
      | apply limbs_firstn; exact LA | exact LRa | exact LTp
      | clear - HK; lia
      | rewrite Lal, pow_n; reflexivity | rewrite ERa, pow_n; reflexivity
      | rewrite ETp; exact HSC
      | ulit | ulit | rewrite pow_n; ulit | ulit
      | exact HAl | exact HRa | exact HTp | rewrite ERa; exact WRa | rewrite ETp; exact WTp
      | rewrite ERa, Lal; clear - D1 G; lia
      | rewrite ETp, Lal; clear - D3 G; lia
      | rewrite ERa, ETp; clear - D5 G; lia
      | rewrite <- HSK; clear - G; lia
      | rewrite <- HSK, ERa; clear - D6 G; lia | rewrite <- HSK, ETp; clear - D7 G; lia
      | rewrite <- HSK, Lal; clear - D8 G; lia
      | kubp G | kubp G | kubp G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HSR HST STc.
    pose proof (sqr_recursive_spec k' a_lo (slice R 0 (2 * n)) (skipn (4 * n) T) (limbs_firstn _ _ LA) LRa LTp
                  ltac:(rewrite Lal, pow_n; reflexivity) ltac:(rewrite ERa, pow_n; reflexivity) ltac:(rewrite ETp; exact HSC)) as MP.
    unfold sqr_post in MP. unfold sgen2_ok in OK.
    destruct (sqr_recursive k' a_lo (slice R 0 (2 * n)) (skipn (4 * n) T)) as [rl p1]. cbn [fst snd] in *.
    destruct MP as (Lrl & Erl & _ & Lp1 & Ep1). rewrite ERa in Erl. rewrite ETp in Ep1.
    pose proof (KAFTER KB_after_RT (FCELLS jb) m1 m2 R T 0%nat rl (4 * n)%nat p1 _ _ (srec_stack CSL k') eq_refl I MUc
                  ltac:(rewrite ERa, Erl; reflexivity) ltac:(rewrite ETp, Ep1; reflexivity) ltac:(rewrite <- HSK; clear - G; lia)
                  WMc MIc HSR HST STc Lrl Lp1 ltac:(rewrite Erl; clear; lia) ltac:(rewrite Ep1; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa WRa HTp LTp ETp WTp HAl MUc WMc HSR HST MIc STc I.
    remember (splice R 0 rl) as R1 eqn:ER1. remember (splice T (4 * n) p1) as T1 eqn:ET1. clear ER1 ET1 Lrl Erl Lp1 Ep1.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I2 ltac:(clear; lia)) as (HRb & LRb & ERb & WRb).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I2 ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n n I2 ltac:(clear - G; lia)) as HAh.
    assert (Lah : length a_hi = n) by (rewrite slice_length; clear - G; lia).
    ub. zstep. ub.
    zstep. setreg 21%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (2 * n))) ltac:(f_equal; clear; lia).
    do 5 zstep.
    eapply call_sqr_rec with (CSL := CSL) (k := k') (a := a_hi) (R := slice R1 (2 * n) (2 * n)) (T := skipn (4 * n) T1)
                             (lo := lo) (SPz := (SP + -112)%Z)
                             (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP112 | ret_even | exact ST | exact MI | exact IH
      | apply slice_limbs; exact LA | exact LRb | exact LTp
      | clear - HK; lia
      | rewrite Lah, pow_n; reflexivity | rewrite ERb, pow_n; reflexivity
      | rewrite ETp; exact HSC
      | ulit | ulit | rewrite pow_n; ulit | ulit
      | exact HAh | exact HRb | exact HTp | rewrite ERb; exact WRb | rewrite ETp; exact WTp
      | rewrite ERb, Lah; clear - D1 G; lia
      | rewrite ETp, Lah; clear - D3 G; lia
      | rewrite ERb, ETp; clear - D5 G; lia
      | rewrite <- HSK; clear - G; lia
      | rewrite <- HSK, ERb; clear - D6 G; lia | rewrite <- HSK, ETp; clear - D7 G; lia
      | rewrite <- HSK, Lah; clear - D8 G; lia
      | kubp G | kubp G | kubp G | ].
    intros m3 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HSR HST STc.
    pose proof (sqr_recursive_spec k' a_hi (slice R1 (2 * n) (2 * n)) (skipn (4 * n) T1) (slice_limbs _ _ _ LA) LRb LTp
                  ltac:(rewrite Lah, pow_n; reflexivity) ltac:(rewrite ERb, pow_n; reflexivity) ltac:(rewrite ETp; exact HSC)) as MP.
    unfold sqr_post in MP. unfold sgen3_ok in OK.
    destruct (sqr_recursive k' a_hi (slice R1 (2 * n) (2 * n)) (skipn (4 * n) T1)) as [rh p2]. cbn [fst snd] in *.
    destruct MP as (Lrh & Erh & _ & Lp2 & Ep2). rewrite ERb in Erh. rewrite ETp in Ep2.
    pose proof (KAFTER KB_after_RT (FCELLS jb) m2 m3 R1 T1 (2 * n)%nat rh (4 * n)%nat p2 _ _ (srec_stack CSL k') eq_refl I2 MUc
                  ltac:(rewrite ERb, Erh; reflexivity) ltac:(rewrite ETp, Ep2; reflexivity) ltac:(rewrite <- HSK; clear - G; lia)
                  WMc MIc HSR HST STc Lrh Lp2 ltac:(rewrite Erh; clear; lia) ltac:(rewrite Ep2; clear - G; lia)) as I3.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRb LRb ERb WRb HTp LTp ETp WTp HAh MUc WMc HSR HST MIc STc I2.
    clear D1 D3 D5 D6 D7 D8 HK.
    eapply B_add1; [exact I3 | exact OK].
  Qed.

  Lemma munch_add_stack : forall (D L8 FB : Z) m1 m2, munch [(D, D + L8)]%Z m1 m2 -> munch [(D, D + L8); (FB - 0, FB)]%Z m1 m2.
  Proof. intros D L8 FB m1 m2 H. eapply munch_weaken; [|exact H]. unfold sub_fp. cbn [outside]. intros x Hx. tauto. Qed.

  Ltac mid_steps G :=
    ub;
    zstep; rewrite A2;
    replace ((2 * N) ≪ 1)%Z with (4 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia);
    rewrite (bn_swrap32_small (4 * N)) by (clear - G; lia);
    do 2 zstep;
    setreg 24%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; clear - G; lia);
    ub;
    zstep; rewrite A2; replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia);
    zstep; setreg 27%Z (Z_to_bv 64 (18446744073709551615 - tq)) ltac:(f_equal; symmetry; apply zb_lxor_ones; lia);
    zstep; rewrite A2; replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).

  Lemma B_join : forall jb m1 R T x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    sjoin_ok RES k' n a R T ->
    evt bgusegs POST (ST 0x1079a8 m1 x1 x5 x6 x7 a0 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 a3 a1 (Z_to_bv 64 (ap + 8 * N)) x23 x24
                         (Z_to_bv 64 (8 * N)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof sqr_scratch_tail as HSC.
    pose proof (zr_word a0) as R0. pose proof (zr_word a3) as R3. unfold inr64 in R0, R3.
    pose proof ubs as UB.
    mid_steps G.
    zstep. if_false.
    ub.
    zstep. setreg 10%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (2 * n))) ltac:(f_equal; clear; lia).
    do 4 zstep.
    pose proof SEPT as D7. pose proof Hk' as HK.
    eapply call_sqr_rec with (CSL := CSL) (k := k') (a := slice T 0 n) (R := slice T (2 * n) (2 * n)) (T := skipn (4 * n) T)
                             (lo := lo) (SPz := (SP + -112)%Z)
                             (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP112 | ret_even | exact ST | exact MI | exact IH
      | exact LTa | exact LTr | exact LTp
      | clear - HK; lia
      | rewrite ETa, pow_n; reflexivity | rewrite ETr, pow_n; reflexivity
      | rewrite ETp; exact HSC
      | ulit | ulit | rewrite pow_n; ulit | ulit
      | exact HTa | exact HTr | exact HTp | rewrite ETr; exact WTr | rewrite ETp; exact WTp
      | rewrite ETr, ETa; clear - G; lia
      | rewrite ETp, ETa; clear - G; lia
      | rewrite ETr, ETp; clear - G; lia
      | rewrite <- HSK; clear - G; lia
      | rewrite <- HSK, ETr; clear - D7 G; lia | rewrite <- HSK, ETp; clear - D7 G; lia
      | rewrite <- HSK, ETa; clear - D7 G; lia
      | kubp G | kubp G | kubp G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HSR HST STc.
    pose proof (sqr_recursive_spec k' (slice T 0 n) (slice T (2 * n) (2 * n)) (skipn (4 * n) T) LTa LTr LTp
                  ltac:(rewrite ETa, pow_n; reflexivity) ltac:(rewrite ETr, pow_n; reflexivity) ltac:(rewrite ETp; exact HSC)) as MP.
    unfold sqr_post in MP. unfold sjoin_ok in OK.
    destruct (sqr_recursive k' (slice T 0 n) (slice T (2 * n) (2 * n)) (skipn (4 * n) T)) as [tm p0]. cbn [fst snd] in *.
    destruct MP as (Ltm & Etm & _ & Lp0 & Ep0). rewrite ETr in Etm. rewrite ETp in Ep0.
    pose proof (KAFTER KB_after_TT (FCELLS jb) m1 m2 R T (2 * n)%nat (4 * n)%nat tm p0 _ _ (srec_stack CSL k') eq_refl I MUc
                  ltac:(rewrite ETr, Etm; reflexivity) ltac:(rewrite ETp, Ep0; reflexivity) ltac:(rewrite Etm; clear; lia)
                  ltac:(rewrite <- HSK; clear - G; lia)
                  WMc MIc HSR HST STc Ltm Lp0 ltac:(rewrite Ep0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTr LTr ETr WTr HTp LTp ETp WTp MUc WMc HSR HST MIc STc I D7 HK.
    zstep.
    eapply B_gen; [exact I2 | exact OK].
  Qed.

  Lemma B_zero : forall jb m1 R T x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    szero_ok RES k' n a R T ->
    evt bgusegs POST (ST 0x1079a8 m1 x1 x5 x6 x7 a0 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 a3 a1 (Z_to_bv 64 (ap + 8 * N)) x23 x24
                         (Z_to_bv 64 (8 * N)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
    pose proof (zr_word a0) as R0. pose proof (zr_word a3) as R3. unfold inr64 in R0, R3.
    pose proof ubs as UB.
    mid_steps G.
    zstep. if_true.
    ub.
    zstep. setreg 10%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (2 * n))) ltac:(f_equal; clear; lia).
    do 4 zstep.
    eapply ucall_memset0 with (L := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -112)%Z) (D := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP112 | ret_even | exact ST | exact MI | ulit | reflexivity | rewrite ETr; ulit | exact HTr | rewrite ETr; exact WTr | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    rewrite ETr in HS.
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T (2 * n)%nat (repeat 0%Z (2 * n)) _ 0%Z eq_refl I (munch_add_stack _ _ _ _ _ MUc)
                  ltac:(rewrite ETr, repeat_length; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc (limbs_repeat _ _ limb_0) ltac:(rewrite repeat_length; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTr LTr ETr WTr MUc WMc HS MIc STc I.
    eapply B_gen; [exact I2 | exact OK].
  Qed.

  Lemma B_diff : forall (sw : bool) jb m1 R T x1 x5 x6 x7 x13 x14 x15 x16 x17 x23 x24 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    sjoin_ok RES k' n a R (splice T 0 (fst (if sw then sub_words a_hi a_lo else sub_words a_lo a_hi))) ->
    evt bgusegs POST (ST 0x107990 m1 x1 x5 x6 x7 a0 a3 (if sw then Z_to_bv 64 (ap + 8 * N) else a1) (if sw then a1 else Z_to_bv 64 (ap + 8 * N))
                         x13 x14 x15 x16 x17 a3 a1 (Z_to_bv 64 (ap + 8 * N)) x23 x24 (Z_to_bv 64 (8 * N)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_a _ _ _ _ n n I ltac:(clear - G; lia)) as HAh.
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (_ & _ & ETn & WTn).
    assert (Lal : length a_lo = n) by (rewrite length_firstn; clear - G; lia).
    assert (Lah : length a_hi = n) by (rewrite slice_length; clear - G; lia).
    pose proof DTA as D3. pose proof SEPT as D7. pose proof SEPA as D8.
    destruct sw.
    - do 2 zstep.
      eapply ucall_sub_words with (a := a_hi) (b := a_lo) (lo := lo) (SPz := (SP + -112)%Z)
                                 (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * N)%Z) (BP := (ap + 8 * Z.of_nat 0)%Z);
        [ exact ESP112 | ret_even | exact ST | exact MI | apply slice_limbs; exact LA | apply limbs_firstn; exact LA
        | rewrite Lah, Lal; reflexivity | rewrite Lah; clear - G; lia | ulit | ulit | ulit | rewrite Lah; ulit
        | exact HAh | exact HAl | rewrite Lah; exact WTn
        | unfold alias_ok; rewrite Lah; clear - D3 G; lia | unfold alias_ok; rewrite Lah; clear - D3 G; lia
        | clear - G; lia | rewrite Lah; clear - D7 G; lia | rewrite Lah; clear - D8 G; lia | rewrite Lah; clear - D8 G; lia
        | kubp G | kubp G | kubp G | ].
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (sub_words_spec _ _ (slice_limbs _ n n LA) (limbs_firstn n _ LA) ltac:(rewrite Lah, Lal; reflexivity)) as SPd.
      destruct (sub_words a_hi a_lo) as [d bw]. cbn [fst snd] in *.
      destruct SPd as (Ld & Ed & _ & _). rewrite Lah in Ed.
      pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T 0%nat d _ 80%Z eq_refl I MUc ltac:(rewrite Lah, Ed; reflexivity)
                    ltac:(clear - G; lia) WMc MIc HS STc Ld ltac:(rewrite Ed; clear - G; lia)) as I2.
      do 2 zstep.
      eapply B_join; [exact I2 | exact OK].
    - do 2 zstep.
      eapply ucall_sub_words with (a := a_lo) (b := a_hi) (lo := lo) (SPz := (SP + -112)%Z)
                                 (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
        [ exact ESP112 | ret_even | exact ST | exact MI | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
        | rewrite Lah, Lal; reflexivity | rewrite Lal; clear - G; lia | ulit | ulit | ulit | rewrite Lal; ulit
        | exact HAl | exact HAh | rewrite Lal; exact WTn
        | unfold alias_ok; rewrite Lal; clear - D3 G; lia | unfold alias_ok; rewrite Lal; clear - D3 G; lia
        | clear - G; lia | rewrite Lal; clear - D7 G; lia | rewrite Lal; clear - D8 G; lia | rewrite Lal; clear - D8 G; lia
        | kubp G | kubp G | kubp G | ].
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (sub_words_spec _ _ (limbs_firstn n _ LA) (slice_limbs _ n n LA) ltac:(rewrite Lah, Lal; reflexivity)) as SPd.
      destruct (sub_words a_lo a_hi) as [d bw]. cbn [fst snd] in *.
      destruct SPd as (Ld & Ed & _ & _). rewrite Lal in Ed.
      pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T 0%nat d _ 80%Z eq_refl I MUc ltac:(rewrite Lal, Ed; reflexivity)
                    ltac:(clear - G; lia) WMc MIc HS STc Ld ltac:(rewrite Ed; clear - G; lia)) as I2.
      do 2 zstep.
      eapply B_join; [exact I2 | exact OK].
  Qed.

  Lemma kara_body : forall jb m1 R T x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    (let c1 := cmp_words a_lo a_hi in
     if (0 <? c1)%Z then sjoin_ok RES k' n a R (splice T 0 (fst (sub_words a_lo a_hi)))
     else if (c1 <? 0)%Z then sjoin_ok RES k' n a R (splice T 0 (fst (sub_words a_hi a_lo)))
     else szero_ok RES k' n a R T) ->
    evt bgusegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 sp a0 (Z_to_bv 64 15) (Z_to_bv 64 8) a2 a3 x14 x15 x16 x17
               a2 s3 a3 a1 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x107948) fc None m1 (seg_rom bgusegs)).
  Proof.
    intros until x31. intros I OK.
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    pose proof (zr_word a0) as R0. pose proof (zr_word a1) as R1. pose proof (zr_word a3) as R3. pose proof (zr_word sp) as RSP. unfold inr64 in R0, R1, R3, RSP.
    destruct (UR ltac:(lia)) as (NZR & AR8). destruct (UA ltac:(lia)) as (NZA & AA8). destruct (UT ltac:(lia)) as (NZT & AT8).
    do 3 zstep. rewrite A2, half_n2 by (clear - G; lia).
    zstep. replace (N ≪ 3)%Z with (8 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    ub. do 3 zstep.
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_a _ _ _ _ n n I ltac:(clear - G; lia)) as HAh.
    assert (Lal : length a_lo = n) by (rewrite length_firstn; clear - G; lia).
    assert (Lah : length a_hi = n) by (rewrite slice_length; clear - G; lia).
    pose proof SEPA as D8.
    zstep.
    eapply call_cmp_words with (a := a_lo) (b := a_hi) (lo := lo) (SPz := (SP + -112)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
      [ exact ESP112 | ret_even | exact STK | exact MI | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
      | rewrite Lah, Lal; reflexivity | rewrite Lal; clear - G; lia | ulit | ulit | rewrite Lal; ulit
      | exact HAl | exact HAh | clear - G; lia
      | rewrite Lal; clear - D8 G; lia | rewrite Lal; clear - D8 G; lia | kubp G | kubp G | ].
    intros m3 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc STc.
    pose proof (KAFTER KB_after_ro (FCELLS jb) m1 m3 R T 16%Z eq_refl I MUc ltac:(clear - G; lia) WMc MIc STc) as I3.
    clear FR STK MI HAl HAh D8 MUc WMc MIc STc I.
    remember (cmp_words a_lo a_hi) as c1 eqn:Ec1.
    assert (Hc1 : (c1 = -1 \/ c1 = 0 \/ c1 = 1)%Z).
    { rewrite Ec1, (cmp_words_spec a_lo a_hi (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA)) by (rewrite Lal, Lah; reflexivity). apply sgn3_range. }
    clear Ec1.
    destruct Hc1 as [E1|[E1|E1]]; rewrite E1 in *; clear E1 c1; cbn [Z.ltb] in OK.
    - setreg 10%Z (Z_to_bv 64 (-1)) ltac:(vm_compute; reflexivity). zstep. if_true.
      zstep. if_true. do 4 zstep.
      eapply (B_diff true); [exact I3 | exact OK].
    - setreg 10%Z (Z_to_bv 64 0) ltac:(vm_compute; reflexivity). zstep. if_true.
      zstep. if_false. zstep.
      eapply B_zero; [exact I3 | exact OK].
    - setreg 10%Z (Z_to_bv 64 1) ltac:(vm_compute; reflexivity). zstep. if_false.
      do 3 zstep.
      eapply (B_diff false); [exact I3 | exact OK].
  Qed.
End Kara.

Lemma pow2_bounds26 : forall k, (k <= 26)%nat -> (1 <= Z.of_nat (Nat.pow 2 k) <= 67108864)%Z.
Proof.
  intros k Hk. rewrite Nat2Z.inj_pow. change (Z.of_nat 2) with 2%Z. split.
  - change 1%Z with (2 ^ 0)%Z at 1. apply Z.pow_le_mono_r; lia.
  - change 67108864%Z with (2 ^ 26)%Z. apply Z.pow_le_mono_r; lia.
Qed.

Lemma pow2_ge16 : forall k, (16 <= Nat.pow 2 k)%nat -> exists k', k = S k' /\ (3 <= k')%nat.
Proof.
  intros k H. destruct k as [|k']; [cbn in H; lia|]. exists k'. split; [reflexivity|].
  destruct k' as [|[|[|k3]]]; cbn in H; lia.
Qed.

Section Main.
  Variables (C4 C8 CSL : Z).
  Hypothesis C4_0 : (0 <= C4)%Z.
  Hypothesis C8_0 : (0 <= C8)%Z.
  Hypothesis HC4 : (C4 <= CSL)%Z.
  Hypothesis HC8 : (C8 <= CSL)%Z.
  Hypothesis H256 : (256 <= CSL)%Z.
  Hypothesis comba4_ok : sqr_comba4_spec C4.
  Hypothesis comba8_ok : sqr_comba8_spec C8.

  Lemma rec_body : forall k, (forall k', k = S k' -> sqr_rec_spec_at CSL k') -> sqr_rec_spec_at CSL k.
  Proof.
    intros k IHk. unfold sqr_rec_spec_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a R T lo
           LA LR LT Hk HLA HLR HLT A2 RA RR RT WR WT DRA DTA DRT STK LO SEPR SEPT SEPA MI0 UR UA UT.
    remember (Nat.pow 2 k) as N2 eqn:EN2.
    assert (HN2 : (1 <= Z.of_nat N2 <= 67108864)%Z) by (subst N2; apply pow2_bounds26; exact Hk).
    remember (srec_stack CSL k - 112)%Z as SK eqn:ESK.
    assert (HSK : (144 <= SK /\ CSL - 112 <= SK)%Z) by (subst SK; unfold srec_stack; lia).
    assert (ERS : srec_stack CSL k = (112 + SK)%Z) by (subst SK; lia).
    rewrite ERS in LO, SEPR, SEPT, SEPA |- *.
    pose proof (proj1 STK) as LO0.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA.
    pose proof (wr_at_below bgusegs m _ _ MI0 WR ltac:(rewrite HLR; lia)) as BR.
    pose proof (sqr_scratch_ge k) as HSG. rewrite <- EN2 in HSG.
    assert (HT2 : (2 * N2 <= length T)%nat) by (clear - HSG HLT; lia).
    pose proof (wr_at_below bgusegs m _ _ MI0 WT ltac:(lia)) as BT.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *. unfold UTOP in *.

    assert (GEO : hide ((bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0) /\
                        (bv_unsigned a3 + 8 * Z.of_nat (length T) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a3) /\
                        (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a3 \/ bv_unsigned a3 + 8 * Z.of_nat (length T) <= bv_unsigned a0) /\
                        (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned sp - (112 + SK) \/ bv_unsigned sp <= bv_unsigned a0) /\
                        (bv_unsigned a3 + 8 * Z.of_nat (length T) <= bv_unsigned sp - (112 + SK) \/ bv_unsigned sp <= bv_unsigned a3) /\
                        (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - (112 + SK) \/ bv_unsigned sp <= bv_unsigned a1) /\
                        length a = N2 /\ length R = (2 * N2)%nat /\ (sqr_scratch k <= length T)%nat /\ (2 * N2 <= length T)%nat)%Z).
    { apply hide_intro. repeat split; assumption. }
    rewrite HLR in WR.
    clear DRA DTA DRT SEPR SEPT SEPA HLA HLR HLT HSG HT2.
    pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length R)); (bv_unsigned a3, bv_unsigned a3 + 8 * Z.of_nat (length T));
                            (bv_unsigned sp - (112 + SK), bv_unsigned sp)]%Z m) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MUF. pose proof (wmono_refl bgusegs m) as WM.
    assert (LO1 : (lo <= bv_unsigned sp - 112)%Z) by (clear - LO HSK; lia).
    carve_frame 112%nat STK.
    apply (rw_cells_split_CB bgusegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 14 zstep. do 4 zstep.

    pose proof (hide_elim _ GEO) as (DRA & DTA & DRT & SEPR & SEPT & SEPA & HLA' & HLR' & HLT' & HT2).
    assert (RA1 : limbs_at bgusegs m0 (bv_unsigned a1) a) by (eapply limbs_at_transport; [exact RA | exact MUF | cbn [disjoint_from]; clear - SEPA HSK; lia]).
    assert (RR1 : limbs_at bgusegs m0 (bv_unsigned a0) R) by (eapply limbs_at_transport; [exact RR | exact MUF | cbn [disjoint_from]; clear - SEPR HSK; lia]).
    assert (RT1 : limbs_at bgusegs m0 (bv_unsigned a3) T) by (eapply limbs_at_transport; [exact RT | exact MUF | cbn [disjoint_from]; clear - SEPT HSK; lia]).
    clear DRA DTA DRT SEPR SEPT SEPA HLA' HLR' HLT' HT2 MUF RA RR RT.

    assert (TAILC : forall (nl : nat) (CS : Z) (entry : Z) (res : list Z),
      N2 = nl -> (0 <= CS <= CSL)%Z -> length res = (2 * nl)%nat ->
      sqr_recursive k a R T = (splice R 0 res, T) ->
      (forall (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         limbs a -> length a = nl -> limbs_at bgusegs m0 (bv_unsigned a1) a -> wr_at bgusegs m0 (bv_unsigned a0) (8 * Z.of_nat (2 * nl)) ->
         (bv_unsigned a0 + 8 * Z.of_nat (2 * nl) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat nl <= bv_unsigned a0)%Z ->
         stk bgusegs m0 lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - CS)%Z ->
         (bv_unsigned a0 + 8 * Z.of_nat (2 * nl) <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
         (bv_unsigned a1 + 8 * Z.of_nat nl <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
         mem_inv bgusegs m0 ->
         ub_ptr_ok 1 (bv_unsigned a0) -> ub_ptr_ok 1 (bv_unsigned a1) ->
         evt bgusegs (vl_post bgusegs ra' sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (Z.of_nat (2 * nl)) CS res lo m0)
           (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0 a1 a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 entry) fc None m0 (seg_rom bgusegs))) ->
      forall (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      stk bgusegs m0 lo (bv_unsigned sp) ->
      evt bgusegs (kr_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (Z.of_nat (length R))
                     (bv_unsigned a3) (Z.of_nat (length T)) (112 + SK) (fst (sqr_recursive k a R T)) (snd (sqr_recursive k a R T)) lo m)
        (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 entry) fc None m0 (seg_rom bgusegs))).
    { intros nl CS entry res Enl HCS Lres EM LEAF t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' STK'.
      pose proof (hide_elim _ GEO) as (DRA & DTA & DRT & SEPR & SEPT & SEPA & HLA' & HLR' & HLT' & HT2).
      rewrite EM. cbn [fst snd].
      eapply evt_mono.
      { eapply LEAF; [ exact LA | clear - HLA' Enl; lia | exact RA1 | rewrite <- Enl; exact WR
        | clear - DRA HLR' HLA' Enl; lia | exact STK' | clear - LO HSK HCS; lia
        | clear - SEPR HLR' Enl HSK HCS; lia | clear - SEPA HLA' Enl HSK HCS; lia | exact MI0 | exact UR | exact UA ]. }
      intros ms' PO. unfold vl_post in PO.
      destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
      exists u0, u1, u2, v0, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m2.
      split; [exact E|].
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx.
               clear - Hx HLR' Enl HSK HCS. lia. }
      split; [eapply wmono_trans; [exact WM | exact WMc]|]. split; [exact MIc|].
      rewrite splice_all by (rewrite Lres, HLR', Enl; reflexivity).
      split; [exact HS|]. split; [|exact STc].
      eapply limbs_at_transport; [exact RT1 | exact MUc | cbn [disjoint_from]; clear - DRT SEPT HLR' Enl HSK HCS; lia]. }
    zstep. if_cases K8; zify_cond K8.
    {
      assert (E8 : N2 = 8%nat) by (clear - K8 A2; lia).
      do 17 zstep.
      release_frame FR STK (bv_unsigned sp).
      destruct (sqr_comba_spec a 8 LA ltac:(pose proof (hide_elim _ GEO) as X; clear - X E8; lia)) as (_ & Lc & _).
      eapply (TAILC 8%nat C8 0x105af4%Z (sqr_comba8 a) E8 ltac:(clear - C8_0 HC8; lia));
        [ exact Lc | rewrite sqr_recursive_c8 by (rewrite <- EN2; exact E8); rewrite firstn_all2 by (pose proof (hide_elim _ GEO) as X; clear - X E8; lia); reflexivity
        | | exact STK ].
      intros. eapply comba8_ok; eassumption. }
    do 2 zstep.
    zstep. if_cases K4; zify_cond K4.
    2: {
      assert (E4 : N2 = 4%nat) by (clear - K4 A2; lia).
      do 17 zstep.
      release_frame FR STK (bv_unsigned sp).
      destruct (sqr_comba_spec a 4 LA ltac:(pose proof (hide_elim _ GEO) as X; clear - X E4; lia)) as (_ & Lc & _).
      eapply (TAILC 4%nat C4 0x106eac%Z (sqr_comba4 a) E4 ltac:(clear - C4_0 HC4; lia));
        [ exact Lc | rewrite sqr_recursive_c4 by (rewrite <- EN2; exact E4); rewrite firstn_all2 by (pose proof (hide_elim _ GEO) as X; clear - X E4; lia); reflexivity
        | | exact STK ].
      intros. eapply comba4_ok; eassumption. }
    do 2 zstep.
    assert (L15 : (bv_unsigned (Z_to_bv 64 15) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (L2 : (bv_unsigned a2 < 9223372036854775808)%Z) by (rewrite A2; clear - HN2; lia).
    zstep. rewrite (lts_words_small (Z_to_bv 64 15) a2 L15 L2). clear L15 L2.
    rewrite A2. if_cases K16; zify_cond K16.
    {
      destruct (pow2_ge16 k ltac:(rewrite <- EN2; clear - K16; lia)) as (k' & Ek & Hk3). subst k.
      remember (Nat.pow 2 k') as n eqn:En.
      assert (EN : N2 = (2 * n)%nat) by (rewrite EN2, En; cbn [Nat.pow]; clear; lia).
      pose proof (hide_elim _ GEO) as (DRA & DTA & DRT & SEPR & SEPT & SEPA & HLA' & HLR' & HLT' & HT2).
      assert (ELR : length R = (4 * n)%nat) by (clear - HLR' EN; lia).
      assert (ESK' : SK = srec_stack CSL k').
      { clear - ESK. unfold srec_stack in *. rewrite !Nat2Z.inj_succ in *. lia. }
      assert (PRE : sqr_pre CSL k' n (length a) (length T) SK (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned sp) lo).
      { unfold sqr_pre. rewrite <- ELR.
        split; [exact En|]. split; [clear - Hk Hk3; lia|]. split; [clear - K16 EN; lia|]. split; [clear - HN2 EN; lia|].
        split; [clear - HLA' EN; lia|].
        split. { cbn [sqr_scratch] in HLT'. rewrite <- EN2 in HLT'. clear - HLT' EN ELR. lia. }
        split; [exact ESK'|].
        split; [exact DRA|]. split; [exact DTA|]. split; [exact DRT|].
        split; [clear - SEPR; lia|]. split; [clear - SEPT; lia|]. split; [clear - SEPA; lia|].
        split; [clear - LO; lia |]. split; [exact LO0 | exact H256]. }
      replace (Z.of_nat (length R)) with (Z.of_nat (4 * n)) by (rewrite ELR; reflexivity).
      eapply (kara_body CSL k' (IHk k' eq_refl)) with (n := n) (nT := length T) (SK := SK);
        [ exact PRE | exact LA | rewrite A2, EN; clear; lia | exact UR | exact UA | exact UT | | ].
      - unfold KB. split; [exact LR|]. split; [exact LT|]. split; [exact ELR|]. split; [reflexivity|].
        split; [exact RR1|]. split; [exact RT1|]. split; [exact RA1|]. split; [exact RA1|].
        split; [rewrite EN in WR; replace (4 * n)%nat with (2 * (2 * n))%nat by (clear; lia); exact WR|]. split; [exact WT|].
        split; [exact FR|]. split; [exact STK|]. split; [exact MI0|].
        split; [|exact WM]. unfold KWfin. rewrite <- ELR. replace (bv_unsigned sp - 112 - SK)%Z with (bv_unsigned sp - (112 + SK))%Z by (clear; lia). exact MU.
      - rewrite En. apply srec_staged; try assumption; rewrite <- ?EN2; try assumption. clear - K16. lia. }
    clear IHk.

    assert (NC : N2 <> 4%nat /\ N2 <> 8%nat) by (clear - K4 K8 A2; split; intros E; [apply K4 | apply K8]; rewrite A2, E; reflexivity).
    do 19 zstep.
    release_frame FR STK (bv_unsigned sp).
    pose proof (hide_elim _ GEO) as (DRA & DTA & DRT & SEPR & SEPT & SEPA & HLA' & HLR' & HLT' & HT2).
    pose proof (BgSqrCorrect.sqr_normal_spec a LA R ltac:(clear - HLA' HN2; lia) LR ltac:(clear - HLA' HLR'; lia)) as NSP.
    assert (EMOD : sqr_recursive k a R T = (let '(ro, tmp) := sqr_normal a R in (splice R 0 ro, splice T 0 tmp))).
    { rewrite sqr_recursive_small by (rewrite <- EN2; clear - K16 NC; lia). cbv zeta. rewrite <- EN2.
      rewrite !firstn_all2 by (clear - HLA' HLR'; lia). reflexivity. }
    rewrite EMOD. clear EMOD.
    destruct (sqr_normal a R) as [ro tmp] eqn:Esn. destruct NSP as (Lro & Ero & _ & Etmp). cbn [fst snd].
    destruct (sqr_words_spec a LA) as (_ & Lsw & _).
    eapply evt_mono.
    { eapply (bn_sqr_normal_spec ra sp gp tp) with (A := a) (r0 := R) (lo := lo);
        [ exact LA | exact LR | clear - HLA' HLR'; lia | clear - HLA' HN2; lia | clear - HLA' HN2; lia | rewrite A2, HLA'; reflexivity
        | exact RA1 | exact RR1
        | rewrite HLA'; replace (8 * (2 * Z.of_nat N2))%Z with (8 * Z.of_nat (2 * N2))%Z by (clear; lia); exact WR
        | pose proof (wr_at_sub bgusegs m0 _ _ 0 (8 * (2 * Z.of_nat (length a))) WT ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - HT2 HLA'; lia)) as X;
          rewrite Z.add_0_r in X; exact X
        | clear - DRA HLA' HLR'; lia | clear - DRT HLA' HLR' HT2; lia | clear - DTA HLA' HT2; lia
        | exact STK | clear - LO HSK; lia
        | clear - SEPR HLA' HLR' HSK; lia | clear - SEPA HSK; lia | clear - SEPT HLA' HT2 HSK; lia | exact MI0
        | intros _; apply UR; lia | intros _; apply UA; lia | intros _; apply UT; lia ]. }
    intros ms' PO. unfold vl_post2 in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & HTs & STc).
    exists u0, u1, u2, v0, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m2.
    split; [exact E|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx.
             clear - Hx HLR' HLA' HT2 HSK. lia. }
    split; [eapply wmono_trans; [exact WM | exact WMc]|]. split; [exact MIc|].
    rewrite Esn in HS. cbn [fst snd] in HS.
    rewrite splice_all by (rewrite Ero, HLR', HLA'; reflexivity).
    split; [exact HS|]. split; [|exact STc].
    eapply (limbs_at_splice bgusegs _ m0 m2 (bv_unsigned a3) T 0 tmp RT1 MUc).
    - rewrite Etmp, Lsw. clear - HT2 HLA'. lia.
    - change (Z.of_nat 0) with 0%Z. rewrite Z.mul_0_r, Z.add_0_r, Etmp. exact HTs.
    - cbn [disjoint_from]. split; [clear - DRT HLA' HLR' HT2; lia|]. split; [clear; lia|]. split; [clear - SEPT HSK HLA' HT2; lia | exact I].
    - cbn [disjoint_from]. rewrite Etmp, Lsw.
      split; [clear - DRT HLA' HLR' HT2; lia|]. split; [clear - HLA' HT2; lia|]. split; [clear - SEPT HSK HLA' HT2; lia | exact I].
  Qed.

  Theorem bn_sqr_recursive_spec : forall k, sqr_rec_spec_at CSL k.
  Proof.
    induction k as [|k IH]; apply rec_body; intros k' E; [discriminate|]. injection E as <-. exact IH.
  Qed.
End Main.
