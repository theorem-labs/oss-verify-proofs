(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp BnKaraX BnKaraMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_cmp_words W_mul_normal BnCalls W_mul_recursive.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import BnCallsU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_mul_recursive_uentry := 0x1013e4%Z.

Lemma munch_add_stack_u : forall (D L8 FB : Z) (m1 m2 : word -> option byte),
  munch [(D, D + L8)]%Z m1 m2 -> munch [(D, D + L8); (FB - 0, FB)]%Z m1 m2.
Proof.
  intros D L8 FB m1 m2 H. eapply munch_weaken; [|exact H]. unfold sub_fp. cbn [outside]. intros x (H1 & _ & H3). split; [exact H1 | exact H3].
Qed.

(* [comment removed for export] *)
Lemma lxor_signbit : forall x, (0 <= x < 9223372036854775808 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808)%Z.
Proof.
  intros x Hx. symmetry. apply Z.add_nocarry_lxor.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0. change 9223372036854775808%Z with (2^63)%Z. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 i) as [<-|]; [|apply andb_false_r]. rewrite andb_true_r.
  destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall x, (0 <= x < 18446744073709551616 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x)%Z.
Proof.
  intros x Hx. change 18446744073709551615%Z with (Z.ones 64) at 1.
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 64) as [H|H].
    - rewrite Z.ones_spec_low by lia. rewrite andb_true_r, xorb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite andb_false_r, xorb_false_r.
      destruct (Z.eq_dec x 0) as [->|Nx]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. assert (Z.log2 x < 64)%Z by (apply Z.log2_lt_pow2; lia). lia. }
  rewrite E, Z.land_ones by lia. unfold Z.lnot, Z.pred. change (2 ^ 64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. lia.
Qed.


(* [comment removed for export] *)
Definition rec_ustack (L : Z) (k : nat) : Z := (160 * Z.of_nat (S k) + L)%Z.

Definition rec_uspec_at (L : Z) (k : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (da db : nat) (R T : list Z) (lo : Z),
    limbs a -> limbs b -> limbs R -> limbs T ->
    (1 <= k <= 26)%nat -> (da <= 1)%nat -> (db <= 1)%nat ->
    length a = (Nat.pow 2 k - da)%nat -> length b = (Nat.pow 2 k - db)%nat -> length R = (2 * Nat.pow 2 k)%nat ->
    (scratch_rec k <= length T)%nat ->
    bv_unsigned a3 = Z.of_nat (Nat.pow 2 k) -> a4 = Z_to_bv 64 (- Z.of_nat da) -> a5 = Z_to_bv 64 (- Z.of_nat db) ->
    limbs_at bgusegs m (bv_unsigned a1) a -> limbs_at bgusegs m (bv_unsigned a2) b ->
    limbs_at bgusegs m (bv_unsigned a0) R -> limbs_at bgusegs m (bv_unsigned a6) T ->
    wr_at bgusegs m (bv_unsigned a0) (8 * Z.of_nat (length R)) -> wr_at bgusegs m (bv_unsigned a6) (8 * Z.of_nat (length T)) ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a0)%Z ->
    (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a6)%Z ->
    (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a6)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a6 \/ bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a0)%Z ->
    stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - rec_ustack L k)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned sp - rec_ustack L k \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned sp - rec_ustack L k \/ bv_unsigned sp <= bv_unsigned a6)%Z ->
    (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - rec_ustack L k \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned sp - rec_ustack L k \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    mem_inv bgusegs m ->
    ub_ptr_ok 1 (bv_unsigned a0) -> ub_ptr_ok 1 (bv_unsigned a1) -> ub_ptr_ok 1 (bv_unsigned a2) -> ub_ptr_ok 1 (bv_unsigned a6) ->
    evt bgusegs (kr_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (bv_unsigned a0) (Z.of_nat (length R)) (bv_unsigned a6) (Z.of_nat (length T)) (rec_ustack L k)
                 (fst (mul_recursive k a b da db R T)) (snd (mul_recursive k a b da db R T)) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1013e4) fc None m (seg_rom bgusegs)).

(* [comment removed for export] *)
Section CallURec.
  Variable POST : machine_state -> Prop.
  Variables (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo SPz RET : Z).
  Hypothesis ESP : bv_unsigned wsp = SPz.
  Hypothesis ERET : ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET.
  Hypothesis STK : stk bgusegs m lo SPz.
  Hypothesis MI0 : mem_inv bgusegs m.

  Lemma call_urec : forall (L : Z) (k : nat) (a b : list Z) (da db : nat) (R T : list Z) (RP AP BP TQ : Z),
    rec_uspec_at L k ->
    limbs a -> limbs b -> limbs R -> limbs T ->
    (1 <= k <= 26)%nat -> (da <= 1)%nat -> (db <= 1)%nat ->
    length a = (Nat.pow 2 k - da)%nat -> length b = (Nat.pow 2 k - db)%nat -> length R = (2 * Nat.pow 2 k)%nat ->
    (scratch_rec k <= length T)%nat ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (Nat.pow 2 k) ->
    w4 = Z_to_bv 64 (- Z.of_nat da) -> w5 = Z_to_bv 64 (- Z.of_nat db) -> bv_unsigned w6 = TQ ->
    limbs_at bgusegs m AP a -> limbs_at bgusegs m BP b -> limbs_at bgusegs m RP R -> limbs_at bgusegs m TQ T ->
    wr_at bgusegs m RP (8 * Z.of_nat (length R)) -> wr_at bgusegs m TQ (8 * Z.of_nat (length T)) ->
    (RP + 8 * Z.of_nat (length R) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (RP + 8 * Z.of_nat (length R) <= BP \/ BP + 8 * Z.of_nat (length b) <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= AP \/ AP + 8 * Z.of_nat (length a) <= TQ)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= BP \/ BP + 8 * Z.of_nat (length b) <= TQ)%Z ->
    (RP + 8 * Z.of_nat (length R) <= TQ \/ TQ + 8 * Z.of_nat (length T) <= RP)%Z ->
    (lo <= SPz - rec_ustack L k)%Z ->
    (RP + 8 * Z.of_nat (length R) <= SPz - rec_ustack L k \/ SPz <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= SPz - rec_ustack L k \/ SPz <= TQ)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - rec_ustack L k \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - rec_ustack L k \/ SPz <= BP)%Z ->
    ub_ptr_ok 1 RP -> ub_ptr_ok 1 AP -> ub_ptr_ok 1 BP -> ub_ptr_ok 1 TQ ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length R)); (TQ, TQ + 8 * Z.of_nat (length T)); (SPz - rec_ustack L k, SPz)]%Z m m2 ->
       wmono bgusegs m m2 -> mem_inv bgusegs m2 ->
       limbs_at bgusegs m2 RP (fst (mul_recursive k a b da db R T)) -> limbs_at bgusegs m2 TQ (snd (mul_recursive k a b da db R T)) ->
       stk bgusegs m2 lo SPz ->
       evt bgusegs POST
         (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
             F (Z_to_bv 64 RET) fc None m2 (seg_rom bgusegs))) ->
    evt bgusegs POST
      (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1013e4) fc None m (seg_rom bgusegs)).
  Proof using ESP ERET STK MI0.
    intros L k a b da db R T RP AP BP TQ SPEC LA LB LR LT Hk Hda Hdb HLA HLB HLR HLT E0 E1 E2 E3 E4 E5 E6
           RA RB RR RT WR WT DRA DRB DTA DTB DRT LO SEPR SEPT SEPA SEPB UBR UBA UBB UBT K.
    subst RP AP BP TQ SPz.
    eapply evt_cut; [ eapply SPEC with (a := a) (b := b) (da := da) (db := db) (R := R) (T := T) (lo := lo); eassumption | ].
    intros ms' PO. unfold kr_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & HT & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.
End CallURec.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kara_upre (L : Z) (k' n da db la lb nT : nat) (SK rp tq ap bp SP lo : Z) : Prop :=
  n = Nat.pow 2 k' /\ (1 <= k' <= 25)%nat /\ (8 <= n)%nat /\ (Z.of_nat n <= 33554432)%Z /\ (da <= 1)%nat /\ (db <= 1)%nat /\
  la = (2 * n - da)%nat /\ lb = (2 * n - db)%nat /\ (4 * n + scratch_rec k' <= nT)%nat /\ SK = rec_ustack L k' /\
  (rp + 8 * Z.of_nat (4 * n) <= ap \/ ap + 8 * Z.of_nat la <= rp)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= bp \/ bp + 8 * Z.of_nat lb <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat la <= tq)%Z /\
  (tq + 8 * Z.of_nat nT <= bp \/ bp + 8 * Z.of_nat lb <= tq)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= tq \/ tq + 8 * Z.of_nat nT <= rp)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= SP - 160 - SK \/ SP <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= SP - 160 - SK \/ SP <= tq)%Z /\
  (ap + 8 * Z.of_nat la <= SP - 160 - SK \/ SP <= ap)%Z /\
  (bp + 8 * Z.of_nat lb <= SP - 160 - SK \/ SP <= bp)%Z /\
  (lo <= SP - 160 - SK)%Z /\ (0 <= lo)%Z /\ (80 <= L)%Z.

Section KaraU.
  Variables (L CS8 FSC FSS FSM : Z).
  Hypothesis LEAF : (0 <= CS8 <= L /\ 0 <= FSC <= L /\ 0 <= FSS <= L /\ 0 <= FSM <= L)%Z.
  Hypothesis comba8_ok : comba8_uspec CS8.
  Hypothesis cmp_part_ok : cmp_part_words_uspec FSC.
  Hypothesis sub_part_ok : sub_part_words_uspec FSS.
  Hypothesis mul_normal_ok : mul_normal_uspec FSM.
  Variable k' : nat.
  Hypothesis IH : rec_uspec_at L k'.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (da db : nat) (lo : Z) (n nT : nat) (SK : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a2).
  Notation tq := (bv_unsigned a6).
  Notation SP := (bv_unsigned sp).
  Notation N := (Z.of_nat n).
  Hypothesis PRE : kara_upre L k' n da db (length a) (length b) nT SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo.
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
  Hypothesis A3 : bv_unsigned a3 = (2 * N)%Z.
  Hypothesis A4 : a4 = Z_to_bv 64 (- Z.of_nat da).
  Hypothesis A5 : a5 = Z_to_bv 64 (- Z.of_nat db).
  Hypothesis UBR : ub_ptr_ok 1 (bv_unsigned a0).
  Hypothesis UBA : ub_ptr_ok 1 (bv_unsigned a1).
  Hypothesis UBB : ub_ptr_ok 1 (bv_unsigned a2).
  Hypothesis UBT : ub_ptr_ok 1 (bv_unsigned a6).
  Variable RES : list Z * list Z.

  Lemma Hn : n = Nat.pow 2 k'. Proof. apply PRE. Qed.
  Lemma Hk' : (1 <= k' <= 25)%nat. Proof. apply PRE. Qed.
  Lemma Hn8 : (8 <= n)%nat. Proof. apply PRE. Qed.
  Lemma HnB : (N <= 33554432)%Z. Proof. apply PRE. Qed.
  Lemma Hda : (da <= 1)%nat. Proof. apply PRE. Qed.
  Lemma Hdb : (db <= 1)%nat. Proof. apply PRE. Qed.
  Lemma HLA : length a = (2 * n - da)%nat. Proof. apply PRE. Qed.
  Lemma HLB : length b = (2 * n - db)%nat. Proof. apply PRE. Qed.
  Lemma HnT : (4 * n + scratch_rec k' <= nT)%nat. Proof. apply PRE. Qed.
  Lemma HSK : SK = rec_ustack L k'. Proof. apply PRE. Qed.
  Lemma HL80 : (80 <= L)%Z. Proof. apply PRE. Qed.
  Lemma DRA : (rp + 8 * Z.of_nat (4 * n) <= ap \/ ap + 8 * Z.of_nat (length a) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma DRB : (rp + 8 * Z.of_nat (4 * n) <= bp \/ bp + 8 * Z.of_nat (length b) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma DTA : (tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat (length a) <= tq)%Z. Proof. apply PRE. Qed.
  Lemma DTB : (tq + 8 * Z.of_nat nT <= bp \/ bp + 8 * Z.of_nat (length b) <= tq)%Z. Proof. apply PRE. Qed.
  Lemma DRT : (rp + 8 * Z.of_nat (4 * n) <= tq \/ tq + 8 * Z.of_nat nT <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPR : (rp + 8 * Z.of_nat (4 * n) <= SP - 160 - SK \/ SP <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPT : (tq + 8 * Z.of_nat nT <= SP - 160 - SK \/ SP <= tq)%Z. Proof. apply PRE. Qed.
  Lemma SEPA : (ap + 8 * Z.of_nat (length a) <= SP - 160 - SK \/ SP <= ap)%Z. Proof. apply PRE. Qed.
  Lemma SEPB : (bp + 8 * Z.of_nat (length b) <= SP - 160 - SK \/ SP <= bp)%Z. Proof. apply PRE. Qed.
  Lemma LO : (lo <= SP - 160 - SK)%Z. Proof. apply PRE. Qed.
  Lemma LO0 : (0 <= lo)%Z. Proof. apply PRE. Qed.
  Lemma SK0 : (0 <= SK)%Z. Proof. rewrite HSK. unfold rec_ustack. pose proof HL80. lia. Qed.
  Lemma SK_ge : (160 + L <= SK)%Z. Proof. rewrite HSK. unfold rec_ustack. lia. Qed.
  Lemma FS0 : (0 <= 160)%Z. Proof. lia. Qed.
  Lemma FBE : (SP + -160 = SP - 160)%Z. Proof. reflexivity. Qed.
  Lemma ESP160 : bv_unsigned (Z_to_bv 64 (SP + -160)) = (SP + -160)%Z.
  Proof.
    apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R.
    pose proof LO. pose proof LO0. pose proof SK0. lia.
  Qed.

  Notation POST := (kr_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                      (bv_unsigned a0) (Z.of_nat (4 * n)) (bv_unsigned a6) (Z.of_nat nT) (160 + SK)%Z (fst RES) (snd RES) lo m).
  Notation KBK := (KB bgusegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      160%Z SK (bv_unsigned sp + -160)%Z).
  Notation KUPD := (KB_upd bgusegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      160%Z SK (bv_unsigned sp + -160)%Z FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB).
  Notation KFRAME := (KB_frame bgusegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      160%Z SK (bv_unsigned sp + -160)%Z FS0 FBE SK0 SEPR SEPT SEPA SEPB).
  Notation KSTORE := (KB_storeR bgusegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      160%Z SK (bv_unsigned sp + -160)%Z FS0 FBE SK0 DRA DRB DRT SEPR).
  Notation KAFTER L := (L bgusegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      160%Z SK (bv_unsigned sp + -160)%Z FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB).
  Notation KACC L := (L bgusegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      160%Z SK (bv_unsigned sp + -160)%Z).


  (* [comment removed for export] *)
  Notation FCELLS jb :=
    [CB 8 jb; C8 a1; C8 a2; C8 (Z_to_bv 64 (bv_unsigned a2 + 8 * Z.of_nat n)); C8 (Z_to_bv 64 (bv_unsigned a1 + 8 * Z.of_nat n));
     C8 (Z_to_bv 64 (8 * Z.of_nat n)); C8 a0;
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  (* [comment removed for export] *)
  Lemma UB_epi : forall jb m1 R T x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T -> RES = (R, T) ->
    evt bgusegs POST (ST 0x101b5c m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM) E.
    do 15 zstep.
    assert (LO1 : (lo <= SP + -160)%Z) by (pose proof LO; pose proof SK0; lia).
    release_frame FR ST (bv_unsigned sp).
    subst RES. cbn [fst snd].
    assert (MU' : munch [(rp, rp + 8 * Z.of_nat (4 * n)); (tq, tq + 8 * Z.of_nat nT); (SP - (160 + SK), SP)]%Z m m1).
    { unfold KWfin in MU. replace (SP - (160 + SK))%Z with (SP - 160 - SK)%Z by (clear; lia). exact MU. }
    finish.
  Qed.

  Ltac ret_even := apply ret_pc_even; [lia | reflexivity].
  Ltac ulit := first [ reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; lia); lia | lia ].
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

  (* [comment removed for export] *)
  Lemma UB_loop : forall (l pre : list Z) jb m1 T x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 (pre ++ l) T -> cu_fit l -> RES = (pre ++ carry_up l, T) -> (1 <= length pre)%nat ->
    evt bgusegs POST (ST 0x101b40 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 (-9)) (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre) + -8)) x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction l as [|x l' IHl]; intros until x31; intros I FIT E Hpre.
    { exfalso. unfold cu_fit in FIT. cbn [lval length] in FIT. rewrite Bp_0 in FIT. clear - FIT. lia. }
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (cu_fit_cons (x :: l') (proj2 (limbs_app_inv _ _ LR)) FIT) as (x' & l'' & Ecs & Hx & Hl' & Hfit').
    injection Ecs as <- <-.
    pose proof (wr_at_below bgusegs m1 _ _ MI WR ltac:(pose proof Hn8; lia)) as BR. unfold UTOP in BR.
    pose proof (proj1 WR) as R0.
    assert (Hi : (length pre < 4 * n)%nat) by (rewrite length_app in ER; cbn [length] in ER; clear - ER; lia).
    chk ltac:(fun C => clear - C BR R0 Hi Hpre; lia).
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    ld_hd HR2.
    do 2 zstep.
    setreg 12%Z (Z_to_bv 64 (addw x 1)) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE (FCELLS jb) m1 (pre ++ x :: l') T (length pre) (addw x 1) eq_refl I Hi (addw_limb _ _)) as (SOK0 & I2).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI MU WM.
    kb_store SOK0 I2.
    zstep.
    rewrite upd_app_mid in I2.
    pose proof (addw_limb x 1) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K; zify_cond K.
    - setreg 11%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x 1])) + -8)) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      eapply IHl; [exact I2 | apply Hfit'; exact K | | rewrite length_app; cbn [length]; clear; lia].
      rewrite E. cbn [carry_up]. rewrite K. cbn [Z.eqb]. rewrite <- app_assoc. reflexivity.
    - eapply UB_epi; [exact I2|].
      rewrite E. cbn [carry_up]. destruct (Z.eqb_spec (addw x 1) 0) as [E0|_]; [contradiction|]. rewrite <- app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma geom : (8 <= N <= 33554432 /\ 0 <= lo /\ lo <= SP - 160 - SK /\ 160 + L <= SK /\ 80 <= L /\
                0 <= CS8 <= L /\ 0 <= FSC <= L /\ 0 <= FSS <= L /\ 0 <= FSM <= L /\
                Z.of_nat (4 * n + scratch_rec k') <= Z.of_nat nT /\ Z.of_nat da <= 1 /\ Z.of_nat db <= 1 /\
                Z.of_nat (length a) = 2 * N - Z.of_nat da /\ Z.of_nat (length b) = 2 * N - Z.of_nat db)%Z.
  Proof.
    pose proof Hn8. pose proof HnB. pose proof LO. pose proof LO0. pose proof SK_ge. pose proof HL80. pose proof LEAF. pose proof HnT.
    pose proof Hda. pose proof Hdb. pose proof HLA. pose proof HLB. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ubs : (0 < rp /\ rp mod 8 = 0 /\ 0 < ap /\ ap mod 8 = 0 /\ 0 < bp /\ bp mod 8 = 0 /\ 0 < tq /\ tq mod 8 = 0)%Z.
  Proof. pose proof (UBR ltac:(lia)). pose proof (UBA ltac:(lia)). pose proof (UBB ltac:(lia)). pose proof (UBT ltac:(lia)). tauto. Qed.

  Ltac ub_tac BND G :=
    unfold ub_ptr_ok; intros _; let UB := fresh "UB" in pose proof ubs as UB;
    split; [ clear - UB BND G; lia | clear - UB; Z.div_mod_to_equations; lia ].

  (* [comment removed for export] *)
  Lemma UB_fin : forall jb m1 R T c12 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T -> kc3_ok RES n R T c12 -> (-1 <= c12 <= 2)%Z ->
    evt bgusegs POST (ST 0x101a8c m1 x1 x5 x6 x7 (Z_to_bv 64 c12) x10 x11 x12 x13 x14 x15 x16 x17 a3 (Z_to_bv 64 N) a6 x21 x22 x23 x24 x25 x26
                       (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK Hc12.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ n (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    do 3 zstep. rewrite lxor_ones64 by (clear - BND; lia).
    chk ltac:(fun C => clear - C BND G; lia).
    zstep.
    chk ltac:(fun C => clear - C BND G; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    do 3 zstep.
    zstep. rewrite A3. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 4 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply ucall_add_words with (a := slice R n (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -160)%Z)
                                (RP := (rp + 8 * N)%Z) (AP := (rp + 8 * N)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact LRa | exact LTb | rewrite ERa, ETb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa, A3; clear; lia
      | exact HRa | exact HTb | rewrite ERa; exact WRa
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D3 G; lia
      | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LTb ltac:(rewrite ERa, ETb; reflexivity)) as SP3.
    unfold kc3_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R n (2 * n)) (slice T (2 * n) (2 * n))) as [sg3 cy3]. cbn [fst snd] in *.
    destruct SP3 as (Ls3 & Es3 & Hc3 & _). rewrite ERa in Es3. destruct OK as (ERES & Hc & FIT).
    pose proof (KAFTER KB_after_R (FCELLS jb) m1 m2 R T n sg3 _ 80%Z eq_refl I MUc ltac:(rewrite ERa, Es3; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls3 ltac:(rewrite Es3; clear; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa WRa HTb LTb ETb MUc WMc HS I D1 D2 D3.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    zstep. rewrite (bn_swrap32_small (cy3 + 0)), Z.add_0_r by (clear - Hc3; lia).
    zstep. rewrite (bn_swrap32_mod c12 0), Z.add_0_r by (clear - Hc12; lia).
    zstep. setreg 10%Z (Z_to_bv 64 (c12 + cy3)) ltac:(apply Z_to_bv_eqm; clear; change (2 ^ 64)%Z with 18446744073709551616%Z; Z.div_mod_to_equations; lia).
    zstep. rewrite (bn_swrap32_mod c12 cy3) by (clear - Hc12 Hc3; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (c12 + cy3 + 0)), Z.add_0_r by (clear - Hc; lia).
    zstep. if_cases K; zify_cond K.
    { eapply UB_epi; [exact I2|]. rewrite ERES. rewrite K. reflexivity. }
    specialize (FIT K). destruct (Z.eqb_spec (c12 + cy3) 0) as [E0|_]; [contradiction|].
    zstep. rewrite A3.
    zstep. rewrite A3, (bn_swrap32_small (N + 2 * N)) by (clear - G; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (N + 2 * N + 0)), Z.add_0_r by (clear - G; lia).
    zstep. replace ((N + 2 * N) ≪ 3)%Z with (8 * Z.of_nat (n + 2 * n))%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 2 zstep.
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    do 5 zstep.
    setreg 12%Z (Z_to_bv 64 1) ltac:(
      replace (rp + 8 * Z.of_nat (n + 2 * n) <? rp)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      rewrite lxor_signbit by (clear - G; lia);
      replace (N + 2 * N + 9223372036854775808 <? 9223372036854775808)%Z with false by (symmetry; apply Z.ltb_ge; clear - G; lia);
      reflexivity).
    zstep. if_false.
    do 3 zstep.
    rewrite land7 by (pose proof ubs as UB; clear - UB; Z.div_mod_to_equations; lia).
    zstep. if_false.
    (* [comment removed for export] *)
    remember (splice R n sg3) as R' eqn:ER'. pose proof ER as ERl.
    assert (Lpre : length (firstn (n + 2 * n) R') = (n + 2 * n)%nat) by (rewrite length_firstn; clear - ER; lia).
    destruct (skipn (n + 2 * n) R') as [|x l'] eqn:Esk.
    { exfalso. pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. clear - HH ER G. lia. }
    assert (ERpl : R' = firstn (n + 2 * n) R' ++ x :: l') by (rewrite <- Esk; symmetry; apply firstn_skipn).
    remember (firstn (n + 2 * n) R') as pre eqn:Epre.
    rewrite ERpl in I2, HR, LR. clear ERpl.
    pose proof (limbs_cons_lit x l' (proj2 (limbs_app_inv _ _ LR))) as (Hx & Ll').
    setreg 11%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre))) ltac:(rewrite Lpre; reflexivity).
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    ld_hd HR2.
    zstep.
    setreg 10%Z (Z_to_bv 64 (addw x (c12 + cy3))) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE (FCELLS jb) m2 (pre ++ x :: l') T (length pre) (addw x (c12 + cy3)) eq_refl I2 ltac:(rewrite Lpre; clear - G; lia) (addw_limb _ _)) as (SOK0 & I3).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI MU WM I2 MIc STc.
    kb_store SOK0 I3. rewrite upd_app_mid in I3.
    pose proof (addw_limb x (c12 + cy3)) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K2; zify_cond K2.
    - eapply UB_epi; [exact I3|]. rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx).
      destruct (Z.ltb_spec (addw x (c12 + cy3)) x) as [HH|_]; [exfalso; clear - HH K2; lia|]. rewrite <- app_assoc. reflexivity.
    - zstep.
      setreg 11%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x (c12 + cy3)])) + -8)) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      assert (TST : (addw x (c12 + cy3) <? x) = true) by (apply Z.ltb_lt; clear - K2; lia).
      eapply UB_loop; [exact I3 | | | rewrite length_app; cbn [length]; clear; lia].
      + eapply (add_carry_fit x l' (c12 + cy3)); [rewrite BW_lit; exact Hx | exact Ll' | rewrite BW_lit; clear - Hc; lia | | exact TST].
        replace (S (length l')) with n; [exact FIT|].
        pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. rewrite HH, ERl. clear. lia.
      + rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx). rewrite TST. rewrite <- app_assoc. reflexivity.

  Qed.

  (* [comment removed for export] *)
  Lemma UB_sub : forall jb m1 R T c1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T -> kc2_ok RES n true R T c1 -> (0 <= c1 <= 1)%Z ->
    evt bgusegs POST (ST 0x101a58 m1 x1 x5 x6 x7 (Z_to_bv 64 c1) (Z_to_bv 64 (16 * N + tq)) x11 x12 x13 x14 x15 x16 x17 a3 (Z_to_bv 64 N) a6 x21 x22 x23 x24 x25 x26
                       (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    chk ltac:(fun C => clear - C BND G; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    zstep. rewrite A3. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 5 zstep.
    pose proof SEPT as D3.
    eapply ucall_sub_words with (a := slice T 0 (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -160)%Z)
                                (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact LTa | exact LTb | rewrite ETa, ETb; reflexivity
      | rewrite ETa; clear - G; lia | ulit | ulit | ulit | rewrite ETa, A3; clear; lia
      | exact HTa | exact HTb | rewrite ETa; exact WTb
      | unfold alias_ok; rewrite ETa; clear; lia | unfold alias_ok; left; reflexivity
      | clear - G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia
      | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (sub_words_spec _ _ LTa LTb ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (sub_words (slice T 0 (2 * n)) (slice T (2 * n) (2 * n))) as [sg2 bw]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hbw & _). rewrite ETa in Es2.
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T (2 * n)%nat sg2 _ 80%Z eq_refl I MUc ltac:(rewrite ETa, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep. rewrite (bn_swrap32_small (bw + 0)), Z.add_0_r by (clear - Hbw; lia).
    zstep. rewrite (bn_swrap32_small (c1 + 0)), Z.add_0_r by (clear - Hc1; lia).
    zstep.
    zstep. rewrite (bn_swrap32_small (c1 - bw)) by (clear - Hc1 Hbw; lia).
    chk ltac:(fun C => clear - C; lia).
    eapply UB_fin; [exact I2 | exact OK | clear - Hc1 Hbw; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma UB_add : forall jb m1 R T c1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T -> kc2_ok RES n false R T c1 -> (0 <= c1 <= 1)%Z ->
    evt bgusegs POST (ST 0x101a20 m1 x1 x5 x6 x7 (Z_to_bv 64 c1) (Z_to_bv 64 (16 * N + tq)) x11 x12 x13 x14 x15 x16 x17 a3 (Z_to_bv 64 N) a6 x21 x22 x23 x24 x25 x26
                       (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    chk ltac:(fun C => clear - C BND G; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    zstep. rewrite A3. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 5 zstep.
    pose proof SEPT as D3.
    eapply ucall_add_words with (a := slice T (2 * n) (2 * n)) (b := slice T 0 (2 * n)) (lo := lo) (SPz := (SP + -160)%Z)
                                (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat (2 * n))%Z) (BP := (tq + 8 * Z.of_nat 0)%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact LTb | exact LTa | rewrite ETa, ETb; reflexivity
      | rewrite ETb; clear - G; lia | ulit | ulit | ulit | rewrite ETb, A3; clear; lia
      | exact HTb | exact HTa | rewrite ETb; exact WTb
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ETb; clear; lia
      | clear - G; lia | rewrite ETb; clear - D3 G; lia | rewrite ETb; clear - D3 G; lia | rewrite ETb; clear - D3 G; lia
      | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LTb LTa ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (add_words (slice T (2 * n) (2 * n)) (slice T 0 (2 * n))) as [sg2 cy]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hcy & _). rewrite ETb in Es2.
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T (2 * n)%nat sg2 _ 80%Z eq_refl I MUc ltac:(rewrite ETb, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep. rewrite (bn_swrap32_small (cy + 0)), Z.add_0_r by (clear - Hcy; lia).
    zstep. rewrite (bn_swrap32_small (c1 + 0)), Z.add_0_r by (clear - Hc1; lia).
    zstep.
    zstep. rewrite (bn_swrap32_small (c1 + cy)) by (clear - Hc1 Hcy; lia).
    zstep. if_true.
    eapply UB_fin; [exact I2 | exact OK | clear - Hc1 Hcy; lia].

  Qed.

  (* [comment removed for export] *)
  Lemma UB_first : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T -> kc_ok RES n neg R T ->
    evt bgusegs POST (ST 0x101a00 m1 x1 x5 x6 x7 (Z_to_bv 64 (rp + 16 * N)) x10 x11 x12 x13 x14 x15 x16 x17 a3 (Z_to_bv 64 N) a6
                       (Z_to_bv 64 (if neg then 0 else 1)) a0 x23 x24 x25 x26 (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & _).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear; lia)) as (HRb & LRb & ERb & _).
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (_ & _ & _ & WTa).
    do 5 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply ucall_add_words with (a := slice R 0 (2 * n)) (b := slice R (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -160)%Z)
                                (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (rp + 8 * Z.of_nat 0)%Z) (BP := (rp + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact LRa | exact LRb | rewrite ERa, ERb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa, A3; clear; lia
      | exact HRa | exact HRb | rewrite ERa; exact WTa
      | unfold alias_ok; rewrite ERa; clear - D1 G; lia | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D3 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia
      | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LRb ltac:(rewrite ERa, ERb; reflexivity)) as SP1.
    unfold kc_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R 0 (2 * n)) (slice R (2 * n) (2 * n))) as [sg1 cy1]. cbn [fst snd] in *.
    destruct SP1 as (Ls1 & Es1 & Hc1 & _). rewrite ERa in Es1.
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T 0%nat sg1 _ 80%Z eq_refl I MUc ltac:(rewrite ERa, Es1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls1 ltac:(rewrite Es1; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa HRb LRb ERb WTa MUc WMc HS I D1 D2 D3 MIc STc.
    do 2 zstep.
    destruct neg.
    - zstep. if_true. eapply UB_sub; [exact I2 | exact OK | exact Hc1].
    - zstep. if_false. eapply UB_add; [exact I2 | exact OK | exact Hc1].

  Qed.

  Notation a_lo := (firstn n a).
  Notation a_hi := (slice a n (n - da)).
  Notation b_lo := (firstn n b).
  Notation b_hi := (slice b n (n - db)).
  Lemma pow_n : Nat.pow 2 k' = n. Proof. symmetry. exact Hn. Qed.

  (* [comment removed for export] *)
  Lemma UB_gen : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    gen2_ok RES k' n neg a b da db R T ->
    evt bgusegs POST (ST 0x10199c m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 a3 (Z_to_bv 64 N) a6 (Z_to_bv 64 (if neg then 0 else 1)) x22
                       (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) a5 a4 x26 (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HBl.
    assert (Lal : length a_lo = n) by (rewrite length_firstn; clear - G; lia).
    assert (Lbl : length b_lo = n) by (rewrite length_firstn; clear - G; lia).
    do 9 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9. pose proof Hk' as HK.
    eapply call_urec with (L := L) (k := k') (a := a_lo) (b := b_lo) (da := 0%nat) (db := 0%nat) (R := slice R 0 (2 * n)) (T := skipn (4 * n) T)
                         (lo := lo) (SPz := (SP + -160)%Z)
                         (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact IH
      | apply limbs_firstn; exact LA | apply limbs_firstn; exact LB | exact LRa | exact LTp
      | clear - HK; lia | clear; lia | clear; lia
      | rewrite Lal, pow_n; clear; lia | rewrite Lbl, pow_n; clear; lia | rewrite ERa, pow_n; reflexivity
      | rewrite ETp; clear - G; lia
      | ulit | ulit | ulit | rewrite pow_n; ulit | reflexivity | reflexivity | ulit
      | exact HAl | exact HBl | exact HRa | exact HTp | rewrite ERa; exact WRa | rewrite ETp; exact WTp
      | rewrite ERa, Lal; clear - D1 G; lia | rewrite ERa, Lbl; clear - D2 G; lia
      | rewrite ETp, Lal; clear - D3 G; lia | rewrite ETp, Lbl; clear - D4 G; lia
      | rewrite ERa, ETp; clear - D5 G; lia
      | rewrite <- HSK; clear - G; lia
      | rewrite <- HSK, ERa; clear - D6 G; lia | rewrite <- HSK, ETp; clear - D7 G; lia
      | rewrite <- HSK, Lal; clear - D8 G; lia | rewrite <- HSK, Lbl; clear - D9 G; lia
      | ub_tac BND G | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k' a_lo b_lo 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T) (limbs_firstn _ _ LA) (limbs_firstn _ _ LB) LRa LTp
                  ltac:(clear - HK; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(rewrite Lal, pow_n; clear; lia) ltac:(rewrite Lbl, pow_n; clear; lia) ltac:(rewrite ERa, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G; lia)) as MP.
    unfold mul_post in MP. unfold gen2_ok in OK.
    destruct (mul_recursive k' a_lo b_lo 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T)) as [rl p1]. cbn [fst snd] in *.
    destruct MP as (Lrl & Erl & _ & Lp1 & Ep1). rewrite ERa in Erl. rewrite ETp in Ep1.
    pose proof (KAFTER KB_after_RT (FCELLS jb) m1 m2 R T 0%nat rl (4 * n)%nat p1 _ _ (rec_ustack L k') eq_refl I MUc
                  ltac:(rewrite ERa, Erl; reflexivity) ltac:(rewrite ETp, Ep1; reflexivity) ltac:(rewrite <- HSK; clear - G; lia)
                  WMc MIc HSR HST STc Lrl Lp1 ltac:(rewrite Erl; clear; lia) ltac:(rewrite Ep1; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa WRa HTp LTp ETp WTp HAl HBl MUc WMc HSR HST MIc STc I.
    remember (splice R 0 rl) as R1 eqn:ER1. remember (splice T (4 * n) p1) as T1 eqn:ET1. clear ER1 ET1 Lrl Erl Lp1 Ep1.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I2 ltac:(clear; lia)) as (HRb & LRb & ERb & WRb).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I2 ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n (n - da)%nat I2 ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n (n - db)%nat I2 ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = (n - da)%nat) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = (n - db)%nat) by (rewrite slice_length; clear - G; lia).
    zstep.
    chk ltac:(fun C => clear - C BND G; lia).
    zstep.
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    zstep. rewrite A3. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 10 zstep.
    pose proof Hda as HDA. pose proof Hdb as HDB.
    eapply call_urec with (L := L) (k := k') (a := a_hi) (b := b_hi) (da := da) (db := db) (R := slice R1 (2 * n) (2 * n)) (T := skipn (4 * n) T1)
                         (lo := lo) (SPz := (SP + -160)%Z)
                         (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact IH
      | apply slice_limbs; exact LA | apply slice_limbs; exact LB | exact LRb | exact LTp
      | clear - HK; lia | exact HDA | exact HDB
      | rewrite Lah, pow_n; reflexivity | rewrite Lbh, pow_n; reflexivity | rewrite ERb, pow_n; reflexivity
      | rewrite ETp; clear - G; lia
      | ulit | ulit | ulit | rewrite pow_n; ulit | exact A4 | exact A5 | ulit
      | exact HAh | exact HBh | exact HRb | exact HTp | rewrite ERb; exact WRb | rewrite ETp; exact WTp
      | rewrite ERb, Lah; clear - D1 G; lia | rewrite ERb, Lbh; clear - D2 G; lia
      | rewrite ETp, Lah; clear - D3 G; lia | rewrite ETp, Lbh; clear - D4 G; lia
      | rewrite ERb, ETp; clear - D5 G; lia
      | rewrite <- HSK; clear - G; lia
      | rewrite <- HSK, ERb; clear - D6 G; lia | rewrite <- HSK, ETp; clear - D7 G; lia
      | rewrite <- HSK, Lah; clear - D8 G; lia | rewrite <- HSK, Lbh; clear - D9 G; lia
      | ub_tac BND G | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m3 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k' a_hi b_hi da db (slice R1 (2 * n) (2 * n)) (skipn (4 * n) T1) (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB) LRb LTp
                  ltac:(clear - HK; lia) HDA HDB
                  ltac:(rewrite Lah, pow_n; reflexivity) ltac:(rewrite Lbh, pow_n; reflexivity) ltac:(rewrite ERb, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G; lia)) as MP.
    unfold mul_post in MP. unfold gen3_ok in OK.
    destruct (mul_recursive k' a_hi b_hi da db (slice R1 (2 * n) (2 * n)) (skipn (4 * n) T1)) as [rh p2]. cbn [fst snd] in *.
    destruct MP as (Lrh & Erh & _ & Lp2 & Ep2). rewrite ERb in Erh. rewrite ETp in Ep2.
    pose proof (KAFTER KB_after_RT (FCELLS jb) m2 m3 R1 T1 (2 * n)%nat rh (4 * n)%nat p2 _ _ (rec_ustack L k') eq_refl I2 MUc
                  ltac:(rewrite ERb, Erh; reflexivity) ltac:(rewrite ETp, Ep2; reflexivity) ltac:(rewrite <- HSK; clear - G; lia)
                  WMc MIc HSR HST STc Lrh Lp2 ltac:(rewrite Erh; clear; lia) ltac:(rewrite Ep2; clear - G; lia)) as I3.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRb LRb ERb WRb HTp LTp ETp WTp HAh HBh MUc WMc HSR HST MIc STc I2.
    clear D1 D2 D3 D4 D5 D6 D7 D8 D9 HK HDA HDB.
    remember (splice R1 (2 * n) rh) as R2 eqn:ER2. remember (splice T1 (4 * n) p2) as T2 eqn:ET2. clear ER2 ET2 Lrh Erh Lp2 Ep2.
    pose proof I3 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    eapply (UB_first neg); [exact I3 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma UB_comba : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    n = 8%nat -> da = 0%nat -> db = 0%nat ->
    KBK (FCELLS jb) m1 R T ->
    kc_ok RES n neg (splice (splice R 0 (mul_comba8 a_lo b_lo)) (2 * n) (mul_comba8 a_hi b_hi)) T ->
    evt bgusegs POST (ST 0x1018c0 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 a3 (Z_to_bv 64 N) a6 (Z_to_bv 64 (if neg then 0 else 1)) x22
                       x23 x24 x25 x26 (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros En Eda Edb I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat 16%nat I ltac:(clear - En; lia)) as (_ & _ & _ & WRa).
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HBl.
    do 5 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof SEPR as D3. pose proof SEPA as D4. pose proof SEPB as D5.
    assert (Lal : length a_lo = 8%nat) by (rewrite length_firstn; clear - G En; lia).
    assert (Lbl : length b_lo = 8%nat) by (rewrite length_firstn; clear - G En; lia).
    eapply ucall_comba8 with (CS8 := CS8) (a := a_lo) (b := b_lo) (lo := lo) (SPz := (SP + -160)%Z)
                            (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact comba8_ok | apply limbs_firstn; exact LA | apply limbs_firstn; exact LB
      | exact Lal | exact Lbl | ulit | ulit | ulit | exact HAl | exact HBl | exact WRa
      | clear - D1 G En; lia | clear - D2 G En; lia | clear - G; lia
      | clear - D3 G En; lia | clear - D4 G En; lia | clear - D5 G En; lia
      | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (mul_comba8_spec a_lo b_lo (limbs_firstn _ _ LA) (limbs_firstn _ _ LB) Lal Lbl) as (Lc1 & Ec1 & _).
    pose proof (KAFTER KB_after_R (FCELLS jb) m1 m2 R T 0%nat (mul_comba8 a_lo b_lo) _ CS8 eq_refl I MUc ltac:(rewrite Ec1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc1 ltac:(rewrite Ec1; clear - En; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM WRa HAl HBl MUc WMc HS I MIc STc.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat 16%nat I2 ltac:(clear - En; lia)) as (_ & _ & _ & WRb).
    pose proof (KACC KB_a _ _ _ _ n (n - da)%nat I2 ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n (n - db)%nat I2 ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = 8%nat) by (rewrite slice_length; clear - G En Eda; lia).
    assert (Lbh : length b_hi = 8%nat) by (rewrite slice_length; clear - G En Edb; lia).
    zstep.
    chk ltac:(fun C => clear - C BND G; lia).
    zstep.
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    zstep. rewrite A3. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 6 zstep.
    eapply ucall_comba8 with (CS8 := CS8) (a := a_hi) (b := b_hi) (lo := lo) (SPz := (SP + -160)%Z)
                            (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact comba8_ok | apply slice_limbs; exact LA | apply slice_limbs; exact LB
      | exact Lah | exact Lbh | ulit | ulit | ulit | exact HAh | exact HBh | exact WRb
      | clear - D1 G En Eda; lia | clear - D2 G En Edb; lia | clear - G; lia
      | clear - D3 G En; lia | clear - D4 G En Eda; lia | clear - D5 G En Edb; lia
      | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m3 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HS STc.
    destruct (mul_comba8_spec a_hi b_hi (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB) Lah Lbh) as (Lc2 & Ec2 & _).
    pose proof (KAFTER KB_after_R (FCELLS jb) m2 m3 _ T (2 * n)%nat (mul_comba8 a_hi b_hi) _ CS8 eq_refl I2 MUc ltac:(rewrite Ec2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc2 ltac:(rewrite Ec2; clear - En; lia)) as I3.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM WRb HAh HBh MUc WMc HS I2 MIc STc D1 D2 D3 D4 D5.
    pose proof I3 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    zstep.
    eapply (UB_first neg); [exact I3 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma UB_join_gen : forall (zf neg : bool) jb m1 R T x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    (if zf then neg = false /\ gen2_ok RES k' n false a b da db R (splice T (2 * n) (repeat 0%Z (2 * n)))
     else let '(tm, p0) := mul_recursive k' (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) in
          gen2_ok RES k' n neg a b da db R (splice T (2 * n) (tm ++ p0))) ->
    evt bgusegs POST (ST 0x101908 m1 x1 x5 x6 x7 x9 x10 x11 (Z_to_bv 64 (if zf then 0 else 1)) x13 x14 x15 x16 x17 a3 (Z_to_bv 64 N) a6
                       (Z_to_bv 64 (if neg then 0 else 1)) x22 x23 a5 a4 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    zstep.
    zstep. rewrite A3, (bn_swrap32_small (2 * N + 1073741824)) by (clear - G; lia).
    zstep. rewrite lts_signed by (clear - G; lia).
    if_cases C0; [exfalso; zify_cond C0; clear - C0 G; lia | clear C0].
    zstep. rewrite A3. replace ((2 * N) ≪ 1)%Z with (4 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    rewrite (bn_swrap32_small (4 * N)) by (clear - G; lia).
    do 2 zstep.
    setreg 23%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) ltac:(f_equal; rewrite !Z.shiftl_mul_pow2 by lia; clear; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    chk ltac:(fun C => clear - C BND G; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    zstep. rewrite A3. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    destruct zf.
    - (* [comment removed for export] *)
      destruct OK as (Eneg & OK). subst neg.
      destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
      zstep. if_true.
      zstep.
      chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
      chk ltac:(fun C => clear - C BND G; lia).
      chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
      do 4 zstep.
      eapply ucall_memset0 with (L := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -160)%Z) (D := (tq + 8 * Z.of_nat (2 * n))%Z);
        [ exact ESP160 | ret_even | exact ST | exact MI | ulit | reflexivity | rewrite ETr; ulit | exact HTr | rewrite ETr; exact WTr | ].
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      rewrite ETr in HS.
      pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T (2 * n)%nat (repeat 0%Z (2 * n)) _ 0%Z eq_refl I (munch_add_stack_u _ _ _ _ _ MUc)
                    ltac:(rewrite ETr, repeat_length; reflexivity)
                    ltac:(clear - G; lia) WMc MIc HS STc (limbs_repeat _ _ limb_0) ltac:(rewrite repeat_length; clear - G; lia)) as I2.
      eapply (UB_gen false); [exact I2 | exact OK].
    - zstep. if_false.
      zstep.
      chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
      chk ltac:(fun C => clear - C BND G; lia).
      chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
      do 2 zstep.
      chk ltac:(fun C => clear - C BND G; lia).
      do 3 zstep.
      setreg 11%Z (Z_to_bv 64 1) ltac:(
        replace (0 <? tq)%Z with true by (symmetry; apply Z.ltb_lt; pose proof ubs as UB; clear - UB; lia);
        replace (8 * N + tq <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - BND G; lia); reflexivity).
      zstep. if_false.
      destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
      destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
      destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
      destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
      do 6 zstep.
      pose proof SEPT as D7. pose proof Hk' as HK.
      eapply call_urec with (L := L) (k := k') (a := slice T 0 n) (b := slice T n n) (da := 0%nat) (db := 0%nat)
                           (R := slice T (2 * n) (2 * n)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -160)%Z)
                           (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
        [ exact ESP160 | ret_even | exact ST | exact MI | exact IH
        | exact LTa | exact LTb | exact LTr | exact LTp
        | clear - HK; lia | clear; lia | clear; lia
        | rewrite ETa, pow_n; clear; lia | rewrite ETb, pow_n; clear; lia | rewrite ETr, pow_n; reflexivity
        | rewrite ETp; clear - G; lia
        | ulit | ulit | ulit | rewrite pow_n; ulit | reflexivity | reflexivity | ulit
        | exact HTa | exact HTb | exact HTr | exact HTp | rewrite ETr; exact WTr | rewrite ETp; exact WTp
        | rewrite ETr, ETa; clear - G; lia | rewrite ETr, ETb; clear - G; lia
        | rewrite ETp, ETa; clear - G; lia | rewrite ETp, ETb; clear - G; lia
        | rewrite ETr, ETp; clear - G; lia
        | rewrite <- HSK; clear - G; lia
        | rewrite <- HSK, ETr; clear - D7 G; lia | rewrite <- HSK, ETp; clear - D7 G; lia
        | rewrite <- HSK, ETa; clear - D7 G; lia | rewrite <- HSK, ETb; clear - D7 G; lia
        | ub_tac BND G | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
      intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HSR HST STc.
      pose proof (mul_recursive_spec k' (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) LTa LTb LTr LTp
                    ltac:(clear - HK; lia) ltac:(clear; lia) ltac:(clear; lia)
                    ltac:(rewrite ETa, pow_n; clear; lia) ltac:(rewrite ETb, pow_n; clear; lia) ltac:(rewrite ETr, pow_n; reflexivity)
                    ltac:(rewrite ETp; clear - G; lia)) as MP.
      unfold mul_post in MP.
      destruct (mul_recursive k' (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T)) as [tm p0]. cbn [fst snd] in *.
      destruct MP as (Ltm & Etm & _ & Lp0 & Ep0). rewrite ETr in Etm. rewrite ETp in Ep0.
      pose proof (KAFTER KB_after_TT (FCELLS jb) m1 m2 R T (2 * n)%nat (4 * n)%nat tm p0 _ _ (rec_ustack L k') eq_refl I MUc
                    ltac:(rewrite ETr, Etm; reflexivity) ltac:(rewrite ETp, Ep0; reflexivity) ltac:(rewrite Etm; clear; lia)
                    ltac:(rewrite <- HSK; clear - G; lia)
                    WMc MIc HSR HST STc Ltm Lp0 ltac:(rewrite Ep0; clear - G; lia)) as I2.
      zstep.
      eapply (UB_gen neg); [exact I2 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma UB_join : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    join_ok RES k' n neg a b da db R T ->
    evt bgusegs POST (ST 0x101874 m1 x1 x5 x6 x7 x9 x10 x11 (Z_to_bv 64 1) x13 x14 x15 x16 x17 a3 (Z_to_bv 64 N) a6
                       (Z_to_bv 64 (if neg then 0 else 1)) (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) x23 a5 a4 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 3 zstep. rewrite A3, land_even31 by (clear - G; lia).
    zstep.
    zstep. if_cases K1; zify_cond K1.
    { eapply (UB_join_gen false neg); [exact I|]. unfold join_ok in OK.
      destruct (Nat.eqb_spec n 8) as [E8|_]; [exfalso; clear - E8 K1; lia|]. exact OK. }
    zstep. if_cases K2; zify_cond K2.
    { eapply (UB_join_gen false neg); [exact I|]. unfold join_ok in OK.
      destruct (Nat.eqb_spec da 0) as [Ea|_]; [destruct (Nat.eqb_spec db 0) as [Eb|_]|]; rewrite ?andb_false_r in OK; cbn [andb] in OK; try exact OK.
      exfalso. apply K2. rewrite A4, A5. apply lor_neg_zero; [exact Hda | exact Hdb | split; assumption]. }
    assert (En : n = 8%nat) by (clear - K1; lia).
    assert (Ed : (da = 0 /\ db = 0)%nat) by (rewrite A4, A5 in K2; apply lor_neg_zero in K2; [exact K2 | exact Hda | exact Hdb]).
    destruct Ed as (Eda & Edb).
    unfold join_ok in OK. rewrite (proj2 (Nat.eqb_eq n 8) En), (proj2 (Nat.eqb_eq da 0) Eda), (proj2 (Nat.eqb_eq db 0) Edb) in OK. cbn [andb] in OK.
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat 16%nat I ltac:(clear - G En; lia)) as (_ & _ & _ & WTr).
    zstep. rewrite A3. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    zstep.
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    chk ltac:(fun C => clear - C BND G; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    do 2 zstep. rewrite lxor_ones64 by (clear - BND; lia).
    chk ltac:(fun C => clear - C BND G; lia).
    do 4 zstep.
    pose proof SEPT as D7.
    eapply ucall_comba8 with (CS8 := CS8) (a := slice T 0 n) (b := slice T n n) (lo := lo) (SPz := (SP + -160)%Z)
                             (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * N)%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact comba8_ok | exact LTa | exact LTb
      | rewrite ETa; exact En | rewrite ETb; exact En | ulit | ulit | ulit | exact HTa | exact HTb | exact WTr
      | clear - G En; lia | clear - G En; lia | clear - G; lia
      | clear - D7 G En; lia | clear - D7 G En; lia | clear - D7 G En; lia
      | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (mul_comba8_spec (slice T 0 n) (slice T n n) LTa LTb ltac:(rewrite ETa; exact En) ltac:(rewrite ETb; exact En)) as (Lc & Ec & _).
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T (2 * n)%nat _ _ CS8 eq_refl I MUc ltac:(rewrite Ec; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc ltac:(rewrite Ec; clear - G En; lia)) as I2.
    eapply (UB_comba neg); [exact En | exact Eda | exact Edb | exact I2 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma UB_zero : forall jb m1 R T x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    zero_ok RES k' n a b da db R T ->
    evt bgusegs POST (ST 0x1016a8 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 a3 (Z_to_bv 64 N) a6
                       x21 (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) x23 a5 a4 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 4 zstep. rewrite A3, land_even31 by (clear - G; lia).
    do 2 zstep.
    zstep. if_cases K1; zify_cond K1.
    { eapply (UB_join_gen true false); [exact I|]. split; [reflexivity|]. unfold zero_ok in OK.
      destruct (Nat.eqb_spec n 8) as [E8|_]; [exfalso; clear - E8 K1; lia|]. exact OK. }
    zstep. if_cases K2; zify_cond K2.
    { eapply (UB_join_gen true false); [exact I|]. split; [reflexivity|]. unfold zero_ok in OK.
      destruct (Nat.eqb_spec da 0) as [Ea|_]; [destruct (Nat.eqb_spec db 0) as [Eb|_]|]; rewrite ?andb_false_r in OK; cbn [andb] in OK; try exact OK.
      exfalso. apply K2. rewrite A4, A5. apply lor_neg_zero; [exact Hda | exact Hdb | split; assumption]. }
    assert (En : n = 8%nat) by (clear - K1; lia).
    assert (Ed : (da = 0 /\ db = 0)%nat) by (rewrite A4, A5 in K2; apply lor_neg_zero in K2; [exact K2 | exact Hda | exact Hdb]).
    destruct Ed as (Eda & Edb).
    unfold zero_ok in OK. rewrite (proj2 (Nat.eqb_eq n 8) En), (proj2 (Nat.eqb_eq da 0) Eda), (proj2 (Nat.eqb_eq db 0) Edb) in OK. cbn [andb] in OK.
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
    zstep. rewrite A3. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    zstep.
    chk ltac:(fun C => clear - C BND G; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    zstep. rewrite A3. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 5 zstep.
    eapply ucall_memset0 with (L := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -160)%Z) (D := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | ulit | reflexivity | rewrite ETr, En; reflexivity | exact HTr | rewrite ETr; exact WTr | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    rewrite ETr in HS.
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T (2 * n)%nat (repeat 0%Z (2 * n)) _ 0%Z eq_refl I (munch_add_stack_u _ _ _ _ _ MUc)
                  ltac:(rewrite ETr, repeat_length; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc (limbs_repeat _ _ limb_0) ltac:(rewrite repeat_length; clear - G; lia)) as I2.
    do 2 zstep.
    unfold comba_ok in OK.
    eapply (UB_comba false); [exact En | exact Eda | exact Edb | exact I2 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Notation t0_of sw := (fst (if sw then sub_part_words a_hi a_lo (n - da) else sub_part_words a_lo a_hi (n - da))).
  Notation t1_of sw := (fst (if sw then sub_part_words b_hi b_lo (n - db) else sub_part_words b_lo b_hi (n - db))).

  Ltac usp1_call I G BND sw :=
    let HAl := fresh "HAl" in let HAh := fresh "HAh" in let WTn := fresh "WTn" in
    let D3 := fresh "D3" in let D7 := fresh "D7" in let D8 := fresh "D8" in
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl;
    pose proof (KACC KB_a _ _ _ _ n (n - da)%nat I ltac:(clear - G; lia)) as HAh;
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (_ & _ & _ & WTn);
    pose proof DTA as D3; pose proof SEPT as D7; pose proof SEPA as D8;
    lazymatch goal with ST : stk bgusegs ?m1 lo _, MI : mem_inv bgusegs ?m1 |- _ =>
    lazymatch sw with
    | false =>
      eapply ucall_sub_part_words with (FS := FSS) (a := a_lo) (b := a_hi) (cl := (n - da)%nat) (da := da) (db := 0%nat) (lo := lo) (SPz := (SP + -160)%Z)
                                      (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
        [ exact ESP160 | ret_even | exact ST | exact MI | exact sub_part_ok | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
        | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | f_equal; clear; lia
        | exact HAl | exact HAh | replace (n - da + da + 0)%nat with n by (clear - G; lia); exact WTn
        | rewrite length_firstn; clear - D3 G; lia | rewrite slice_length by (clear - G; lia); clear - D3 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite length_firstn; clear - D8 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia
        | ub_tac BND G | ub_tac BND G | ub_tac BND G | ]
    | true =>
      eapply ucall_sub_part_words with (FS := FSS) (a := a_hi) (b := a_lo) (cl := (n - da)%nat) (da := 0%nat) (db := da) (lo := lo) (SPz := (SP + -160)%Z)
                                      (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * N)%Z) (BP := (ap + 8 * Z.of_nat 0)%Z);
        [ exact ESP160 | ret_even | exact ST | exact MI | exact sub_part_ok | apply slice_limbs; exact LA | apply limbs_firstn; exact LA
        | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | f_equal; clear; lia
        | exact HAh | exact HAl | replace (n - da + 0 + da)%nat with n by (clear - G; lia); exact WTn
        | rewrite slice_length by (clear - G; lia); clear - D3 G; lia | rewrite length_firstn; clear - D3 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia | rewrite length_firstn; clear - D8 G; lia
        | ub_tac BND G | ub_tac BND G | ub_tac BND G | ]
    end end.

  Ltac usp2_call I G BND sw :=
    let HBl := fresh "HBl" in let HBh := fresh "HBh" in let WTn := fresh "WTn" in
    let D4 := fresh "D4" in let D7 := fresh "D7" in let D9 := fresh "D9" in
    pose proof (KACC KB_b _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HBl;
    pose proof (KACC KB_b _ _ _ _ n (n - db)%nat I ltac:(clear - G; lia)) as HBh;
    destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (_ & _ & _ & WTn);
    pose proof DTB as D4; pose proof SEPT as D7; pose proof SEPB as D9;
    lazymatch goal with ST : stk bgusegs ?m1 lo _, MI : mem_inv bgusegs ?m1 |- _ =>
    lazymatch sw with
    | false =>
      eapply ucall_sub_part_words with (FS := FSS) (a := b_lo) (b := b_hi) (cl := (n - db)%nat) (da := db) (db := 0%nat) (lo := lo) (SPz := (SP + -160)%Z)
                                      (RP := (tq + 8 * N)%Z) (AP := (bp + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * N)%Z);
        [ exact ESP160 | ret_even | exact ST | exact MI | exact sub_part_ok | apply limbs_firstn; exact LB | apply slice_limbs; exact LB
        | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | f_equal; clear; lia
        | exact HBl | exact HBh | replace (n - db + db + 0)%nat with n by (clear - G; lia); exact WTn
        | rewrite length_firstn; clear - D4 G; lia | rewrite slice_length by (clear - G; lia); clear - D4 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite length_firstn; clear - D9 G; lia | rewrite slice_length by (clear - G; lia); clear - D9 G; lia
        | ub_tac BND G | ub_tac BND G | ub_tac BND G | ]
    | true =>
      eapply ucall_sub_part_words with (FS := FSS) (a := b_hi) (b := b_lo) (cl := (n - db)%nat) (da := 0%nat) (db := db) (lo := lo) (SPz := (SP + -160)%Z)
                                      (RP := (tq + 8 * N)%Z) (AP := (bp + 8 * N)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
        [ exact ESP160 | ret_even | exact ST | exact MI | exact sub_part_ok | apply slice_limbs; exact LB | apply limbs_firstn; exact LB
        | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | rewrite A5; f_equal; clear; lia
        | exact HBh | exact HBl | replace (n - db + 0 + db)%nat with n by (clear - G; lia); exact WTn
        | rewrite slice_length by (clear - G; lia); clear - D4 G; lia | rewrite length_firstn; clear - D4 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | rewrite length_firstn; clear - D9 G; lia
        | ub_tac BND G | ub_tac BND G | ub_tac BND G | ]
    end end.

  (* [comment removed for export] *)
  Notation STC pc mm x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 :=
    (ST pc mm x1 x5 x6 x7 (Z_to_bv 64 (Z.of_nat da)) x10 x11 x12 a1 x14 x15 x16 x17 a3 (Z_to_bv 64 N) a6 x21
        (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (N - Z.of_nat da)) a5 a4 a5 (Z_to_bv 64 (N - Z.of_nat db)) x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma UB_case_p2 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    join_ok RES k' n true a b da db R (splice (splice T 0 (t0_of false)) n (t1_of false)) ->
    evt bgusegs POST (STC 0x1016fc m1 x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 6 zstep. usp1_call I G BND false.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_lo a_hi (n - da) (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA)
                ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T 0%nat _ _ FSS eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 3 zstep.
    chk ltac:(fun C => clear - C BND G; lia).
    do 3 zstep.
    setreg 12%Z (Z_to_bv 64 1) ltac:(
      replace (0 <? tq)%Z with true by (symmetry; apply Z.ltb_lt; pose proof ubs as UB; clear - UB; lia);
      replace (tq + 8 * N <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - BND G; lia); reflexivity).
    zstep. if_false.
    do 2 zstep. rewrite (bn_swrap32_small (N - (N - Z.of_nat db))) by (clear - G; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (N - (N - Z.of_nat db) + 0)) by (clear - G; lia).
    do 3 zstep. usp2_call I2 G BND false.
    intros m3 u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HS STc.
    destruct (sub_part_words_fst b_lo b_hi (n - db) (limbs_firstn _ _ LB) (slice_limbs _ _ _ LB)
                ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
    rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb) m2 m3 R _ n _ _ FSS eq_refl I2 MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I3.
    do 4 zstep.
    eapply (UB_join true); [exact I3 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma UB_case_m4 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    join_ok RES k' n false a b da db R (splice (splice T 0 (t0_of true)) n (t1_of false)) ->
    evt bgusegs POST (STC 0x101758 m1 x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 2 zstep. rewrite (bn_swrap32_small (N - Z.of_nat da - N)) by (clear - G; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_mod (N - Z.of_nat da - N) 0), Z.add_0_r by (clear - G; lia).
    do 5 zstep. usp1_call I G BND true.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_hi a_lo (n - da) (slice_limbs _ _ _ LA) (limbs_firstn _ _ LA)
                ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T 0%nat _ _ FSS eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 3 zstep.
    chk ltac:(fun C => clear - C BND G; lia).
    do 3 zstep.
    setreg 12%Z (Z_to_bv 64 1) ltac:(
      replace (0 <? tq)%Z with true by (symmetry; apply Z.ltb_lt; pose proof ubs as UB; clear - UB; lia);
      replace (tq + 8 * N <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - BND G; lia); reflexivity).
    zstep. if_false.
    do 2 zstep. rewrite (bn_swrap32_small (N - (N - Z.of_nat db))) by (clear - G; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (N - (N - Z.of_nat db) + 0)) by (clear - G; lia).
    do 3 zstep. usp2_call I2 G BND false.
    intros m3 u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HS STc.
    destruct (sub_part_words_fst b_lo b_hi (n - db) (limbs_firstn _ _ LB) (slice_limbs _ _ _ LB)
                ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
    rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb) m2 m3 R _ n _ _ FSS eq_refl I2 MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I3.
    do 3 zstep.
    eapply (UB_join false); [exact I3 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma UB_case_m2 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    join_ok RES k' n true a b da db R (splice (splice T 0 (t0_of true)) n (t1_of true)) ->
    evt bgusegs POST (STC 0x1017c4 m1 x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 2 zstep. rewrite (bn_swrap32_small (N - Z.of_nat da - N)) by (clear - G; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_mod (N - Z.of_nat da - N) 0), Z.add_0_r by (clear - G; lia).
    do 5 zstep. usp1_call I G BND true.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_hi a_lo (n - da) (slice_limbs _ _ _ LA) (limbs_firstn _ _ LA)
                ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T 0%nat _ _ FSS eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 3 zstep.
    chk ltac:(fun C => clear - C BND G; lia).
    do 3 zstep.
    setreg 11%Z (Z_to_bv 64 1) ltac:(
      replace (0 <? tq)%Z with true by (symmetry; apply Z.ltb_lt; pose proof ubs as UB; clear - UB; lia);
      replace (8 * N + tq <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - BND G; lia); reflexivity).
    zstep. if_false.
    do 4 zstep. usp2_call I2 G BND true.
    intros m3 u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HS STc.
    destruct (sub_part_words_fst b_hi b_lo (n - db) (slice_limbs _ _ _ LB) (limbs_firstn _ _ LB)
                ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
    rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb) m2 m3 R _ n _ _ FSS eq_refl I2 MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I3.
    do 3 zstep.
    eapply (UB_join true); [exact I3 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma UB_case_p4 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31,
    KBK (FCELLS jb) m1 R T ->
    join_ok RES k' n false a b da db R (splice (splice T 0 (t0_of false)) n (t1_of true)) ->
    evt bgusegs POST (STC 0x101824 m1 x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 6 zstep. usp1_call I G BND false.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_lo a_hi (n - da) (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA)
                ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb) m1 m2 R T 0%nat _ _ FSS eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 3 zstep.
    chk ltac:(fun C => clear - C BND G; lia).
    do 3 zstep.
    setreg 11%Z (Z_to_bv 64 1) ltac:(
      replace (0 <? tq)%Z with true by (symmetry; apply Z.ltb_lt; pose proof ubs as UB; clear - UB; lia);
      replace (8 * N + tq <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - BND G; lia); reflexivity).
    zstep. if_false.
    do 4 zstep. usp2_call I2 G BND true.
    intros m3 u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HS STc.
    destruct (sub_part_words_fst b_hi b_lo (n - db) (slice_limbs _ _ _ LB) (limbs_firstn _ _ LB)
                ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
    rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb) m2 m3 R _ n _ _ FSS eq_refl I2 MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I3.
    do 2 zstep.
    eapply (UB_join false); [exact I3 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Ltac litreg r :=
    let v := reg_val r in let z := eval vm_compute in (bv_unsigned v) in
    replace v with (Z_to_bv 64 z) by (apply bv_eq; vm_compute; reflexivity).

  (* [comment removed for export] *)
  Ltac sw_steps :=
    zstep; litreg 12%Z; zstep; litreg 11%Z; zstep; litreg 12%Z;
    zstep; if_false;
    zstep; litreg 12%Z; zstep; litreg 11%Z; zstep; litreg 10%Z;
    zstep; if_false;
    zstep; litreg 10%Z; zstep; zstep; litreg 10%Z; do 2 zstep;
    zstep; if_false;
    zstep; litreg 10%Z; do 6 zstep.

  (* [comment removed for export] *)
  Notation FCELLS0 jb48 := [CB 48 jb48; C8 a0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma UB_body : forall jb48 m1 R T x1 x5 x6 x7 x9 x11 x12 x13 x14 x17 x21 x26 x28 x29 x30 x31,
    KBK (FCELLS0 jb48) m1 R T ->
    match rec_diffs a_lo a_hi b_lo b_hi (n - da) (n - db) (cmp_part_words a_lo a_hi (n - da)) (cmp_part_words b_hi b_lo (n - db)) with
    | Some (t0', t1', neg) => join_ok RES k' n neg a b da db R (splice (splice T 0 t0') n t1')
    | None => zero_ok RES k' n a b da db R T
    end ->
    evt bgusegs POST (ST 0x1015b4 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 15) x11 x12 x13 x14 a2 a1 x17 a3 (Z_to_bv 64 N) a6 x21
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (N - Z.of_nat da)) a5 a4 x26
                       (Z_to_bv 64 (N - Z.of_nat db)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BNDab.
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    pose proof (munch_refl [(SP + -160, SP + -160 + 160)]%Z m1) as MUF. pose proof (wmono_refl bgusegs m1) as WMF.
    zstep. replace (N ≪ 3)%Z with (8 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 3 zstep.
    chk ltac:(fun C => clear - C BNDab G; lia).
    do 4 zstep.
    setreg 10%Z (Z_to_bv 64 1) ltac:(
      replace (0 <? ap)%Z with true by (symmetry; apply Z.ltb_lt; pose proof ubs as UB; clear - UB; lia);
      replace (ap + 8 * N <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - BND G; lia); reflexivity).
    zstep. if_false.
    do 2 zstep. rewrite (bn_swrap32_small (N - (N - Z.of_nat da))) by (clear - G; lia).
    chk ltac:(fun C => clear - C; lia).
    do 7 zstep.
    pose proof (KFRAME _ _ m1 _ R T I MUF WMF MI STK FR) as I2.
    clear I MUF WMF. clear m1.
    pose proof (KACC KB_a _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_a _ _ _ _ n (n - da)%nat I2 ltac:(clear - G; lia)) as HAh.
    pose proof SEPA as D8.
    eapply ucall_cmp_part_words with (FS := FSC) (a := a_lo) (b := a_hi) (cl := (n - da)%nat) (da := da) (db := 0%nat) (lo := lo) (SPz := (SP + -160)%Z)
                                    (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
      [ exact ESP160 | ret_even | exact STK | exact MI | exact cmp_part_ok | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
      | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
      | clear - G; lia | ulit | ulit | ulit | f_equal; clear; lia
      | exact HAl | exact HAh | clear - G; lia
      | rewrite length_firstn; clear - D8 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia
      | ub_tac BND G | ub_tac BND G | ].
    intros m3 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc STc.
    lazymatch type of I2 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_ro cells mm m3 R T FSC eq_refl I2 MUc ltac:(clear - G; lia) WMc MIc STc) as I3 end.
    clear FR STK MI HAl HAh D8 MUc WMc MIc STc I2.
    pose proof I3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    lazymatch type of MI with mem_inv _ ?mm => pose proof (munch_refl [(SP + -160, SP + -160 + 160)]%Z mm) as MUF; pose proof (wmono_refl bgusegs mm) as WMF end.
    remember (cmp_part_words a_lo a_hi (n - da)) as c1 eqn:Ec1.
    do 4 zstep.
    chk ltac:(fun C => clear - C BNDab G; lia).
    do 5 zstep.
    setreg 10%Z (Z_to_bv 64 1) ltac:(
      replace (0 <? bp)%Z with true by (symmetry; apply Z.ltb_lt; pose proof ubs as UB; clear - UB; lia);
      replace (bp + 8 * N <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - BND G; lia); reflexivity).
    zstep. if_false.
    do 2 zstep. rewrite (bn_swrap32_small (N - Z.of_nat db - N)) by (clear - G; lia).
    chk ltac:(fun C => clear - C; lia).
    do 5 zstep.
    lazymatch type of I3 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ _ =>
      lazymatch type of MI with mem_inv _ ?mm' => pose proof (KFRAME _ _ mm mm' R T I3 MUF WMF MI STK FR) as I4 end end.
    clear I3 MUF WMF.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I4 ltac:(clear - G; lia)) as HBl.
    pose proof (KACC KB_b _ _ _ _ n (n - db)%nat I4 ltac:(clear - G; lia)) as HBh.
    pose proof SEPB as D9.
    eapply ucall_cmp_part_words with (FS := FSC) (a := b_hi) (b := b_lo) (cl := (n - db)%nat) (da := 0%nat) (db := db) (lo := lo) (SPz := (SP + -160)%Z)
                                    (AP := (bp + 8 * N)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
      [ exact ESP160 | ret_even | exact STK | exact MI | exact cmp_part_ok | apply slice_limbs; exact LB | apply limbs_firstn; exact LB
      | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
      | clear - G; lia | ulit | ulit | ulit | f_equal; clear; lia
      | exact HBh | exact HBl | clear - G; lia
      | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | rewrite length_firstn; clear - D9 G; lia
      | ub_tac BND G | ub_tac BND G | ].
    intros m5 u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc STc.
    lazymatch type of I4 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_ro cells mm m5 R T FSC eq_refl I4 MUc ltac:(clear - G; lia) WMc MIc STc) as I5 end.
    clear FR STK MI HBl HBh D9 MUc WMc MIc STc I4.
    pose proof I5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    remember (cmp_part_words b_hi b_lo (n - db)) as c2 eqn:Ec2.
    setreg 26%Z a5 ltac:(rewrite A5; f_equal; clear; lia).
    setreg 9%Z (Z_to_bv 64 (Z.of_nat da)) ltac:(f_equal; clear; lia).
    zstep.
    assert (Hc1 : (c1 = -1 \/ c1 = 0 \/ c1 = 1)%Z).
    { rewrite Ec1, (cmp_part_words_spec a_lo a_hi (n - da) (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA))
        by (right; rewrite slice_length, length_firstn; clear - G; lia). apply sgn3_range. }
    assert (Hc2 : (c2 = -1 \/ c2 = 0 \/ c2 = 1)%Z).
    { rewrite Ec2, (cmp_part_words_spec b_hi b_lo (n - db) (slice_limbs _ _ _ LB) (limbs_firstn _ _ LB))
        by (left; rewrite slice_length, length_firstn; clear - G; lia). apply sgn3_range. }
    clear Ec1 Ec2.
    destruct Hc1 as [E1|[E1|E1]]; destruct Hc2 as [E2|[E2|E2]]; rewrite E1, E2 in *; clear E1 E2 c1 c2.
    - sw_steps. rewrite rec_diffs_m1_m1 in OK. eapply UB_case_m4; [exact I5 | exact OK].
    - sw_steps. rewrite rec_diffs_m1_0 in OK. eapply UB_zero; [exact I5 | exact OK].
    - sw_steps. rewrite rec_diffs_m1_p1 in OK. eapply UB_case_m2; [exact I5 | exact OK].
    - sw_steps. rewrite rec_diffs_0_m1 in OK. eapply UB_zero; [exact I5 | exact OK].
    - sw_steps. rewrite rec_diffs_0_0 in OK. eapply UB_zero; [exact I5 | exact OK].
    - sw_steps. rewrite rec_diffs_0_p1 in OK. eapply UB_zero; [exact I5 | exact OK].
    - sw_steps. rewrite rec_diffs_p1_m1 in OK. eapply UB_case_p2; [exact I5 | exact OK].
    - sw_steps. rewrite rec_diffs_p1_0 in OK. eapply UB_zero; [exact I5 | exact OK].
    - sw_steps. rewrite rec_diffs_p1_p1 in OK. eapply UB_case_p4; [exact I5 | exact OK].
  Qed.
End KaraU.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac wnorm :=
  rewrite ?Z_to_bv_unsigned, ?Z.shiftl_mul_pow2 by lia; change (2 ^ 1)%Z with 2%Z; change (2 ^ 3)%Z with 8%Z;
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z; change (2 ^ Z.of_N 32)%Z with 4294967296%Z;
  change (4294967296 `div` 2)%Z with 2147483648%Z; change (2 ^ 64)%Z with 18446744073709551616%Z;
  Z.div_mod_to_equations; lia.

Section MainU.
  Variables (L CS8 FSC FSS FSM : Z).
  Hypothesis LEAF : (0 <= CS8 <= L /\ 0 <= FSC <= L /\ 0 <= FSS <= L /\ 0 <= FSM <= L)%Z.
  Hypothesis L80 : (80 <= L)%Z.
  Hypothesis comba8_ok : comba8_uspec CS8.
  Hypothesis cmp_part_ok : cmp_part_words_uspec FSC.
  Hypothesis sub_part_ok : sub_part_words_uspec FSS.
  Hypothesis mul_normal_ok : mul_normal_uspec FSM.

  Lemma urec_body : forall k, (forall k', k = S k' -> rec_uspec_at L k') -> rec_uspec_at L k.
  Proof.
    intros k IHk. unfold rec_uspec_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a b da db R T lo
           LA LB LR LT Hk Hda Hdb HLA HLB HLR HLT A3 A4 A5 RA RB RR RT WR WT DRA DRB DTA DTB DRT STK LO SEPR SEPT SEPA SEPB MI0 UBR UBA UBB UBT.
    remember (Nat.pow 2 k) as N2 eqn:EN2.
    assert (HN2 : (2 <= Z.of_nat N2 <= 67108864)%Z) by (subst N2; apply pow2_Z_bounds; exact Hk).
    remember (rec_ustack L k - 160)%Z as SK eqn:ESK.
    assert (HSK : (160 + L <= SK)%Z) by (subst SK; unfold rec_ustack; lia).
    assert (ERS : rec_ustack L k = (160 + SK)%Z) by (subst SK; lia).
    rewrite ERS in LO, SEPR, SEPT, SEPA, SEPB |- *.
    pose proof (proj1 STK) as LO0.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA. pose proof (limbs_at_bound _ _ _ _ RB) as BB.
    pose proof (wr_at_below bgusegs m _ _ MI0 WR ltac:(rewrite HLR; lia)) as BR. pose proof (wr_at_below bgusegs m _ _ MI0 WT) as BT.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *. unfold UTOP in *.
    (* [comment removed for export] *)
    assert (GEO : hide ((bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0) /\
                        (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a0) /\
                        (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a6) /\
                        (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a6) /\
                        (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a6 \/ bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a0) /\
                        (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned sp - (160 + SK) \/ bv_unsigned sp <= bv_unsigned a0) /\
                        (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned sp - (160 + SK) \/ bv_unsigned sp <= bv_unsigned a6) /\
                        (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - (160 + SK) \/ bv_unsigned sp <= bv_unsigned a1) /\
                        (bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned sp - (160 + SK) \/ bv_unsigned sp <= bv_unsigned a2) /\
                        length a = (N2 - da)%nat /\ length b = (N2 - db)%nat /\ length R = (2 * N2)%nat /\ (scratch_rec k <= length T)%nat)%Z).
    { apply hide_intro. repeat split; assumption. }
    rewrite HLR in WR.
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB HLA HLB HLR HLT.
    pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length R)); (bv_unsigned a6, bv_unsigned a6 + 8 * Z.of_nat (length T));
                            (bv_unsigned sp - (160 + SK), bv_unsigned sp)]%Z m) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)]%Z m) as MUF. pose proof (wmono_refl bgusegs m) as WM.
    assert (HSK0 : (0 <= SK)%Z) by (clear - HSK L80; lia).
    assert (LO1 : (lo <= bv_unsigned sp - 160)%Z) by (clear - LO HSK0; lia).
    destruct k as [|k']; [exfalso; clear - Hk; lia|].
    remember (Nat.pow 2 k') as n eqn:En.
    assert (EN : N2 = (2 * n)%nat) by (rewrite EN2, En; cbn [Nat.pow]; clear; lia).
    assert (A3' : bv_unsigned a3 = (2 * Z.of_nat n)%Z) by (rewrite A3, EN; clear; lia).
    assert (HN : (1 <= Z.of_nat n <= 33554432)%Z) by (clear - HN2 EN; lia).
    carve_frame 160%nat STK.
    do 20 zstep. rewrite A3', half_n2 by (clear - HN; lia).
    do 2 zstep.
    setreg 23%Z (Z_to_bv 64 (Z.of_nat n - Z.of_nat da)) ltac:(rewrite A4; f_equal; symmetry; apply addw_dn; [exact Hda | clear - HN; lia]).
    setreg 11%Z (Z_to_bv 64 (Z.of_nat n - Z.of_nat da)) ltac:(rewrite A4; apply Z_to_bv_eqm; clear - Hda; wnorm).
    zstep.
    chk ltac:(fun C => clear - C; lia).
    do 3 zstep.
    setreg 27%Z (Z_to_bv 64 (Z.of_nat n - Z.of_nat db)) ltac:(rewrite A5; f_equal; symmetry; apply addw_dn; [exact Hdb | clear - HN; lia]).
    setreg 10%Z (Z_to_bv 64 (Z.of_nat n - Z.of_nat db)) ltac:(rewrite A5; apply Z_to_bv_eqm; clear - Hdb; wnorm).
    chk ltac:(fun C => clear - C; lia).
    do 5 zstep.
    (* [comment removed for export] *)
    pose proof (hide_elim _ GEO) as (DRA & DRB & DTA & DTB & DRT & SEPR & SEPT & SEPA & SEPB & HLA' & HLB' & HLR' & HLT').
    assert (RA1 : limbs_at bgusegs m1 (bv_unsigned a1) a) by (eapply limbs_at_transport; [exact RA | exact MUF | cbn [disjoint_from]; clear - SEPA HSK0; lia]).
    assert (RB1 : limbs_at bgusegs m1 (bv_unsigned a2) b) by (eapply limbs_at_transport; [exact RB | exact MUF | cbn [disjoint_from]; clear - SEPB HSK0; lia]).
    assert (RR1 : limbs_at bgusegs m1 (bv_unsigned a0) R) by (eapply limbs_at_transport; [exact RR | exact MUF | cbn [disjoint_from]; clear - SEPR HSK0; lia]).
    assert (RT1 : limbs_at bgusegs m1 (bv_unsigned a6) T) by (eapply limbs_at_transport; [exact RT | exact MUF | cbn [disjoint_from]; clear - SEPT HSK0; lia]).
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB HLA' HLB' HLR' HLT' MUF RA RB RR RT.
    eassert (CONT : ~ (N2 = 8 /\ da = 0 /\ db = 0)%nat -> _); cycle 1.
    { zstep. if_cases K8; zify_cond K8.
      { apply CONT. intros (E & _). clear - E K8 A3. lia. }
      zstep. if_cases K0; zify_cond K0.
      { apply CONT. intros (_ & Ea & Eb). apply K0. rewrite A4, A5. apply lor_neg_zero; [exact Hda | exact Hdb | split; assumption]. }
      (* [comment removed for export] *)
      assert (E8 : N2 = 8%nat) by (clear - K8 A3; lia).
      assert (Ed : (da = 0 /\ db = 0)%nat) by (rewrite A4, A5 in K0; apply lor_neg_zero in K0; [exact K0 | exact Hda | exact Hdb]).
      destruct Ed as (Eda & Edb). subst da db.
      do 18 zstep.
      release_frame FR STK (bv_unsigned sp).
      pose proof (hide_elim _ GEO) as (DRA & DRB & DTA & DTB & DRT & SEPR & SEPT & SEPA & SEPB & HLA' & HLB' & HLR' & HLT').
      assert (La8 : length a = 8%nat) by (clear - HLA' E8; lia). assert (Lb8 : length b = 8%nat) by (clear - HLB' E8; lia).
      assert (LR16 : length R = 16%nat) by (clear - HLR' E8; lia).
      eapply evt_mono.
      { eapply comba8_ok with (a := a) (b := b) (lo := lo);
          [ exact LA | exact LB | exact La8 | exact Lb8 | exact RA1 | exact RB1 | rewrite E8 in WR; exact WR
          | clear - DRA LR16 La8; lia | clear - DRB LR16 Lb8; lia | exact STK | clear - LO HSK LEAF; lia
          | clear - SEPR LR16 HSK LEAF; lia | clear - SEPA La8 HSK LEAF; lia | clear - SEPB Lb8 HSK LEAF; lia | exact MI0
          | exact UBR | exact UBA | exact UBB ]. }
      intros ms' PO. unfold vl_post in PO.
      destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
      exists u0, u1, u2, v0, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m2.
      split; [exact E|].
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx.
               clear - Hx LR16 HSK LEAF. lia. }
      split; [eapply wmono_trans; [exact WM | exact WMc]|]. split; [exact MIc|].
      rewrite mul_recursive_comba by (rewrite <- EN2; exact E8). cbn [fst snd].
      destruct (mul_comba8_spec a b LA LB La8 Lb8) as (_ & Lc & _).
      rewrite !firstn_all2 by (clear - La8 Lb8; lia). rewrite splice_all by (rewrite Lc, LR16; reflexivity).
      split; [exact HS|]. split; [|exact STc].
      eapply limbs_at_transport; [exact RT1 | exact MUc | cbn [disjoint_from]; clear - DRT SEPT LR16 HSK LEAF; lia]. }
    intros NC.
    zstep.
    zstep.
    assert (L15 : (bv_unsigned (Z_to_bv 64 15) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (L3 : (bv_unsigned a3 < 9223372036854775808)%Z) by (rewrite A3; clear - HN2; lia).
    rewrite (lts_words_small (Z_to_bv 64 15) a3 L15 L3). clear L15 L3.
    rewrite A3. if_cases K16; zify_cond K16.
    { (* [comment removed for export] *)
      pose proof (hide_elim _ GEO) as (DRA & DRB & DTA & DTB & DRT & SEPR & SEPT & SEPA & SEPB & HLA' & HLB' & HLR' & HLT').
      assert (ELR : length R = (4 * n)%nat) by (clear - HLR' EN; lia).
      assert (ESK' : SK = rec_ustack L k').
      { clear - ESK. unfold rec_ustack in *. rewrite !Nat2Z.inj_succ in *. lia. }
      assert (PRE : kara_upre L k' n da db (length a) (length b) (length T) SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1)
                             (bv_unsigned a2) (bv_unsigned sp) lo).
      { unfold kara_upre. rewrite <- ELR.
        assert (Hk1 : (1 <= k')%nat) by (destruct k' as [|k'']; [cbn in En; exfalso; clear - En EN K16; lia | clear; lia]).
        split; [exact En|]. split; [clear - Hk Hk1; lia|]. split; [clear - K16 EN; lia|]. split; [clear - HN2 EN; lia|].
        split; [exact Hda|]. split; [exact Hdb|]. split; [clear - HLA' EN; lia|]. split; [clear - HLB' EN; lia|].
        split. { rewrite scratch_rec_S in HLT' by (rewrite <- EN2; clear - K16; lia). rewrite <- EN2 in HLT'. clear - HLT' EN ELR. lia. }
        split; [exact ESK'|].
        split; [exact DRA|]. split; [exact DRB|]. split; [exact DTA|]. split; [exact DTB|]. split; [exact DRT|].
        split; [clear - SEPR; lia|]. split; [clear - SEPT; lia|]. split; [clear - SEPA; lia|]. split; [clear - SEPB; lia|].
        split; [clear - LO; lia|]. split; [exact LO0 | exact L80]. }
      replace (Z.of_nat (length R)) with (Z.of_nat (4 * n)) by (rewrite ELR; reflexivity).
      eapply UB_body with (L := L) (CS8 := CS8) (FSC := FSC) (FSS := FSS) (k' := k') (n := n) (nT := length T) (SK := SK) (da := da) (db := db);
        [ first [ exact LEAF | exact comba8_ok | exact cmp_part_ok | exact sub_part_ok | exact mul_normal_ok | exact (IHk k' eq_refl)
                | exact PRE | exact LA | exact LB | exact A3' | exact A4 | exact A5 | exact UBR | exact UBA | exact UBB | exact UBT | exact a7 ] .. | | ].
      - unfold KB. split; [exact LR|]. split; [exact LT|]. split; [exact ELR|]. split; [reflexivity|].
        split; [exact RR1|]. split; [exact RT1|]. split; [exact RA1|]. split; [exact RB1|].
        split; [rewrite EN in WR; replace (4 * n)%nat with (2 * (2 * n))%nat by (clear; lia); exact WR|]. split; [exact WT|].
        split; [exact FR|]. split; [exact STK|]. split; [exact MI0|].
        split; [|exact WM]. unfold KWfin. rewrite <- ELR. replace (bv_unsigned sp - 160 - SK)%Z with (bv_unsigned sp - (160 + SK))%Z by (clear; lia). exact MU.
      - rewrite En. apply rec_staged; try assumption; rewrite <- ?EN2; try assumption.
        clear - K16. lia. }
    clear IHk.
    (* [comment removed for export] *)
    do 2 zstep.
    setreg 12%Z (Z_to_bv 64 (Z.of_nat N2 - Z.of_nat da)) ltac:(rewrite A3, A4; apply Z_to_bv_eqm; clear - Hda HN2; wnorm).
    setreg 10%Z (Z_to_bv 64 (Z.of_nat N2 - Z.of_nat da)) ltac:(rewrite A3, A4; apply Z_to_bv_eqm; clear - Hda HN2; wnorm).
    chk ltac:(fun C => clear - C; lia).
    do 2 zstep.
    setreg 10%Z (Z_to_bv 64 (Z.of_nat N2 - Z.of_nat db)) ltac:(rewrite A3, A5; apply Z_to_bv_eqm; clear - Hdb HN2; wnorm).
    setreg 14%Z (Z_to_bv 64 (Z.of_nat N2 - Z.of_nat db)) ltac:(rewrite A3, A5; apply Z_to_bv_eqm; clear - Hdb HN2; wnorm).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat N2 - Z.of_nat db + 0)), Z.add_0_r by (clear - Hdb HN2; lia).
    do 4 zstep.
    pose proof (hide_elim _ GEO) as (DRA & DRB & DTA & DTB & DRT & SEPR & SEPT & SEPA & SEPB & HLA' & HLB' & HLR' & HLT').
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = (bv_unsigned sp + -160)%Z).
    { apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
      pose proof (zr_word sp) as RS. unfold inr64 in RS. change (2 ^ 64)%Z with 18446744073709551616%Z in RS. clear - RS LO0 LO1. lia. }
    assert (Lab : (Z.of_nat (length a) = Z.of_nat N2 - Z.of_nat da /\ Z.of_nat (length b) = Z.of_nat N2 - Z.of_nat db /\ Z.of_nat (length R) = 2 * Z.of_nat N2)%Z)
      by (clear - HLA' HLB' HLR' HN2 Hda Hdb; lia).
    eapply ucall_mul_normal with (FS := FSM) (a := a) (b := b) (lo := lo) (SPz := (bv_unsigned sp + -160)%Z)
                                (RP := bv_unsigned a0) (AP := bv_unsigned a1) (BP := bv_unsigned a2);
      [ exact ESP | apply ret_pc_even; [lia | reflexivity] | exact STK | exact MI0 | exact mul_normal_ok | exact LA | exact LB | clear - Lab HN2; lia
      | reflexivity | reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - HN2 Hda; lia); clear - Lab; lia
      | reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - HN2 Hdb; lia); clear - Lab; lia
      | exact RA1 | exact RB1
      | pose proof (wr_at_sub bgusegs m1 _ _ 0 (8 * (Z.of_nat (length a) + Z.of_nat (length b))) WR ltac:(lia) ltac:(lia) ltac:(clear - Lab Hda Hdb; lia)) as X;
        rewrite Z.add_0_r in X; exact X
      | clear - DRA Lab; lia | clear - DRB Lab; lia | clear - LO HSK LEAF; lia
      | clear - SEPR Lab HSK LEAF; lia | clear - SEPA HSK LEAF; lia | clear - SEPB HSK LEAF; lia
      | exact UBR | exact UBA | exact UBB | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (mul_normal_spec a b LA LB) as (LMN & _ & EMN).
    assert (EMN' : length (mul_normal a b) = (length a + length b)%nat).
    { rewrite EMN. destruct (Nat.eqb_spec (length a) 0) as [E|_]; [exfalso; clear - E Lab HN2 Hda; lia|].
      destruct (Nat.eqb_spec (length b) 0) as [E|_]; [exfalso; clear - E Lab HN2 Hdb; lia|]. reflexivity. }
    clear EMN.
    (* [comment removed for export] *)
    assert (RR2 : limbs_at bgusegs m2 (bv_unsigned a0) (splice R 0 (mul_normal a b))).
    { eapply (limbs_at_splice bgusegs _ m1 m2 (bv_unsigned a0) R 0 (mul_normal a b) RR1 MUc).
      - rewrite EMN'. clear - Lab Hda Hdb. lia.
      - change (Z.of_nat 0) with 0%Z. rewrite Z.mul_0_r, Z.add_0_r. exact HS.
      - cbn [disjoint_from]. clear - SEPR Lab HSK LEAF. lia.
      - cbn [disjoint_from]. rewrite EMN'. clear - SEPR Lab HSK LEAF Hda Hdb. lia. }
    assert (RT2 : limbs_at bgusegs m2 (bv_unsigned a6) T)
      by (eapply limbs_at_transport; [exact RT1 | exact MUc | cbn [disjoint_from]; clear - DRT SEPT Lab HSK LEAF; lia]).
    assert (WR2 : wr_at bgusegs m2 (bv_unsigned a0) (8 * Z.of_nat (2 * N2))) by (eapply wr_at_transport; [exact WR | exact WMc]).
    assert (FR2 := rw_cells_transport bgusegs _ m1 m2 _ _ FR MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - SEPR Lab HSK LEAF; lia)).
    assert (MU2 : munch [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length R)); (bv_unsigned a6, bv_unsigned a6 + 8 * Z.of_nat (length T));
                         (bv_unsigned sp - (160 + SK), bv_unsigned sp)]%Z m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx Lab HSK LEAF Hda Hdb. lia. }
    assert (WM2 := wmono_trans bgusegs _ _ _ WM WMc).
    assert (Lab2 : length a = (N2 - da)%nat /\ length b = (N2 - db)%nat) by (split; assumption).
    clear MU WM MUc WMc FR WR RR1 RT1 RA1 RB1 STK MI0 HS. rename FR2 into FR.
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB HLA' HLB' HLR' HLT'.
    assert (EMOD : mul_recursive (S k') a b da db R T =
                   ((if (0 <? da + db)%nat then splice (splice R 0 (mul_normal a b)) (2 * N2 - da - db) (repeat 0%Z (da + db))
                     else splice R 0 (mul_normal a b)), T)).
    { rewrite mul_recursive_small.
      - cbv zeta. rewrite <- EN2. rewrite !firstn_all2 by (clear - Lab2; lia). reflexivity.
      - rewrite <- EN2. clear - K16. lia.
      - rewrite <- EN2. destruct (Nat.eqb_spec N2 8) as [E1|_]; [|reflexivity].
        destruct (Nat.eqb_spec da 0) as [E2|_]; [|reflexivity]. destruct (Nat.eqb_spec db 0) as [E3|_]; [|reflexivity].
        exfalso. apply NC. repeat split; assumption. }
    rewrite EMOD. cbn [fst snd]. clear EMOD.
    do 2 zstep.
    setreg 11%Z (Z_to_bv 64 (- (Z.of_nat da + Z.of_nat db))) ltac:(rewrite A4, A5; apply Z_to_bv_eqm; clear - Hda Hdb; wnorm).
    setreg 10%Z (Z_to_bv 64 (- (Z.of_nat da + Z.of_nat db))) ltac:(rewrite A4, A5; apply Z_to_bv_eqm; clear - Hda Hdb; wnorm).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite lts_signed by (clear - Hda Hdb; lia).
    if_cases KZ; zify_cond KZ.
    { (* [comment removed for export] *)
      destruct (Nat.ltb_spec 0 (da + db)) as [HH|_]; [exfalso; clear - HH KZ; lia|].
      do 15 zstep. release_frame FR STc (bv_unsigned sp).
      finish. }
    destruct (Nat.ltb_spec 0 (da + db)) as [_|HH]; [|exfalso; clear - HH KZ; lia].
    do 2 zstep.
    setreg 18%Z (Z_to_bv 64 (Z.of_nat N2)) ltac:(rewrite <- A3; apply Z_to_bv_bv_unsigned).
    zstep. rewrite lts_signed by (clear - HN2; lia).
    if_cases C0; [exfalso; zify_cond C0; clear - C0 HN2; lia | clear C0].
    do 3 zstep.
    setreg 12%Z (Z_to_bv 64 (2 * Z.of_nat N2 - Z.of_nat da)) ltac:(rewrite A4; apply Z_to_bv_eqm; clear - Hda HN2; wnorm).
    setreg 10%Z (Z_to_bv 64 (2 * Z.of_nat N2 - Z.of_nat da)) ltac:(rewrite A4; apply Z_to_bv_eqm; clear - Hda HN2; wnorm).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (2 * Z.of_nat N2 - Z.of_nat da + 0)), Z.add_0_r by (clear - Hda HN2; lia).
    do 2 zstep.
    setreg 10%Z (Z_to_bv 64 (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db)) ltac:(rewrite A5; apply Z_to_bv_eqm; clear - Hda Hdb HN2; wnorm).
    setreg 12%Z (Z_to_bv 64 (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db)) ltac:(rewrite A5; apply Z_to_bv_eqm; clear - Hda Hdb HN2; wnorm).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db + 0)), Z.add_0_r by (clear - Hda Hdb HN2; lia).
    zstep. replace ((2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db) ≪ 3)%Z with (8 * (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db))%Z
      by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    pose proof (hide_elim _ GEO) as (DRA & DRB & DTA & DTB & DRT & SEPR & SEPT & SEPA & SEPB & HLA' & HLB' & HLR' & HLT').
    assert (BR' : (0 < bv_unsigned a0 /\ bv_unsigned a0 + 16 * Z.of_nat N2 <= 140737488355328)%Z).
    { split; [exact (proj1 (UBR ltac:(lia)))|]. clear - BR HLR'. lia. }
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB HLA' HLB' HLR' HLT'.
    do 4 zstep.
    setreg 13%Z (Z_to_bv 64 1) ltac:(replace (0 <? bv_unsigned a0)%Z with true by (symmetry; apply Z.ltb_lt; clear - BR'; lia); reflexivity).
    setreg 14%Z (Z_to_bv 64 0) ltac:(
      replace (bv_unsigned a0 + 8 * (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db) <? 1)%Z with false
        by (symmetry; apply Z.ltb_ge; clear - BR' Hda Hdb HN2; lia); reflexivity).
    zstep. if_false.
    do 5 zstep.
    setreg 12%Z (Z_to_bv 64 1) ltac:(
      replace (bv_unsigned a0 + 8 * (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db) <? bv_unsigned a0)%Z with false
        by (symmetry; apply Z.ltb_ge; clear - Hda Hdb HN2; lia);
      rewrite lxor_signbit by (clear - Hda Hdb HN2; lia);
      replace (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db + 9223372036854775808 <? 9223372036854775808)%Z with false
        by (symmetry; apply Z.ltb_ge; clear - Hda Hdb HN2; lia);
      reflexivity).
    zstep. if_false.
    do 2 zstep.
    setreg 11%Z (Z_to_bv 64 (Z.of_nat da + Z.of_nat db)) ltac:(apply Z_to_bv_eqm; clear - Hda Hdb; wnorm).
    setreg 12%Z (Z_to_bv 64 (Z.of_nat da + Z.of_nat db)) ltac:(apply Z_to_bv_eqm; clear - Hda Hdb; wnorm).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat da + Z.of_nat db + 0)), Z.add_0_r by (clear - Hda Hdb; lia).
    zstep. replace ((Z.of_nat da + Z.of_nat db) ≪ 3)%Z with (8 * Z.of_nat (da + db))%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 17 zstep.
    release_frame FR STc (bv_unsigned sp).
    pose proof (hide_elim _ GEO) as (DRA & DRB & DTA & DTB & DRT & SEPR & SEPT & SEPA & SEPB & HLA' & HLB' & HLR' & HLT').
    remember (splice R 0 (mul_normal a b)) as R1 eqn:ER1.
    assert (LR1 : length R1 = (2 * N2)%nat) by (rewrite ER1, splice_length; [exact HLR' | rewrite EMN'; clear - HLA' HLB' HLR'; lia]).
    assert (Hoff : (2 * N2 - da - db + (da + db) <= length R1)%nat) by (rewrite LR1; clear - HN2 Hda Hdb; lia).
    pose proof (limbs_at_slice bgusegs m2 _ R1 (2 * N2 - da - db) (da + db) RR2 Hoff) as HL.
    assert (LL : length (slice R1 (2 * N2 - da - db) (da + db)) = (da + db)%nat) by (apply slice_length; exact Hoff).
    assert (ED : (bv_unsigned a0 + 8 * (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db) = bv_unsigned a0 + 8 * Z.of_nat (2 * N2 - da - db))%Z)
      by (clear - HN2 Hda Hdb; lia).
    rewrite ED.
    pose proof (zr_word a0) as R0. unfold inr64 in R0.
    eapply evt_mono.
    { eapply umemset0_limbs_spec with (L := slice R1 (2 * N2 - da - db) (da + db)) (D := (bv_unsigned a0 + 8 * Z.of_nat (2 * N2 - da - db))%Z)
                                     (lo := lo) (SPz := bv_unsigned sp);
        [ apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - R0 BR HLR' HN2 Hda Hdb; lia
        | reflexivity
        | rewrite LL; apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - Hda Hdb; lia
        | exact HL
        | rewrite LL; pose proof (wr_at_sub bgusegs m2 _ _ (8 * Z.of_nat (2 * N2 - da - db)) (8 * Z.of_nat (da + db)) WR2 ltac:(lia) ltac:(lia)
                                    ltac:(clear - HN2 Hda Hdb; lia)) as X; exact X
        | exact STc | exact MIc ]. }
    intros ms' PO. unfold umemset0_post in PO.
    destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m3 & E & MUm & WMm & MIm & HZ & STm).
    rewrite LL in MUm, HZ.
    eexists w0, w1, w2, _, y1, y2, y3, y4, y5, y6, y7, w3, w4, w5, w6, m3.
    split; [exact E|].
    split. { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [|exact MUm]. unfold sub_fp. cbn [outside]. intros x Hx.
             clear - Hx HLR' HN2 Hda Hdb. lia. }
    split; [eapply wmono_trans; [exact WM2 | exact WMm]|]. split; [exact MIm|].
    split.
    { eapply (limbs_at_splice bgusegs _ m2 m3 (bv_unsigned a0) R1 (2 * N2 - da - db) (repeat 0%Z (da + db)) RR2 MUm).
      - rewrite repeat_length. exact Hoff.
      - exact HZ.
      - cbn [disjoint_from]. clear. lia.
      - cbn [disjoint_from]. rewrite repeat_length. clear. lia. }
    split; [|exact STm].
    eapply limbs_at_transport; [exact RT2 | exact MUm | cbn [disjoint_from]; clear - DRT HLR' HN2 Hda Hdb; lia].

  Qed.

  (* [comment removed for export] *)
  Theorem bn_mul_recursive_uspec : forall k, rec_uspec_at L k.
  Proof.
    induction k as [|k IH]; apply urec_body; intros k' E; [discriminate|]. injection E as <-. exact IH.
  Qed.
End MainU.
