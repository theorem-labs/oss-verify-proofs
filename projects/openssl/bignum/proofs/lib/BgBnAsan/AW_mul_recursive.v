(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp BnKaraX.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require BnKaraMem.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require W_mul_recursive.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require BnKit2.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA BnIfaceA AsStruct ImplA RtCallA BnKaraMemA BnCallsKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_mul_recursive_aentry := 0x229bcc%Z.

Notation land_even31 := W_mul_recursive.land_even31.
Notation lor_neg_zero := W_mul_recursive.lor_neg_zero.
Notation half_n2 := W_mul_recursive.half_n2.
Notation addw_dn := W_mul_recursive.addw_dn.
Notation negw_dn := W_mul_recursive.negw_dn.
Notation upd_app_mid := W_mul_recursive.upd_app_mid.

Lemma land_m64 : forall z, Z.land z 18446744073709551615 = (z mod 18446744073709551616)%Z.
Proof. intros z. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.

Definition rec_stackA (CS8 : Z) (k : nat) : Z := (176 * Z.of_nat (S k) + Z.max CS8 65536)%Z.

Section Spec.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).

  Definition kr_apost (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block)
      (lo RP NR TQ NT : Z) (r' t' : list Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
      ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom bgasegs)
      /\ mem_inv bgasegs m' /\ stk bgasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ wmono bgasegs m m'
      /\ agree_on (fun x => aclient_addr (OW ++ LB) (bv_unsigned sp) x /\ ~ (RP <= x < RP + 8 * NR)%Z /\ ~ (TQ <= x < TQ + 8 * NT)%Z) m m'
      /\ limbs_at bgasegs m' RP r' /\ limbs_at bgasegs m' TQ t'.

  Definition kara_blocks (OW LB : list block) (bR bT bA bB : block) (rp tq ap bp : Z) (nR nT la lb : nat) : Prop :=
    In bR OW /\ In bT OW /\ In bA (OW ++ LB) /\ In bB (OW ++ LB) /\
    (blk_addr bR <= rp /\ rp + 8 * Z.of_nat nR <= blk_addr bR + blk_size bR)%Z /\
    (blk_addr bT <= tq /\ tq + 8 * Z.of_nat nT <= blk_addr bT + blk_size bT)%Z /\
    (blk_addr bA <= ap /\ ap + 8 * Z.of_nat la <= blk_addr bA + blk_size bA)%Z /\
    (blk_addr bB <= bp /\ bp + 8 * Z.of_nat lb <= blk_addr bB + blk_size bB)%Z /\
    (rp mod 8 = 0 /\ tq mod 8 = 0 /\ ap mod 8 = 0 /\ bp mod 8 = 0)%Z.

  Definition rec_spec_atA (CS8 : Z) (k : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (bR bT bA bB : block)
           (a b : list Z) (da db : nat) (R T : list Z) (lo : Z),
      limbs a -> limbs b -> limbs R -> limbs T ->
      (1 <= k <= 26)%nat -> (da <= 1)%nat -> (db <= 1)%nat ->
      length a = (Nat.pow 2 k - da)%nat -> length b = (Nat.pow 2 k - db)%nat -> length R = (2 * Nat.pow 2 k)%nat ->
      (scratch_rec k <= length T)%nat ->
      bv_unsigned a3 = Z.of_nat (Nat.pow 2 k) -> a4 = Z_to_bv 64 (- Z.of_nat da) -> a5 = Z_to_bv 64 (- Z.of_nat db) ->
      limbs_at bgasegs m (bv_unsigned a1) a -> limbs_at bgasegs m (bv_unsigned a2) b ->
      limbs_at bgasegs m (bv_unsigned a0) R -> limbs_at bgasegs m (bv_unsigned a6) T ->
      wr_at bgasegs m (bv_unsigned a0) (8 * Z.of_nat (length R)) -> wr_at bgasegs m (bv_unsigned a6) (8 * Z.of_nat (length T)) ->
      (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0)%Z ->
      (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a0)%Z ->
      (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a6)%Z ->
      (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a6)%Z ->
      (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a6 \/ bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a0)%Z ->
      stk bgasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - rec_stackA CS8 k)%Z ->
      (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned sp - rec_stackA CS8 k \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
      (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned sp - rec_stackA CS8 k \/ bv_unsigned sp <= bv_unsigned a6)%Z ->
      (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - rec_stackA CS8 k \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
      (bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned sp - rec_stackA CS8 k \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
      mem_inv bgasegs m ->

      AHEAP Σ OW LB m ->
      kara_blocks OW LB bR bT bA bB (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (length R) (length T) (length a) (length b) ->
      (ACEIL <= lo)%Z -> (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> tp = wz TP_A ->
      cps bgasegs
        (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x229bcc) fc None m (seg_rom bgasegs))))
        (ASTA RT Σ PMc (kr_apost ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo
                          (bv_unsigned a0) (Z.of_nat (length R)) (bv_unsigned a6) (Z.of_nat (length T))
                          (fst (mul_recursive k a b da db R T)) (snd (mul_recursive k a b da db R T)) m)).

  Lemma call_recA : forall (Σ : rts RT) (Q : config -> Prop)
      (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (OW LB : list block) (lo SPz RET : Z)
      (CS8 : Z) (k : nat) (a b : list Z) (da db : nat) (R T : list Z) (RP AP BP TQ : Z) (bR bT bA bB : block),
    bv_unsigned wsp = SPz -> ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET -> stk bgasegs m lo SPz -> mem_inv bgasegs m ->
    rec_spec_atA CS8 k ->
    limbs a -> limbs b -> limbs R -> limbs T ->
    (1 <= k <= 26)%nat -> (da <= 1)%nat -> (db <= 1)%nat ->
    length a = (Nat.pow 2 k - da)%nat -> length b = (Nat.pow 2 k - db)%nat -> length R = (2 * Nat.pow 2 k)%nat ->
    (scratch_rec k <= length T)%nat ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (Nat.pow 2 k) ->
    w4 = Z_to_bv 64 (- Z.of_nat da) -> w5 = Z_to_bv 64 (- Z.of_nat db) -> bv_unsigned w6 = TQ ->
    limbs_at bgasegs m AP a -> limbs_at bgasegs m BP b -> limbs_at bgasegs m RP R -> limbs_at bgasegs m TQ T ->
    wr_at bgasegs m RP (8 * Z.of_nat (length R)) -> wr_at bgasegs m TQ (8 * Z.of_nat (length T)) ->
    (RP + 8 * Z.of_nat (length R) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (RP + 8 * Z.of_nat (length R) <= BP \/ BP + 8 * Z.of_nat (length b) <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= AP \/ AP + 8 * Z.of_nat (length a) <= TQ)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= BP \/ BP + 8 * Z.of_nat (length b) <= TQ)%Z ->
    (RP + 8 * Z.of_nat (length R) <= TQ \/ TQ + 8 * Z.of_nat (length T) <= RP)%Z ->
    (lo <= SPz - rec_stackA CS8 k)%Z ->
    (RP + 8 * Z.of_nat (length R) <= SPz - rec_stackA CS8 k \/ SPz <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= SPz - rec_stackA CS8 k \/ SPz <= TQ)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - rec_stackA CS8 k \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - rec_stackA CS8 k \/ SPz <= BP)%Z ->
    (AHEAP Σ OW LB m /\ kara_blocks OW LB bR bT bA bB RP TQ AP BP (length R) (length T) (length a) (length b) /\
     (ACEIL <= lo)%Z /\ (SPz + 16 <= USTACK_TOP)%Z /\ (SPz mod 16 = 0)%Z /\ tp = wz TP_A) ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 (F2 : bvmap 5 word) (fc2 : bv 32),
       AHEAP Σ OW LB m2 ->
       agree_on (fun x => aclient_addr (OW ++ LB) SPz x /\ ~ (RP <= x < RP + 8 * Z.of_nat (length R))%Z /\ ~ (TQ <= x < TQ + 8 * Z.of_nat (length T))%Z) m m2 ->
       wmono bgasegs m m2 -> mem_inv bgasegs m2 ->
       limbs_at bgasegs m2 RP (fst (mul_recursive k a b da db R T)) -> limbs_at bgasegs m2 TQ (snd (mul_recursive k a b da db R T)) ->
       stk bgasegs m2 lo SPz ->
       evt bgasegs (kpost Σ Q)
         (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
             F2 (Z_to_bv 64 RET) fc2 None m2 (seg_rom bgasegs))) ->
    evt bgasegs (kpost Σ Q)
      (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x229bcc) fc None m (seg_rom bgasegs)).
  Proof.
    intros until bB. intros ESP ERET STK MI0 SPEC LA LB' LR LT Hk Hda Hdb HLA HLB HLR HLT E0 E1 E2 E3 E4 E5 E6
           RA RB RR RT WR WT DRA DRB DTA DTB DRT LO SEPR SEPT SEPA SEPB (HEAP & KBL & CEIL & SPT & SP16 & ETP) K.
    subst RP AP BP TQ SPz.
    apply evt_done. unfold kpost.
    eapply cps_step_same.
    - eapply SPEC with (a := a) (b := b) (da := da) (db := db) (R := R) (T := T) (lo := lo) (bR := bR) (bT := bT) (bA := bA) (bB := bB); eassumption.
    - intros ms2 PO. unfold kr_apost in PO.
      destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & HR2 & HT2).
      rewrite ERET. apply cps_from_evt'. rewrite <- ETP.
      eapply K; eassumption.
  Qed.
End Spec.

Definition kara_preA (CS8 : Z) (k' n da db la lb nT : nat) (SK rp tq ap bp SP lo : Z) : Prop :=
  n = Nat.pow 2 k' /\ (1 <= k' <= 25)%nat /\ (8 <= n)%nat /\ (Z.of_nat n <= 33554432)%Z /\ (da <= 1)%nat /\ (db <= 1)%nat /\
  la = (2 * n - da)%nat /\ lb = (2 * n - db)%nat /\ (4 * n + scratch_rec k' <= nT)%nat /\ SK = rec_stackA CS8 k' /\
  (rp + 8 * Z.of_nat (4 * n) <= ap \/ ap + 8 * Z.of_nat la <= rp)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= bp \/ bp + 8 * Z.of_nat lb <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat la <= tq)%Z /\
  (tq + 8 * Z.of_nat nT <= bp \/ bp + 8 * Z.of_nat lb <= tq)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= tq \/ tq + 8 * Z.of_nat nT <= rp)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= SP - 176 - SK \/ SP <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= SP - 176 - SK \/ SP <= tq)%Z /\
  (ap + 8 * Z.of_nat la <= SP - 176 - SK \/ SP <= ap)%Z /\
  (bp + 8 * Z.of_nat lb <= SP - 176 - SK \/ SP <= bp)%Z /\
  (lo <= SP - 176 - SK)%Z /\ (0 <= lo)%Z.

Section Kara.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).
  Variable CS8 : Z.
  Hypothesis CS8_0 : (0 <= CS8)%Z.
  Hypothesis comba8_ok : comba8_aspec CS8.
  Variable k' : nat.
  Hypothesis IH : rec_spec_atA CS8 k'.
  Variables (Σ : rts RT) (OW LB : list block) (bR bT bA bB : block).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : word -> option byte) (a b : list Z) (da db : nat) (lo : Z) (n nT : nat) (SK : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a2).
  Notation tq := (bv_unsigned a6).
  Notation SP := (bv_unsigned sp).
  Notation N := (Z.of_nat n).
  Hypothesis PRE : kara_preA CS8 k' n da db (length a) (length b) nT SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo.
  Hypothesis KBL : kara_blocks OW LB bR bT bA bB (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (4 * n) nT (length a) (length b).
  Hypothesis CEIL : (ACEIL <= lo)%Z.
  Hypothesis SPT16 : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis ETP : tp = wz TP_A.
  Hypothesis LA : limbs a.
  Hypothesis LB' : limbs b.
  Hypothesis A3 : bv_unsigned a3 = (2 * N)%Z.
  Hypothesis A4 : a4 = Z_to_bv 64 (- Z.of_nat da).
  Hypothesis A5 : a5 = Z_to_bv 64 (- Z.of_nat db).
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
  Lemma HSK : SK = rec_stackA CS8 k'. Proof. apply PRE. Qed.
  Lemma DRA : (rp + 8 * Z.of_nat (4 * n) <= ap \/ ap + 8 * Z.of_nat (length a) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma DRB : (rp + 8 * Z.of_nat (4 * n) <= bp \/ bp + 8 * Z.of_nat (length b) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma DTA : (tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat (length a) <= tq)%Z. Proof. apply PRE. Qed.
  Lemma DTB : (tq + 8 * Z.of_nat nT <= bp \/ bp + 8 * Z.of_nat (length b) <= tq)%Z. Proof. apply PRE. Qed.
  Lemma DRT : (rp + 8 * Z.of_nat (4 * n) <= tq \/ tq + 8 * Z.of_nat nT <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPR : (rp + 8 * Z.of_nat (4 * n) <= SP - 176 - SK \/ SP <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPT : (tq + 8 * Z.of_nat nT <= SP - 176 - SK \/ SP <= tq)%Z. Proof. apply PRE. Qed.
  Lemma SEPA : (ap + 8 * Z.of_nat (length a) <= SP - 176 - SK \/ SP <= ap)%Z. Proof. apply PRE. Qed.
  Lemma SEPB : (bp + 8 * Z.of_nat (length b) <= SP - 176 - SK \/ SP <= bp)%Z. Proof. apply PRE. Qed.
  Lemma LO : (lo <= SP - 176 - SK)%Z. Proof. apply PRE. Qed.
  Lemma LO0 : (0 <= lo)%Z. Proof. apply PRE. Qed.
  Lemma SK0 : (0 <= SK)%Z. Proof. rewrite HSK. unfold rec_stackA. lia. Qed.
  Lemma SK_ge : (65536 <= SK /\ CS8 <= SK)%Z. Proof. rewrite HSK. unfold rec_stackA. lia. Qed.
  Lemma FS0 : (0 <= 176)%Z. Proof. lia. Qed.
  Lemma FBE : (SP + -176 = SP - 176)%Z. Proof. reflexivity. Qed.
  Lemma SPTop : (SP <= USTACK_TOP)%Z. Proof. pose proof SPT16. lia. Qed.
  Lemma ESP176 : bv_unsigned (Z_to_bv 64 (SP + -176)) = (SP + -176)%Z.
  Proof.
    apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R.
    pose proof LO. pose proof LO0. pose proof SK0. lia.
  Qed.
  Lemma INR : In bR OW. Proof. apply KBL. Qed.
  Lemma INT : In bT OW. Proof. apply KBL. Qed.
  Lemma INA : In bA (OW ++ LB). Proof. apply KBL. Qed.
  Lemma INB : In bB (OW ++ LB). Proof. apply KBL. Qed.
  Lemma RGR : (blk_addr bR <= rp /\ rp + 8 * Z.of_nat (4 * n) <= blk_addr bR + blk_size bR)%Z. Proof. apply KBL. Qed.
  Lemma RGT : (blk_addr bT <= tq /\ tq + 8 * Z.of_nat nT <= blk_addr bT + blk_size bT)%Z. Proof. apply KBL. Qed.
  Lemma RGA : (blk_addr bA <= ap /\ ap + 8 * Z.of_nat (length a) <= blk_addr bA + blk_size bA)%Z. Proof. apply KBL. Qed.
  Lemma RGB : (blk_addr bB <= bp /\ bp + 8 * Z.of_nat (length b) <= blk_addr bB + blk_size bB)%Z. Proof. apply KBL. Qed.
  Lemma AL8 : (rp mod 8 = 0 /\ tq mod 8 = 0 /\ ap mod 8 = 0 /\ bp mod 8 = 0)%Z. Proof. apply KBL. Qed.

  Notation POST := (kpost Σ (ASTA RT Σ PMc (kr_apost ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo
                      (bv_unsigned a0) (Z.of_nat (4 * n)) (bv_unsigned a6) (Z.of_nat nT) (fst RES) (snd RES) m))).

  Notation KK L := (L Σ OW LB m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      176%Z SK (bv_unsigned sp + -176)%Z bR bT bA bB FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB
                      INR INT INA INB RGR RGT RGA RGB CEIL LO SPTop).
  Notation KBK := (KB Σ OW LB m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      (bv_unsigned sp + -176)%Z).
  Notation KUPD := (KK KB_upd).
  Notation KFRAME := (KK KB_frame).
  Notation KSTORE := (KK KB_storeR).
  Notation KAFTER L := (KK L).
  Notation KACC L := (KK L).

  Notation FCELLS jb v152 v128 :=
    [CB 8 jb; C8 (Z_to_bv 64 (Z.of_nat da)); C8 (Z_to_bv 64 (Z.of_nat n - Z.of_nat da)); C8 v152;
     C8 (Z_to_bv 64 (Z.of_nat n)); C8 (Z_to_bv 64 SHB); C8 v128; C8 (Z_to_bv 64 (bv_unsigned a1 + 8 * Z.of_nat n));
     C8 (Z_to_bv 64 (8 * Z.of_nat n));
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation ST F fc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp x5 x6 x7 sp a0 x10 x11 x12 x13 x14 x15 x16 x17
             a3 a6 x20 (Z_to_bv 64 (16 * Z.of_nat n)) a2 a1 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).

  Lemma B_epi : forall jb v152 v128 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x27 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb v152 v128) m1 R T -> RES = (R, T) ->
    evt bgasegs POST (ST F fc 0x22a07c m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM) E.
    do 15 zstep.
    assert (LO1 : (lo <= SP + -176)%Z) by (pose proof LO; pose proof SK0; lia).
    release_frame FR ST (bv_unsigned sp).
    subst RES. cbn [fst snd].
    apply evt_done. unfold kpost. apply cps_done. unfold kr_apost. rewrite ETP.
    do 18 eexists. split; [reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact HEAP|]. split; [exact WM|].
    split; [exact MU|]. split; [exact HR | exact HT].
  Qed.

  Ltac kb_store SOK0 I2 :=
    lazymatch type of SOK0 with
    | store_ok _ ?m2 ?a0' _ = true =>
        let ad := cur_mem_addr in
        let SOK := fresh "SOK" in
        assert (SOK : store_ok bgasegs m2 ad 8 = true) by (replace ad with a0' by (unfold wa; f_equal; lia); exact SOK0);
        replace a0' with ad in I2 by (unfold wa; f_equal; lia);
        zstep; clear SOK SOK0;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => let m' := fresh "m" in gen_mem mm m' end
    end.

  Lemma shR_rd : forall cells m1 R T (i : nat) ad, KBK cells m1 R T -> (i < 4 * n)%nat -> (0 <= rp /\ rp + 8 * Z.of_nat (4 * n) <= 140737488355328)%Z ->
    ad = wa (shad (rp + 8 * Z.of_nat i)) -> ov_read_bytes bgasegs m1 ad 1 = Some [z8].
  Proof.
    intros cells m1 R T i ad I Hi BR ->.
    pose proof (KACC KB_accR _ _ _ _ 0%nat (4 * n)%nat I ltac:(clear; lia)) as AC.
    destruct AL8 as (AR8 & _).
    eapply (acc_rd0_same bgasegs m1 _ _ (rp + 8 * Z.of_nat i)%Z _ AC); [ | | | | reflexivity].
    - clear - AR8. Z.div_mod_to_equations. lia.
    - clear - Hi. lia.
    - clear - Hi. lia.
    - clear - BR Hi. lia.
  Qed.

  Lemma B_loop : forall (l pre : list Z) jb v152 v128 m1 T x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x24 x26 x27 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb v152 v128) m1 (pre ++ l) T -> cu_fit l -> RES = (pre ++ carry_up l, T) ->
    evt bgasegs POST (ST F fc 0x22a058 m1 x1 x5 x6 x7 (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre))) (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre)))
                       (Z_to_bv 64 (shad (rp + 8 * Z.of_nat (length pre)))) x13 x14 x15 x16 x17 x20 x24 (Z_to_bv 64 SHB) x26 x27 x28 x29 x30 x31).
  Proof.
    induction l as [|x l' IHl]; intros until fc; intros I FIT E.
    { exfalso. unfold cu_fit in FIT. cbn [lval length] in FIT. rewrite Bp_0 in FIT. clear - FIT. lia. }
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    destruct (cu_fit_cons (x :: l') (proj2 (limbs_app_inv _ _ LR)) FIT) as (x' & l'' & Ecs & Hx & Hl' & Hfit').
    injection Ecs as <- <-.
    assert (Hi : (length pre < 4 * n)%nat) by (rewrite length_app in ER; cbn [length] in ER; clear - ER; lia).
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(pose proof Hn8; lia) ltac:(pose proof HnT; pose proof Hn8; lia)) as (BR0 & BR1 & _).
    assert (BP : (0 <= rp + 8 * Z.of_nat (length pre) /\ rp + 8 * Z.of_nat (length pre) + 8 <= 140737488355328)%Z) by (clear - BR0 BR1 Hi; lia).
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    (let ad := cur_mem_addr in pose proof (shR_rd _ m1 _ T (length pre) ad I Hi (conj BR0 BR1) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    ld_hd HR2.
    do 3 zstep.
    setreg 13%Z (Z_to_bv 64 (addw x 1)) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE (FCELLS jb v152 v128) m1 (pre ++ x :: l') T (length pre) (addw x 1) eq_refl I Hi (addw_limb _ _)) as (SOK0 & I2).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI HEAP MU WM BR0 BR1.
    kb_store SOK0 I2.
    zstep.
    rewrite upd_app_mid in I2.
    pose proof (addw_limb x 1) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K; zify_cond K.
    - setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x 1])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      setreg 12%Z (Z_to_bv 64 (shad (rp + 8 * Z.of_nat (length (pre ++ [addw x 1]))))) ltac:(f_equal; unfold shad; rewrite length_app; cbn [length]; clear; Z.div_mod_to_equations; lia).
      eapply IHl; [exact I2 | apply Hfit'; exact K |].
      rewrite E. cbn [carry_up]. rewrite K. cbn [Z.eqb]. rewrite <- app_assoc. reflexivity.
    - eapply B_epi; [exact I2|].
      rewrite E. cbn [carry_up]. destruct (Z.eqb_spec (addw x 1) 0) as [E0|_]; [contradiction|]. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma geom : (8 <= N <= 33554432 /\ 0 <= lo /\ lo <= SP - 176 - SK /\ 65536 <= SK /\ CS8 <= SK /\ 0 <= CS8 /\
                Z.of_nat (4 * n + scratch_rec k') <= Z.of_nat nT /\ Z.of_nat da <= 1 /\ Z.of_nat db <= 1 /\
                Z.of_nat (length a) = 2 * N - Z.of_nat da /\ Z.of_nat (length b) = 2 * N - Z.of_nat db)%Z.
  Proof.
    pose proof Hn8. pose proof HnB. pose proof LO. pose proof LO0. pose proof SK_ge. pose proof HnT. pose proof Hda. pose proof Hdb.
    pose proof HLA. pose proof HLB. lia.
  Qed.

  Ltac ret_even := apply ret_pc_even; [lia | reflexivity].
  Ltac ulit := first [ reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; lia); lia | lia ].

  Ltac kacc I G := first
    [ eapply (KACC KB_accRz _ _ _ _ _ _ I); clear - G; lia
    | eapply (KACC KB_accTz _ _ _ _ _ _ I); clear - G; lia
    | eapply (KACC KB_accaz _ _ _ _ _ _ I); clear - G; lia
    | eapply (KACC KB_accbz _ _ _ _ _ _ I); clear - G; lia ].
  Ltac kal8 := repeat apply mod8_add8; apply AL8.
  Ltac kapt I G := first
    [ eapply (KACC KB_aptR _ _ _ _ _ _ _ _ I); [kal8 | kal8 | kal8 | clear - G; lia]
    | eapply (KACC KB_aptT _ _ _ _ _ _ _ _ I); [kal8 | kal8 | kal8 | clear - G; lia] ].
  Ltac klen := repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end.
  Ltac kasan I G := klen; split; [kacc I G|]; split; [kacc I G|]; split; [kacc I G|]; kapt I G.

  Ltac kpos8 I G := let P := fresh "P4" in
    pose proof (KACC KB_pos _ _ _ _ I) as P;
    split; [clear - P G; lia|]; split; [clear - P G; lia|]; split; [clear - P G; lia|];
    first [ eapply (KACC KB_offiR _ _ _ _ _ _ I); clear - G; lia | eapply (KACC KB_offiT _ _ _ _ _ _ I); clear - G; lia ].
  Ltac kasan8 I G := klen; split; [kacc I G|]; split; [kacc I G|]; split; [kacc I G|]; split; [kapt I G|]; kpos8 I G.

  Lemma B_fin : forall jb v152 v128 m1 R T c12 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x26 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb v152 v128) m1 R T -> kc3_ok RES n R T c12 -> (-1 <= c12 <= 2)%Z ->
    evt bgasegs POST (ST F fc 0x229ffc m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c12) x24 (Z_to_bv 64 SHB) x26 (Z_to_bv 64 N) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK Hc12.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ n (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    do 6 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply call_add_wordsK with (a := slice R n (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -176)%Z)
                               (RP := (rp + 8 * N)%Z) (AP := (rp + 8 * N)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | exact LRa | exact LTb | rewrite ERa, ETb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa, A3; clear; lia
      | exact HRa | exact HTb | rewrite ERa; exact WRa
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D3 G; lia | kasan I G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LTb ltac:(rewrite ERa, ETb; reflexivity)) as SP3.
    unfold kc3_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R n (2 * n)) (slice T (2 * n) (2 * n))) as [sg3 cy3]. cbn [fst snd] in *.
    destruct SP3 as (Ls3 & Es3 & Hc3 & _). rewrite ERa in Es3. destruct OK as (ERES & Hc & FIT).
    pose proof (KAFTER KB_after_R (FCELLS jb v152 v128) m1 m2 R T n sg3 _ 48%Z eq_refl I MUc ltac:(rewrite ERa, Es3; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls3 ltac:(rewrite Es3; clear; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa WRa HTb LTb ETb MUc WMc HS I D1 D2 D3 HEAP.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_mod c12 cy3) by (clear - Hc12 Hc3; lia).
    zstep. if_cases K; zify_cond K.
    { eapply B_epi; [exact I2|]. rewrite ERES. rewrite K. reflexivity. }
    specialize (FIT K). destruct (Z.eqb_spec (c12 + cy3) 0) as [E0|_]; [contradiction|].
    do 2 zstep. rewrite A3, (bn_swrap32_small (N + 2 * N)) by (clear - G; lia).
    zstep.

    remember (splice R n sg3) as R' eqn:ER'. pose proof ER as ERl.
    assert (Lpre : length (firstn (n + 2 * n) R') = (n + 2 * n)%nat) by (rewrite length_firstn; clear - ER; lia).
    destruct (skipn (n + 2 * n) R') as [|x l'] eqn:Esk.
    { exfalso. pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. clear - HH ER G. lia. }
    assert (ERpl : R' = firstn (n + 2 * n) R' ++ x :: l') by (rewrite <- Esk; symmetry; apply firstn_skipn).
    remember (firstn (n + 2 * n) R') as pre eqn:Epre.
    rewrite ERpl in I2, HR, LR. clear ERpl.
    pose proof (limbs_cons_lit x l' (proj2 (limbs_app_inv _ _ LR))) as (Hx & Ll').
    setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre)))
      ltac:(f_equal; rewrite land_m64, Z.mod_small by (clear - G; lia); rewrite Z.shiftl_mul_pow2 by lia; rewrite Lpre; clear; lia).
    pose proof (KACC KB_bounds _ _ _ _ I2 ltac:(clear - G; lia) ltac:(clear - G; lia)) as (BR0 & BR1 & _).
    assert (Hi : (length pre < 4 * n)%nat) by (rewrite Lpre; clear - G; lia).
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shR_rd _ m2 _ T (length pre) ad I2 Hi (conj BR0 BR1) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    ld_hd HR2.
    zstep.
    setreg 11%Z (Z_to_bv 64 (addw x (c12 + cy3))) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE (FCELLS jb v152 v128) m2 (pre ++ x :: l') T (length pre) (addw x (c12 + cy3)) eq_refl I2 Hi (addw_limb _ _)) as (SOK0 & I3).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI MU WM I2 MIc STc HEAP BR0 BR1.
    kb_store SOK0 I3. rewrite upd_app_mid in I3.
    pose proof (addw_limb x (c12 + cy3)) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K2; zify_cond K2.
    - eapply B_epi; [exact I3|]. rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx).
      destruct (Z.ltb_spec (addw x (c12 + cy3)) x) as [HH|_]; [exfalso; clear - HH K2; lia|]. rewrite <- app_assoc. reflexivity.
    - do 4 zstep.
      setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x (c12 + cy3)])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      setreg 12%Z (Z_to_bv 64 (shad (rp + 8 * Z.of_nat (length (pre ++ [addw x (c12 + cy3)])))))
        ltac:(f_equal; unfold shad; rewrite length_app; cbn [length]; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; Z.div_mod_to_equations; lia).
      assert (TST : (addw x (c12 + cy3) <? x) = true) by (apply Z.ltb_lt; clear - K2; lia).
      eapply B_loop; [exact I3 | |].
      + eapply (add_carry_fit x l' (c12 + cy3)); [rewrite BW_lit; exact Hx | exact Ll' | rewrite BW_lit; clear - Hc; lia | | exact TST].
        replace (S (length l')) with n; [exact FIT|].
        pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. rewrite HH, ERl. clear. lia.
      + rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx). rewrite TST. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma B_sub : forall jb v152 v128 m1 R T c1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x26 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb v152 v128) m1 R T -> kc2_ok RES n true R T c1 -> (0 <= c1 <= 1)%Z ->
    evt bgasegs POST (ST F fc 0x229f28 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c1) x24 (Z_to_bv 64 SHB) x26 (Z_to_bv 64 N) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    do 5 zstep.
    pose proof SEPT as D3.
    eapply call_sub_wordsK with (a := slice T 0 (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -176)%Z)
                               (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | exact LTa | exact LTb | rewrite ETa, ETb; reflexivity
      | rewrite ETa; clear - G; lia | ulit | ulit | ulit | rewrite ETa, A3; clear; lia
      | exact HTa | exact HTb | rewrite ETa; exact WTb
      | unfold alias_ok; rewrite ETa; clear; lia | unfold alias_ok; left; reflexivity
      | clear - G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia | kasan I G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (sub_words_spec _ _ LTa LTb ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (sub_words (slice T 0 (2 * n)) (slice T (2 * n) (2 * n))) as [sg2 bw]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hbw & _). rewrite ETa in Es2.
    pose proof (KAFTER KB_after_T (FCELLS jb v152 v128) m1 m2 R T (2 * n)%nat sg2 _ 48%Z eq_refl I MUc ltac:(rewrite ETa, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep. rewrite (bn_swrap32_small (c1 - bw)) by (clear - Hc1 Hbw; lia).
    zstep.
    eapply B_fin; [exact I2 | exact OK | clear - Hc1 Hbw; lia].
  Qed.

  Lemma B_add : forall jb v152 v128 m1 R T c1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x26 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb v152 v128) m1 R T -> kc2_ok RES n false R T c1 -> (0 <= c1 <= 1)%Z ->
    evt bgasegs POST (ST F fc 0x229fe4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c1) x24 (Z_to_bv 64 SHB) x26 (Z_to_bv 64 N) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    do 5 zstep.
    pose proof SEPT as D3.
    eapply call_add_wordsK with (a := slice T (2 * n) (2 * n)) (b := slice T 0 (2 * n)) (lo := lo) (SPz := (SP + -176)%Z)
                               (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat (2 * n))%Z) (BP := (tq + 8 * Z.of_nat 0)%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | exact LTb | exact LTa | rewrite ETa, ETb; reflexivity
      | rewrite ETb; clear - G; lia | ulit | ulit | ulit | rewrite ETb, A3; clear; lia
      | exact HTb | exact HTa | rewrite ETb; exact WTb
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ETb; clear; lia
      | clear - G; lia | rewrite ETb; clear - D3 G; lia | rewrite ETb; clear - D3 G; lia | rewrite ETb; clear - D3 G; lia | kasan I G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LTb LTa ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (add_words (slice T (2 * n) (2 * n)) (slice T 0 (2 * n))) as [sg2 cy]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hcy & _). rewrite ETb in Es2.
    pose proof (KAFTER KB_after_T (FCELLS jb v152 v128) m1 m2 R T (2 * n)%nat sg2 _ 48%Z eq_refl I MUc ltac:(rewrite ETb, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep.
    eapply B_fin; [exact I2 | exact OK | clear - Hc1 Hcy; lia].
  Qed.
  Notation a_lo := (firstn n a).
  Notation a_hi := (slice a n (n - da)).
  Notation b_lo := (firstn n b).
  Notation b_hi := (slice b n (n - db)).

  Ltac first_add I OK G BND jb v152 v128 Inew :=
    let HRa := fresh "HRa" in let LRa := fresh "LRa" in let ERa := fresh "ERa" in
    let HRb := fresh "HRb" in let LRb := fresh "LRb" in let ERb := fresh "ERb" in
    let WTa := fresh "WTa" in let D1 := fresh "D1" in let D2 := fresh "D2" in let D3 := fresh "D3" in
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & _);
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear; lia)) as (HRb & LRb & ERb & _);
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (_ & _ & _ & WTa);
    pose proof DRT as D1; pose proof SEPR as D2; pose proof SEPT as D3;
    lazymatch goal with ST : stk bgasegs ?m1 lo _, MI : mem_inv bgasegs ?m1 |- _ =>
    eapply call_add_wordsK with (a := slice _ 0 (2 * n)) (b := slice _ (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -176)%Z)
                               (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (rp + 8 * Z.of_nat 0)%Z) (BP := (rp + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | exact LRa | exact LRb | rewrite ERa, ERb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa, A3; clear; lia
      | exact HRa | exact HRb | rewrite ERa; exact WTa
      | unfold alias_ok; rewrite ERa; clear - D1 G; lia | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D3 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia | kasan I G | ];
    let m4 := fresh "m" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIc" in
    let HS := fresh "HS" in let STc := fresh "STc" in let SP1 := fresh "SP1" in
    let sg1 := fresh "sg" in let cy1 := fresh "cy" in let Ls1 := fresh "Ls" in let Es1 := fresh "Es" in let Hc1 := fresh "Hcy" in
    intros m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MUc WMc MIc HS STc;
    pose proof (add_words_spec _ _ LRa LRb ltac:(rewrite ERa, ERb; reflexivity)) as SP1;
    unfold kc_ok in OK; cbv zeta in OK;
    lazymatch type of SP1 with (let '(_, _) := ?AW in _) => destruct AW as [sg1 cy1] end;
    cbn [fst snd] in *;
    destruct SP1 as (Ls1 & Es1 & Hc1 & _); rewrite ERa in Es1;
    pose proof (KAFTER KB_after_T (FCELLS jb v152 v128) m1 m4 _ _ 0%nat sg1 _ 48%Z eq_refl I MUc ltac:(rewrite ERa, Es1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls1 ltac:(rewrite Es1; clear - G; lia)) as Inew;
    clear HRa LRa ERa HRb LRb ERb WTa D1 D2 D3 MUc WMc HS MIc STc
    end.

  Lemma B_comba : forall (neg : bool) jb v152 v128 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x29 x30 x31 F fc,
    n = 8%nat -> da = 0%nat -> db = 0%nat ->
    KBK (FCELLS jb v152 v128) m1 R T ->
    kc_ok RES n neg (splice (splice R 0 (mul_comba8 a_lo b_lo)) (2 * n) (mul_comba8 a_hi b_hi)) T ->
    evt bgasegs POST (ST F fc 0x229ee4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 (Z_to_bv 64 (if neg then 0 else 1)) (Z_to_bv 64 SHB) x26 (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros En Eda Edb I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G. pose proof (conj G (conj En (conj Eda Edb))) as G2.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat 16%nat I ltac:(clear - En; lia)) as (_ & _ & _ & WRa).
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HBl.
    do 4 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof SEPR as D3. pose proof SEPA as D4. pose proof SEPB as D5.
    assert (Lal : length a_lo = 8%nat) by (rewrite length_firstn; clear - G En; lia).
    assert (Lbl : length b_lo = 8%nat) by (rewrite length_firstn; clear - G En; lia).
    eapply call_comba8A with (CS8 := CS8) (a := a_lo) (b := b_lo) (lo := lo) (SPz := (SP + -176)%Z)
                            (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | exact comba8_ok | apply limbs_firstn; exact LA | apply limbs_firstn; exact LB'
      | exact Lal | exact Lbl | ulit | ulit | ulit | exact HAl | exact HBl | exact WRa
      | clear - D1 G En; lia | clear - D2 G En; lia | clear - G; lia
      | clear - D3 G En; lia | clear - D4 G En; lia | clear - D5 G En; lia | kasan8 I G2 | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (mul_comba8_spec a_lo b_lo (limbs_firstn _ _ LA) (limbs_firstn _ _ LB') Lal Lbl) as (Lc1 & Ec1 & _).
    pose proof (KAFTER KB_after_R (FCELLS jb v152 v128) m1 m2 R T 0%nat (mul_comba8 a_lo b_lo) _ CS8 eq_refl I MUc ltac:(rewrite Ec1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc1 ltac:(rewrite Ec1; clear - En; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP WRa HAl HBl MUc WMc HS I MIc STc.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat 16%nat I2 ltac:(clear - En; lia)) as (_ & _ & _ & WRb).
    pose proof (KACC KB_a _ _ _ _ n (n - da)%nat I2 ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n (n - db)%nat I2 ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = 8%nat) by (rewrite slice_length; clear - G En Eda; lia).
    assert (Lbh : length b_hi = 8%nat) by (rewrite slice_length; clear - G En Edb; lia).
    do 5 zstep.
    eapply call_comba8A with (CS8 := CS8) (a := a_hi) (b := b_hi) (lo := lo) (SPz := (SP + -176)%Z)
                            (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | exact comba8_ok | apply slice_limbs; exact LA | apply slice_limbs; exact LB'
      | exact Lah | exact Lbh | ulit | ulit | ulit | exact HAh | exact HBh | exact WRb
      | clear - D1 G En Eda; lia | clear - D2 G En Edb; lia | clear - G; lia
      | clear - D3 G En; lia | clear - D4 G En Eda; lia | clear - D5 G En Edb; lia | kasan8 I2 G2 | ].
    intros m3 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HS STc.
    destruct (mul_comba8_spec a_hi b_hi (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB') Lah Lbh) as (Lc2 & Ec2 & _).
    pose proof (KAFTER KB_after_R (FCELLS jb v152 v128) m2 m3 _ T (2 * n)%nat (mul_comba8 a_hi b_hi) _ CS8 eq_refl I2 MUc ltac:(rewrite Ec2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc2 ltac:(rewrite Ec2; clear - En; lia)) as I3.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP WRb HAh HBh MUc WMc HS I2 MIc STc D1 D2 D3 D4 D5.
    pose proof I3 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    do 5 zstep.
    remember (splice (splice R 0 (mul_comba8 a_lo b_lo)) (2 * n) (mul_comba8 a_hi b_hi)) as R2 eqn:ER2. clear ER2.
    first_add I3 OK G BND jb v152 v128 I4.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM I3 HEAP.
    pose proof I4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
    do 2 zstep.
    destruct neg.
    - zstep. if_false. eapply B_sub; [exact I4 | exact OK | assumption].
    - zstep. if_true. eapply B_add; [exact I4 | exact OK | assumption].
  Qed.

  Lemma pow_n : Nat.pow 2 k' = n. Proof. symmetry. exact Hn. Qed.

  Ltac kin := first [ exact INR | exact INT | exact INA | exact INB | apply in_or_app; left; first [exact INR | exact INT] ].
  Ltac krng G := let r := fresh in let t := fresh in let a' := fresh in let b' := fresh in
    pose proof RGR as r; pose proof RGT as t; pose proof RGA as a'; pose proof RGB as b'; clear - G r t a' b'; lia.
  Ltac kblocks G := klen; unfold kara_blocks; split; [kin|]; split; [kin|]; split; [kin|]; split; [kin|];
    split; [krng G|]; split; [krng G|]; split; [krng G|]; split; [krng G|];
    split; [kal8|]; split; [kal8|]; split; [kal8|]; kal8.
  Ltac kaside HEAP G :=
    split; [exact HEAP|]; split; [kblocks G|]; split; [exact CEIL|];
    split; [pose proof SPT16 as s16; clear - s16; lia|];
    split; [pose proof SP16 as s16; clear - s16; Z.div_mod_to_equations; lia | exact ETP].

  Lemma B_gen : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb (Z_to_bv 64 (bp + 8 * N)) (Z_to_bv 64 (if neg then 0 else 1))) m1 R T ->
    gen2_ok RES k' n neg a b da db R T ->
    evt bgasegs POST (ST F fc 0x229f7c m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5 a4
                       (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 N) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HBl.
    assert (Lal : length a_lo = n) by (rewrite length_firstn; clear - G; lia).
    assert (Lbl : length b_lo = n) by (rewrite length_firstn; clear - G; lia).
    do 8 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9. pose proof Hk' as HK.
    eapply call_recA with (CS8 := CS8) (k := k') (a := a_lo) (b := b_lo) (da := 0%nat) (db := 0%nat) (R := slice R 0 (2 * n)) (T := skipn (4 * n) T)
                         (lo := lo) (SPz := (SP + -176)%Z) (bR := bR) (bT := bT) (bA := bA) (bB := bB)
                         (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact IH
      | apply limbs_firstn; exact LA | apply limbs_firstn; exact LB' | exact LRa | exact LTp
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
      | kaside HEAP G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k' a_lo b_lo 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T) (limbs_firstn _ _ LA) (limbs_firstn _ _ LB') LRa LTp
                  ltac:(clear - HK; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(rewrite Lal, pow_n; clear; lia) ltac:(rewrite Lbl, pow_n; clear; lia) ltac:(rewrite ERa, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G; lia)) as MP.
    unfold mul_post in MP. unfold gen2_ok in OK.
    destruct (mul_recursive k' a_lo b_lo 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T)) as [rl p1]. cbn [fst snd] in *.
    destruct MP as (Lrl & Erl & _ & Lp1 & Ep1). rewrite ERa in Erl. rewrite ETp in Ep1.
    assert (I2 : KBK (FCELLS jb (Z_to_bv 64 (bp + 8 * N)) (Z_to_bv 64 (if neg then 0 else 1))) m2 (splice R 0 rl) (splice T (4 * n) p1)).
    { eapply (KK KB_cps) with (m1 := m1);
        [ reflexivity | exact I | exact HEAPc | rewrite Erl, Ep1; rewrite ERa, ETp in AGc; exact AGc | exact WMc | exact MIc | exact STc
        | exact Lrl | exact Lp1 | rewrite Erl; clear; lia | rewrite Ep1; clear - G; lia | exact HSR | exact HST ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HRa LRa ERa WRa HTp LTp ETp WTp HAl HBl HEAPc AGc WMc HSR HST MIc STc I.
    remember (splice R 0 rl) as R1 eqn:ER1. remember (splice T (4 * n) p1) as T1 eqn:ET1. clear ER1 ET1 Lrl Erl Lp1 Ep1.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I2 ltac:(clear; lia)) as (HRb & LRb & ERb & WRb).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I2 ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n (n - da)%nat I2 ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n (n - db)%nat I2 ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = (n - da)%nat) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = (n - db)%nat) by (rewrite slice_length; clear - G; lia).
    do 9 zstep.
    pose proof Hda as HDA. pose proof Hdb as HDB.
    eapply call_recA with (CS8 := CS8) (k := k') (a := a_hi) (b := b_hi) (da := da) (db := db) (R := slice R1 (2 * n) (2 * n)) (T := skipn (4 * n) T1)
                         (lo := lo) (SPz := (SP + -176)%Z) (bR := bR) (bT := bT) (bA := bA) (bB := bB)
                         (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact IH
      | apply slice_limbs; exact LA | apply slice_limbs; exact LB' | exact LRb | exact LTp
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
      | kaside HEAP G | ].
    intros m3 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' F3 fc3 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k' a_hi b_hi da db (slice R1 (2 * n) (2 * n)) (skipn (4 * n) T1) (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB') LRb LTp
                  ltac:(clear - HK; lia) HDA HDB
                  ltac:(rewrite Lah, pow_n; reflexivity) ltac:(rewrite Lbh, pow_n; reflexivity) ltac:(rewrite ERb, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G; lia)) as MP.
    unfold mul_post in MP. unfold gen3_ok in OK.
    destruct (mul_recursive k' a_hi b_hi da db (slice R1 (2 * n) (2 * n)) (skipn (4 * n) T1)) as [rh p2]. cbn [fst snd] in *.
    destruct MP as (Lrh & Erh & _ & Lp2 & Ep2). rewrite ERb in Erh. rewrite ETp in Ep2.
    assert (I3 : KBK (FCELLS jb (Z_to_bv 64 (bp + 8 * N)) (Z_to_bv 64 (if neg then 0 else 1))) m3 (splice R1 (2 * n) rh) (splice T1 (4 * n) p2)).
    { eapply (KK KB_cps) with (m1 := m2);
        [ reflexivity | exact I2 | exact HEAPc | rewrite Erh, Ep2; rewrite ERb, ETp in AGc; exact AGc | exact WMc | exact MIc | exact STc
        | exact Lrh | exact Lp2 | rewrite Erh; clear; lia | rewrite Ep2; clear - G; lia | exact HSR | exact HST ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HRb LRb ERb WRb HTp LTp ETp WTp HAh HBh HEAPc AGc WMc HSR HST MIc STc I2.
    clear D1 D2 D3 D4 D5 D6 D7 D8 D9 HK HDA HDB.
    remember (splice R1 (2 * n) rh) as R2 eqn:ER2. remember (splice T1 (4 * n) p2) as T2 eqn:ET2. clear ER2 ET2 Lrh Erh Lp2 Ep2.
    pose proof I3 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    do 5 zstep.
    first_add I3 OK G BND jb (Z_to_bv 64 (bp + 8 * N)) (Z_to_bv 64 (if neg then 0 else 1)) I4.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM I3 HEAP.
    pose proof I4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
    do 3 zstep.
    destruct neg.
    - zstep. if_true. eapply B_sub; [exact I4 | exact OK | assumption].
    - zstep. if_false. eapply B_add; [exact I4 | exact OK | assumption].
  Qed.

  Lemma B_join_gen : forall (neg : bool) jb v152 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb v152 (Z_to_bv 64 (if neg then 0 else 1))) m1 R T ->
    (let '(tm, p0) := mul_recursive k' (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) in
     gen2_ok RES k' n neg a b da db R (splice T (2 * n) (tm ++ p0))) ->
    evt bgasegs POST (ST F fc 0x229f44 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5 a4 x26 (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I0 OK.
    pose proof I0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & ST & MI & _).
    pose proof (munch_refl [(SP + -176, SP + -176 + 176)]%Z m1) as MUF. pose proof (wmono_refl bgasegs m1) as WMF.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (KFRAME _ _ m1 mm R T I0 MUF WMF MI ST FR) as I end.
    clear I0 FR ST MI MUF WMF. try clear m1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    zstep. rewrite A3.
    replace ((2 * N) ≪ 1)%Z with (4 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    rewrite (bn_swrap32_small (4 * N)) by (clear - G; lia).
    do 3 zstep.
    setreg 26%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) ltac:(f_equal; rewrite ?land_m64, ?Z.shiftl_mul_pow2 by lia; clear - G; lia).
    do 9 zstep.
    pose proof SEPT as D7. pose proof Hk' as HK.
    eapply call_recA with (CS8 := CS8) (k := k') (a := slice T 0 n) (b := slice T n n) (da := 0%nat) (db := 0%nat)
                         (R := slice T (2 * n) (2 * n)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -176)%Z)
                         (bR := bT) (bT := bT) (bA := bT) (bB := bT)
                         (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact IH
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
      | kaside HEAP G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k' (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) LTa LTb LTr LTp
                  ltac:(clear - HK; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(rewrite ETa, pow_n; clear; lia) ltac:(rewrite ETb, pow_n; clear; lia) ltac:(rewrite ETr, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G; lia)) as MP.
    unfold mul_post in MP.
    destruct (mul_recursive k' (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T)) as [tm p0]. cbn [fst snd] in *.
    destruct MP as (Ltm & Etm & _ & Lp0 & Ep0). rewrite ETr in Etm. rewrite ETp in Ep0.
    assert (I2 : KBK (FCELLS jb (Z_to_bv 64 (bp + 8 * N)) (Z_to_bv 64 (if neg then 0 else 1))) m2 R (splice T (2 * n) (tm ++ p0))).
    { eapply (KK KB_cps_TT);
        [ reflexivity | exact I | exact HEAPc | rewrite Etm, Ep0; rewrite ETr, ETp in AGc; exact AGc | rewrite Etm; clear; lia
        | exact WMc | exact MIc | exact STc | exact Ltm | exact Lp0 | rewrite Ep0; clear - G; lia | exact HSR | exact HST ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HTa LTa ETa HTb LTb ETb HTr LTr ETr WTr HTp LTp ETp WTp HEAPc AGc WMc HSR HST MIc STc I D7 HK.
    eapply B_gen; [exact I2 | exact OK].
  Qed.

  Lemma B_join : forall (neg : bool) jb v152 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb v152 (Z_to_bv 64 (if neg then 0 else 1))) m1 R T ->
    join_ok RES k' n neg a b da db R T ->
    evt bgasegs POST (ST F fc 0x229eb0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5 a4
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 3 zstep. rewrite A3, land_even31 by (clear - G; lia).
    do 1 zstep.
    zstep. if_cases K1; zify_cond K1.
    { eapply B_join_gen; [exact I|]. unfold join_ok in OK.
      destruct (Nat.eqb_spec n 8) as [E8|_]; [exfalso; clear - E8 K1; lia|]. exact OK. }
    zstep. if_cases K2; zify_cond K2.
    { eapply B_join_gen; [exact I|]. unfold join_ok in OK.
      destruct (Nat.eqb_spec da 0) as [Ea|_]; [destruct (Nat.eqb_spec db 0) as [Eb|_]|]; rewrite ?andb_false_r in OK; cbn [andb] in OK; try exact OK.
      exfalso. apply K2. rewrite A4, A5. apply lor_neg_zero; [exact Hda | exact Hdb | split; assumption]. }
    assert (En : n = 8%nat) by (clear - K1; lia).
    assert (Ed : (da = 0 /\ db = 0)%nat) by (rewrite A4, A5 in K2; apply lor_neg_zero in K2; [exact K2 | exact Hda | exact Hdb]).
    destruct Ed as (Eda & Edb).
    unfold join_ok in OK. rewrite (proj2 (Nat.eqb_eq n 8) En), (proj2 (Nat.eqb_eq da 0) Eda), (proj2 (Nat.eqb_eq db 0) Edb) in OK. cbn [andb] in OK.
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat 16%nat I ltac:(clear - G En; lia)) as (_ & _ & _ & WTr).
    do 5 zstep.
    pose proof SEPT as D7. pose proof (conj G En) as G2.
    eapply call_comba8A with (CS8 := CS8) (a := slice T 0 n) (b := slice T n n) (lo := lo) (SPz := (SP + -176)%Z)
                            (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * N)%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | exact comba8_ok | exact LTa | exact LTb
      | rewrite ETa; exact En | rewrite ETb; exact En | ulit | ulit | ulit | exact HTa | exact HTb | exact WTr
      | clear - G En; lia | clear - G En; lia | clear - G; lia
      | clear - D7 G En; lia | clear - D7 G En; lia | clear - D7 G En; lia | kasan8 I G2 | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (mul_comba8_spec (slice T 0 n) (slice T n n) LTa LTb ltac:(rewrite ETa; exact En) ltac:(rewrite ETb; exact En)) as (Lc & Ec & _).
    pose proof (KAFTER KB_after_T (FCELLS jb v152 (Z_to_bv 64 (if neg then 0 else 1))) m1 m2 R T (2 * n)%nat _ _ CS8 eq_refl I MUc ltac:(rewrite Ec; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc ltac:(rewrite Ec; clear - G En; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HTa LTa ETa HTb LTb ETb WTr MUc WMc HS MIc STc I D7.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    do 2 zstep.
    eapply B_comba; [exact En | exact Eda | exact Edb | exact I2 | exact OK].
  Qed.

  Lemma ms_stack : (lo + RT_STACK <= SP + -176 /\ SP + -176 + 16 <= USTACK_TOP /\ (SP + -176) mod 16 = 0)%Z.
  Proof.
    pose proof geom as G. pose proof SPT16 as S1. pose proof SP16 as S2. unfold RT_STACK.
    split; [clear - G; lia|]. split; [clear - S1; lia|]. clear - S2. Z.div_mod_to_equations. lia.
  Qed.

  Lemma B_zero_gen : forall jb v152 v128 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb v152 v128) m1 R T ->
    gen2_ok RES k' n false a b da db R (splice T (2 * n) (repeat 0%Z (2 * n))) ->
    evt bgasegs POST (ST F fc 0x229da8 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5 a4 x26 (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I0 OK.
    pose proof I0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & ST & MI & _).
    pose proof (munch_refl [(SP + -176, SP + -176 + 176)]%Z m1) as MUF. pose proof (wmono_refl bgasegs m1) as WMF.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (KFRAME _ _ m1 mm R T I0 MUF WMF MI ST FR) as I end.
    clear I0 FR ST MI MUF WMF. try clear m1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
    zstep. rewrite A3.
    replace ((2 * N) ≪ 1)%Z with (4 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    rewrite (bn_swrap32_small (4 * N)) by (clear - G; lia).
    do 2 zstep.
    setreg 26%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) ltac:(f_equal; rewrite ?land_m64, ?Z.shiftl_mul_pow2 by lia; clear - G; lia).
    do 4 zstep.
    pose proof ms_stack as (MS1 & MS2 & MS3). pose proof RGT as RT'.
    eapply call_memset0A with (L := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -176)%Z) (D := (tq + 8 * Z.of_nat (2 * n))%Z) (bd := bT);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact HEAP | exact CEIL | exact MS1 | exact MS2 | exact MS3 | exact ETP
      | apply in_or_app; left; exact INT | clear - RT' G; lia | rewrite ETr; clear - RT' G; lia | rewrite ETr; clear - G; lia
      | ulit | reflexivity | rewrite ETr; ulit | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HZ STc.
    rewrite ETr in HZ, AGc.
    assert (I2 : KBK (FCELLS jb (Z_to_bv 64 (bp + 8 * N)) v128) m2 R (splice T (2 * n) (repeat 0%Z (2 * n)))).
    { eapply (KK KB_cps_T);
        [ reflexivity | exact I | exact HEAPc | rewrite repeat_length; exact AGc | exact WMc | exact MIc | exact STc
        | exact (limbs_repeat _ _ limb_0) | rewrite repeat_length; clear - G; lia | exact HZ ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HTr LTr ETr WTr HEAPc AGc WMc HZ MIc STc I MS1 MS2 MS3 RT'.
    pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & ST & MI & _).
    pose proof (munch_refl [(SP + -176, SP + -176 + 176)]%Z m2) as MUF. pose proof (wmono_refl bgasegs m2) as WMF.
    do 2 zstep. change (Z_to_le_bytes 8 1) with (le8 (Z_to_bv 64 1)). mem_after_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (KFRAME _ _ m2 mm R (splice T (2 * n) (repeat 0%Z (2 * n))) I2 MUF WMF MI ST FR) as I3 end.
    clear I2 MUF WMF MI ST.
    do 2 zstep.
    eapply (B_gen false); [exact I3 | exact OK].
  Qed.

  Lemma B_zero : forall jb v152 v128 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb v152 v128) m1 R T ->
    zero_ok RES k' n a b da db R T ->
    evt bgasegs POST (ST F fc 0x229d78 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5 a4
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 3 zstep. rewrite A3, land_even31 by (clear - G; lia).
    do 1 zstep.
    zstep. if_cases K1; zify_cond K1.
    { eapply B_zero_gen; [exact I|]. unfold zero_ok in OK.
      destruct (Nat.eqb_spec n 8) as [E8|_]; [exfalso; clear - E8 K1; lia|]. exact OK. }
    zstep. if_cases K2; zify_cond K2.
    { eapply B_zero_gen; [exact I|]. unfold zero_ok in OK.
      destruct (Nat.eqb_spec da 0) as [Ea|_]; [destruct (Nat.eqb_spec db 0) as [Eb|_]|]; rewrite ?andb_false_r in OK; cbn [andb] in OK; try exact OK.
      exfalso. apply K2. rewrite A4, A5. apply lor_neg_zero; [exact Hda | exact Hdb | split; assumption]. }
    assert (En : n = 8%nat) by (clear - K1; lia).
    assert (Ed : (da = 0 /\ db = 0)%nat) by (rewrite A4, A5 in K2; apply lor_neg_zero in K2; [exact K2 | exact Hda | exact Hdb]).
    destruct Ed as (Eda & Edb).
    unfold zero_ok in OK. rewrite (proj2 (Nat.eqb_eq n 8) En), (proj2 (Nat.eqb_eq da 0) Eda), (proj2 (Nat.eqb_eq db 0) Edb) in OK. cbn [andb] in OK.
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
    do 4 zstep.
    pose proof ms_stack as (MS1 & MS2 & MS3). pose proof RGT as RT'.
    eapply call_memset0A with (L := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -176)%Z) (D := (tq + 8 * Z.of_nat (2 * n))%Z) (bd := bT);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact HEAP | exact CEIL | exact MS1 | exact MS2 | exact MS3 | exact ETP
      | apply in_or_app; left; exact INT | clear - RT' G; lia | rewrite ETr; clear - RT' G; lia | rewrite ETr; clear - G; lia
      | ulit | reflexivity | rewrite ETr, En; reflexivity | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HZ STc.
    rewrite ETr in HZ, AGc.
    assert (I2 : KBK (FCELLS jb v152 v128) m2 R (splice T (2 * n) (repeat 0%Z (2 * n)))).
    { eapply (KK KB_cps_T);
        [ reflexivity | exact I | exact HEAPc | rewrite repeat_length; exact AGc | exact WMc | exact MIc | exact STc
        | exact (limbs_repeat _ _ limb_0) | rewrite repeat_length; clear - G; lia | exact HZ ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HTr LTr ETr WTr HEAPc AGc WMc HZ MIc STc I MS1 MS2 MS3 RT'.
    pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
    do 3 zstep.
    eapply (B_comba false); [exact En | exact Eda | exact Edb | exact I2 | exact OK].
  Qed.

  Notation t1_of sw := (fst (if sw then sub_part_words b_hi b_lo (n - db) else sub_part_words b_lo b_hi (n - db))).

  Ltac sp2_call I G BND sw :=
    let HBl := fresh "HBl" in let HBh := fresh "HBh" in let WTn := fresh "WTn" in
    let D4 := fresh "D4" in let D7 := fresh "D7" in let D9 := fresh "D9" in
    pose proof (KACC KB_b _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HBl;
    pose proof (KACC KB_b _ _ _ _ n (n - db)%nat I ltac:(clear - G; lia)) as HBh;
    destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (_ & _ & _ & WTn);
    pose proof DTB as D4; pose proof SEPT as D7; pose proof SEPB as D9;
    assert (length b_lo = n) by (rewrite length_firstn; clear - G; lia);
    assert (length b_hi = (n - db)%nat) by (rewrite slice_length; clear - G; lia);
    lazymatch goal with ST : stk bgasegs ?m1 lo _, MI : mem_inv bgasegs ?m1 |- _ =>
    lazymatch sw with
    | false =>
      eapply call_sub_part_wordsA with (a := b_lo) (b := b_hi) (cl := (n - db)%nat) (da := db) (db := 0%nat) (lo := lo) (SPz := (SP + -176)%Z)
                                      (RP := (tq + 8 * N)%Z) (AP := (bp + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * N)%Z);
        [ exact ESP176 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | apply limbs_firstn; exact LB' | apply slice_limbs; exact LB'
        | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | f_equal; clear; lia
        | exact HBl | exact HBh | replace (n - db + db + 0)%nat with n by (clear - G; lia); exact WTn
        | rewrite length_firstn; clear - D4 G; lia | rewrite slice_length by (clear - G; lia); clear - D4 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite length_firstn; clear - D9 G; lia | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | kasan I G | ]
    | true =>
      eapply call_sub_part_wordsA with (a := b_hi) (b := b_lo) (cl := (n - db)%nat) (da := 0%nat) (db := db) (lo := lo) (SPz := (SP + -176)%Z)
                                      (RP := (tq + 8 * N)%Z) (AP := (bp + 8 * N)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
        [ exact ESP176 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | apply slice_limbs; exact LB' | apply limbs_firstn; exact LB'
        | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | rewrite A5; f_equal; clear; lia
        | exact HBh | exact HBl | replace (n - db + 0 + db)%nat with n by (clear - G; lia); exact WTn
        | rewrite slice_length by (clear - G; lia); clear - D4 G; lia | rewrite length_firstn; clear - D4 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | rewrite length_firstn; clear - D9 G; lia | kasan I G | ]
    end end.

  Lemma B_sp2_pos : forall (sw : bool) jb v152 m1 R T x1 x5 x6 x7 x15 x16 x17 x20 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb v152 (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n false a b da db R (splice T n (t1_of sw)) ->
    evt bgasegs POST (ST F fc 0x229eac m1 x1 x5 x6 x7 (Z_to_bv 64 (tq + 8 * N))
                       (if sw then Z_to_bv 64 (bp + 8 * N) else a2) (if sw then a2 else Z_to_bv 64 (bp + 8 * N))
                       (Z_to_bv 64 (N - Z.of_nat db)) (if sw then a5 else Z_to_bv 64 (Z.of_nat db))
                       x15 x16 x17 x20 a5 a4 (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct sw.
    - zstep. sp2_call I G BND true.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      destruct (sub_part_words_fst b_hi b_lo (n - db) (slice_limbs _ _ _ LB') (limbs_firstn _ _ LB')
                  ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
      rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
      pose proof (KAFTER KB_after_T (FCELLS jb v152 (Z_to_bv 64 1)) m1 m2 R T n _ _ 128%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      eapply (B_join false); [exact I2 | exact OK].
    - zstep. sp2_call I G BND false.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      destruct (sub_part_words_fst b_lo b_hi (n - db) (limbs_firstn _ _ LB') (slice_limbs _ _ _ LB')
                  ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
      rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
      pose proof (KAFTER KB_after_T (FCELLS jb v152 (Z_to_bv 64 1)) m1 m2 R T n _ _ 128%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      eapply (B_join false); [exact I2 | exact OK].
  Qed.

  Lemma B_sp2_neg : forall (sw : bool) jb v152 m1 R T x1 x5 x6 x7 x15 x16 x17 x20 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb v152 (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n true a b da db R (splice T n (t1_of sw)) ->
    evt bgasegs POST (ST F fc 0x229e70 m1 x1 x5 x6 x7 (Z_to_bv 64 (tq + 8 * N))
                       (if sw then Z_to_bv 64 (bp + 8 * N) else a2) (if sw then a2 else Z_to_bv 64 (bp + 8 * N))
                       (Z_to_bv 64 (N - Z.of_nat db)) (if sw then a5 else Z_to_bv 64 (Z.of_nat db))
                       x15 x16 x17 x20 a5 a4 (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    assert (CONT : forall m2 T' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
               KBK (FCELLS jb v152 (Z_to_bv 64 1)) m2 R T' -> join_ok RES k' n true a b da db R T' ->
               evt bgasegs POST (ST F fc 0x229e74 m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5 a4
                                  (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31)).
    { clear I OK. intros m2 T' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 I2 OK2.
      pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & ST & MI & _ & _).
      pose proof (munch_refl [(SP + -176, SP + -176 + 176)]%Z m2) as MUF. pose proof (wmono_refl bgasegs m2) as WMF.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (KFRAME _ _ m2 mm R T' I2 MUF WMF MI ST FR) as I3 end.
      zstep.
      eapply (B_join true); [exact I3 | exact OK2]. }
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct sw.
    - zstep. sp2_call I G BND true.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      destruct (sub_part_words_fst b_hi b_lo (n - db) (slice_limbs _ _ _ LB') (limbs_firstn _ _ LB')
                  ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
      rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
      pose proof (KAFTER KB_after_T (FCELLS jb v152 (Z_to_bv 64 1)) m1 m2 R T n _ _ 128%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      eapply CONT; [exact I2 | exact OK].
    - zstep. sp2_call I G BND false.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      destruct (sub_part_words_fst b_lo b_hi (n - db) (limbs_firstn _ _ LB') (slice_limbs _ _ _ LB')
                  ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
      rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
      pose proof (KAFTER KB_after_T (FCELLS jb v152 (Z_to_bv 64 1)) m1 m2 R T n _ _ 128%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      eapply CONT; [exact I2 | exact OK].
  Qed.

  Notation t0_of sw := (fst (if sw then sub_part_words a_hi a_lo (n - da) else sub_part_words a_lo a_hi (n - da))).

  Ltac sp1_call I G BND sw :=
    let HAl := fresh "HAl" in let HAh := fresh "HAh" in let WTn := fresh "WTn" in
    let D3 := fresh "D3" in let D7 := fresh "D7" in let D8 := fresh "D8" in
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl;
    pose proof (KACC KB_a _ _ _ _ n (n - da)%nat I ltac:(clear - G; lia)) as HAh;
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (_ & _ & _ & WTn);
    pose proof DTA as D3; pose proof SEPT as D7; pose proof SEPA as D8;
    assert (length a_lo = n) by (rewrite length_firstn; clear - G; lia);
    assert (length a_hi = (n - da)%nat) by (rewrite slice_length; clear - G; lia);
    lazymatch goal with ST : stk bgasegs ?m1 lo _, MI : mem_inv bgasegs ?m1 |- _ =>
    lazymatch sw with
    | false =>
      eapply call_sub_part_wordsA with (a := a_lo) (b := a_hi) (cl := (n - da)%nat) (da := da) (db := 0%nat) (lo := lo) (SPz := (SP + -176)%Z)
                                      (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
        [ exact ESP176 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
        | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | f_equal; clear; lia
        | exact HAl | exact HAh | replace (n - da + da + 0)%nat with n by (clear - G; lia); exact WTn
        | rewrite length_firstn; clear - D3 G; lia | rewrite slice_length by (clear - G; lia); clear - D3 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite length_firstn; clear - D8 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia | kasan I G | ]
    | true =>
      eapply call_sub_part_wordsA with (a := a_hi) (b := a_lo) (cl := (n - da)%nat) (da := 0%nat) (db := da) (lo := lo) (SPz := (SP + -176)%Z)
                                      (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * N)%Z) (BP := (ap + 8 * Z.of_nat 0)%Z);
        [ exact ESP176 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | apply slice_limbs; exact LA | apply limbs_firstn; exact LA
        | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | rewrite A4; f_equal; clear; lia
        | exact HAh | exact HAl | replace (n - da + 0 + da)%nat with n by (clear - G; lia); exact WTn
        | rewrite slice_length by (clear - G; lia); clear - D3 G; lia | rewrite length_firstn; clear - D3 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia | rewrite length_firstn; clear - D8 G; lia | kasan I G | ]
    end end.

  Lemma B_case_p2 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb (Z_to_bv 64 (N - Z.of_nat db)) (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n true a b da db R (splice (splice T 0 (t0_of false)) n (t1_of false)) ->
    evt bgasegs POST (ST F fc 0x229dd8 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5 a4
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 6 zstep. sp1_call I G BND false.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_lo a_hi (n - da) (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA)
                ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 (N - Z.of_nat db)) (Z_to_bv 64 1)) m1 m2 R T 0%nat _ _ 128%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    do 3 zstep. replace (bv_swrap 32 (0 - bv_unsigned a5)) with (Z.of_nat db) by (rewrite A5; symmetry; apply negw_dn; exact Hdb).
    do 4 zstep.
    eapply (B_sp2_neg false); [exact I2 | exact OK].
  Qed.

  Lemma B_case_m4 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb (Z_to_bv 64 (N - Z.of_nat db)) (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n false a b da db R (splice (splice T 0 (t0_of true)) n (t1_of false)) ->
    evt bgasegs POST (ST F fc 0x229e0c m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5 a4
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 6 zstep. sp1_call I G BND true.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_hi a_lo (n - da) (slice_limbs _ _ _ LA) (limbs_firstn _ _ LA)
                ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 (N - Z.of_nat db)) (Z_to_bv 64 1)) m1 m2 R T 0%nat _ _ 128%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    do 3 zstep. replace (bv_swrap 32 (0 - bv_unsigned a5)) with (Z.of_nat db) by (rewrite A5; symmetry; apply negw_dn; exact Hdb).
    do 4 zstep.
    eapply (B_sp2_pos false); [exact I2 | exact OK].
  Qed.

  Lemma B_case_m2 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb (Z_to_bv 64 (N - Z.of_nat db)) (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n true a b da db R (splice (splice T 0 (t0_of true)) n (t1_of true)) ->
    evt bgasegs POST (ST F fc 0x229e40 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5 a4
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 6 zstep. sp1_call I G BND true.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_hi a_lo (n - da) (slice_limbs _ _ _ LA) (limbs_firstn _ _ LA)
                ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 (N - Z.of_nat db)) (Z_to_bv 64 1)) m1 m2 R T 0%nat _ _ 128%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    do 6 zstep.
    eapply (B_sp2_neg true); [exact I2 | exact OK].
  Qed.

  Lemma B_case_p4 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 F fc,
    KBK (FCELLS jb (Z_to_bv 64 (N - Z.of_nat db)) (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n false a b da db R (splice (splice T 0 (t0_of false)) n (t1_of true)) ->
    evt bgasegs POST (ST F fc 0x229e7c m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5 a4
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 6 zstep. sp1_call I G BND false.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_lo a_hi (n - da) (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA)
                ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 (N - Z.of_nat db)) (Z_to_bv 64 1)) m1 m2 R T 0%nat _ _ 128%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    do 6 zstep.
    eapply (B_sp2_pos true); [exact I2 | exact OK].
  Qed.

  Ltac kasan2 I G := klen; split; [kacc I G|]; split; [kacc I G|]; split; [kal8|]; split; [kal8|]; exact (KACC KB_shhi _ _ _ _ I).

  Notation FCELLS0 jb72 := [CB 72 jb72; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma kara_body : forall jb72 m1 R T x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x27 x28 x29 x30 x31 F fc,
    KBK (FCELLS0 jb72) m1 R T ->
    match rec_diffs a_lo a_hi b_lo b_hi (n - da) (n - db) (cmp_part_words a_lo a_hi (n - da)) (cmp_part_words b_hi b_lo (n - db)) with
    | Some (t0', t1', neg) => join_ok RES k' n neg a b da db R (splice (splice T 0 t0') n t1')
    | None => zero_ok RES k' n a b da db R T
    end ->
    evt bgasegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp x5 x6 x7 sp a0 (Z_to_bv 64 15) (Z_to_bv 64 SHB) x12 x13 x14 x15 x16 x17
               a3 a6 x20 x21 a2 a1 a5 a4 (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x229cd8) fc None m1 (seg_rom bgasegs)).
  Proof.
    intros until fc. intros I OK.
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    pose proof (munch_refl [(SP + -176, SP + -176 + 176)]%Z m1) as MUF. pose proof (wmono_refl bgasegs m1) as WMF.
    zstep.
    do 3 zstep. rewrite A3, ?land_m64, half_n2 by (clear - G; lia).
    do 2 zstep.
    replace (bv_swrap 32 (N + bv_unsigned a4)) with (N - Z.of_nat da)%Z by (rewrite A4; symmetry; apply addw_dn; [exact Hda | clear - G; lia]).
    replace (bv_swrap 32 (bv_unsigned a5 + N)) with (N - Z.of_nat db)%Z by (rewrite A5, Z.add_comm; symmetry; apply addw_dn; [exact Hdb | clear - G; lia]).
    zstep.
    zstep. replace (N ≪ 3)%Z with (8 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 2 zstep. replace (bv_swrap 32 (0 - bv_unsigned a4)) with (Z.of_nat da) by (rewrite A4; symmetry; apply negw_dn; exact Hda).
    do 5 zstep.
    pose proof (KFRAME _ _ m1 _ R T I MUF WMF MI STK FR) as I2.
    clear I MUF WMF. clear m1.
    pose proof (KACC KB_a _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_a _ _ _ _ n (n - da)%nat I2 ltac:(clear - G; lia)) as HAh.
    pose proof SEPA as D8.
    assert (Lal : length a_lo = n) by (rewrite length_firstn; clear - G; lia).
    assert (Lah : length a_hi = (n - da)%nat) by (rewrite slice_length; clear - G; lia).
    eapply call_cmp_part_wordsA with (a := a_lo) (b := a_hi) (cl := (n - da)%nat) (da := da) (db := 0%nat) (lo := lo) (SPz := (SP + -176)%Z)
                                    (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
      [ exact ESP176 | ret_even | exact STK | exact MI | exact (KACC KB_shb _ _ _ _ I2) | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
      | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
      | clear - G; lia | ulit | ulit | ulit | f_equal; clear; lia
      | exact HAl | exact HAh | clear - G; lia
      | rewrite length_firstn; clear - D8 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia | kasan2 I2 G | ].
    intros m3 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc STc.
    lazymatch type of I2 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_ro cells mm m3 R T 16%Z eq_refl I2 MUc ltac:(clear - G; lia) WMc MIc STc) as I3 end.
    clear FR STK MI HAl HAh D8 MUc WMc MIc STc I2 Lal Lah.
    pose proof I3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    lazymatch type of MI with mem_inv _ ?mm => pose proof (munch_refl [(SP + -176, SP + -176 + 176)]%Z mm) as MUF; pose proof (wmono_refl bgasegs mm) as WMF end.
    remember (cmp_part_words a_lo a_hi (n - da)) as c1 eqn:Ec1.
    do 9 zstep.
    lazymatch type of I3 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ _ =>
      lazymatch type of MI with mem_inv _ ?mm' => pose proof (KFRAME _ _ mm mm' R T I3 MUF WMF MI STK FR) as I4 end end.
    clear I3 MUF WMF.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I4 ltac:(clear - G; lia)) as HBl.
    pose proof (KACC KB_b _ _ _ _ n (n - db)%nat I4 ltac:(clear - G; lia)) as HBh.
    pose proof SEPB as D9.
    assert (Lbl : length b_lo = n) by (rewrite length_firstn; clear - G; lia).
    assert (Lbh : length b_hi = (n - db)%nat) by (rewrite slice_length; clear - G; lia).
    eapply call_cmp_part_wordsA with (a := b_hi) (b := b_lo) (cl := (n - db)%nat) (da := 0%nat) (db := db) (lo := lo) (SPz := (SP + -176)%Z)
                                    (AP := (bp + 8 * N)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
      [ exact ESP176 | ret_even | exact STK | exact MI | exact (KACC KB_shb _ _ _ _ I4) | apply slice_limbs; exact LB' | apply limbs_firstn; exact LB'
      | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
      | clear - G; lia | ulit | ulit | ulit | rewrite A5; f_equal; clear; lia
      | exact HBh | exact HBl | clear - G; lia
      | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | rewrite length_firstn; clear - D9 G; lia | kasan2 I4 G | ].
    intros m5 u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc STc.
    lazymatch type of I4 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_ro cells mm m5 R T 16%Z eq_refl I4 MUc ltac:(clear - G; lia) WMc MIc STc) as I5 end.
    clear FR STK MI HBl HBh D9 MUc WMc MIc STc I4 Lbl Lbh.
    pose proof I5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    pose proof (munch_refl [(SP + -176, SP + -176 + 176)]%Z m5) as MUF. pose proof (wmono_refl bgasegs m5) as WMF.
    remember (cmp_part_words b_hi b_lo (n - db)) as c2 eqn:Ec2.
    do 4 zstep. change (Z_to_le_bytes 8 1) with (le8 (Z_to_bv 64 1)). mem_after_store.
    do 3 zstep.
    zstep. rewrite A3. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    lazymatch type of I5 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ _ =>
      lazymatch type of MI with mem_inv _ ?mm' => pose proof (KFRAME _ _ mm mm' R T I5 MUF WMF MI STK FR) as I6 end end.
    clear I5 MUF WMF FR STK.
    assert (Hc1 : (c1 = -1 \/ c1 = 0 \/ c1 = 1)%Z).
    { rewrite Ec1, (cmp_part_words_spec a_lo a_hi (n - da) (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA))
        by (right; rewrite slice_length, length_firstn; clear - G; lia). apply sgn3_range. }
    assert (Hc2 : (c2 = -1 \/ c2 = 0 \/ c2 = 1)%Z).
    { rewrite Ec2, (cmp_part_words_spec b_hi b_lo (n - db) (slice_limbs _ _ _ LB') (limbs_firstn _ _ LB'))
        by (left; rewrite slice_length, length_firstn; clear - G; lia). apply sgn3_range. }
    clear Ec1 Ec2.
    destruct Hc1 as [E1|[E1|E1]]; destruct Hc2 as [E2|[E2|E2]]; rewrite E1, E2 in *; clear E1 E2 c1 c2.
    - setreg 10%Z (Z_to_bv 64 0) ltac:(vm_compute; reflexivity). zstep. if_false. do 7 zstep.
      rewrite rec_diffs_m1_m1 in OK. eapply B_case_m4; [exact I6 | exact OK].
    - setreg 10%Z (Z_to_bv 64 1) ltac:(vm_compute; reflexivity). zstep. if_false. do 7 zstep.
      rewrite rec_diffs_m1_0 in OK. eapply B_zero; [exact I6 | exact OK].
    - setreg 10%Z (Z_to_bv 64 2) ltac:(vm_compute; reflexivity). zstep. if_false. do 7 zstep.
      rewrite rec_diffs_m1_p1 in OK. eapply B_case_m2; [exact I6 | exact OK].
    - setreg 10%Z (Z_to_bv 64 3) ltac:(vm_compute; reflexivity). zstep. if_false. do 7 zstep.
      rewrite rec_diffs_0_m1 in OK. eapply B_zero; [exact I6 | exact OK].
    - setreg 10%Z (Z_to_bv 64 4) ltac:(vm_compute; reflexivity). zstep. if_false. do 7 zstep.
      rewrite rec_diffs_0_0 in OK. eapply B_zero; [exact I6 | exact OK].
    - setreg 10%Z (Z_to_bv 64 5) ltac:(vm_compute; reflexivity). zstep. if_false. do 7 zstep.
      rewrite rec_diffs_0_p1 in OK. eapply B_zero; [exact I6 | exact OK].
    - setreg 10%Z (Z_to_bv 64 6) ltac:(vm_compute; reflexivity). zstep. if_false. do 7 zstep.
      rewrite rec_diffs_p1_m1 in OK. eapply B_case_p2; [exact I6 | exact OK].
    - setreg 10%Z (Z_to_bv 64 7) ltac:(vm_compute; reflexivity). zstep. if_false. do 7 zstep.
      rewrite rec_diffs_p1_0 in OK. eapply B_zero; [exact I6 | exact OK].
    - setreg 10%Z (Z_to_bv 64 8) ltac:(vm_compute; reflexivity). zstep. if_false. do 7 zstep.
      rewrite rec_diffs_p1_p1 in OK. eapply B_case_p4; [exact I6 | exact OK].
  Qed.
End Kara.
