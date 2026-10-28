(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp BnKaraX BnKaraPX.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require BnKaraMem W_mul_normal W_mul_recursive W_mul_part_recursive.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnWU Require WU_mul_recursive WU_mul_part_recursive.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require BnKit2.  (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnIfaceA AsStruct ImplA RtCallA BnKaraMemA BnCallsKA AW_mul_recursive AW_mul_rec_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_mul_part_recursive_aentry := 0x24dc08%Z.

Notation land_even_mask64 := W_mul_part_recursive.land_even_mask64.
Notation srliw_half := W_mul_part_recursive.srliw_half.
Notation munch_add_stack_u := WU_mul_recursive.munch_add_stack_u.
Notation lxor_signbit := WU_mul_recursive.lxor_signbit.
Notation lxor_ones64 := WU_mul_recursive.lxor_ones64.
Notation pow2_Z_bounds := W_mul_recursive.pow2_Z_bounds.
Notation lts_words_small := W_mul_normal.lts_words_small.

(* [comment removed for export] *)
Definition part_stackA (CS8 : Z) (k : nat) : Z := (160 * Z.of_nat (S k) + rec_stackA CS8 k)%Z.

Lemma rec_stackA_mono : forall CS8 j k, (j <= k)%nat -> (rec_stackA CS8 j <= rec_stackA CS8 k)%Z.
Proof. intros CS8 j k H. unfold rec_stackA. lia. Qed.
Lemma part_stackA_mono : forall CS8 j k, (j <= k)%nat -> (part_stackA CS8 j <= part_stackA CS8 k)%Z.
Proof. intros CS8 j k H. unfold part_stackA, rec_stackA. lia. Qed.
Lemma part_stackA_S : forall CS8 j k, (S j <= k)%nat -> (part_stackA CS8 j <= part_stackA CS8 k - 160)%Z.
Proof. intros CS8 j k H. unfold part_stackA, rec_stackA. lia. Qed.
Lemma part_stackA_rec : forall CS8 k, (rec_stackA CS8 k <= part_stackA CS8 k - 160)%Z.
Proof. intros CS8 k. unfold part_stackA. lia. Qed.

Section Spec.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).

  Definition part_spec_atA (CS8 : Z) (fuel : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (bR bT bA bB : block)
           (a b : list Z) (k tna tnb : nat) (R T : list Z) (lo : Z),
      limbs a -> limbs b -> limbs R -> limbs T ->
      (3 <= k)%nat -> (k <= fuel)%nat -> (k <= 26)%nat ->
      (tna < Nat.pow 2 k)%nat -> (tnb < Nat.pow 2 k)%nat -> (tna <= tnb + 1)%nat -> (tnb <= tna + 1)%nat ->
      length a = (Nat.pow 2 k + tna)%nat -> length b = (Nat.pow 2 k + tnb)%nat -> length R = (4 * Nat.pow 2 k)%nat ->
      (8 * Nat.pow 2 k <= length T)%nat ->
      bv_unsigned a3 = Z.of_nat (Nat.pow 2 k) -> bv_unsigned a4 = Z.of_nat tna -> bv_unsigned a5 = Z.of_nat tnb ->
      limbs_at bsegs m (bv_unsigned a1) a -> limbs_at bsegs m (bv_unsigned a2) b ->
      limbs_at bsegs m (bv_unsigned a0) R -> limbs_at bsegs m (bv_unsigned a6) T ->
      wr_at bsegs m (bv_unsigned a0) (8 * Z.of_nat (length R)) -> wr_at bsegs m (bv_unsigned a6) (8 * Z.of_nat (length T)) ->
      (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0)%Z ->
      (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a0)%Z ->
      (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a6)%Z ->
      (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a6)%Z ->
      (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a6 \/ bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a0)%Z ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - part_stackA CS8 k)%Z ->
      (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned sp - part_stackA CS8 k \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
      (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned sp - part_stackA CS8 k \/ bv_unsigned sp <= bv_unsigned a6)%Z ->
      (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - part_stackA CS8 k \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
      (bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned sp - part_stackA CS8 k \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
      mem_inv bsegs m ->
      (* [comment removed for export] *)
      AHEAP Σ OW LB m ->
      kara_blocks OW LB bR bT bA bB (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (length R) (length T) (length a) (length b) ->
      (ACEIL <= lo)%Z -> (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> tp = wz TP_A ->

      kara_ub (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) ->
      cps bsegs
        (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x24dc08) fc None m (seg_rom bsegs))))
        (ASTA RT Σ PMc (kr_apost ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo
                          (bv_unsigned a0) (Z.of_nat (length R)) (bv_unsigned a6) (Z.of_nat (length T))
                          (fst (mul_part_recursive fuel k a b tna tnb R T)) (snd (mul_part_recursive fuel k a b tna tnb R T)) m)).

  (* [comment removed for export] *)
  Lemma call_partA : forall (Σ : rts RT) (Q : config -> Prop)
      (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (OW LB : list block) (lo SPz RET : Z)
      (CS8 : Z) (fuel k : nat) (a b : list Z) (tna tnb : nat) (R T : list Z) (RP AP BP TQ : Z) (bR bT bA bB : block),
    bv_unsigned wsp = SPz -> ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET -> stk bsegs m lo SPz -> mem_inv bsegs m ->
    part_spec_atA CS8 fuel ->
    limbs a -> limbs b -> limbs R -> limbs T ->
    (3 <= k)%nat -> (k <= fuel)%nat -> (k <= 26)%nat ->
    (tna < Nat.pow 2 k)%nat -> (tnb < Nat.pow 2 k)%nat -> (tna <= tnb + 1)%nat -> (tnb <= tna + 1)%nat ->
    length a = (Nat.pow 2 k + tna)%nat -> length b = (Nat.pow 2 k + tnb)%nat -> length R = (4 * Nat.pow 2 k)%nat ->
    (8 * Nat.pow 2 k <= length T)%nat ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (Nat.pow 2 k) ->
    bv_unsigned w4 = Z.of_nat tna -> bv_unsigned w5 = Z.of_nat tnb -> bv_unsigned w6 = TQ ->
    limbs_at bsegs m AP a -> limbs_at bsegs m BP b -> limbs_at bsegs m RP R -> limbs_at bsegs m TQ T ->
    wr_at bsegs m RP (8 * Z.of_nat (length R)) -> wr_at bsegs m TQ (8 * Z.of_nat (length T)) ->
    (RP + 8 * Z.of_nat (length R) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (RP + 8 * Z.of_nat (length R) <= BP \/ BP + 8 * Z.of_nat (length b) <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= AP \/ AP + 8 * Z.of_nat (length a) <= TQ)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= BP \/ BP + 8 * Z.of_nat (length b) <= TQ)%Z ->
    (RP + 8 * Z.of_nat (length R) <= TQ \/ TQ + 8 * Z.of_nat (length T) <= RP)%Z ->
    (lo <= SPz - part_stackA CS8 k)%Z ->
    (RP + 8 * Z.of_nat (length R) <= SPz - part_stackA CS8 k \/ SPz <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= SPz - part_stackA CS8 k \/ SPz <= TQ)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - part_stackA CS8 k \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - part_stackA CS8 k \/ SPz <= BP)%Z ->
    (AHEAP Σ OW LB m /\ kara_blocks OW LB bR bT bA bB RP TQ AP BP (length R) (length T) (length a) (length b) /\
     (ACEIL <= lo)%Z /\ (SPz + 16 <= USTACK_TOP)%Z /\ (SPz mod 16 = 0)%Z /\ tp = wz TP_A) ->
    kara_ub RP TQ AP BP ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 (F2 : bvmap 5 word) (fc2 : bv 32),
       AHEAP Σ OW LB m2 ->
       agree_on (fun x => aclient_addr (OW ++ LB) SPz x /\ ~ (RP <= x < RP + 8 * Z.of_nat (length R))%Z /\ ~ (TQ <= x < TQ + 8 * Z.of_nat (length T))%Z) m m2 ->
       wmono bsegs m m2 -> mem_inv bsegs m2 ->
       limbs_at bsegs m2 RP (fst (mul_part_recursive fuel k a b tna tnb R T)) ->
       limbs_at bsegs m2 TQ (snd (mul_part_recursive fuel k a b tna tnb R T)) ->
       stk bsegs m2 lo SPz ->
       evt bsegs (kpost Σ Q)
         (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
             F2 (Z_to_bv 64 RET) fc2 None m2 (seg_rom bsegs))) ->
    evt bsegs (kpost Σ Q)
      (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24dc08) fc None m (seg_rom bsegs)).
  Proof.
    intros until bB. intros ESP ERET STK MI0 SPEC LA LB' LR LT Hk3 Hkf Hk26 Htna Htnb Hd1 Hd2 HLA HLB HLR HLT E0 E1 E2 E3 E4 E5 E6
           RA RB RR RT WR WT DRA DRB DTA DTB DRT LO SEPR SEPT SEPA SEPB (HEAP & KBL & CEIL & SPT & SP16 & ETP) UB K.
    subst RP AP BP TQ SPz.
    apply evt_done. unfold kpost.
    eapply cps_step_same.
    - eapply SPEC with (a := a) (b := b) (k := k) (tna := tna) (tnb := tnb) (R := R) (T := T) (lo := lo) (bR := bR) (bT := bT) (bA := bA) (bB := bB); eassumption.
    - intros ms2 PO. unfold kr_apost in PO.
      destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & HR2 & HT2).
      rewrite ERET. apply cps_from_evt'. rewrite <- ETP.
      eapply K; eassumption.
  Qed.
End Spec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kpart_preA (CS8 : Z) (fuel' k n tna tnb la lb nT : nat) (SK rp tq ap bp SP lo : Z) : Prop :=
  n = Nat.pow 2 k /\ (3 <= k <= 26)%nat /\ (k <= S fuel')%nat /\ (8 <= n)%nat /\ (Z.of_nat n <= 67108864)%Z /\
  (tna < n)%nat /\ (tnb < n)%nat /\ (tna <= tnb + 1)%nat /\ (tnb <= tna + 1)%nat /\
  la = (n + tna)%nat /\ lb = (n + tnb)%nat /\ (8 * n <= nT)%nat /\ SK = (part_stackA CS8 k - 160)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= ap \/ ap + 8 * Z.of_nat la <= rp)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= bp \/ bp + 8 * Z.of_nat lb <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat la <= tq)%Z /\
  (tq + 8 * Z.of_nat nT <= bp \/ bp + 8 * Z.of_nat lb <= tq)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= tq \/ tq + 8 * Z.of_nat nT <= rp)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= SP - 160 - SK \/ SP <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= SP - 160 - SK \/ SP <= tq)%Z /\
  (ap + 8 * Z.of_nat la <= SP - 160 - SK \/ SP <= ap)%Z /\
  (bp + 8 * Z.of_nat lb <= SP - 160 - SK \/ SP <= bp)%Z /\
  (lo <= SP - 160 - SK)%Z /\ (0 <= lo)%Z /\
  (0 < rp /\ rp mod 8 = 0 /\ 0 < ap /\ ap mod 8 = 0 /\ 0 < bp /\ bp mod 8 = 0 /\ 0 < tq /\ tq mod 8 = 0)%Z.

Section KaraP.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).
  Variable CS8 : Z.
  Hypothesis CS8_0 : (0 <= CS8)%Z.
  Hypothesis comba8_ok : comba8_aspec CS8.
  Hypothesis sub_part_ok : sub_part_words_bspec.
  Hypothesis mul_normal_ok : mul_normal_bspec.
  Variable fuel' : nat.
  Hypothesis IHp : part_spec_atA CS8 fuel'.
  Variables (Σ : rts RT) (OW LB : list block) (bR bT bA bB : block).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : word -> option byte) (a b : list Z) (k tna tnb : nat) (lo : Z) (n nT : nat) (SK : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a2).
  Notation tq := (bv_unsigned a6).
  Notation SP := (bv_unsigned sp).
  Notation N := (Z.of_nat n).
  Hypothesis PRE : kpart_preA CS8 fuel' k n tna tnb (length a) (length b) nT SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo.
  Hypothesis KBL : kara_blocks OW LB bR bT bA bB (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (4 * n) nT (length a) (length b).
  Hypothesis CEIL : (ACEIL <= lo)%Z.
  Hypothesis SPT16 : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis ETP : tp = wz TP_A.
  Hypothesis LA : limbs a.
  Hypothesis LB' : limbs b.
  Hypothesis A3 : bv_unsigned a3 = N.
  Hypothesis A4 : bv_unsigned a4 = Z.of_nat tna.
  Hypothesis A5 : bv_unsigned a5 = Z.of_nat tnb.
  Variable RES : list Z * list Z.

  Lemma Hn : n = Nat.pow 2 k. Proof. apply PRE. Qed.
  Lemma Hk : (3 <= k <= 26)%nat. Proof. apply PRE. Qed.
  Lemma Hkf : (k <= S fuel')%nat. Proof. apply PRE. Qed.
  Lemma Hn8 : (8 <= n)%nat. Proof. apply PRE. Qed.
  Lemma HnB : (N <= 67108864)%Z. Proof. apply PRE. Qed.
  Lemma Htna : (tna < n)%nat. Proof. apply PRE. Qed.
  Lemma Htnb : (tnb < n)%nat. Proof. apply PRE. Qed.
  Lemma Hd1 : (tna <= tnb + 1)%nat. Proof. apply PRE. Qed.
  Lemma Hd2 : (tnb <= tna + 1)%nat. Proof. apply PRE. Qed.
  Lemma HLA : length a = (n + tna)%nat. Proof. apply PRE. Qed.
  Lemma HLB : length b = (n + tnb)%nat. Proof. apply PRE. Qed.
  Lemma HnT : (8 * n <= nT)%nat. Proof. apply PRE. Qed.
  Lemma HSK : SK = (part_stackA CS8 k - 160)%Z. Proof. apply PRE. Qed.
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
  Lemma ubs : (0 < rp /\ rp mod 8 = 0 /\ 0 < ap /\ ap mod 8 = 0 /\ 0 < bp /\ bp mod 8 = 0 /\ 0 < tq /\ tq mod 8 = 0)%Z. Proof. apply PRE. Qed.
  Lemma SK_rec : (rec_stackA CS8 k <= SK)%Z. Proof. rewrite HSK. apply part_stackA_rec. Qed.
  Lemma SK_ge : (65536 <= SK /\ CS8 <= SK)%Z. Proof. pose proof SK_rec. unfold rec_stackA in *. lia. Qed.
  Lemma SK0 : (0 <= SK)%Z. Proof. pose proof SK_ge. lia. Qed.
  Lemma FS0 : (0 <= 160)%Z. Proof. lia. Qed.
  Lemma FBE : (SP + -160 = SP - 160)%Z. Proof. reflexivity. Qed.
  Lemma SPTop : (SP <= USTACK_TOP)%Z. Proof. pose proof SPT16. lia. Qed.
  Lemma ESP160 : bv_unsigned (Z_to_bv 64 (SP + -160)) = (SP + -160)%Z.
  Proof.
    apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R.
    pose proof LO. pose proof LO0. pose proof SK0. lia.
  Qed.
  Lemma pow_n : Nat.pow 2 k = n. Proof. symmetry. exact Hn. Qed.
  Lemma INR : In bR OW. Proof. apply KBL. Qed.
  Lemma INT : In bT OW. Proof. apply KBL. Qed.
  Lemma INA : In bA (OW ++ LB). Proof. apply KBL. Qed.
  Lemma INB : In bB (OW ++ LB). Proof. apply KBL. Qed.
  Lemma RGR : (blk_addr bR <= rp /\ rp + 8 * Z.of_nat (4 * n) <= blk_addr bR + blk_size bR)%Z. Proof. apply KBL. Qed.
  Lemma RGT : (blk_addr bT <= tq /\ tq + 8 * Z.of_nat nT <= blk_addr bT + blk_size bT)%Z. Proof. apply KBL. Qed.
  Lemma RGA : (blk_addr bA <= ap /\ ap + 8 * Z.of_nat (length a) <= blk_addr bA + blk_size bA)%Z. Proof. apply KBL. Qed.
  Lemma RGB : (blk_addr bB <= bp /\ bp + 8 * Z.of_nat (length b) <= blk_addr bB + blk_size bB)%Z. Proof. apply KBL. Qed.
  Lemma AL8 : (rp mod 8 = 0 /\ tq mod 8 = 0 /\ ap mod 8 = 0 /\ bp mod 8 = 0)%Z. Proof. apply KBL. Qed.

  (* [comment removed for export] *)
  Lemma geom : (8 <= N <= 67108864 /\ 0 <= lo /\ lo <= SP - 160 - SK /\ 65536 <= SK /\ CS8 <= SK /\ 0 <= CS8 /\ rec_stackA CS8 k <= SK /\
                8 * N <= Z.of_nat nT /\ Z.of_nat tna < N /\ Z.of_nat tnb < N /\ Z.of_nat tna <= Z.of_nat tnb + 1 /\ Z.of_nat tnb <= Z.of_nat tna + 1 /\
                Z.of_nat (length a) = N + Z.of_nat tna /\ Z.of_nat (length b) = N + Z.of_nat tnb)%Z.
  Proof.
    pose proof Hn8. pose proof HnB. pose proof LO. pose proof LO0. pose proof SK_ge. pose proof SK_rec. pose proof HnT. pose proof Htna.
    pose proof Htnb. pose proof Hd1. pose proof Hd2. pose proof HLA. pose proof HLB. lia.
  Qed.

  Ltac ub_tac BND G :=
    unfold ub_ptr_ok; intros _; let UB := fresh "UB" in pose proof ubs as UB;
    split; [ clear - UB BND G; lia | clear - UB; Z.div_mod_to_equations; lia ].

  Notation POST := (kpost Σ (ASTA RT Σ PMc (kr_apost ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo
                      (bv_unsigned a0) (Z.of_nat (4 * n)) (bv_unsigned a6) (Z.of_nat nT) (fst RES) (snd RES) m))).
  (* [comment removed for export] *)
  Notation KK L := (L Σ OW LB m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      160%Z SK (bv_unsigned sp + -160)%Z bR bT bA bB FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB
                      INR INT INA INB RGR RGT RGA RGB CEIL LO SPTop).
  Notation KBK := (KB Σ OW LB m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      (bv_unsigned sp + -160)%Z).
  Notation KUPD := (KK KB_upd).
  Notation KFRAME := (KK KB_frame).
  Notation KSTORE := (KK KB_storeR).
  Notation KAFTER L := (KK L).
  Notation KACC L := (KK L).

  (* [comment removed for export] *)
  Notation FCELLS neg jb :=
    [CB 8 jb; C8 (Z_to_bv 64 (if neg then 0 else 1)); C8 (Z_to_bv 64 (bv_unsigned a2 + 8 * Z.of_nat n)); C8 (Z_to_bv 64 (8 * Z.of_nat n));
     C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (8 * Z.of_nat n)); C8 (Z_to_bv 64 (bv_unsigned a1 + 8 * Z.of_nat n));
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Notation ST F fc pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Ltac ret_even := apply ret_pc_even; [lia | reflexivity].
  Ltac ulit := first [ reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; lia); lia | lia ].
  (* [comment removed for export] *)
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

  Ltac kasanN I G := klen; split; [kacc I G|]; split; [kacc I G|]; split; [kacc I G|]; split; [kapt I G|];
    first [ eapply (KACC KB_offiR _ _ _ _ _ _ I); clear - G; lia | eapply (KACC KB_offiT _ _ _ _ _ _ I); clear - G; lia ].
  Ltac kasan2 I G := klen; split; [kacc I G|]; split; [kacc I G|]; split; [kal8|]; split; [kal8|]; exact (KACC KB_shhi _ _ _ _ I).
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
  Ltac kub BND G := unfold kara_ub; split; [ub_tac BND G|]; split; [ub_tac BND G|]; split; [ub_tac BND G | ub_tac BND G].

  (* [comment removed for export] *)
  Ltac kb_store SOK0 I2 :=
    lazymatch type of SOK0 with
    | store_ok _ ?m2 ?a0' _ = true =>
        let ad := cur_mem_addr in
        let SOK := fresh "SOK" in
        assert (SOK : store_ok bsegs m2 ad 8 = true) by (replace ad with a0' by (unfold wa; f_equal; lia); exact SOK0);
        replace a0' with ad in I2 by (unfold wa; f_equal; lia);
        zstep; clear SOK SOK0;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => let m' := fresh "m" in gen_mem mm m' end
    end.

  (* [comment removed for export] *)
  Lemma shR_rd : forall cells m1 R T (i : nat) ad, KBK cells m1 R T -> (i < 4 * n)%nat -> (0 <= rp /\ rp + 8 * Z.of_nat (4 * n) <= 140737488355328)%Z ->
    ad = wa (shad (rp + 8 * Z.of_nat i)) -> ov_read_bytes bsegs m1 ad 1 = Some [z8].
  Proof.
    intros cells m1 R T i ad I Hi BR ->.
    pose proof (KACC KB_accR _ _ _ _ 0%nat (4 * n)%nat I ltac:(clear; lia)) as AC.
    destruct AL8 as (AR8 & _).
    eapply (acc_rd0_same bsegs m1 _ _ (rp + 8 * Z.of_nat i)%Z _ AC); [ | | | | reflexivity].
    - clear - AR8. Z.div_mod_to_equations. lia.
    - clear - Hi. lia.
    - clear - Hi. lia.
    - clear - BR Hi. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma BP_epi : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc,
    KBK (FCELLS neg jb) m1 R T -> RES = (R, T) ->
    evt bsegs POST (ST F fc 0x24e3dc m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM) E.
    do 15 zstep.
    assert (LO1 : (lo <= SP + -160)%Z) by (pose proof LO; pose proof SK0; lia).
    release_frame FR ST (bv_unsigned sp).
    subst RES. cbn [fst snd].
    apply evt_done. unfold kpost. apply cps_done. unfold kr_apost. rewrite ETP.
    do 18 eexists. split; [reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact HEAP|]. split; [exact WM|].
    split; [exact MU|]. split; [exact HR | exact HT].
  Qed.

  (* [comment removed for export] *)
  Lemma BP_loop : forall (l pre : list Z) (neg : bool) jb m1 T x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F fc,
    KBK (FCELLS neg jb) m1 (pre ++ l) T -> cu_fit l -> RES = (pre ++ carry_up l, T) -> (1 <= length pre)%nat ->
    evt bsegs POST (ST F fc 0x24e3b0 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre) + -8)) (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre)))
                       (Z_to_bv 64 (-9)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 SHB) x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction l as [|x l' IHl]; intros until fc; intros I FIT E Hpre.
    { exfalso. unfold cu_fit in FIT. cbn [lval length] in FIT. rewrite Bp_0 in FIT. clear - FIT. lia. }
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    destruct (cu_fit_cons (x :: l') (proj2 (limbs_app_inv _ _ LR)) FIT) as (x' & l'' & Ecs & Hx & Hl' & Hfit').
    injection Ecs as <- <-.
    assert (Hi : (length pre < 4 * n)%nat) by (rewrite length_app in ER; cbn [length] in ER; clear - ER; lia).
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(pose proof Hn8; lia) ltac:(pose proof HnT; pose proof Hn8; lia)) as (BR0 & BR1 & _).
    pose proof (proj1 WR) as R0.
    chk ltac:(fun C => clear - C BR0 BR1 R0 Hi Hpre; lia).
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shR_rd _ m1 _ T (length pre) ad I Hi (conj BR0 BR1) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    zstep. setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre))) ltac:(f_equal; clear; lia).
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    ld_hd HR2.
    zstep.
    setreg 13%Z (Z_to_bv 64 (addw x 1)) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE (FCELLS neg jb) m1 (pre ++ x :: l') T (length pre) (addw x 1) eq_refl I Hi (addw_limb _ _)) as (SOK0 & I2).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI HEAP MU WM BR0 BR1.
    kb_store SOK0 I2.
    zstep.
    rewrite upd_app_mid in I2.
    pose proof (addw_limb x 1) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K; zify_cond K.
    - setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x 1])) + -8)) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      setreg 11%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x 1])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      eapply IHl; [exact I2 | apply Hfit'; exact K | | rewrite length_app; cbn [length]; clear; lia].
      rewrite E. cbn [carry_up]. rewrite K. cbn [Z.eqb]. rewrite <- app_assoc. reflexivity.
    - eapply BP_epi; [exact I2|].
      rewrite E. cbn [carry_up]. destruct (Z.eqb_spec (addw x 1) 0) as [E0|_]; [contradiction|]. rewrite <- app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma BP_fin : forall (neg : bool) jb m1 R T c12 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 F fc,
    KBK (FCELLS neg jb) m1 R T -> kc3_ok RES n R T c12 -> (-1 <= c12 <= 2)%Z ->
    evt bsegs POST (ST F fc 0x24e304 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 a6 (Z_to_bv 64 (16 * N)) (Z_to_bv 64 (2 * N))
                       (Z_to_bv 64 (16 * N + tq)) (Z_to_bv 64 SHB) (Z_to_bv 64 1) (Z_to_bv 64 c12) x26 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK Hc12.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ n (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    do 2 zstep. rewrite ?land_m64. rewrite lxor_ones64 by (clear - BND; lia).
    chk ltac:(fun C => clear - C BND G; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    zstep. if_false.
    do 6 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply call_add_wordsK with (a := slice R n (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -160)%Z)
                                (RP := (rp + 8 * N)%Z) (AP := (rp + 8 * N)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | exact LRa | exact LTb | rewrite ERa, ETb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa; ulit
      | exact HRa | exact HTb | rewrite ERa; exact WRa
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D3 G; lia
      | kasan I G | rewrite ERa; ub_tac BND G | rewrite ERa; ub_tac BND G | rewrite ERa; ub_tac BND G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LTb ltac:(rewrite ERa, ETb; reflexivity)) as SP3.
    unfold kc3_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R n (2 * n)) (slice T (2 * n) (2 * n))) as [sg3 cy3]. cbn [fst snd] in *.
    destruct SP3 as (Ls3 & Es3 & Hc3 & _). rewrite ERa in Es3. destruct OK as (ERES & Hc & FIT).
    pose proof (KAFTER KB_after_R (FCELLS neg jb) m1 m2 R T n sg3 _ 112%Z eq_refl I MUc ltac:(rewrite ERa, Es3; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls3 ltac:(rewrite Es3; clear; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM HRa LRa ERa WRa HTb LTb ETb MUc WMc HS I D1 D2 D3.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    zstep. rewrite (bn_swrap32_small (cy3 + 0)), Z.add_0_r by (clear - Hc3; lia).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_mod c12 0), Z.add_0_r by (clear - Hc12; lia).
    zstep. setreg 11%Z (Z_to_bv 64 (c12 + cy3)) ltac:(apply Z_to_bv_eqm; clear; change (2 ^ 64)%Z with 18446744073709551616%Z; Z.div_mod_to_equations; lia).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_mod c12 cy3) by (clear - Hc12 Hc3; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite (bn_swrap32_small (c12 + cy3 + 0)), Z.add_0_r by (clear - Hc; lia).
    zstep. if_cases K; zify_cond K.
    { eapply BP_epi; [exact I2|]. rewrite ERES. rewrite K. reflexivity. }
    specialize (FIT K). destruct (Z.eqb_spec (c12 + cy3) 0) as [E0|_]; [contradiction|].
    zstep. rewrite A3.
    zstep. rewrite A3, (bn_swrap32_small (N + 2 * N)) by (clear - G; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite (bn_swrap32_small (N + 2 * N + 0)), Z.add_0_r by (clear - G; lia).
    zstep. replace ((N + 2 * N) ≪ 3)%Z with (8 * Z.of_nat (n + 2 * n))%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    zstep.
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    do 4 zstep.
    setreg 13%Z (Z_to_bv 64 1) ltac:(
      replace (rp + 8 * Z.of_nat (n + 2 * n) <? rp)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      rewrite lxor_signbit by (clear - G; lia);
      replace (N + 2 * N + 9223372036854775808 <? 9223372036854775808)%Z with false by (symmetry; apply Z.ltb_ge; clear - G; lia);
      reflexivity).
    zstep. if_false.
    do 2 zstep.
    rewrite land7 by (pose proof ubs as UB; clear - UB; Z.div_mod_to_equations; lia).
    zstep. if_false.

    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shR_rd _ m2 _ T (n + 2 * n)%nat ad I2 ltac:(clear - G; lia) ltac:(clear - BND; lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    (* [comment removed for export] *)
    remember (splice R n sg3) as R' eqn:ER'. pose proof ER as ERl.
    assert (Lpre : length (firstn (n + 2 * n) R') = (n + 2 * n)%nat) by (rewrite length_firstn; clear - ER; lia).
    destruct (skipn (n + 2 * n) R') as [|x l'] eqn:Esk.
    { exfalso. pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. clear - HH ER G. lia. }
    assert (ERpl : R' = firstn (n + 2 * n) R' ++ x :: l') by (rewrite <- Esk; symmetry; apply firstn_skipn).
    remember (firstn (n + 2 * n) R') as pre eqn:Epre.
    rewrite ERpl in I2, HR, LR. clear ERpl.
    pose proof (limbs_cons_lit x l' (proj2 (limbs_app_inv _ _ LR))) as (Hx & Ll').
    setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre))) ltac:(rewrite Lpre; reflexivity).
    setreg 12%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre))) ltac:(rewrite Lpre; reflexivity).
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    ld_hd HR2.
    zstep.
    setreg 11%Z (Z_to_bv 64 (addw x (c12 + cy3))) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE (FCELLS neg jb) m2 (pre ++ x :: l') T (length pre) (addw x (c12 + cy3)) eq_refl I2 ltac:(rewrite Lpre; clear - G; lia) (addw_limb _ _)) as (SOK0 & I3).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI HEAP MU WM I2 MIc STc.
    kb_store SOK0 I3. rewrite upd_app_mid in I3.
    pose proof (addw_limb x (c12 + cy3)) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K2; zify_cond K2.
    - eapply BP_epi; [exact I3|]. rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx).
      destruct (Z.ltb_spec (addw x (c12 + cy3)) x) as [HH|_]; [exfalso; clear - HH K2; lia|]. rewrite <- app_assoc. reflexivity.
    - do 2 zstep.
      setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x (c12 + cy3)])) + -8)) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      setreg 11%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x (c12 + cy3)])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      assert (TST : (addw x (c12 + cy3) <? x) = true) by (apply Z.ltb_lt; clear - K2; lia).
      eapply BP_loop; [exact I3 | | | rewrite length_app; cbn [length]; clear; lia].
      + eapply (add_carry_fit x l' (c12 + cy3)); [rewrite BW_lit; exact Hx | exact Ll' | rewrite BW_lit; clear - Hc; lia | | exact TST].
        replace (S (length l')) with n; [exact FIT|].
        pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. rewrite HH, ERl. clear. lia.
      + rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx). rewrite TST. rewrite <- app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma BP_sub : forall (neg : bool) jb m1 R T c1 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 F fc,
    KBK (FCELLS neg jb) m1 R T -> kc2_ok RES n true R T c1 -> (0 <= c1 <= 1)%Z ->
    evt bsegs POST (ST F fc 0x24e2d8 m1 x1 x5 x6 x7 a0 (Z_to_bv 64 c1) (Z_to_bv 64 1) x12 x13 x14 x15 x16 x17 a3 a6 (Z_to_bv 64 (16 * N)) (Z_to_bv 64 (2 * N))
                       (Z_to_bv 64 (16 * N + tq)) (Z_to_bv 64 SHB) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    zstep. if_false.
    zstep. rewrite (bn_swrap32_small (c1 + 0)), Z.add_0_r by (clear - Hc1; lia).
    do 5 zstep.
    pose proof SEPT as D3.
    eapply call_sub_wordsK with (a := slice T 0 (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -160)%Z)
                                (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | exact LTa | exact LTb | rewrite ETa, ETb; reflexivity
      | rewrite ETa; clear - G; lia | ulit | ulit | ulit | rewrite ETa; ulit
      | exact HTa | exact HTb | rewrite ETa; exact WTb
      | unfold alias_ok; rewrite ETa; clear; lia | unfold alias_ok; left; reflexivity
      | clear - G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia
      | kasan I G | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (sub_words_spec _ _ LTa LTb ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (sub_words (slice T 0 (2 * n)) (slice T (2 * n) (2 * n))) as [sg2 bw]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hbw & _). rewrite ETa in Es2.
    pose proof (KAFTER KB_after_T (FCELLS neg jb) m1 m2 R T (2 * n)%nat sg2 _ 112%Z eq_refl I MUc ltac:(rewrite ETa, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep. rewrite (bn_swrap32_small (bw + 0)), Z.add_0_r by (clear - Hbw; lia).
    zstep.
    zstep. rewrite (bn_swrap32_small (c1 - bw)) by (clear - Hc1 Hbw; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    eapply BP_fin; [exact I2 | exact OK | clear - Hc1 Hbw; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma BP_add : forall (neg : bool) jb m1 R T c1 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 F fc,
    KBK (FCELLS neg jb) m1 R T -> kc2_ok RES n false R T c1 -> (0 <= c1 <= 1)%Z ->
    evt bsegs POST (ST F fc 0x24e2a8 m1 x1 x5 x6 x7 a0 (Z_to_bv 64 c1) (Z_to_bv 64 1) x12 x13 x14 x15 x16 x17 a3 a6 (Z_to_bv 64 (16 * N)) (Z_to_bv 64 (2 * N))
                       (Z_to_bv 64 (16 * N + tq)) (Z_to_bv 64 SHB) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    zstep. if_false.
    zstep. rewrite (bn_swrap32_small (c1 + 0)), Z.add_0_r by (clear - Hc1; lia).
    do 5 zstep.
    pose proof SEPT as D3.
    eapply call_add_wordsK with (a := slice T (2 * n) (2 * n)) (b := slice T 0 (2 * n)) (lo := lo) (SPz := (SP + -160)%Z)
                                (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat (2 * n))%Z) (BP := (tq + 8 * Z.of_nat 0)%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | exact LTb | exact LTa | rewrite ETa, ETb; reflexivity
      | rewrite ETb; clear - G; lia | ulit | ulit | ulit | rewrite ETb; ulit
      | exact HTb | exact HTa | rewrite ETb; exact WTb
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ETb; clear; lia
      | clear - G; lia | rewrite ETb; clear - D3 G; lia | rewrite ETb; clear - D3 G; lia | rewrite ETb; clear - D3 G; lia
      | kasan I G | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LTb LTa ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (add_words (slice T (2 * n) (2 * n)) (slice T 0 (2 * n))) as [sg2 cy]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hcy & _). rewrite ETb in Es2.
    pose proof (KAFTER KB_after_T (FCELLS neg jb) m1 m2 R T (2 * n)%nat sg2 _ 112%Z eq_refl I MUc ltac:(rewrite ETb, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep. rewrite (bn_swrap32_small (cy + 0)), Z.add_0_r by (clear - Hcy; lia).
    zstep.
    zstep. rewrite (bn_swrap32_small (c1 + cy)) by (clear - Hc1 Hcy; lia).
    zstep. if_true.
    eapply BP_fin; [exact I2 | exact OK | clear - Hc1 Hcy; lia].

  Qed.

  (* [comment removed for export] *)
  Lemma BP_tail : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x26 x28 x29 x30 x31 F fc,
    KBK (FCELLS neg jb) m1 R T -> kc_ok RES n neg R T ->
    evt bsegs POST (ST F fc 0x24e248 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 a6 (Z_to_bv 64 (2 * N)) (Z_to_bv 64 (2 * N))
                       x22 (Z_to_bv 64 SHB) x24 (Z_to_bv 64 (16 * N + rp)) x26 (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & _).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear; lia)) as (HRb & LRb & ERb & _).
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (_ & _ & _ & WTa).
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    do 4 zstep.
    setreg 10%Z (Z_to_bv 64 1) ltac:(replace (16 * N + rp <? rp)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia); reflexivity).
    zstep. if_false.
    zstep.
    zstep. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 3 zstep.
    setreg 24%Z (Z_to_bv 64 0) ltac:(replace (16 * N + tq <? 16 * N)%Z with false by (symmetry; apply Z.ltb_ge; clear - BND; lia); reflexivity).
    do 5 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply call_add_wordsK with (a := slice R 0 (2 * n)) (b := slice R (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -160)%Z)
                                (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (rp + 8 * Z.of_nat 0)%Z) (BP := (rp + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | exact LRa | exact LRb | rewrite ERa, ERb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa; ulit
      | exact HRa | exact HRb | rewrite ERa; exact WTa
      | unfold alias_ok; rewrite ERa; clear - D1 G; lia | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D3 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia
      | kasan I G | ub_tac BND G | ub_tac BND G | ub_tac BND G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LRb ltac:(rewrite ERa, ERb; reflexivity)) as SP1.
    unfold kc_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R 0 (2 * n)) (slice R (2 * n) (2 * n))) as [sg1 cy1]. cbn [fst snd] in *.
    destruct SP1 as (Ls1 & Es1 & Hc1 & _). rewrite ERa in Es1.
    pose proof (KAFTER KB_after_T (FCELLS neg jb) m1 m2 R T 0%nat sg1 _ 112%Z eq_refl I MUc ltac:(rewrite ERa, Es1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls1 ltac:(rewrite Es1; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM HRa LRa ERa HRb LRb ERb WTa MUc WMc HS I D1 D2 D3 MIc STc.
    pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
    do 5 zstep.
    setreg 11%Z (Z_to_bv 64 1) ltac:(
      replace (0 <? tq)%Z with true by (symmetry; apply Z.ltb_lt; pose proof ubs as UB; clear - UB; lia);
      replace (0 <? 16 * N + tq)%Z with true by (symmetry; apply Z.ltb_lt; pose proof ubs as UB; clear - UB G; lia); reflexivity).
    zstep.
    destruct neg.
    - zstep. if_true. eapply (BP_sub true); [exact I2 | exact OK | exact Hc1].
    - zstep. if_false. eapply (BP_add false); [exact I2 | exact OK | exact Hc1].

  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ms_stack : (lo + RT_STACK <= SP + -160 /\ SP + -160 + 16 <= USTACK_TOP /\ (SP + -160) mod 16 = 0)%Z.
  Proof.
    pose proof geom as G. pose proof SPT16 as S1. pose proof SP16 as S2. unfold RT_STACK.
    split; [clear - G; lia|]. split; [clear - S1; lia|]. clear - S2. Z.div_mod_to_equations. lia.
  (* [comment removed for export] *)
  Qed.

  Notation a_lo := (firstn n a).
  Notation a_hi := (slice a n tna).
  Notation b_lo := (firstn n b).
  Notation b_hi := (slice b n tnb).

  Ltac fill_steps G BND :=
    do 2 zstep; rewrite A4, (bn_swrap32_small (2 * N + Z.of_nat tna)) by (clear - G; lia);
    chk ltac:(fun C => clear - C; lia);
    zstep; rewrite (bn_swrap32_small (2 * N + Z.of_nat tna + 0)), Z.add_0_r by (clear - G; lia);
    do 2 zstep; rewrite A5, (bn_swrap32_small (2 * N + Z.of_nat tna + Z.of_nat tnb)) by (clear - G; lia);
    chk ltac:(fun C => clear - C; lia);
    zstep; rewrite (bn_swrap32_small (2 * N + Z.of_nat tna + Z.of_nat tnb + 0)), Z.add_0_r by (clear - G; lia);
    zstep; replace ((2 * N + Z.of_nat tna + Z.of_nat tnb) ≪ 3)%Z with (8 * Z.of_nat (2 * n + tna + tnb))%Z
      by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia);
    zstep;
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia);
    do 4 zstep;
    setreg 11%Z (Z_to_bv 64 1) ltac:(
      replace (rp + 8 * Z.of_nat (2 * n + tna + tnb) <? rp)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      rewrite lxor_signbit by (clear - G; lia);
      replace (2 * N + Z.of_nat tna + Z.of_nat tnb + 9223372036854775808 <? 9223372036854775808)%Z with false
        by (symmetry; apply Z.ltb_ge; clear - G; lia);
      reflexivity);
    zstep; if_false;
    do 2 zstep; rewrite A4, (bn_swrap32_small (2 * N - Z.of_nat tna)) by (clear - G; lia);
    chk ltac:(fun C => clear - C; lia);
    zstep; rewrite (bn_swrap32_small (2 * N - Z.of_nat tna + 0)), Z.add_0_r by (clear - G; lia);
    do 2 zstep; rewrite A5, (bn_swrap32_small (2 * N - Z.of_nat tna - Z.of_nat tnb)) by (clear - G; lia);
    chk ltac:(fun C => clear - C; lia);
    zstep; rewrite (bn_swrap32_small (2 * N - Z.of_nat tna - Z.of_nat tnb + 0)), Z.add_0_r by (clear - G; lia);
    zstep; replace ((2 * N - Z.of_nat tna - Z.of_nat tnb) ≪ 3)%Z with (8 * Z.of_nat (2 * n - tna - tnb))%Z
      by (rewrite Z.shiftl_mul_pow2 by lia; clear - G; lia).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma BP_comba : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x27 x28 x29 x30 x31 F fc,
    n = 8%nat ->
    KBK (FCELLS neg jb) m1 R T -> pcomba_ok RES n neg a b tna tnb R T ->
    evt bsegs POST (ST F fc 0x24df38 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 a6 a5 (Z_to_bv 64 (2 * N))
                       a4 (Z_to_bv 64 SHB) x24 a2 a1 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros En I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat 16%nat I ltac:(clear - G En; lia)) as (_ & _ & _ & WTr).
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    zstep.
    chk ltac:(fun C => clear - C BND G; lia).
    do 2 zstep. rewrite lxor_ones64 by (clear - BND; lia).
    chk ltac:(fun C => clear - C BND G; lia).
    zstep. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 5 zstep.
    pose proof SEPT as D7.
    eapply call_comba8A with (CS8 := CS8) (a := slice T 0 n) (b := slice T n n) (lo := lo) (SPz := (SP + -160)%Z)
                             (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * N)%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | exact comba8_ok | exact LTa | exact LTb
      | rewrite ETa; exact En | rewrite ETb; exact En | ulit | ulit | ulit | exact HTa | exact HTb | exact WTr
      | clear - G En; lia | clear - G En; lia | clear - G; lia
      | clear - D7 G En; lia | clear - D7 G En; lia | clear - D7 G En; lia
      | kasan8 I G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (mul_comba8_spec (slice T 0 n) (slice T n n) LTa LTb ltac:(rewrite ETa; exact En) ltac:(rewrite ETb; exact En)) as (Lc & Ec & _).
    pose proof (KAFTER KB_after_T (FCELLS neg jb) m1 m2 R T (2 * n)%nat _ _ CS8 eq_refl I MUc ltac:(rewrite Ec; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc ltac:(rewrite Ec; clear - G En; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM HTa LTa ETa HTb LTb ETb WTr MUc WMc HS MIc STc I D7.
    unfold pcomba_ok in OK. cbv zeta in OK.
    remember (splice T (2 * n) (mul_comba8 (slice T 0 n) (slice T n n))) as T1 eqn:ET1. clear ET1 Lc Ec.
    (* [comment removed for export] *)
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    destruct (KACC KB_R _ _ _ _ 0%nat 16%nat I2 ltac:(clear - En; lia)) as (_ & _ & _ & WRa).
    pose proof (KACC KB_a _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HBl.
    assert (Lal : length a_lo = 8%nat) by (rewrite length_firstn; clear - G En; lia).
    assert (Lbl : length b_lo = 8%nat) by (rewrite length_firstn; clear - G En; lia).
    do 4 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof SEPR as D3. pose proof SEPA as D4. pose proof SEPB as D5.
    eapply call_comba8A with (CS8 := CS8) (a := a_lo) (b := b_lo) (lo := lo) (SPz := (SP + -160)%Z)
                             (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I2) | exact comba8_ok | apply limbs_firstn; exact LA | apply limbs_firstn; exact LB'
      | exact Lal | exact Lbl | ulit | ulit | ulit | exact HAl | exact HBl | exact WRa
      | clear - D1 G En; lia | clear - D2 G En; lia | clear - G; lia
      | clear - D3 G En; lia | clear - D4 G En; lia | clear - D5 G En; lia
      | kasan8 I2 G | ].
    intros m3 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HS STc.
    destruct (mul_comba8_spec a_lo b_lo (limbs_firstn _ _ LA) (limbs_firstn _ _ LB') Lal Lbl) as (Lc1 & Ec1 & _).
    pose proof (KAFTER KB_after_R (FCELLS neg jb) m2 m3 R T1 0%nat (mul_comba8 a_lo b_lo) _ CS8 eq_refl I2 MUc ltac:(rewrite Ec1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc1 ltac:(rewrite Ec1; clear - En; lia)) as I3.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM WRa HAl HBl MUc WMc HS I2 MIc STc.
    remember (splice R 0 (mul_comba8 a_lo b_lo)) as R1 eqn:ER1. clear ER1 Lc1 Ec1.
    (* [comment removed for export] *)
    pose proof I3 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (tna + tnb)%nat I3 ltac:(clear - G; lia)) as (_ & _ & _ & WRn).
    pose proof (KACC KB_a _ _ _ _ n tna I3 ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n tnb I3 ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    zstep.
    chk ltac:(fun C => clear - C BND G; lia).
    do 6 zstep.
    eapply call_mul_normalA with (a := a_hi) (b := b_hi) (lo := lo) (SPz := (SP + -160)%Z)
                                (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I3) | exact mul_normal_ok | apply slice_limbs; exact LA | apply slice_limbs; exact LB'
      | rewrite Lah, Lbh; clear - G; lia
      | ulit | ulit | rewrite Lah; exact A4 | ulit | rewrite Lbh; exact A5
      | exact HAh | exact HBh
      | rewrite Lah, Lbh; replace (Z.of_nat tna + Z.of_nat tnb)%Z with (Z.of_nat (tna + tnb)) by (clear; lia); exact WRn
      | rewrite Lah, Lbh; clear - D1 G; lia | rewrite Lah, Lbh; clear - D2 G; lia | clear - G; lia
      | rewrite Lah, Lbh; clear - D3 G; lia | rewrite Lah; clear - D4 G; lia | rewrite Lbh; clear - D5 G; lia
      | kasanN I3 G | ub_tac BND G | ub_tac BND2 G | ub_tac BND2 G | ].
    intros m4 w0 w1 w2 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 MUc WMc MIc HS STc.
    destruct (mul_normal_spec a_hi b_hi (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB')) as (LMN & _ & EMN).
    assert (EMN' : length (mul_normal a_hi b_hi) = (tna + tnb)%nat).
    { rewrite EMN, Lah, Lbh. destruct (Nat.eqb_spec tna 0); destruct (Nat.eqb_spec tnb 0); cbn [orb]; clear - G e || clear - G e e0 || clear - G; lia. }
    clear EMN.
    pose proof (KAFTER KB_after_R (FCELLS neg jb) m3 m4 R1 T1 (2 * n)%nat (mul_normal a_hi b_hi) _ 240%Z eq_refl I3 MUc
                  ltac:(rewrite Lah, Lbh, EMN'; clear; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc LMN ltac:(rewrite EMN'; clear - G; lia)) as I4.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM WRn HAh HBh MUc WMc HS I3 MIc STc D1 D2 D3 D4 D5.
    remember (splice R1 (2 * n) (mul_normal a_hi b_hi)) as R2 eqn:ER2. clear ER2 LMN EMN'.
    (* [comment removed for export] *)
    pose proof I4 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    destruct (KACC KB_R _ _ _ _ (2 * n + tna + tnb)%nat (2 * n - tna - tnb)%nat I4 ltac:(clear - G; lia)) as (HRz & LRz & ERz & WRz).
    fill_steps G BND.
    do 2 zstep.
    pose proof ms_stack as (MS1 & MS2 & MS3). pose proof RGR as RR'.
    eapply call_memset0A with (L := slice R2 (2 * n + tna + tnb) (2 * n - tna - tnb)) (lo := lo) (SPz := (SP + -160)%Z)
                              (D := (rp + 8 * Z.of_nat (2 * n + tna + tnb))%Z) (bd := bR);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact HEAP | exact CEIL | exact MS1 | exact MS2 | exact MS3 | exact ETP
      | apply in_or_app; left; exact INR | clear - RR' G; lia | rewrite ERz; clear - RR' G; lia | rewrite ERz; clear - G; lia
      | ulit | reflexivity | rewrite ERz; ulit | ].
    intros m5 w0' w1' w2' y1' y2' y3' y4' y5' y6' y7' w3' w4' w5' w6' F2 fc2 HEAPc AGc WMc MIc HZ STc.
    rewrite ERz in HZ, AGc.
    assert (I5 : KBK (FCELLS neg jb) m5 (splice R2 (2 * n + tna + tnb) (repeat 0%Z (2 * n - tna - tnb))) T1).
    { eapply (KK KB_cps_R);
        [ reflexivity | exact I4 | exact HEAPc | rewrite repeat_length; exact AGc | exact WMc | exact MIc | exact STc
        | exact (limbs_repeat _ _ limb_0) | rewrite repeat_length; clear - G; lia | exact HZ ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRz LRz ERz WRz HEAPc AGc WMc HZ MIc STc I4 HEAP MS1 MS2 MS3 RR'.
    do 4 zstep.
    replace (Z_to_bv 64 16) with (Z_to_bv 64 (2 * N)) by (f_equal; clear - En; lia).
    replace (Z_to_bv 64 128) with (Z_to_bv 64 (16 * N)) by (f_equal; clear - En; lia).
    setreg 25%Z (Z_to_bv 64 (16 * N + rp)) ltac:(f_equal; clear - En; lia).
    eapply (BP_tail neg); [exact I5 | exact OK].

  Qed.
  (* [comment removed for export] *)

  Lemma pow2_le_n : forall j, (j <= k)%nat -> (Nat.pow 2 j * Nat.pow 2 (k - j) = n)%nat.
  Proof. intros j Hj. rewrite <- Nat.pow_add_r. rewrite Hn. f_equal. lia. Qed.

  Lemma BP_tail_dc : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x26 x28 x29 x30 x31 F fc,
    KBK (FCELLS neg jb) m1 R T -> kc_ok RES n neg R T ->
    evt bsegs POST (ST F fc 0x24e244 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 a6 x20 (Z_to_bv 64 (2 * N))
                       x22 (Z_to_bv 64 SHB) x24 (Z_to_bv 64 (16 * N + rp)) x26 (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK. zstep. eapply (BP_tail neg); [exact I | exact OK].
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma BP_fpart : forall (kc : nat) (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc,
    (kc + 2 <= k)%nat -> (3 <= kc)%nat -> (Nat.pow 2 kc <= tna)%nat -> (Nat.pow 2 kc <= tnb)%nat ->
    (tna < 2 * Nat.pow 2 kc)%nat -> (tnb < 2 * Nat.pow 2 kc)%nat ->
    KBK (FCELLS neg jb) m1 R T -> pfpart_ok RES fuel' n neg a b tna tnb kc R T ->
    evt bsegs POST (ST F fc 0x24e4ac m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 a6 a5 (Z_to_bv 64 (2 * N))
                       a4 (Z_to_bv 64 SHB) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 (16 * N + rp))
                       (Z_to_bv 64 (Z.of_nat (Nat.pow 2 kc))) (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros Hkc Hkc3 Hia Hib Hta Htb I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    remember (Nat.pow 2 kc) as ic eqn:Eic.
    assert (Hic : (4 * ic <= n)%nat).
    { pose proof (pow2_le_n (kc + 2) Hkc) as HH. rewrite Nat.pow_add_r, <- Eic in HH. cbn [Nat.pow] in HH.
      pose proof (pow2_pos (k - (kc + 2))) as HP. clear - HH HP. nia. }
    pose proof (conj G Hic) as GH.
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (4 * ic)%nat I ltac:(clear - Hic; lia)) as (HRh & LRh & ERh & WRh).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n tna I ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n tnb I ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    do 2 zstep. rewrite A4, (bn_swrap32_small (Z.of_nat tna - Z.of_nat ic)) by (clear - G Hia; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    do 2 zstep. rewrite A5, (bn_swrap32_small (Z.of_nat tnb - Z.of_nat ic)) by (clear - G Hib; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite (bn_swrap32_small (Z.of_nat tnb - Z.of_nat ic + 0)), Z.add_0_r by (clear - G Hib; lia).
    do 6 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9. pose proof Hk as HK. pose proof Hkf as HKF.
    pose proof Hd1 as HD1. pose proof Hd2 as HD2.
    assert (HPS : (part_stackA CS8 kc <= SK)%Z) by (rewrite HSK; apply part_stackA_S; clear - Hkc; lia).
    eapply call_partA with (CS8 := CS8) (fuel := fuel') (k := kc) (a := a_hi) (b := b_hi) (tna := (tna - ic)%nat) (tnb := (tnb - ic)%nat)
                          (R := slice R (2 * n) (4 * ic)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -160)%Z)
                          (bR := bR) (bT := bT) (bA := bA) (bB := bB)
                          (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact IHp
      | apply slice_limbs; exact LA | apply slice_limbs; exact LB' | exact LRh | exact LTp
      | exact Hkc3 | clear - Hkc HKF; lia | clear - Hkc HK; lia
      | rewrite <- Eic; clear - Hta; lia | rewrite <- Eic; clear - Htb; lia | clear - HD1 Hia Hib; lia | clear - HD2 Hia Hib; lia
      | rewrite Lah, <- Eic; clear - Hia; lia | rewrite Lbh, <- Eic; clear - Hib; lia | rewrite ERh, <- Eic; reflexivity
      | rewrite ETp, <- Eic; clear - G Hic; lia
      | ulit | ulit | ulit | rewrite <- Eic; ulit | ulit | ulit | ulit
      | exact HAh | exact HBh | exact HRh | exact HTp | rewrite ERh; exact WRh | rewrite ETp; exact WTp
      | rewrite ERh, Lah; clear - D1 G Hic; lia | rewrite ERh, Lbh; clear - D2 G Hic; lia
      | rewrite ETp, Lah; clear - D3 G; lia | rewrite ETp, Lbh; clear - D4 G; lia
      | rewrite ERh, ETp; clear - D5 G Hic; lia
      | clear - G HPS; lia
      | rewrite ERh; clear - D6 G Hic HPS; lia | rewrite ETp; clear - D7 G HPS; lia
      | rewrite Lah; clear - D8 G HPS; lia | rewrite Lbh; clear - D9 G HPS; lia
      | kaside HEAP GH | kub BND G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (mul_part_recursive_spec fuel' kc a_hi b_hi (tna - ic)%nat (tnb - ic)%nat (slice R (2 * n) (4 * ic)) (skipn (4 * n) T)
                  (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB') LRh LTp Hkc3 ltac:(clear - Hkc HKF; lia)
                  ltac:(rewrite <- Eic; clear - Hta; lia) ltac:(rewrite <- Eic; clear - Htb; lia) ltac:(clear - HD1 Hia Hib; lia) ltac:(clear - HD2 Hia Hib; lia)
                  ltac:(rewrite Lah, <- Eic; clear - Hia; lia) ltac:(rewrite Lbh, <- Eic; clear - Hib; lia) ltac:(rewrite ERh, <- Eic; reflexivity)
                  ltac:(rewrite ETp, <- Eic; clear - G Hic; lia)) as MP.
    unfold mul_post in MP. unfold pfpart_ok in OK. cbv zeta in OK. rewrite <- Eic in OK.
    destruct (mul_part_recursive fuel' kc a_hi b_hi (tna - ic) (tnb - ic) (slice R (2 * n) (4 * ic)) (skipn (4 * n) T)) as [o p2]. cbn [fst snd] in *.
    destruct MP as (Lo & Eo & _ & Lp2 & Ep2). rewrite ERh in Eo. rewrite ETp in Ep2.
    assert (I2 : KBK (FCELLS neg jb) m2 (splice R (2 * n) o) (splice T (4 * n) p2)).
    { eapply (KK KB_cps) with (m1 := m1);
        [ reflexivity | exact I | exact HEAPc | rewrite Eo, Ep2; rewrite ERh, ETp in AGc; exact AGc | exact WMc | exact MIc | exact STc
        | exact Lo | exact Lp2 | rewrite Eo; clear - Hic; lia | rewrite Ep2; clear - G; lia | exact HSR | exact HST ]. }
    zstep.
    eapply (BP_tail_dc neg); [exact I2 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma BP_frec : forall (kc : nat) (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc,
    (kc + 2 <= k)%nat -> (1 <= kc)%nat -> (tna <= Nat.pow 2 kc)%nat -> (tnb <= Nat.pow 2 kc)%nat ->
    (Nat.pow 2 kc <= tna + 1)%nat -> (Nat.pow 2 kc <= tnb + 1)%nat ->
    KBK (FCELLS neg jb) m1 R T -> pfrec_ok RES n neg a b tna tnb kc R T ->
    evt bsegs POST (ST F fc 0x24e474 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 a6 a5 (Z_to_bv 64 (2 * N))
                       a4 (Z_to_bv 64 SHB) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 (16 * N + rp))
                       (Z_to_bv 64 (Z.of_nat (Nat.pow 2 kc))) (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros Hkc Hkc1 Hia Hib Hta Htb I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    pose proof (scratch_rec_le kc) as HSC.
    remember (Nat.pow 2 kc) as ic eqn:Eic.
    assert (Hic : (4 * ic <= n)%nat).
    { pose proof (pow2_le_n (kc + 2) Hkc) as HH. rewrite Nat.pow_add_r, <- Eic in HH. cbn [Nat.pow] in HH.
      pose proof (pow2_pos (k - (kc + 2))) as HP. clear - HH HP. nia. }
    pose proof (conj G (conj Hic HSC)) as GH.
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * ic)%nat I ltac:(clear - Hic; lia)) as (HRh & LRh & ERh & WRh).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n tna I ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n tnb I ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    do 2 zstep. rewrite A4, (bn_swrap32_small (Z.of_nat tna - Z.of_nat ic)) by (clear - G Hia Hic; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    do 2 zstep. rewrite A5, (bn_swrap32_small (Z.of_nat tnb - Z.of_nat ic)) by (clear - G Hib Hic; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_mod (Z.of_nat tnb - Z.of_nat ic) 0), Z.add_0_r by (clear - G Hib Hic; lia).
    do 6 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9. pose proof Hk as HK.
    assert (HPS : (rec_stackA CS8 kc <= SK)%Z) by (pose proof SK_rec; pose proof (rec_stackA_mono CS8 kc k ltac:(clear - Hkc; lia)); lia).
    eapply call_recA with (CS8 := CS8) (k := kc) (a := a_hi) (b := b_hi) (da := (ic - tna)%nat) (db := (ic - tnb)%nat)
                         (R := slice R (2 * n) (2 * ic)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -160)%Z)
                         (bR := bR) (bT := bT) (bA := bA) (bB := bB)
                         (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (bn_mul_recursive_aspec CS8 CS8_0 comba8_ok sub_part_ok mul_normal_ok kc)
      | apply slice_limbs; exact LA | apply slice_limbs; exact LB' | exact LRh | exact LTp
      | clear - Hkc Hkc1 HK; lia | clear - Hta; lia | clear - Htb; lia
      | rewrite Lah, <- Eic; clear - Hia; lia | rewrite Lbh, <- Eic; clear - Hib; lia | rewrite ERh, <- Eic; reflexivity
      | rewrite ETp; clear - G Hic HSC; lia
      | ulit | ulit | ulit | rewrite <- Eic; ulit | f_equal; clear - Hia; lia | f_equal; clear - Hib; lia | ulit
      | exact HAh | exact HBh | exact HRh | exact HTp | rewrite ERh; exact WRh | rewrite ETp; exact WTp
      | rewrite ERh, Lah; clear - D1 G Hic; lia | rewrite ERh, Lbh; clear - D2 G Hic; lia
      | rewrite ETp, Lah; clear - D3 G; lia | rewrite ETp, Lbh; clear - D4 G; lia
      | rewrite ERh, ETp; clear - D5 G Hic; lia
      | clear - G HPS; lia
      | rewrite ERh; clear - D6 G Hic HPS; lia | rewrite ETp; clear - D7 G HPS; lia
      | rewrite Lah; clear - D8 G HPS; lia | rewrite Lbh; clear - D9 G HPS; lia
      | kaside HEAP GH | kub BND G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec kc a_hi b_hi (ic - tna)%nat (ic - tnb)%nat (slice R (2 * n) (2 * ic)) (skipn (4 * n) T)
                  (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB') LRh LTp Hkc1 ltac:(clear - Hta; lia) ltac:(clear - Htb; lia)
                  ltac:(rewrite Lah, <- Eic; clear - Hia; lia) ltac:(rewrite Lbh, <- Eic; clear - Hib; lia) ltac:(rewrite ERh, <- Eic; reflexivity)
                  ltac:(rewrite ETp; clear - G Hic HSC; lia)) as MP.
    unfold mul_post in MP. unfold pfrec_ok in OK. cbv zeta in OK. rewrite <- Eic in OK.
    destruct (mul_recursive kc a_hi b_hi (ic - tna) (ic - tnb) (slice R (2 * n) (2 * ic)) (skipn (4 * n) T)) as [o p2]. cbn [fst snd] in *.
    destruct MP as (Lo & Eo & _ & Lp2 & Ep2). rewrite ERh in Eo. rewrite ETp in Ep2.
    assert (I2 : KBK (FCELLS neg jb) m2 (splice R (2 * n) o) (splice T (4 * n) p2)).
    { eapply (KK KB_cps) with (m1 := m1);
        [ reflexivity | exact I | exact HEAPc | rewrite Eo, Ep2; rewrite ERh, ETp in AGc; exact AGc | exact WMc | exact MIc | exact STc
        | exact Lo | exact Lp2 | rewrite Eo; clear - Hic; lia | rewrite Ep2; clear - G; lia | exact HSR | exact HST ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HRh LRh ERh WRh HTp LTp ETp WTp HAh HBh HEAPc AGc WMc HSR HST MIc STc I.
    zstep.
    eapply (BP_tail_dc neg); [exact I2 | exact OK].

  Qed.

  Lemma pow2_gt8 : forall j, (8 < Nat.pow 2 j)%nat -> (4 <= j)%nat.
  Proof.
    intros j H. destruct (Nat.le_gt_cases 4 j) as [|Hlt]; [assumption|exfalso].
    assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3)%nat as [->|[->|[->| ->]]] by lia; cbn in H; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma BP_find : forall (ki : nat) (neg : bool) jb m1 R T x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc,
    (ki + 2 <= k)%nat -> (Nat.max tna tnb < 2 * Nat.pow 2 ki)%nat -> (16 <= Nat.max tna tnb)%nat ->
    KBK (FCELLS neg jb) m1 R T -> pfind_ok RES fuel' n neg a b tna tnb ki R T ->
    evt bsegs POST (ST F fc 0x24e464 m1 x1 x5 x6 x7 a0 (Z_to_bv 64 (Z.of_nat (Nat.max tna tnb))) x11 x12 x13 x14 x15 x16 x17 a3 a6 a5 (Z_to_bv 64 (2 * N))
                       a4 (Z_to_bv 64 SHB) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 (16 * N + rp))
                       (Z_to_bv 64 (Z.of_nat (2 * Nat.pow 2 ki))) (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    induction ki as [|ki' IHk]; intros until fc; intros Hki Hmx H16 I OK.
    { exfalso. cbn [Nat.pow] in Hmx. clear - Hmx H16. lia. }
    pose proof geom as G.
    remember (Nat.pow 2 (S ki')) as ic eqn:Eic.
    assert (Hic : (4 * ic <= n)%nat).
    { pose proof (pow2_le_n (S ki' + 2) Hki) as HH. rewrite Nat.pow_add_r, <- Eic in HH. cbn [Nat.pow] in HH.
      pose proof (pow2_pos (k - (S ki' + 2))) as HP. clear - HH HP. nia. }
    pose proof Hd1 as HD1. pose proof Hd2 as HD2.
    assert (Eic2 : ic = (2 * Nat.pow 2 ki')%nat) by (rewrite Eic; cbn [Nat.pow]; clear; lia).
    zstep. rewrite (Nat2Z.inj_mul 2 ic). change (Z.of_nat 2) with 2%Z. rewrite srliw_half by (clear - G Hic; lia).
    zstep. rewrite lts_small by (clear - G Hic; lia).
    if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      unfold pfind_ok in OK. rewrite kara_find_lt in OK by (rewrite <- Eic; clear - K1; lia).
      rewrite Eic. eapply (BP_fpart (S ki') neg); [exact Hki | assert (H4 : (4 <= S ki')%nat) by (apply pow2_gt8; rewrite <- Eic; clear - Hmx H16 Eic2; lia); clear - H4; lia
        | rewrite <- Eic; clear - K1 HD1 HD2; lia | rewrite <- Eic; clear - K1 HD1 HD2; lia
        | rewrite <- Eic; clear - Hmx; lia | rewrite <- Eic; clear - Hmx; lia | exact I | exact OK]. }
    zstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      unfold pfind_ok in OK. rewrite kara_find_eq in OK by (rewrite <- Eic; clear - K1 K2 A4; lia).
      rewrite Eic. eapply (BP_frec (S ki') neg); [exact Hki | clear; lia
        | rewrite <- Eic; clear - K1; lia | rewrite <- Eic; clear - K1; lia
        | rewrite <- Eic; clear - K2 A4; lia | rewrite <- Eic; clear - K2 A4 HD1 HD2; lia | exact I | exact OK]. }
    zstep. if_cases K3; zify_cond K3.
    { (* [comment removed for export] *)
      assert (Hlt : (tna < ic /\ tnb < ic)%nat) by (clear - K1 K2 K3 A4 A5; lia).
      unfold pfind_ok in OK. rewrite kara_find_S in OK by (rewrite <- Eic; clear - Hlt; lia).
      replace (Z_to_bv 64 (Z.of_nat ic)) with (Z_to_bv 64 (Z.of_nat (2 * Nat.pow 2 ki'))) by (rewrite Eic2; reflexivity).
      eapply (IHk neg); [clear - Hki; lia | rewrite <- Eic2; clear - Hlt; lia | exact H16 | exact I | exact OK]. }
    (* [comment removed for export] *)
    unfold pfind_ok in OK. rewrite kara_find_eq in OK by (rewrite <- Eic; clear - K1 K3 A5; lia).
    rewrite Eic. eapply (BP_frec (S ki') neg); [exact Hki | clear; lia
      | rewrite <- Eic; clear - K1; lia | rewrite <- Eic; clear - K1; lia
      | rewrite <- Eic; clear - K3 A5 HD1 HD2; lia | rewrite <- Eic; clear - K3 A5; lia | exact I | exact OK].

  Qed.

  Lemma BP_fill : forall (neg : bool) jb (off len : nat) m1 R T x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x20 x22 x24 x26 x28 x29 x30 x31 F fc,
    (off + len <= 4 * n)%nat ->
    KBK (FCELLS neg jb) m1 R T -> kc_ok RES n neg (splice R off (repeat 0%Z len)) T ->
    evt bsegs POST (ST F fc 0x24e23c m1 x1 x5 x6 x7 a0 (Z_to_bv 64 (rp + 8 * Z.of_nat off)) x11 (Z_to_bv 64 (8 * Z.of_nat len)) x13 x14 x15 x16 x17
                       a3 a6 x20 (Z_to_bv 64 (2 * N)) x22 (Z_to_bv 64 SHB) x24 (Z_to_bv 64 (16 * N + rp)) x26 (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros Hol I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ off len I Hol) as (HRz & LRz & ERz & WRz).
    do 2 zstep.
    pose proof ms_stack as (MS1 & MS2 & MS3). pose proof RGR as RR'.
    eapply call_memset0A with (L := slice R off len) (lo := lo) (SPz := (SP + -160)%Z) (D := (rp + 8 * Z.of_nat off)%Z) (bd := bR);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact HEAP | exact CEIL | exact MS1 | exact MS2 | exact MS3 | exact ETP
      | apply in_or_app; left; exact INR | clear - RR' G; lia | rewrite ERz; clear - RR' G Hol; lia | rewrite ERz; clear - G Hol; lia
      | ulit | reflexivity | rewrite ERz; ulit | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HZ STc.
    rewrite ERz in HZ, AGc.
    assert (I2 : KBK (FCELLS neg jb) m2 (splice R off (repeat 0%Z len)) T).
    { eapply (KK KB_cps_R);
        [ reflexivity | exact I | exact HEAPc | rewrite repeat_length; exact AGc | exact WMc | exact MIc | exact STc
        | exact (limbs_repeat _ _ limb_0) | rewrite repeat_length; exact Hol | exact HZ ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRz LRz ERz WRz HEAPc AGc WMc HZ MIc STc I HEAP MS1 MS2 MS3 RR'.
    eapply (BP_tail_dc neg); [exact I2 | exact OK].

  Qed.

  Lemma BP_find' : forall (ki : nat) (neg : bool) jb m1 R T (w10 : word) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc,
    w10 = Z_to_bv 64 (Z.of_nat (Nat.max tna tnb)) ->
    (ki + 2 <= k)%nat -> (Nat.max tna tnb < 2 * Nat.pow 2 ki)%nat -> (16 <= Nat.max tna tnb)%nat ->
    KBK (FCELLS neg jb) m1 R T -> pfind_ok RES fuel' n neg a b tna tnb ki R T ->
    evt bsegs POST (ST F fc 0x24e464 m1 x1 x5 x6 x7 a0 w10 x11 x12 x13 x14 x15 x16 x17 a3 a6 a5 (Z_to_bv 64 (2 * N))
                       a4 (Z_to_bv 64 SHB) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 (16 * N + rp))
                       (Z_to_bv 64 (Z.of_nat (2 * Nat.pow 2 ki))) (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof. intros until fc. intros E. subst w10. apply BP_find. Qed.

  Notation i_ := (Nat.pow 2 (k - 1)).
  Lemma n_2i : (4 <= k)%nat -> n = (2 * i_)%nat.
  Proof. intros H. rewrite Hn. replace k with (S (k - 1)) at 1 by lia. cbn [Nat.pow]. lia. Qed.

  (* [comment removed for export] *)
  Lemma BP_jneg : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc,
    (4 <= k)%nat -> (Nat.max tna tnb < i_)%nat ->
    KBK (FCELLS neg jb) m1 R T -> pjneg_ok RES fuel' k n neg a b tna tnb R T ->
    evt bsegs POST (ST F fc 0x24e418 m1 x1 x5 x6 x7 a0 x10 (Z_to_bv 64 1) x12 x13 x14 x15 x16 x17 a3 a6 a5 (Z_to_bv 64 (2 * N))
                       a4 (Z_to_bv 64 SHB) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 (16 * N + rp))
                       (Z_to_bv 64 (Z.of_nat i_)) (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros Hk4 Hmx I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G. pose proof (n_2i Hk4) as En.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear; lia)) as (HRz & LRz & ERz & WRz).
    zstep. if_false.
    do 4 zstep.
    pose proof ms_stack as (MS1 & MS2 & MS3). pose proof RGR as RR'.
    eapply call_memset0A with (L := slice R (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -160)%Z) (D := (rp + 8 * Z.of_nat (2 * n))%Z) (bd := bR);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact HEAP | exact CEIL | exact MS1 | exact MS2 | exact MS3 | exact ETP
      | apply in_or_app; left; exact INR | clear - RR' G; lia | rewrite ERz; clear - RR' G; lia | rewrite ERz; clear - G; lia
      | ulit | reflexivity | rewrite ERz; ulit | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HZ STc.
    rewrite ERz in HZ, AGc.
    assert (I2 : KBK (FCELLS neg jb) m2 (splice R (2 * n) (repeat 0%Z (2 * n))) T).
    { eapply (KK KB_cps_R);
        [ reflexivity | exact I | exact HEAPc | rewrite repeat_length; exact AGc | exact WMc | exact MIc | exact STc
        | exact (limbs_repeat _ _ limb_0) | rewrite repeat_length; clear; lia | exact HZ ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRz LRz ERz WRz HEAPc AGc WMc HZ MIc STc I HEAP MS1 MS2 MS3 RR'.
    unfold pjneg_ok in OK. cbv zeta in OK.
    remember (splice R (2 * n) (repeat 0%Z (2 * n))) as R2 eqn:ER2. clear ER2.
    assert (TOFIND : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 F' fc',
               ((tna <? 16)%nat && (tnb <? 16)%nat = false) ->
               evt bsegs POST (ST F' fc' 0x24e458 m2 y1 y5 y6 y7 a0 y10 y11 y12 y13 y14 y15 y16 y17 a3 a6 a5 (Z_to_bv 64 (2 * N))
                                  a4 (Z_to_bv 64 SHB) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 (16 * N + rp))
                                  (Z_to_bv 64 (Z.of_nat i_)) (Z_to_bv 64 (16 * N)) y28 y29 y30 y31)).
    { intros until fc'. intros Esm. rewrite Esm in OK.
      assert (H16 : (16 <= Nat.max tna tnb)%nat).
      { apply andb_false_elim in Esm. destruct Esm as [E|E]; apply Nat.ltb_ge in E; clear - E; lia. }
      assert (Ei2 : i_ = (2 * Nat.pow 2 (k - 1 - 1))%nat).
      { replace (k - 1)%nat with (S (k - 1 - 1)) at 1 by (clear - Hk4; lia). cbn [Nat.pow]. clear. lia. }
      rewrite Ei2.
      assert (L4 : (bv_unsigned a4 < 9223372036854775808)%Z) by (rewrite A4; clear - G; lia).
      assert (L5 : (bv_unsigned a5 < 9223372036854775808)%Z) by (rewrite A5; clear - G; lia).
      zstep.
      zstep. rewrite (lts_words_small a5 a4 L5 L4). rewrite A4, A5.
      if_cases K1; zify_cond K1.
      - eapply (BP_find' (k - 1 - 1) neg); [ | clear - Hk4; lia | rewrite <- Ei2; exact Hmx | exact H16 | exact I2 | exact OK].
        rewrite <- (Z_to_bv_bv_unsigned a4), A4. f_equal. clear - K1. lia.
      - zstep.
        eapply (BP_find' (k - 1 - 1) neg); [ | clear - Hk4; lia | rewrite <- Ei2; exact Hmx | exact H16 | exact I2 | exact OK].
        rewrite <- (Z_to_bv_bv_unsigned a5), A5. f_equal. clear - K1. lia. }
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    zstep.
    assert (L15 : (bv_unsigned (Z_to_bv 64 15) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (L4 : (bv_unsigned a4 < 9223372036854775808)%Z) by (rewrite A4; clear - G; lia).
    zstep. rewrite (lts_words_small (Z_to_bv 64 15) a4 L15 L4). rewrite A4.
    if_cases K1; zify_cond K1.
    { eapply TOFIND. destruct (Nat.ltb_spec tna 16) as [HH|_]; [exfalso; clear - HH K1; lia | reflexivity]. }
    zstep.
    assert (L16 : (bv_unsigned (Z_to_bv 64 16) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (L5 : (bv_unsigned a5 < 9223372036854775808)%Z) by (rewrite A5; clear - G; lia).
    zstep. rewrite (lts_words_small a5 (Z_to_bv 64 16) L5 L16). rewrite A5.
    if_cases K2; zify_cond K2.
    { eapply TOFIND. destruct (Nat.ltb_spec tnb 16) as [HH|_]; [exfalso; clear - HH K2; lia | apply andb_false_r]. }
    (* [comment removed for export] *)
    assert (Esm : ((tna <? 16)%nat && (tnb <? 16)%nat = true)).
    { apply andb_true_iff. split; apply Nat.ltb_lt; [clear - K1 | clear - K2]; lia. }
    rewrite Esm in OK. clear TOFIND.
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (tna + tnb)%nat I2 ltac:(clear - G; lia)) as (_ & _ & _ & WRn).
    pose proof (KACC KB_a _ _ _ _ n tna I2 ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n tnb I2 ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    do 6 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof SEPR as D3. pose proof SEPA as D4. pose proof SEPB as D5.
    eapply call_mul_normalA with (a := a_hi) (b := b_hi) (lo := lo) (SPz := (SP + -160)%Z)
                                (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I2) | exact mul_normal_ok | apply slice_limbs; exact LA | apply slice_limbs; exact LB'
      | rewrite Lah, Lbh; clear - G; lia
      | ulit | ulit | rewrite Lah; exact A4 | ulit | rewrite Lbh; exact A5
      | exact HAh | exact HBh
      | rewrite Lah, Lbh; replace (Z.of_nat tna + Z.of_nat tnb)%Z with (Z.of_nat (tna + tnb)) by (clear; lia); exact WRn
      | rewrite Lah, Lbh; clear - D1 G; lia | rewrite Lah, Lbh; clear - D2 G; lia | clear - G; lia
      | rewrite Lah, Lbh; clear - D3 G; lia | rewrite Lah; clear - D4 G; lia | rewrite Lbh; clear - D5 G; lia
      | kasanN I2 G | ub_tac BND G | ub_tac BND2 G | ub_tac BND2 G | ].
    intros m4 w0 w1 w2 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 MUc WMc MIc' HS STc.
    destruct (mul_normal_spec a_hi b_hi (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB')) as (LMN & _ & EMN).
    assert (EMN' : length (mul_normal a_hi b_hi) = (tna + tnb)%nat).
    { rewrite EMN, Lah, Lbh. destruct (Nat.eqb_spec tna 0); destruct (Nat.eqb_spec tnb 0); cbn [orb]; clear - G e || clear - G e e0 || clear - G; lia. }
    clear EMN.
    pose proof (KAFTER KB_after_R (FCELLS neg jb) m2 m4 R2 T (2 * n)%nat (mul_normal a_hi b_hi) _ 240%Z eq_refl I2 MUc
                  ltac:(rewrite Lah, Lbh, EMN'; clear; lia)
                  ltac:(clear - G; lia) WMc MIc' HS STc LMN ltac:(rewrite EMN'; clear - G; lia)) as I4.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM WRn HAh HBh MUc WMc HS I2 MIc' STc D1 D2 D3 D4 D5.
    zstep.
    eapply (BP_tail_dc neg); [exact I4 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma BP_jpos : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc,
    (4 <= k)%nat -> (i_ < Nat.max tna tnb)%nat ->
    KBK (FCELLS neg jb) m1 R T -> pjpos_ok RES fuel' k n neg a b tna tnb R T ->
    evt bsegs POST (ST F fc 0x24e110 m1 x1 x5 x6 x7 a0 x10 (Z_to_bv 64 1) x12 x13 x14 x15 x16 x17 a3 a6 a5 (Z_to_bv 64 (2 * N))
                       a4 (Z_to_bv 64 SHB) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 (16 * N + rp))
                       (Z_to_bv 64 (Z.of_nat i_)) (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros Hk4 Hmx I OK.
    pose proof (n_2i Hk4) as En2i. pose proof Hd1 as HD1'. pose proof Hd2 as HD2'. pose proof Htna as HTA. pose proof Htnb as HTB.
    assert (Hkc : (k - 1 + 1 <= k)%nat) by (clear - Hk4; lia). assert (Hkc3 : (3 <= k - 1)%nat) by (clear - Hk4; lia).
    assert (Hia : (Nat.pow 2 (k - 1) <= tna)%nat) by (clear - Hmx HD1' HD2'; lia).
    assert (Hib : (Nat.pow 2 (k - 1) <= tnb)%nat) by (clear - Hmx HD1' HD2'; lia).
    assert (Hta : (tna < 2 * Nat.pow 2 (k - 1))%nat) by (clear - En2i HTA; lia).
    assert (Htb : (tnb < 2 * Nat.pow 2 (k - 1))%nat) by (clear - En2i HTB; lia).
    clear HD1' HD2' HTA HTB. set (kc := (k - 1)%nat) in *.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    remember (Nat.pow 2 kc) as ic eqn:Eic.
    assert (Hic : (2 * ic = n)%nat) by (clear - En2i; lia).
    pose proof (conj G Hic) as GH.
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (4 * ic)%nat I ltac:(clear - Hic; lia)) as (HRh & LRh & ERh & WRh).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n tna I ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n tnb I ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    zstep. if_false.
    do 2 zstep. rewrite A4, (bn_swrap32_small (Z.of_nat tna - Z.of_nat ic)) by (clear - G Hia; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    do 2 zstep. rewrite A5, (bn_swrap32_small (Z.of_nat tnb - Z.of_nat ic)) by (clear - G Hib; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite (bn_swrap32_small (Z.of_nat tnb - Z.of_nat ic + 0)), Z.add_0_r by (clear - G Hib; lia).
    do 6 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9. pose proof Hk as HK. pose proof Hkf as HKF.
    pose proof Hd1 as HD1. pose proof Hd2 as HD2.
    assert (HPS : (part_stackA CS8 kc <= SK)%Z) by (rewrite HSK; apply part_stackA_S; subst kc; clear - Hk4; lia).
    eapply call_partA with (CS8 := CS8) (fuel := fuel') (k := kc) (a := a_hi) (b := b_hi) (tna := (tna - ic)%nat) (tnb := (tnb - ic)%nat)
                          (R := slice R (2 * n) (4 * ic)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -160)%Z)
                          (bR := bR) (bT := bT) (bA := bA) (bB := bB)
                          (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact IHp
      | apply slice_limbs; exact LA | apply slice_limbs; exact LB' | exact LRh | exact LTp
      | exact Hkc3 | subst kc; clear - Hk4 HKF; lia | subst kc; clear - HK; lia
      | rewrite <- Eic; clear - Hta; lia | rewrite <- Eic; clear - Htb; lia | clear - HD1 Hia Hib; lia | clear - HD2 Hia Hib; lia
      | rewrite Lah, <- Eic; clear - Hia; lia | rewrite Lbh, <- Eic; clear - Hib; lia | rewrite ERh, <- Eic; reflexivity
      | rewrite ETp, <- Eic; clear - G Hic; lia
      | ulit | ulit | ulit | rewrite <- Eic; ulit | ulit | ulit | ulit
      | exact HAh | exact HBh | exact HRh | exact HTp | rewrite ERh; exact WRh | rewrite ETp; exact WTp
      | rewrite ERh, Lah; clear - D1 G Hic; lia | rewrite ERh, Lbh; clear - D2 G Hic; lia
      | rewrite ETp, Lah; clear - D3 G; lia | rewrite ETp, Lbh; clear - D4 G; lia
      | rewrite ERh, ETp; clear - D5 G Hic; lia
      | clear - G HPS; lia
      | rewrite ERh; clear - D6 G Hic HPS; lia | rewrite ETp; clear - D7 G HPS; lia
      | rewrite Lah; clear - D8 G HPS; lia | rewrite Lbh; clear - D9 G HPS; lia
      | kaside HEAP GH | kub BND G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (mul_part_recursive_spec fuel' kc a_hi b_hi (tna - ic)%nat (tnb - ic)%nat (slice R (2 * n) (4 * ic)) (skipn (4 * n) T)
                  (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB') LRh LTp Hkc3 ltac:(subst kc; clear - Hk4 HKF; lia)
                  ltac:(rewrite <- Eic; clear - Hta; lia) ltac:(rewrite <- Eic; clear - Htb; lia) ltac:(clear - HD1 Hia Hib; lia) ltac:(clear - HD2 Hia Hib; lia)
                  ltac:(rewrite Lah, <- Eic; clear - Hia; lia) ltac:(rewrite Lbh, <- Eic; clear - Hib; lia) ltac:(rewrite ERh, <- Eic; reflexivity)
                  ltac:(rewrite ETp, <- Eic; clear - G Hic; lia)) as MP.
    unfold mul_post in MP. unfold pjpos_ok in OK. cbv zeta in OK. fold kc in OK. rewrite <- Eic in OK.
    destruct (mul_part_recursive fuel' kc a_hi b_hi (tna - ic) (tnb - ic) (slice R (2 * n) (4 * ic)) (skipn (4 * n) T)) as [o p2]. cbn [fst snd] in *.
    destruct MP as (Lo & Eo & _ & Lp2 & Ep2). rewrite ERh in Eo. rewrite ETp in Ep2.
    assert (I2 : KBK (FCELLS neg jb) m2 (splice R (2 * n) o) (splice T (4 * n) p2)).
    { eapply (KK KB_cps) with (m1 := m1);
        [ reflexivity | exact I | exact HEAPc | rewrite Eo, Ep2; rewrite ERh, ETp in AGc; exact AGc | exact WMc | exact MIc | exact STc
        | exact Lo | exact Lp2 | rewrite Eo; clear - Hic; lia | rewrite Ep2; clear - G; lia | exact HSR | exact HST ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRh LRh ERh WRh HTp LTp ETp WTp HAh HBh HEAPc AGc WMc HSR HST MIc STc I.
    pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ST & MI & _).
    fill_steps G BND.
    zstep.
    eapply (BP_fill neg jb (2 * n + tna + tnb) (2 * n - tna - tnb)); [clear - G; lia | exact I2 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma BP_j0 : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 F fc,
    (4 <= k)%nat -> (Nat.max tna tnb = i_)%nat ->
    KBK (FCELLS neg jb) m1 R T -> pj0_ok RES k n neg a b tna tnb R T ->
    evt bsegs POST (ST F fc 0x24e1b0 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 a6 a5 (Z_to_bv 64 (2 * N))
                       a4 (Z_to_bv 64 SHB) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) x25
                       (Z_to_bv 64 (Z.of_nat i_)) (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros Hk4 Hmx I OK.
    pose proof (n_2i Hk4) as En2i. pose proof Hd1 as HD1'. pose proof Hd2 as HD2'.
    assert (Hkc1 : (1 <= k - 1)%nat) by (clear - Hk4; lia).
    assert (Hia : (tna <= Nat.pow 2 (k - 1))%nat) by (clear - Hmx; lia).
    assert (Hib : (tnb <= Nat.pow 2 (k - 1))%nat) by (clear - Hmx; lia).
    assert (Hta : (Nat.pow 2 (k - 1) <= tna + 1)%nat) by (clear - Hmx HD1' HD2'; lia).
    assert (Htb : (Nat.pow 2 (k - 1) <= tnb + 1)%nat) by (clear - Hmx HD1' HD2'; lia).
    clear HD1' HD2'. set (kc := (k - 1)%nat) in *.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    pose proof (scratch_rec_le kc) as HSC.
    remember (Nat.pow 2 kc) as ic eqn:Eic.
    assert (Hic : (2 * ic = n)%nat) by (clear - En2i; lia).
    pose proof (conj G (conj Hic HSC)) as GH.
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * ic)%nat I ltac:(clear - Hic; lia)) as (HRh & LRh & ERh & WRh).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n tna I ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n tnb I ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    zstep.
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    do 4 zstep.
    setreg 10%Z (Z_to_bv 64 1) ltac:(replace (16 * N + rp <? 16 * N)%Z with false by (symmetry; apply Z.ltb_ge; clear - BND; lia); reflexivity).
    zstep. if_false.
    do 2 zstep. rewrite A4, (bn_swrap32_small (Z.of_nat tna - Z.of_nat ic)) by (clear - G Hia Hic; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    do 2 zstep. rewrite A5, (bn_swrap32_small (Z.of_nat tnb - Z.of_nat ic)) by (clear - G Hib Hic; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_mod (Z.of_nat tnb - Z.of_nat ic) 0), Z.add_0_r by (clear - G Hib Hic; lia).
    do 6 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9. pose proof Hk as HK.
    assert (HPS : (rec_stackA CS8 kc <= SK)%Z) by (pose proof SK_rec; pose proof (rec_stackA_mono CS8 kc k ltac:(subst kc; clear; lia)); lia).
    eapply call_recA with (CS8 := CS8) (k := kc) (a := a_hi) (b := b_hi) (da := (ic - tna)%nat) (db := (ic - tnb)%nat)
                         (R := slice R (2 * n) (2 * ic)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -160)%Z)
                         (bR := bR) (bT := bT) (bA := bA) (bB := bB)
                         (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (bn_mul_recursive_aspec CS8 CS8_0 comba8_ok sub_part_ok mul_normal_ok kc)
      | apply slice_limbs; exact LA | apply slice_limbs; exact LB' | exact LRh | exact LTp
      | subst kc; clear - Hkc1 HK; lia | clear - Hta; lia | clear - Htb; lia
      | rewrite Lah, <- Eic; clear - Hia; lia | rewrite Lbh, <- Eic; clear - Hib; lia | rewrite ERh, <- Eic; reflexivity
      | rewrite ETp; clear - G Hic HSC; lia
      | ulit | ulit | ulit | rewrite <- Eic; ulit | f_equal; clear - Hia; lia | f_equal; clear - Hib; lia | ulit
      | exact HAh | exact HBh | exact HRh | exact HTp | rewrite ERh; exact WRh | rewrite ETp; exact WTp
      | rewrite ERh, Lah; clear - D1 G Hic; lia | rewrite ERh, Lbh; clear - D2 G Hic; lia
      | rewrite ETp, Lah; clear - D3 G; lia | rewrite ETp, Lbh; clear - D4 G; lia
      | rewrite ERh, ETp; clear - D5 G Hic; lia
      | clear - G HPS; lia
      | rewrite ERh; clear - D6 G Hic HPS; lia | rewrite ETp; clear - D7 G HPS; lia
      | rewrite Lah; clear - D8 G HPS; lia | rewrite Lbh; clear - D9 G HPS; lia
      | kaside HEAP GH | kub BND G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec kc a_hi b_hi (ic - tna)%nat (ic - tnb)%nat (slice R (2 * n) (2 * ic)) (skipn (4 * n) T)
                  (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB') LRh LTp Hkc1 ltac:(clear - Hta; lia) ltac:(clear - Htb; lia)
                  ltac:(rewrite Lah, <- Eic; clear - Hia; lia) ltac:(rewrite Lbh, <- Eic; clear - Hib; lia) ltac:(rewrite ERh, <- Eic; reflexivity)
                  ltac:(rewrite ETp; clear - G Hic HSC; lia)) as MP.
    unfold mul_post in MP. unfold pj0_ok in OK. cbv zeta in OK. fold kc in OK. rewrite <- Eic in OK.
    destruct (mul_recursive kc a_hi b_hi (ic - tna) (ic - tnb) (slice R (2 * n) (2 * ic)) (skipn (4 * n) T)) as [o p2]. cbn [fst snd] in *.
    destruct MP as (Lo & Eo & _ & Lp2 & Ep2). rewrite ERh in Eo. rewrite ETp in Ep2.
    assert (I2 : KBK (FCELLS neg jb) m2 (splice R (2 * n) o) (splice T (4 * n) p2)).
    { eapply (KK KB_cps) with (m1 := m1);
        [ reflexivity | exact I | exact HEAPc | rewrite Eo, Ep2; rewrite ERh, ETp in AGc; exact AGc | exact WMc | exact MIc | exact STc
        | exact Lo | exact Lp2 | rewrite Eo; clear - Hic; lia | rewrite Ep2; clear - G; lia | exact HSR | exact HST ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRh LRh ERh WRh HTp LTp ETp WTp HAh HBh HEAPc AGc WMc HSR HST MIc STc I.
    pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ST & MI & _).
    do 3 zstep.
    setreg 11%Z (Z_to_bv 64 N) ltac:(rewrite A3; replace N with (2 * Z.of_nat ic)%Z by (clear - Hic; lia);
                                     rewrite land_even_mask64 by (clear - G Hic; lia); reflexivity).
    zstep. rewrite (bn_swrap32_small (2 * N + N)) by (clear - G; lia).
    zstep. replace ((2 * N + N) ≪ 3)%Z with (8 * Z.of_nat (2 * n + 2 * ic))%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear - Hic; lia).
    zstep.
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB Hic; lia).
    do 4 zstep.
    setreg 12%Z (Z_to_bv 64 1) ltac:(
      replace (8 * Z.of_nat (2 * n + 2 * ic) + rp <? rp)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      rewrite lxor_signbit by (clear - G; lia);
      replace (2 * N + N + 9223372036854775808 <? 9223372036854775808)%Z with false by (symmetry; apply Z.ltb_ge; clear - G; lia);
      reflexivity).
    zstep. if_false.
    zstep. rewrite (bn_swrap32_small (2 * N - N)) by (clear - G; lia).
    zstep. replace ((2 * N - N) ≪ 3)%Z with (8 * Z.of_nat (2 * n - 2 * ic))%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear - Hic; lia).
    setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (2 * n + 2 * ic))) ltac:(f_equal; clear; lia).
    eapply (BP_fill neg jb (2 * n + 2 * ic) (2 * n - 2 * ic)); [clear - Hic; lia | exact I2 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma BP_split : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 F fc,
    (4 <= k)%nat ->
    KBK (FCELLS neg jb) m1 R T -> pgen3_ok RES fuel' k n neg a b tna tnb R T ->
    evt bsegs POST (ST F fc 0x24e0bc m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 a6 a5 (Z_to_bv 64 (2 * N))
                       a4 (Z_to_bv 64 SHB) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) x25 x26 (Z_to_bv 64 (16 * N)) x28 x29 x30 x31).
  Proof.
    intros until fc. intros Hk4 I OK.
    pose proof geom as G. pose proof (n_2i Hk4) as En2i.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    unfold pgen3_ok in OK. cbv zeta in OK.
    assert (CONT : forall y11,
               evt bsegs POST (ST F fc 0x24e0e0 m1 x1 x5 x6 x7 a0 (Z_to_bv 64 (Z.of_nat (Nat.max tna tnb) - Z.of_nat i_)) y11 x12 x13 x14 x15 x16 x17 a3 a6 a5
                                  (Z_to_bv 64 (2 * N)) a4 (Z_to_bv 64 SHB) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) x25
                                  (Z_to_bv 64 (Z.of_nat i_)) (Z_to_bv 64 (16 * N)) x28 x29 x30 x31)).
    { intros y11.
      pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
      zstep. rewrite ?land_m64. rewrite (bn_swrap32_mod (Z.of_nat (Nat.max tna tnb) - Z.of_nat i_) 0), Z.add_0_r by (clear - G En2i; lia).
      zstep. if_cases K0; zify_cond K0; rewrite ?land_m64 in K0.
      { destruct (Nat.eqb_spec (Nat.max tna tnb) i_) as [E|NE]; [|exfalso; apply NE; clear - K0 G En2i; Z.div_mod_to_equations; lia].
        eapply (BP_j0 neg); [exact Hk4 | exact E | exact I | exact OK]. }
    (* [comment removed for export] *)
      destruct (Nat.eqb_spec (Nat.max tna tnb) i_) as [E|NE]; [exfalso; apply K0; rewrite E, Z.sub_diag; reflexivity|].
      do 9 zstep.
      setreg 11%Z (Z_to_bv 64 1) ltac:(
        replace (0 <? rp)%Z with true by (symmetry; apply Z.ltb_lt; pose proof ubs as UB; clear - UB; lia);
        replace (0 <? 16 * N + rp)%Z with true by (symmetry; apply Z.ltb_lt; pose proof ubs as UB; clear - UB G; lia);
        replace (16 * N + rp <? 16 * N)%Z with false by (symmetry; apply Z.ltb_ge; clear - BND; lia); reflexivity).
      zstep. rewrite lts_signed by (clear - G En2i; lia).
      if_cases K2; zify_cond K2.
      + destruct (Nat.ltb_spec i_ (Nat.max tna tnb)) as [HH|_]; [exfalso; clear - HH K2; lia|].
        eapply (BP_jneg neg); [exact Hk4 | clear - NE K2; lia | exact I | exact OK].
      + destruct (Nat.ltb_spec i_ (Nat.max tna tnb)) as [HH|HH]; [|exfalso; clear - HH K2; lia].
        eapply (BP_jpos neg); [exact Hk4 | exact HH | exact I | exact OK]. }
    zstep. rewrite A3.
    replace (bv_swrap 32 (bv_wrap 32 N ≫ 1)) with (Z.of_nat i_)
      by (replace N with (2 * Z.of_nat i_)%Z by (clear - En2i; lia); symmetry; apply srliw_half; clear - G En2i; lia).
    assert (L4 : (bv_unsigned a4 < 9223372036854775808)%Z) by (rewrite A4; clear - G; lia).
    assert (L5 : (bv_unsigned a5 < 9223372036854775808)%Z) by (rewrite A5; clear - G; lia).
    zstep. rewrite (lts_words_small a5 a4 L5 L4). rewrite A4, A5.
    if_cases K1; zify_cond K1.
    -
      do 2 zstep. rewrite A5, (bn_swrap32_small (Z.of_nat tnb - Z.of_nat i_)) by (clear - G En2i; lia).
      chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
      setreg 10%Z (Z_to_bv 64 (Z.of_nat (Nat.max tna tnb) - Z.of_nat i_)) ltac:(f_equal; clear - K1; lia).
      apply CONT.
    - do 2 zstep. rewrite A4, (bn_swrap32_small (Z.of_nat tna - Z.of_nat i_)) by (clear - G En2i; lia).
      zstep. if_true.
      setreg 10%Z (Z_to_bv 64 (Z.of_nat (Nat.max tna tnb) - Z.of_nat i_)) ltac:(f_equal; clear - K1; lia).
      apply CONT.

  Qed.

  (* [comment removed for export] *)
  Lemma BP_gen : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x27 x28 x29 x30 x31 F fc,
    (4 <= k)%nat ->
    KBK (FCELLS neg jb) m1 R T ->
    (let '(tm, p0) := mul_recursive k (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) in
     pgen2_ok RES fuel' k n neg a b tna tnb R (splice T (2 * n) (tm ++ p0))) ->
    evt bsegs POST (ST F fc 0x24e018 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 a6 a5 (Z_to_bv 64 (2 * N))
                       a4 (Z_to_bv 64 SHB) x24 a2 a1 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros Hk4 I OK.
    pose proof geom as G. pose proof (n_2i Hk4) as En2i.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    zstep.
    zstep. rewrite (bn_swrap32_small (2 * N + 1073741824)) by (clear - G; lia).
    zstep. rewrite lts_signed by (clear - G; lia).
    if_cases C0; [exfalso; zify_cond C0; clear - C0 G; lia | clear C0].
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    zstep. rewrite A3. replace (N ≪ 2)%Z with (4 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    rewrite (bn_swrap32_small (4 * N)) by (clear - G; lia).
    do 2 zstep.
    setreg 24%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) ltac:(f_equal; rewrite !Z.shiftl_mul_pow2 by lia; clear; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    do 4 zstep.
    setreg 10%Z (Z_to_bv 64 1) ltac:(
      replace (tq + 8 * Z.of_nat (4 * n) <? tq)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      rewrite lxor_signbit by (clear - G; lia);
      replace (4 * N + 9223372036854775808 <? 9223372036854775808)%Z with false by (symmetry; apply Z.ltb_ge; clear - G; lia);
      reflexivity).
    zstep. if_false.
    zstep. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    zstep.
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    do 4 zstep.
    setreg 11%Z (Z_to_bv 64 1) ltac:(replace (tq + 16 * N <? 16 * N)%Z with false by (symmetry; apply Z.ltb_ge; clear - BND; lia); reflexivity).
    zstep. if_false.
    do 2 zstep.
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).
    chk ltac:(fun C => clear - C BND G; lia).
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    do 8 zstep.
    pose proof SEPT as D7. pose proof Hk as HK. pose proof (scratch_rec_le k) as HSC. rewrite pow_n in HSC. pose proof (conj G HSC) as GH.
    eapply call_recA with (CS8 := CS8) (k := k) (a := slice T 0 n) (b := slice T n n) (da := 0%nat) (db := 0%nat)
                         (R := slice T (2 * n) (2 * n)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -160)%Z)
                         (bR := bT) (bT := bT) (bA := bT) (bB := bT)
                         (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (bn_mul_recursive_aspec CS8 CS8_0 comba8_ok sub_part_ok mul_normal_ok k)
      | exact LTa | exact LTb | exact LTr | exact LTp
      | clear - HK; lia | clear; lia | clear; lia
      | rewrite ETa, pow_n; clear; lia | rewrite ETb, pow_n; clear; lia | rewrite ETr, pow_n; reflexivity
      | rewrite ETp; clear - G HSC; lia
      | ulit | ulit | ulit | rewrite pow_n; exact A3 | reflexivity | reflexivity | ulit
      | exact HTa | exact HTb | exact HTr | exact HTp | rewrite ETr; exact WTr | rewrite ETp; exact WTp
      | rewrite ETr, ETa; clear - G; lia | rewrite ETr, ETb; clear - G; lia
      | rewrite ETp, ETa; clear - G; lia | rewrite ETp, ETb; clear - G; lia
      | rewrite ETr, ETp; clear - G; lia
      | clear - G; lia
      | rewrite ETr; clear - D7 G; lia | rewrite ETp; clear - D7 G; lia
      | rewrite ETa; clear - D7 G; lia | rewrite ETb; clear - D7 G; lia
      | kaside HEAP GH | kub BND G | ].
    intros m3 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) LTa LTb LTr LTp
                  ltac:(clear - HK; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(rewrite ETa, pow_n; clear; lia) ltac:(rewrite ETb, pow_n; clear; lia) ltac:(rewrite ETr, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G HSC; lia)) as MP.
    unfold mul_post in MP.
    destruct (mul_recursive k (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T)) as [tm p0]. cbn [fst snd] in *.
    destruct MP as (Ltm & Etm & _ & Lp0 & Ep0). rewrite ETr in Etm. rewrite ETp in Ep0.
    assert (I2 : KBK (FCELLS neg jb) m3 R (splice T (2 * n) (tm ++ p0))).
    { eapply (KK KB_cps_TT);
        [ reflexivity | exact I | exact HEAPc | rewrite Etm, Ep0; rewrite ETr, ETp in AGc; exact AGc | rewrite Etm; clear; lia
        | exact WMc | exact MIc | exact STc | exact Ltm | exact Lp0 | rewrite Ep0; clear - G; lia | exact HSR | exact HST ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb HTr LTr ETr WTr HTp LTp ETp WTp HEAPc AGc WMc HSR HST MIc STc I D7 HEAP.
    remember (splice T (2 * n) (tm ++ p0)) as T1 eqn:ET1. clear ET1 Ltm Etm Lp0 Ep0.
    (* [comment removed for export] *)
    unfold pgen2_ok in OK.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I2 ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I2 ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HBl.
    assert (Lal : length a_lo = n) by (rewrite length_firstn; clear - G; lia).
    assert (Lbl : length b_lo = n) by (rewrite length_firstn; clear - G; lia).
    do 8 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9.
    eapply call_recA with (CS8 := CS8) (k := k) (a := a_lo) (b := b_lo) (da := 0%nat) (db := 0%nat) (R := slice R 0 (2 * n)) (T := skipn (4 * n) T1)
                         (lo := lo) (SPz := (SP + -160)%Z) (bR := bR) (bT := bT) (bA := bA) (bB := bB)
                         (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP160 | ret_even | exact ST | exact MI | exact (bn_mul_recursive_aspec CS8 CS8_0 comba8_ok sub_part_ok mul_normal_ok k)
      | apply limbs_firstn; exact LA | apply limbs_firstn; exact LB' | exact LRa | exact LTp
      | clear - HK; lia | clear; lia | clear; lia
      | rewrite Lal, pow_n; clear; lia | rewrite Lbl, pow_n; clear; lia | rewrite ERa, pow_n; reflexivity
      | rewrite ETp; clear - G HSC; lia
      | ulit | ulit | ulit | rewrite pow_n; exact A3 | reflexivity | reflexivity | ulit
      | exact HAl | exact HBl | exact HRa | exact HTp | rewrite ERa; exact WRa | rewrite ETp; exact WTp
      | rewrite ERa, Lal; clear - D1 G; lia | rewrite ERa, Lbl; clear - D2 G; lia
      | rewrite ETp, Lal; clear - D3 G; lia | rewrite ETp, Lbl; clear - D4 G; lia
      | rewrite ERa, ETp; clear - D5 G; lia
      | clear - G; lia
      | rewrite ERa; clear - D6 G; lia | rewrite ETp; clear - D7 G; lia
      | rewrite Lal; clear - D8 G; lia | rewrite Lbl; clear - D9 G; lia
      | kaside HEAP GH | kub BND G | ].
    intros m4 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' F3 fc3 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k a_lo b_lo 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T1) (limbs_firstn _ _ LA) (limbs_firstn _ _ LB') LRa LTp
                  ltac:(clear - HK; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(rewrite Lal, pow_n; clear; lia) ltac:(rewrite Lbl, pow_n; clear; lia) ltac:(rewrite ERa, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G HSC; lia)) as MP.
    unfold mul_post in MP.
    destruct (mul_recursive k a_lo b_lo 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T1)) as [rl p1]. cbn [fst snd] in *.
    destruct MP as (Lrl & Erl & _ & Lp1 & Ep1). rewrite ERa in Erl. rewrite ETp in Ep1.
    assert (I3 : KBK (FCELLS neg jb) m4 (splice R 0 rl) (splice T1 (4 * n) p1)).
    { eapply (KK KB_cps) with (m1 := m3);
        [ reflexivity | exact I2 | exact HEAPc | rewrite Erl, Ep1; rewrite ERa, ETp in AGc; exact AGc | exact WMc | exact MIc | exact STc
        | exact Lrl | exact Lp1 | rewrite Erl; clear; lia | rewrite Ep1; clear - G; lia | exact HSR | exact HST ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa WRa HTp LTp ETp WTp HAl HBl HEAPc AGc WMc HSR HST MIc STc I2 HEAP.
    clear D1 D2 D3 D4 D5 D6 D7 D8 D9.
    remember (splice R 0 rl) as R1 eqn:ER1. remember (splice T1 (4 * n) p1) as T2 eqn:ET2. clear ER1 ET2 Lrl Erl Lp1 Ep1.
    eapply (BP_split neg); [exact Hk4 | exact I3 | exact OK].

  Qed.

  Notation JCELLS j16 j128 :=
    [CB 16 j16; C8 (Z_to_bv 64 (bv_unsigned a2 + 8 * Z.of_nat n)); C8 (Z_to_bv 64 (8 * Z.of_nat n));
     CB 8 j128; C8 (Z_to_bv 64 (8 * Z.of_nat n)); C8 (Z_to_bv 64 (bv_unsigned a1 + 8 * Z.of_nat n));
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma BP_join : forall (neg : bool) j16 j128 m1 R T x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x21 x24 x27 x28 x29 x30 x31 F fc,
    KBK (JCELLS j16 j128) m1 R T -> pjoin_ok RES fuel' k n neg a b tna tnb R T ->
    evt bsegs POST (ST F fc 0x24df20 m1 x1 x5 x6 x7 a0 x10 x11 x12 (Z_to_bv 64 (if neg then 0 else 1)) x14 x15 x16 x17 a3 a6 a5 x21
                       a4 (Z_to_bv 64 SHB) x24 a2 a1 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof geom as G.
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _ & _).
    pose proof (munch_refl [(SP + -160, SP + -160 + 160)]%Z m1) as MUF. pose proof (wmono_refl bsegs m1) as WMF.
    zstep. rewrite A3. replace (N ≪ 1)%Z with (2 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    rewrite (bn_swrap32_small (2 * N)) by (clear - G; lia).
    do 2 zstep.
    setreg 11%Z (Z_to_bv 64 0) ltac:(
      rewrite lxor_signbit by (clear - G; lia);
      replace (2 * N + 9223372036854775808 <? 0 + 9223372036854775808)%Z with false by (symmetry; apply Z.ltb_ge; clear - G; lia); reflexivity).
    zstep.
    zstep.
    lazymatch type of MI with mem_inv _ ?mm' => pose proof (KFRAME _ _ m1 mm' R T I MUF WMF MI STK FR) as I2 end.
    clear I MUF WMF FR STK MI.
    zstep. if_cases K1; zify_cond K1.
    - assert (Hk4 : (4 <= k)%nat).
      { pose proof Hk as HK. pose proof Hn as HN. destruct (Nat.eq_dec k 3) as [E3|NE]; [|clear - HK NE; lia].
        exfalso. rewrite E3 in HN. cbn in HN. clear - HN K1 A3. lia. }
      unfold pjoin_ok in OK. destruct (Nat.eqb_spec n 8) as [E8|_]; [exfalso; clear - E8 K1 A3; lia|].
      eapply (BP_gen neg); [exact Hk4 | exact I2 | exact OK].
    - assert (En : n = 8%nat) by (clear - K1 A3; lia).
      unfold pjoin_ok in OK. rewrite (proj2 (Nat.eqb_eq n 8) En) in OK.
      eapply (BP_comba neg); [exact En | exact I2 | exact OK].

  Qed.
  (* [comment removed for export] *)
  Notation t0_of sw := (fst (if sw then sub_part_words a_hi a_lo tna else sub_part_words a_lo a_hi tna)).
  Notation t1_of sw := (fst (if sw then sub_part_words b_hi b_lo tnb else sub_part_words b_lo b_hi tnb)).

  Ltac usp1_call I G BND sw :=
    let HAl := fresh "HAl" in let HAh := fresh "HAh" in let WTn := fresh "WTn" in
    let D3 := fresh "D3" in let D7 := fresh "D7" in let D8 := fresh "D8" in
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl;
    pose proof (KACC KB_a _ _ _ _ n tna I ltac:(clear - G; lia)) as HAh;
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (_ & _ & _ & WTn);
    pose proof DTA as D3; pose proof SEPT as D7; pose proof SEPA as D8;
    assert (length a_lo = n) by (rewrite length_firstn; clear - G; lia);
    assert (length a_hi = tna) by (rewrite slice_length; clear - G; lia);
    lazymatch goal with ST : stk bsegs ?m1 lo _, MI : mem_inv bsegs ?m1 |- _ =>
    lazymatch sw with
    | false =>
      eapply call_sub_part_wordsA with (a := a_lo) (b := a_hi) (cl := tna) (da := (n - tna)%nat) (db := 0%nat) (lo := lo) (SPz := (SP + -160)%Z)
                                      (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
        [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | exact sub_part_ok | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
        | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
        | clear - G; lia | ulit | ulit | ulit | exact A4 | f_equal; clear - G; lia
        | exact HAl | exact HAh | replace (tna + (n - tna) + 0)%nat with n by (clear - G; lia); exact WTn
        | rewrite length_firstn; clear - D3 G; lia | rewrite slice_length by (clear - G; lia); clear - D3 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite length_firstn; clear - D8 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia
        | kasan I G | ub_tac BND G | ub_tac BND G | ub_tac BND G | ]
    | true =>
      eapply call_sub_part_wordsA with (a := a_hi) (b := a_lo) (cl := tna) (da := 0%nat) (db := (n - tna)%nat) (lo := lo) (SPz := (SP + -160)%Z)
                                      (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * N)%Z) (BP := (ap + 8 * Z.of_nat 0)%Z);
        [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | exact sub_part_ok | apply slice_limbs; exact LA | apply limbs_firstn; exact LA
        | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
        | clear - G; lia | ulit | ulit | ulit | exact A4 | f_equal; clear - G; lia
        | exact HAh | exact HAl | replace (tna + 0 + (n - tna))%nat with n by (clear - G; lia); exact WTn
        | rewrite slice_length by (clear - G; lia); clear - D3 G; lia | rewrite length_firstn; clear - D3 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia | rewrite length_firstn; clear - D8 G; lia
        | kasan I G | ub_tac BND G | ub_tac BND G | ub_tac BND G | ]
    end end.

  Ltac usp2_call I G BND sw :=
    let HBl := fresh "HBl" in let HBh := fresh "HBh" in let WTn := fresh "WTn" in
    let D4 := fresh "D4" in let D7 := fresh "D7" in let D9 := fresh "D9" in
    pose proof (KACC KB_b _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HBl;
    pose proof (KACC KB_b _ _ _ _ n tnb I ltac:(clear - G; lia)) as HBh;
    destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (_ & _ & _ & WTn);
    pose proof DTB as D4; pose proof SEPT as D7; pose proof SEPB as D9;
    assert (length b_lo = n) by (rewrite length_firstn; clear - G; lia);
    assert (length b_hi = tnb) by (rewrite slice_length; clear - G; lia);
    lazymatch goal with ST : stk bsegs ?m1 lo _, MI : mem_inv bsegs ?m1 |- _ =>
    lazymatch sw with
    | false =>
      eapply call_sub_part_wordsA with (a := b_lo) (b := b_hi) (cl := tnb) (da := (n - tnb)%nat) (db := 0%nat) (lo := lo) (SPz := (SP + -160)%Z)
                                      (RP := (tq + 8 * N)%Z) (AP := (bp + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * N)%Z);
        [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | exact sub_part_ok | apply limbs_firstn; exact LB' | apply slice_limbs; exact LB'
        | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
        | clear - G; lia | ulit | ulit | ulit | exact A5 | f_equal; clear - G; lia
        | exact HBl | exact HBh | replace (tnb + (n - tnb) + 0)%nat with n by (clear - G; lia); exact WTn
        | rewrite length_firstn; clear - D4 G; lia | rewrite slice_length by (clear - G; lia); clear - D4 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite length_firstn; clear - D9 G; lia | rewrite slice_length by (clear - G; lia); clear - D9 G; lia
        | kasan I G | ub_tac BND G | ub_tac BND G | ub_tac BND G | ]
    | true =>
      eapply call_sub_part_wordsA with (a := b_hi) (b := b_lo) (cl := tnb) (da := 0%nat) (db := (n - tnb)%nat) (lo := lo) (SPz := (SP + -160)%Z)
                                      (RP := (tq + 8 * N)%Z) (AP := (bp + 8 * N)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
        [ exact ESP160 | ret_even | exact ST | exact MI | exact (KACC KB_shb _ _ _ _ I) | exact sub_part_ok | apply slice_limbs; exact LB' | apply limbs_firstn; exact LB'
        | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
        | clear - G; lia | ulit | ulit | ulit | exact A5 | f_equal; clear - G; lia
        | exact HBh | exact HBl | replace (tnb + 0 + (n - tnb))%nat with n by (clear - G; lia); exact WTn
        | rewrite slice_length by (clear - G; lia); clear - D4 G; lia | rewrite length_firstn; clear - D4 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | rewrite length_firstn; clear - D9 G; lia
        | kasan I G | ub_tac BND G | ub_tac BND G | ub_tac BND G | ]
    end end.

  Lemma t1_facts : forall sw : bool, limbs (t1_of sw) /\ length (t1_of sw) = n.
  Proof.
    intros sw. pose proof geom as G. destruct sw.
    - destruct (sub_part_words_fst b_hi b_lo tnb (slice_limbs _ _ _ LB') (limbs_firstn _ _ LB')
                  ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (L1 & E1 & _).
      rewrite slice_length, length_firstn in E1 by (clear - G; lia). split; [exact L1 | rewrite E1; clear - G; lia].
    - destruct (sub_part_words_fst b_lo b_hi tnb (limbs_firstn _ _ LB') (slice_limbs _ _ _ LB')
                  ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (L1 & E1 & _).
      rewrite slice_length, length_firstn in E1 by (clear - G; lia). split; [exact L1 | rewrite E1; clear - G; lia].
  Qed.
  Lemma t0_facts : forall sw : bool, limbs (t0_of sw) /\ length (t0_of sw) = n.
  Proof.
    intros sw. pose proof geom as G. destruct sw.
    - destruct (sub_part_words_fst a_hi a_lo tna (slice_limbs _ _ _ LA) (limbs_firstn _ _ LA)
                  ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (L1 & E1 & _).
      rewrite slice_length, length_firstn in E1 by (clear - G; lia). split; [exact L1 | rewrite E1; clear - G; lia].
    - destruct (sub_part_words_fst a_lo a_hi tna (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA)
                  ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (L1 & E1 & _).
      rewrite slice_length, length_firstn in E1 by (clear - G; lia). split; [exact L1 | rewrite E1; clear - G; lia].
  Qed.

  Notation STC F fc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 :=
    (ST F fc pc mm x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 a3 a6 a5 (Z_to_bv 64 (Z.of_nat tnb - N)) a4 (Z_to_bv 64 SHB)
        (Z_to_bv 64 (N - Z.of_nat tna)) a2 a1 x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma BP_sp2_neg : forall (sw : bool) j16 j128 m1 R T x1 x5 x6 x7 x15 x16 x17 x27 x28 x29 x30 x31 F fc,
    KBK (JCELLS j16 j128) m1 R T ->
    pjoin_ok RES fuel' k n true a b tna tnb R (splice T n (t1_of sw)) ->
    evt bsegs POST (STC F fc 0x24de60 m1 x1 x5 x6 x7 (Z_to_bv 64 (tq + 8 * N))
                       (if sw then Z_to_bv 64 (bp + 8 * N) else a2) (if sw then a2 else Z_to_bv 64 (bp + 8 * N))
                       a5 (if sw then Z_to_bv 64 (Z.of_nat tnb - N) else Z_to_bv 64 (N - Z.of_nat tnb))
                       x15 x16 x17 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t1_facts sw) as (Lt1 & Et1).
    destruct sw.
    - zstep. usp2_call I G BND true.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (KAFTER KB_after_T (JCELLS j16 j128) m1 m2 R T n _ _ 224%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      do 2 zstep. eapply (BP_join true); [exact I2 | exact OK].
    - zstep. usp2_call I G BND false.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (KAFTER KB_after_T (JCELLS j16 j128) m1 m2 R T n _ _ 224%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      do 2 zstep. eapply (BP_join true); [exact I2 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma BP_sp2_pos : forall (sw : bool) j16 j128 m1 R T x1 x5 x6 x7 x15 x16 x17 x27 x28 x29 x30 x31 F fc,
    KBK (JCELLS j16 j128) m1 R T ->
    pjoin_ok RES fuel' k n false a b tna tnb R (splice T n (t1_of sw)) ->
    evt bsegs POST (STC F fc 0x24df18 m1 x1 x5 x6 x7 (Z_to_bv 64 (tq + 8 * N))
                       (if sw then Z_to_bv 64 (bp + 8 * N) else a2) (if sw then a2 else Z_to_bv 64 (bp + 8 * N))
                       a5 (if sw then Z_to_bv 64 (Z.of_nat tnb - N) else Z_to_bv 64 (N - Z.of_nat tnb))
                       x15 x16 x17 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t1_facts sw) as (Lt1 & Et1).
    destruct sw.
    - zstep. usp2_call I G BND true.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (KAFTER KB_after_T (JCELLS j16 j128) m1 m2 R T n _ _ 224%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      zstep. eapply (BP_join false); [exact I2 | exact OK].
    - zstep. usp2_call I G BND false.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (KAFTER KB_after_T (JCELLS j16 j128) m1 m2 R T n _ _ 224%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      zstep. eapply (BP_join false); [exact I2 | exact OK].

  Qed.

  Ltac tn_checks G BND :=
    do 2 zstep;
    chk ltac:(fun C => clear - C BND G; lia);
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia);
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND G UB; lia).

  (* [comment removed for export] *)
  Lemma BP_case_A : forall j16 j128 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 F fc,
    KBK (JCELLS j16 j128) m1 R T ->
    pjoin_ok RES fuel' k n true a b tna tnb R (splice (splice T 0 (t0_of false)) n (t1_of false)) ->
    evt bsegs POST (STC F fc 0x24ddac m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t0_facts false) as (Lt0 & Et0).
    do 6 zstep. usp1_call I G BND false.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (KAFTER KB_after_T (JCELLS j16 j128) m1 m2 R T 0%nat _ _ 224%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    tn_checks G BND.
    do 2 zstep. rewrite A3, A5, (bn_swrap32_small (N - Z.of_nat tnb)) by (clear - G; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    do 2 zstep.
    zstep. rewrite (bn_swrap32_small (N - Z.of_nat tnb + 0)), Z.add_0_r by (clear - G; lia).
    do 4 zstep.
    eapply (BP_sp2_neg false); [exact I2 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma BP_case_B : forall j16 j128 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 F fc,
    KBK (JCELLS j16 j128) m1 R T ->
    pjoin_ok RES fuel' k n true a b tna tnb R (splice (splice T 0 (t0_of true)) n (t1_of true)) ->
    evt bsegs POST (STC F fc 0x24de10 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t0_facts true) as (Lt0 & Et0).
    do 2 zstep. rewrite A4, A3, (bn_swrap32_small (Z.of_nat tna - N)) by (clear - G; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_mod (Z.of_nat tna - N) 0), Z.add_0_r by (clear - G; lia).
    do 5 zstep. usp1_call I G BND true.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (KAFTER KB_after_T (JCELLS j16 j128) m1 m2 R T 0%nat _ _ 224%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    tn_checks G BND.
    do 6 zstep.
    eapply (BP_sp2_neg true); [exact I2 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma BP_case_C : forall j16 j128 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 F fc,
    KBK (JCELLS j16 j128) m1 R T ->
    pjoin_ok RES fuel' k n false a b tna tnb R (splice (splice T 0 (t0_of false)) n (t1_of true)) ->
    evt bsegs POST (STC F fc 0x24de6c m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t0_facts false) as (Lt0 & Et0).
    do 6 zstep. usp1_call I G BND false.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (KAFTER KB_after_T (JCELLS j16 j128) m1 m2 R T 0%nat _ _ 224%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    tn_checks G BND.
    do 7 zstep.
    eapply (BP_sp2_pos true); [exact I2 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma BP_case_D : forall j16 j128 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 F fc,
    KBK (JCELLS j16 j128) m1 R T ->
    pjoin_ok RES fuel' k n false a b tna tnb R (splice (splice T 0 (t0_of true)) n (t1_of false)) ->
    evt bsegs POST (STC F fc 0x24debc m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t0_facts true) as (Lt0 & Et0).
    do 2 zstep. rewrite A4, A3, (bn_swrap32_small (Z.of_nat tna - N)) by (clear - G; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_mod (Z.of_nat tna - N) 0), Z.add_0_r by (clear - G; lia).
    do 5 zstep. usp1_call I G BND true.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (KAFTER KB_after_T (JCELLS j16 j128) m1 m2 R T 0%nat _ _ 224%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI HEAP MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    tn_checks G BND.
    do 2 zstep. rewrite A3, A5, (bn_swrap32_small (N - Z.of_nat tnb)) by (clear - G; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    do 2 zstep.
    zstep. rewrite (bn_swrap32_small (N - Z.of_nat tnb + 0)), Z.add_0_r by (clear - G; lia).
    do 3 zstep.
    eapply (BP_sp2_pos false); [exact I2 | exact OK].

  Qed.
  Ltac litreg r :=
    let v := reg_val r in let z := eval vm_compute in (bv_unsigned v) in
    replace v with (Z_to_bv 64 z) by (apply bv_eq; vm_compute; reflexivity).

  Ltac code_steps :=
    zstep; litreg 12%Z; zstep; litreg 11%Z; zstep; litreg 12%Z;
    zstep; if_false;
    zstep; litreg 12%Z; zstep; litreg 11%Z; zstep; litreg 10%Z;
    zstep; if_false;
    zstep; litreg 11%Z; zstep; litreg 10%Z; do 2 zstep; zstep.
  (* [comment removed for export] *)

  Ltac bit60 := zstep; zstep; litreg 11%Z; zstep; litreg 11%Z; zstep.
  Ltac bit3 := zstep; zstep; litreg 10%Z; zstep; litreg 10%Z; zstep.

  Notation PCELLS0 jb56 := [CB 56 jb56; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma BP_body : forall jb56 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x19 x21 x23 x24 x27 x28 x29 x30 x31 F fc,
    KBK (PCELLS0 jb56) m1 R T ->
    (let '(t0', t1', neg) := part_diffs a_lo a_hi b_lo b_hi tna tnb (cmp_part_words a_lo a_hi tna) (cmp_part_words b_hi b_lo tnb) in
     pjoin_ok RES fuel' k n neg a b tna tnb R (splice (splice T 0 t0') n t1')) ->
    evt bsegs POST (ST F fc 0x24dcd4 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 a6 x17 a3 x19 a5 x21 a4 x23 x24 a2 a1 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _ & _).
    pose proof (munch_refl [(SP + -160, SP + -160 + 160)]%Z m1) as MUF. pose proof (wmono_refl bsegs m1) as WMF.
    zstep. rewrite A3. replace (N ≪ 3)%Z with (8 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 3 zstep.
    chk ltac:(fun C => clear - C BND2 G; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    zstep.
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND2 G UB; lia).
    do 2 zstep. rewrite A3, A4, (bn_swrap32_small (N - Z.of_nat tna)) by (clear - G; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    (* [comment removed for export] *)
    zstep.
    pose proof (KFRAME _ _ m1 _ R T I MUF WMF MI STK FR) as I2.
    clear I MUF WMF. clear m1.

    pose proof (KACC KB_shb _ _ _ _ I2) as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    do 3 zstep. clear G1 G2.
    do 5 zstep.
    pose proof (KACC KB_a _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_a _ _ _ _ n tna I2 ltac:(clear - G; lia)) as HAh.
    pose proof SEPA as D8.
    assert (Lal : length a_lo = n) by (rewrite length_firstn; clear - G; lia).
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    eapply call_cmp_part_wordsA with (a := a_lo) (b := a_hi) (cl := tna) (da := (n - tna)%nat) (db := 0%nat) (lo := lo) (SPz := (SP + -160)%Z)
                                    (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
      [ exact ESP160 | ret_even | exact STK | exact MI | exact (KACC KB_shb _ _ _ _ I2) | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
      | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
      | clear - G; lia | ulit | ulit | exact A4 | f_equal; clear - G; lia
      | exact HAl | exact HAh | clear - G; lia
      | rewrite length_firstn; clear - D8 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia
      | kasan2 I2 G | ub_tac BND G | ub_tac BND G | ].
    intros m3 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc STc.
    lazymatch type of I2 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_ro cells mm m3 R T 16%Z eq_refl I2 MUc ltac:(clear - G; lia) WMc MIc STc) as I3 end.
    clear FR STK MI HAl HAh D8 MUc WMc MIc STc I2.
    pose proof I3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _ & _).
    lazymatch type of MI with mem_inv _ ?mm => pose proof (munch_refl [(SP + -160, SP + -160 + 160)]%Z mm) as MUF; pose proof (wmono_refl bsegs mm) as WMF end.
    remember (cmp_part_words a_lo a_hi tna) as c1 eqn:Ec1.
    do 2 zstep.
    chk ltac:(fun C => clear - C BND2 G; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C UB; lia).
    chk ltac:(fun C => pose proof ubs as UB; clear - C BND2 G UB; lia).
    zstep.
    do 2 zstep. rewrite A5, A3, (bn_swrap32_small (Z.of_nat tnb - N)) by (clear - G; lia).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite A3. replace (N ≪ 3)%Z with (8 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 7 zstep.
    lazymatch type of I3 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ _ =>
      lazymatch type of MI with mem_inv _ ?mm' => pose proof (KFRAME _ _ mm mm' R T I3 MUF WMF MI STK FR) as I4 end end.
    clear I3 MUF WMF.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I4 ltac:(clear - G; lia)) as HBl.
    pose proof (KACC KB_b _ _ _ _ n tnb I4 ltac:(clear - G; lia)) as HBh.
    pose proof SEPB as D9.
    assert (Lbl : length b_lo = n) by (rewrite length_firstn; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    eapply call_cmp_part_wordsA with (a := b_hi) (b := b_lo) (cl := tnb) (da := 0%nat) (db := (n - tnb)%nat) (lo := lo) (SPz := (SP + -160)%Z)
                                    (AP := (bp + 8 * N)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
      [ exact ESP160 | ret_even | exact STK | exact MI | exact (KACC KB_shb _ _ _ _ I4) | apply slice_limbs; exact LB' | apply limbs_firstn; exact LB'
      | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
      | clear - G; lia | ulit | ulit | exact A5 | f_equal; clear - G; lia
      | exact HBh | exact HBl | clear - G; lia
      | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | rewrite length_firstn; clear - D9 G; lia
      | kasan2 I4 G | ub_tac BND G | ub_tac BND G | ].
    intros m5 u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc STc.
    lazymatch type of I4 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_ro cells mm m5 R T 16%Z eq_refl I4 MUc ltac:(clear - G; lia) WMc MIc STc) as I5 end.
    clear FR STK MI HBl HBh D9 MUc WMc MIc STc I4.
    remember (cmp_part_words b_hi b_lo tnb) as c2 eqn:Ec2.
    assert (Hc1 : (c1 = -1 \/ c1 = 0 \/ c1 = 1)%Z).
    { rewrite Ec1, (cmp_part_words_spec a_lo a_hi tna (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA))
        by (right; rewrite slice_length, length_firstn; clear - G; lia). apply sgn3_range. }
    assert (Hc2 : (c2 = -1 \/ c2 = 0 \/ c2 = 1)%Z).
    { rewrite Ec2, (cmp_part_words_spec b_hi b_lo tnb (slice_limbs _ _ _ LB') (limbs_firstn _ _ LB'))
        by (left; rewrite slice_length, length_firstn; clear - G; lia). apply sgn3_range. }
    clear Ec1 Ec2.
    pose proof I5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & _ & _).
    destruct Hc1 as [E1|[E1|E1]]; destruct Hc2 as [E2|[E2|E2]]; rewrite E1, E2 in *; clear E1 E2 c1 c2.
    - (* [comment removed for export] *) code_steps. if_true. zstep. zstep. if_false.
      rewrite part_diffs_m1_m1 in OK. eapply BP_case_D; [exact I5 | exact OK].
    - (* [comment removed for export] *) code_steps. if_false. bit60. if_true. bit3. if_false.
      rewrite part_diffs_m1_0 in OK. eapply BP_case_B; [exact I5 | exact OK].
    - (* [comment removed for export] *) code_steps. if_false. bit60. if_true. bit3. if_false.
      rewrite part_diffs_m1_p1 in OK. eapply BP_case_B; [exact I5 | exact OK].
    - (* [comment removed for export] *) code_steps. if_false. bit60. if_false.
      rewrite part_diffs_0_m1 in OK. eapply BP_case_A; [exact I5 | exact OK].
    - (* [comment removed for export] *) code_steps. if_false. bit60. if_false.
      rewrite part_diffs_0_0 in OK. eapply BP_case_A; [exact I5 | exact OK].
    - (* [comment removed for export] *) code_steps. if_false. bit60. if_false.
      rewrite part_diffs_0_p1 in OK. eapply BP_case_A; [exact I5 | exact OK].
    - (* [comment removed for export] *) code_steps. if_false. bit60. if_false.
      rewrite part_diffs_p1_m1 in OK. eapply BP_case_A; [exact I5 | exact OK].
    - (* [comment removed for export] *) code_steps. if_false. bit60. if_true. bit3. if_true.
      rewrite part_diffs_p1_0 in OK. eapply BP_case_C; [exact I5 | exact OK].
    - (* [comment removed for export] *) code_steps. if_false. bit60. if_true. bit3. if_true.
      rewrite part_diffs_p1_p1 in OK. eapply BP_case_C; [exact I5 | exact OK].

  Qed.

  (* [comment removed for export] *)
  Lemma P_entry : forall R T F fc,
    limbs R -> limbs T -> length R = (4 * n)%nat -> length T = nT ->
    limbs_at bsegs m ap a -> limbs_at bsegs m bp b -> limbs_at bsegs m rp R -> limbs_at bsegs m tq T ->
    wr_at bsegs m rp (8 * Z.of_nat (4 * n)) -> wr_at bsegs m tq (8 * Z.of_nat nT) ->
    stk bsegs m lo SP -> mem_inv bsegs m -> AHEAP Σ OW LB m ->
    (let '(t0', t1', neg) := part_diffs a_lo a_hi b_lo b_hi tna tnb (cmp_part_words a_lo a_hi tna) (cmp_part_words b_hi b_lo tnb) in
     pjoin_ok RES fuel' k n neg a b tna tnb R (splice (splice T 0 t0') n t1')) ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24dc08) fc None m (seg_rom bsegs)).
  Proof.
    intros R T F fc LR LT ER ET RA RB RR RT' WR WT STK MI0 HEAP OK.
    pose proof geom as G.
    assert (LO1 : (lo <= SP - 160)%Z) by (clear - G; lia).
    carve_frame 160%nat STK.
    pose proof (munch_refl [(SP + -160, SP + -160 + 160)]%Z m) as MUF. pose proof (wmono_refl bsegs m) as WMF.
    assert (I0 : KBK [CB 160 junk] m R T).
    { unfold KB. split; [exact LR|]. split; [exact LT|]. split; [exact ER|]. split; [exact ET|].
      split; [exact RR|]. split; [exact RT'|]. split; [exact RA|]. split; [exact RB|]. split; [exact WR|]. split; [exact WT|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact HEAP|].
      split; [|exact WMF]. unfold KAG. intros x _. reflexivity. }
    clear RA RB RR RT' WR WT HEAP.
    do 18 zstep. rewrite A3, (bn_swrap32_small (N + 1073741824)) by (clear - G; lia).
    zstep. rewrite lts_signed by (clear - G; lia).
    if_cases C0; [exfalso; zify_cond C0; clear - C0 G; lia | clear C0].
    do 6 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (KFRAME _ _ m mm R T I0 MUF WMF MI0 STK FR) as I end.
    clear I0 MUF WMF.
    assert (L7 : (bv_unsigned (Z_to_bv 64 7) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (L3 : (bv_unsigned a3 < 9223372036854775808)%Z) by (rewrite A3; clear - G; lia).
    zstep. rewrite (lts_words_small (Z_to_bv 64 7) a3 L7 L3). rewrite A3.
    if_cases K8; zify_cond K8; [|exfalso; clear - K8 G; lia].
    eapply BP_body; [exact I | exact OK].
  Qed.
End KaraP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MainP.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).
  Variable CS8 : Z.
  Hypothesis CS8_0 : (0 <= CS8)%Z.
  Hypothesis comba8_ok : comba8_aspec CS8.
  Hypothesis sub_part_ok : sub_part_words_bspec.
  Hypothesis mul_normal_ok : mul_normal_bspec.

  Lemma part_body : forall fuel', part_spec_atA CS8 fuel' -> part_spec_atA CS8 (S fuel').
  Proof.
    intros fuel' IHp. unfold part_spec_atA.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB bR bT bA bB a b k tna tnb R T lo
           LA LB' LR LT Hk3 Hkf Hk26 Htna Htnb Hd1 Hd2 HLA HLB HLR HLT A3 A4 A5 RA RB RR RT WR WT DRA DRB DTA DTB DRT STK LO SEPR SEPT SEPA SEPB MI0
           HEAP KBL CEIL SPT16 SP16 ETP UB.
    remember (Nat.pow 2 k) as n eqn:En.
    assert (HN : (2 <= Z.of_nat n <= 67108864)%Z) by (subst n; apply W_mul_recursive.pow2_Z_bounds; clear - Hk3 Hk26; lia).
    assert (Hn8 : (8 <= n)%nat).
    { subst n. replace k with (3 + (k - 3))%nat by (clear - Hk3; lia). rewrite Nat.pow_add_r. pose proof (pow2_pos (k - 3)) as HP.
      cbn [Nat.pow] in *. clear - HP. lia. }
    remember (part_stackA CS8 k - 160)%Z as SK eqn:ESK.
    assert (HSK : (65536 <= SK)%Z) by (subst SK; unfold part_stackA, rec_stackA; clear - CS8_0; lia).
    assert (ERS : part_stackA CS8 k = (160 + SK)%Z) by (subst SK; clear; lia).
    rewrite ERS in LO, SEPR, SEPT, SEPA, SEPB.
    replace (bv_unsigned sp - (160 + SK))%Z with (bv_unsigned sp - 160 - SK)%Z in LO by (clear; lia).
    replace (bv_unsigned sp - (160 + SK))%Z with (bv_unsigned sp - 160 - SK)%Z in SEPR by (clear; lia).
    replace (bv_unsigned sp - (160 + SK))%Z with (bv_unsigned sp - 160 - SK)%Z in SEPT by (clear; lia).
    replace (bv_unsigned sp - (160 + SK))%Z with (bv_unsigned sp - 160 - SK)%Z in SEPA by (clear; lia).
    replace (bv_unsigned sp - (160 + SK))%Z with (bv_unsigned sp - 160 - SK)%Z in SEPB by (clear; lia).
    pose proof (proj1 STK) as LO0.
    rewrite HLR in WR, DRA, DRB, DRT, SEPR, KBL.
    assert (UBS : (0 < bv_unsigned a0 /\ bv_unsigned a0 mod 8 = 0 /\ 0 < bv_unsigned a1 /\ bv_unsigned a1 mod 8 = 0 /\
                   0 < bv_unsigned a2 /\ bv_unsigned a2 mod 8 = 0 /\ 0 < bv_unsigned a6 /\ bv_unsigned a6 mod 8 = 0)%Z).
    { destruct UB as (U1 & U2 & U3 & U4). pose proof (U1 ltac:(lia)). pose proof (U2 ltac:(lia)). pose proof (U3 ltac:(lia)). pose proof (U4 ltac:(lia)). tauto. }
    assert (PRE : kpart_preA CS8 fuel' k n tna tnb (length a) (length b) (length T) SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1)
                            (bv_unsigned a2) (bv_unsigned sp) lo).
    { unfold kpart_preA.
      split; [exact En|]. split; [clear - Hk3 Hk26; lia|]. split; [exact Hkf|]. split; [exact Hn8|]. split; [clear - HN; lia|].
      split; [exact Htna|]. split; [exact Htnb|]. split; [exact Hd1|]. split; [exact Hd2|].
      split; [exact HLA|]. split; [exact HLB|]. split; [exact HLT|]. split; [exact ESK|].
      split; [exact DRA|]. split; [exact DRB|]. split; [exact DTA|]. split; [exact DTB|]. split; [exact DRT|].
      split; [exact SEPR|]. split; [exact SEPT|]. split; [exact SEPA|]. split; [exact SEPB|].
      split; [exact LO|]. split; [exact LO0 | exact UBS]. }
    apply cps_from_evt'.
    replace (Z.of_nat (length R)) with (Z.of_nat (4 * n)) by (rewrite HLR; reflexivity).
    eapply (P_entry CS8 CS8_0 comba8_ok sub_part_ok mul_normal_ok fuel' IHp) with (n := n) (nT := length T) (SK := SK) (k := k) (tna := tna) (tnb := tnb)
                                                      (bR := bR) (bT := bT) (bA := bA) (bB := bB);
      [ exact PRE | exact KBL | exact CEIL | exact SPT16 | exact SP16 | exact ETP | exact LA | exact LB' | rewrite A3; reflexivity | exact A4 | exact A5
      | exact LR | exact LT | exact HLR | reflexivity | exact RA | exact RB | exact RR | exact RT | exact WR | exact WT | exact STK | exact MI0 | exact HEAP | ].
    rewrite En. apply part_staged; try assumption; rewrite <- ?En; try assumption.
  Qed.

  (* [comment removed for export] *)
  Theorem bn_mul_part_recursive_aspec : forall fuel, part_spec_atA CS8 fuel.
  Proof.
    induction fuel as [|fuel' IH]; [|apply part_body; exact IH].
    unfold part_spec_atA. intros. exfalso. lia.
  Qed.
End MainP.
