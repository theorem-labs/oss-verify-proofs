(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BgWords BgSqrCorrect.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp BnKaraX.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require BnKaraMem.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require W_mul_normal W_mul_recursive W_cmp_words.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW2 Require W_sqr_words W_sqr_normal SqrKaraX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require BnKit2.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA BnIfaceA AsStruct ImplA RtCallA BnKaraMemA BnCallsKA AW_cmp_words AW_mul_recursive.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import AW_sqr_words AW_sqr_normal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_sqr_recursive_aentry := 0x23095c%Z.

Notation half_n2 := W_mul_recursive.half_n2.
Notation upd_app_mid := W_mul_recursive.upd_app_mid.
Notation sgen3_ok := SqrKaraX.sgen3_ok.
Notation sgen2_ok := SqrKaraX.sgen2_ok.
Notation sjoin_ok := SqrKaraX.sjoin_ok.
Notation szero_ok := SqrKaraX.szero_ok.
Notation srec_staged := SqrKaraX.srec_staged.
Notation sqr_recursive_c4 := SqrKaraX.sqr_recursive_c4.
Notation sqr_recursive_c8 := SqrKaraX.sqr_recursive_c8.
Notation sqr_recursive_small := SqrKaraX.sqr_recursive_small.
Notation vl_post := W_mul_normal.vl_post.
Notation vl_post2 := W_sqr_normal.vl_post2.

Definition sqr_comba4_aspec (CS : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : list Z) (lo : Z),
    limbs a -> length a = 4%nat ->
    limbs_at bgasegs m (bv_unsigned a1) a ->
    wr_at bgasegs m (bv_unsigned a0) 64 ->
    (bv_unsigned a0 + 64 <= bv_unsigned a1 \/ bv_unsigned a1 + 32 <= bv_unsigned a0)%Z ->
    stk bgasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - CS)%Z ->
    (bv_unsigned a0 + 64 <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 32 <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    mem_inv bgasegs m ->
    shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m ->
    acc bgasegs m (bv_unsigned a0) 64 -> acc bgasegs m (bv_unsigned a1) 32 ->
    aptrs2 (bv_unsigned a0) (bv_unsigned a1) 8 lo ->
    (0 < bv_unsigned a0)%Z -> (0 < bv_unsigned a1)%Z ->
    (bv_unsigned a0 + 64 <= 65536 \/ 12345344 <= bv_unsigned a0)%Z ->
    evt bgasegs (vl_post bgasegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) 8 CS (sqr_comba4 a) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x22fa80) fc None m (seg_rom bgasegs)).

Definition sqr_comba8_aspec (CS : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : list Z) (lo : Z),
    limbs a -> length a = 8%nat ->
    limbs_at bgasegs m (bv_unsigned a1) a ->
    wr_at bgasegs m (bv_unsigned a0) 128 ->
    (bv_unsigned a0 + 128 <= bv_unsigned a1 \/ bv_unsigned a1 + 64 <= bv_unsigned a0)%Z ->
    stk bgasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - CS)%Z ->
    (bv_unsigned a0 + 128 <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 64 <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    mem_inv bgasegs m ->
    shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m ->
    acc bgasegs m (bv_unsigned a0) 128 -> acc bgasegs m (bv_unsigned a1) 64 ->
    aptrs2 (bv_unsigned a0) (bv_unsigned a1) 16 lo ->
    (0 < bv_unsigned a0)%Z -> (0 < bv_unsigned a1)%Z ->
    (bv_unsigned a0 + 128 <= 65536 \/ 12345344 <= bv_unsigned a0)%Z ->
    evt bgasegs (vl_post bgasegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) 16 CS (sqr_comba8 a) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x22e558) fc None m (seg_rom bgasegs)).

Definition srec_stackA (CSL : Z) (k : nat) : Z := (96 * Z.of_nat (S k) + Z.max CSL 65536)%Z.

Section Spec.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).

  Definition sqr_rec_spec_atA (CSL : Z) (k : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (bR bT bA : block)
           (a R T : list Z) (lo : Z),
      limbs a -> limbs R -> limbs T ->
      (k <= 26)%nat ->
      length a = Nat.pow 2 k -> length R = (2 * Nat.pow 2 k)%nat -> (sqr_scratch k <= length T)%nat ->
      bv_unsigned a2 = Z.of_nat (Nat.pow 2 k) ->
      limbs_at bgasegs m (bv_unsigned a1) a -> limbs_at bgasegs m (bv_unsigned a0) R -> limbs_at bgasegs m (bv_unsigned a3) T ->
      wr_at bgasegs m (bv_unsigned a0) (8 * Z.of_nat (length R)) -> wr_at bgasegs m (bv_unsigned a3) (8 * Z.of_nat (length T)) ->
      (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0)%Z ->
      (bv_unsigned a3 + 8 * Z.of_nat (length T) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a3)%Z ->
      (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a3 \/ bv_unsigned a3 + 8 * Z.of_nat (length T) <= bv_unsigned a0)%Z ->
      stk bgasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - srec_stackA CSL k)%Z ->
      (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned sp - srec_stackA CSL k \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
      (bv_unsigned a3 + 8 * Z.of_nat (length T) <= bv_unsigned sp - srec_stackA CSL k \/ bv_unsigned sp <= bv_unsigned a3)%Z ->
      (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - srec_stackA CSL k \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
      mem_inv bgasegs m ->

      AHEAP Σ OW LB m ->
      kara_blocks OW LB bR bT bA bA (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (length R) (length T) (length a) (length a) ->
      (ACEIL <= lo)%Z -> (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> tp = wz TP_A ->
      cps bgasegs
        (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x23095c) fc None m (seg_rom bgasegs))))
        (ASTA RT Σ PMc (kr_apost ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo
                          (bv_unsigned a0) (Z.of_nat (length R)) (bv_unsigned a3) (Z.of_nat (length T))
                          (fst (sqr_recursive k a R T)) (snd (sqr_recursive k a R T)) m)).

  Lemma call_sqr_recA : forall (Σ : rts RT) (Q : config -> Prop)
      (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (OW LB : list block) (lo SPz RET : Z)
      (CSL : Z) (k : nat) (a R T : list Z) (RP AP TQ : Z) (bR bT bA : block),
    bv_unsigned wsp = SPz -> ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET -> stk bgasegs m lo SPz -> mem_inv bgasegs m ->
    sqr_rec_spec_atA CSL k ->
    limbs a -> limbs R -> limbs T -> (k <= 26)%nat ->
    length a = Nat.pow 2 k -> length R = (2 * Nat.pow 2 k)%nat -> (sqr_scratch k <= length T)%nat ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = Z.of_nat (Nat.pow 2 k) -> bv_unsigned w3 = TQ ->
    limbs_at bgasegs m AP a -> limbs_at bgasegs m RP R -> limbs_at bgasegs m TQ T ->
    wr_at bgasegs m RP (8 * Z.of_nat (length R)) -> wr_at bgasegs m TQ (8 * Z.of_nat (length T)) ->
    (RP + 8 * Z.of_nat (length R) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= AP \/ AP + 8 * Z.of_nat (length a) <= TQ)%Z ->
    (RP + 8 * Z.of_nat (length R) <= TQ \/ TQ + 8 * Z.of_nat (length T) <= RP)%Z ->
    (lo <= SPz - srec_stackA CSL k)%Z ->
    (RP + 8 * Z.of_nat (length R) <= SPz - srec_stackA CSL k \/ SPz <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= SPz - srec_stackA CSL k \/ SPz <= TQ)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - srec_stackA CSL k \/ SPz <= AP)%Z ->
    (AHEAP Σ OW LB m /\ kara_blocks OW LB bR bT bA bA RP TQ AP AP (length R) (length T) (length a) (length a) /\
     (ACEIL <= lo)%Z /\ (SPz + 16 <= USTACK_TOP)%Z /\ (SPz mod 16 = 0)%Z /\ tp = wz TP_A) ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 (F2 : bvmap 5 word) (fc2 : bv 32),
       AHEAP Σ OW LB m2 ->
       agree_on (fun x => aclient_addr (OW ++ LB) SPz x /\ ~ (RP <= x < RP + 8 * Z.of_nat (length R))%Z /\ ~ (TQ <= x < TQ + 8 * Z.of_nat (length T))%Z) m m2 ->
       wmono bgasegs m m2 -> mem_inv bgasegs m2 ->
       limbs_at bgasegs m2 RP (fst (sqr_recursive k a R T)) -> limbs_at bgasegs m2 TQ (snd (sqr_recursive k a R T)) ->
       stk bgasegs m2 lo SPz ->
       evt bgasegs (kpost Σ Q)
         (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
             F2 (Z_to_bv 64 RET) fc2 None m2 (seg_rom bgasegs))) ->
    evt bgasegs (kpost Σ Q)
      (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x23095c) fc None m (seg_rom bgasegs)).
  Proof.
    intros until bA. intros ESP ERET STK MI0 SPEC LA LR LT Hk HLA HLR HLT E0 E1 E2 E3
           RA RR RT WR WT DRA DTA DRT LO SEPR SEPT SEPA (HEAP & KBL & CEIL & SPT & SP16 & ETP) K.
    subst RP AP TQ SPz.
    apply evt_done. unfold kpost.
    eapply cps_step_same.
    - eapply SPEC with (a := a) (R := R) (T := T) (lo := lo) (bR := bR) (bT := bT) (bA := bA); eassumption.
    - intros ms2 PO. unfold kr_apost in PO.
      destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & HR2 & HT2).
      rewrite ERET. apply cps_from_evt'. rewrite <- ETP.
      eapply K; eassumption.
  Qed.
End Spec.

Section CmpCall.
  Variable POST : machine_state -> Prop.
  Variables (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo SPz RET : Z).
  Hypothesis ESP : bv_unsigned wsp = SPz.
  Hypothesis ERET : ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET.
  Hypothesis STK : stk bgasegs m lo SPz.
  Hypothesis MI0 : mem_inv bgasegs m.
  Hypothesis SHBC : shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.

  Lemma call_cmp_wordsA : forall (a b : list Z) (AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2 ^ 31)%Z ->
    bv_unsigned w0 = AP -> bv_unsigned w1 = BP -> bv_unsigned w2 = Z.of_nat (length a) ->
    limbs_at bgasegs m AP a -> limbs_at bgasegs m BP b ->
    (lo <= SPz - 16)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= BP)%Z ->
    (acc bgasegs m AP (8 * Z.of_nat (length a)) /\ acc bgasegs m BP (8 * Z.of_nat (length a)) /\
     (AP mod 8 = 0)%Z /\ (BP mod 8 = 0)%Z /\ (SHHI <= lo)%Z) ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(SPz - 16, SPz)]%Z m m2 -> wmono bgasegs m m2 -> mem_inv bgasegs m2 -> stk bgasegs m2 lo SPz ->
       evt bgasegs POST
         (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 (cmp_words a b)) v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
             F (Z_to_bv 64 RET) fc None m2 (seg_rom bgasegs))) ->
    evt bgasegs POST
      (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x226504) fc None m (seg_rom bgasegs)).
  Proof using ESP ERET STK MI0 SHBC.
    intros a b AP BP LA LB LEN N31 E0 E1 E2 RA RB LO SEPA SEPB (ACA & ACB & AL8A & AL8B & SHLO) K.
    subst AP BP SPz.
    eapply evt_cut; [ eapply bn_cmp_words_aspec with (a := a) (b := b) (lo := lo); try eassumption | ].
    intros ms' PO. unfold W_cmp_words.ro_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.
End CmpCall.

Definition sqr_preA (CSL : Z) (k' n la nT : nat) (SK rp tq ap SP lo : Z) : Prop :=
  n = Nat.pow 2 k' /\ (3 <= k' <= 25)%nat /\ (8 <= n)%nat /\ (Z.of_nat n <= 33554432)%Z /\
  la = (2 * n)%nat /\ (4 * n + sqr_scratch k' <= nT)%nat /\ SK = srec_stackA CSL k' /\
  (rp + 8 * Z.of_nat (4 * n) <= ap \/ ap + 8 * Z.of_nat la <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat la <= tq)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= tq \/ tq + 8 * Z.of_nat nT <= rp)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= SP - 96 - SK \/ SP <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= SP - 96 - SK \/ SP <= tq)%Z /\
  (ap + 8 * Z.of_nat la <= SP - 96 - SK \/ SP <= ap)%Z /\
  (lo <= SP - 96 - SK)%Z /\ (0 <= lo)%Z.

Section Kara.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).
  Variable CSL : Z.
  Variable k' : nat.
  Hypothesis IH : sqr_rec_spec_atA CSL k'.
  Variables (Σ : rts RT) (OW LB : list block) (bR bT bA : block).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : word -> option byte) (a : list Z) (lo : Z) (n nT : nat) (SK : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation tq := (bv_unsigned a3).
  Notation SP := (bv_unsigned sp).
  Notation N := (Z.of_nat n).
  Hypothesis PRE : sqr_preA CSL k' n (length a) nT SK (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned sp) lo.
  Hypothesis KBL : kara_blocks OW LB bR bT bA bA (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (4 * n) nT (length a) (length a).
  Hypothesis CEIL : (ACEIL <= lo)%Z.
  Hypothesis SPT16 : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis ETP : tp = wz TP_A.
  Hypothesis LA : limbs a.
  Hypothesis A2 : bv_unsigned a2 = (2 * N)%Z.
  Variable RES : list Z * list Z.

  Lemma Hn : n = Nat.pow 2 k'. Proof. apply PRE. Qed.
  Lemma Hk' : (3 <= k' <= 25)%nat. Proof. apply PRE. Qed.
  Lemma Hn8 : (8 <= n)%nat. Proof. apply PRE. Qed.
  Lemma HnB : (N <= 33554432)%Z. Proof. apply PRE. Qed.
  Lemma HLA : length a = (2 * n)%nat. Proof. apply PRE. Qed.
  Lemma HnT : (4 * n + sqr_scratch k' <= nT)%nat. Proof. apply PRE. Qed.
  Lemma HSK : SK = srec_stackA CSL k'. Proof. apply PRE. Qed.
  Lemma DRA : (rp + 8 * Z.of_nat (4 * n) <= ap \/ ap + 8 * Z.of_nat (length a) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma DTA : (tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat (length a) <= tq)%Z. Proof. apply PRE. Qed.
  Lemma DRT : (rp + 8 * Z.of_nat (4 * n) <= tq \/ tq + 8 * Z.of_nat nT <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPR : (rp + 8 * Z.of_nat (4 * n) <= SP - 96 - SK \/ SP <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPT : (tq + 8 * Z.of_nat nT <= SP - 96 - SK \/ SP <= tq)%Z. Proof. apply PRE. Qed.
  Lemma SEPA : (ap + 8 * Z.of_nat (length a) <= SP - 96 - SK \/ SP <= ap)%Z. Proof. apply PRE. Qed.
  Lemma LO : (lo <= SP - 96 - SK)%Z. Proof. apply PRE. Qed.
  Lemma LO0 : (0 <= lo)%Z. Proof. apply PRE. Qed.
  Lemma SK0 : (0 <= SK)%Z. Proof. rewrite HSK. unfold srec_stackA. lia. Qed.
  Lemma SK_ge : (65536 <= SK /\ CSL <= SK)%Z. Proof. rewrite HSK. unfold srec_stackA. lia. Qed.
  Lemma FS0 : (0 <= 96)%Z. Proof. lia. Qed.
  Lemma FBE : (SP + -96 = SP - 96)%Z. Proof. reflexivity. Qed.
  Lemma SPTop : (SP <= USTACK_TOP)%Z. Proof. pose proof SPT16. lia. Qed.
  Lemma ESP96 : bv_unsigned (Z_to_bv 64 (SP + -96)) = (SP + -96)%Z.
  Proof.
    apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R.
    pose proof LO. pose proof LO0. pose proof SK0. lia.
  Qed.
  Lemma pow_n : Nat.pow 2 k' = n. Proof. symmetry. exact Hn. Qed.
  Lemma sqr_scratch_tail : (sqr_scratch k' <= nT - 4 * n)%nat. Proof. pose proof HnT. lia. Qed.
  Lemma INR : In bR OW. Proof. apply KBL. Qed.
  Lemma INT : In bT OW. Proof. apply KBL. Qed.
  Lemma INA : In bA (OW ++ LB). Proof. apply KBL. Qed.
  Lemma RGR : (blk_addr bR <= rp /\ rp + 8 * Z.of_nat (4 * n) <= blk_addr bR + blk_size bR)%Z. Proof. apply KBL. Qed.
  Lemma RGT : (blk_addr bT <= tq /\ tq + 8 * Z.of_nat nT <= blk_addr bT + blk_size bT)%Z. Proof. apply KBL. Qed.
  Lemma RGA : (blk_addr bA <= ap /\ ap + 8 * Z.of_nat (length a) <= blk_addr bA + blk_size bA)%Z. Proof. apply KBL. Qed.
  Lemma AL8 : (rp mod 8 = 0 /\ tq mod 8 = 0 /\ ap mod 8 = 0 /\ ap mod 8 = 0)%Z. Proof. apply KBL. Qed.

  Notation POST := (kpost Σ (ASTA RT Σ PMc (kr_apost ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo
                      (bv_unsigned a0) (Z.of_nat (4 * n)) (bv_unsigned a3) (Z.of_nat nT) (fst RES) (snd RES) m))).

  Notation KK L := (L Σ OW LB m (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a (4 * n)%nat nT
                      96%Z SK (bv_unsigned sp + -96)%Z bR bT bA bA FS0 FBE SK0 DRA DRA DTA DTA DRT SEPR SEPT SEPA SEPA
                      INR INT INA INA RGR RGT RGA RGA CEIL LO SPTop).
  Notation KBK := (KB Σ OW LB m (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a (4 * n)%nat nT
                      (bv_unsigned sp + -96)%Z).
  Notation KUPD := (KK KB_upd).
  Notation KFRAME := (KK KB_frame).
  Notation KSTORE := (KK KB_storeR).
  Notation KAFTER L := (KK L).
  Notation KACC L := (KK L).

  Notation FCELLS := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation ST F fc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 sp a2 x10 x11 x12 x13 x14 x15 x16 x17
             a0 x19 (Z_to_bv 64 (Z.of_nat n)) x21 x22 (Z_to_bv 64 (bv_unsigned a1 + 8 * Z.of_nat n)) x24 x25 (Z_to_bv 64 (8 * Z.of_nat n)) s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).

  Lemma geom : (8 <= N <= 33554432 /\ 0 <= lo /\ lo <= SP - 96 - SK /\ 65536 <= SK /\ CSL <= SK /\
                Z.of_nat (4 * n + sqr_scratch k') <= Z.of_nat nT /\ Z.of_nat (length a) = 2 * N)%Z.
  Proof.
    pose proof Hn8. pose proof HnB. pose proof LO. pose proof LO0. pose proof SK_ge. pose proof HnT. pose proof HLA. lia.
  Qed.

  Lemma B_epi : forall m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x28 x29 x30 x31 F fc,
    KBK FCELLS m1 R T -> RES = (R, T) ->
    evt bgasegs POST (ST F fc 0x230bf0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x28 x29 x30 x31).
  Proof.
    intros until fc. intros (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM) E.
    do 14 zstep.
    assert (LO1 : (lo <= SP + -96)%Z) by (pose proof LO; pose proof SK0; lia).
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

  Lemma B_loop : forall (l pre : list Z) m1 T x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x28 x29 x30 x31 F fc,
    KBK FCELLS m1 (pre ++ l) T -> cu_fit l -> RES = (pre ++ carry_up l, T) ->
    evt bgasegs POST (ST F fc 0x230bcc m1 x1 x5 x6 x7 (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre))) (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre)))
                       x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 (Z_to_bv 64 (shad (rp + 8 * Z.of_nat (length pre)))) x28 x29 x30 x31).
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
    setreg 12%Z (Z_to_bv 64 (addw x 1)) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE FCELLS m1 (pre ++ x :: l') T (length pre) (addw x 1) eq_refl I Hi (addw_limb _ _)) as (SOK0 & I2).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI HEAP MU WM BR0 BR1.
    kb_store SOK0 I2.
    zstep.
    rewrite upd_app_mid in I2.
    pose proof (addw_limb x 1) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K; zify_cond K.
    - setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x 1])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      setreg 11%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x 1])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      setreg 25%Z (Z_to_bv 64 (shad (rp + 8 * Z.of_nat (length (pre ++ [addw x 1]))))) ltac:(f_equal; unfold shad; rewrite length_app; cbn [length]; clear; Z.div_mod_to_equations; lia).
      eapply IHl; [exact I2 | apply Hfit'; exact K |].
      rewrite E. cbn [carry_up]. rewrite K. cbn [Z.eqb]. rewrite <- app_assoc. reflexivity.
    - eapply B_epi; [exact I2|].
      rewrite E. cbn [carry_up]. destruct (Z.eqb_spec (addw x 1) 0) as [E0|_]; [contradiction|]. rewrite <- app_assoc. reflexivity.
  Qed.

  Ltac ret_even := apply ret_pc_even; [lia | reflexivity].
  Ltac ulit := first [ reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; lia); lia | lia ].

  Ltac kacc I G := first
    [ eapply (KACC KB_accRz _ _ _ _ _ _ I); clear - G; lia
    | eapply (KACC KB_accTz _ _ _ _ _ _ I); clear - G; lia
    | eapply (KACC KB_accaz _ _ _ _ _ _ I); clear - G; lia ].
  Ltac kal8 := repeat apply mod8_add8; apply AL8.
  Ltac kapt I G := first
    [ eapply (KACC KB_aptR _ _ _ _ _ _ _ _ I); [kal8 | kal8 | kal8 | clear - G; lia]
    | eapply (KACC KB_aptT _ _ _ _ _ _ _ _ I); [kal8 | kal8 | kal8 | clear - G; lia] ].
  Ltac klen := repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end.
  Ltac kasan I G := klen; split; [kacc I G|]; split; [kacc I G|]; split; [kacc I G|]; kapt I G.
  Ltac kasan2 I G := klen; split; [kacc I G|]; split; [kacc I G|]; split; [kal8|]; split; [kal8|]; exact (KACC KB_shhi _ _ _ _ I).

  Lemma B_fin : forall m1 R T c12 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 F fc,
    KBK FCELLS m1 R T -> kc3_ok RES n R T c12 -> (-1 <= c12 <= 2)%Z ->
    evt bgasegs POST (ST F fc 0x230b74 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c12) x21
                         (Z_to_bv 64 (tq + 8 * Z.of_nat (2 * n))) x24 (Z_to_bv 64 SHB) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK Hc12.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ n (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    do 5 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply call_add_wordsK with (a := slice R n (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -96)%Z)
                               (RP := (rp + 8 * N)%Z) (AP := (rp + 8 * N)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP96 | ret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | exact LRa | exact LTb | rewrite ERa, ETb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa, A2; clear; lia
      | exact HRa | exact HTb | rewrite ERa; exact WRa
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D3 G; lia | kasan I G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LTb ltac:(rewrite ERa, ETb; reflexivity)) as SP3.
    unfold kc3_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R n (2 * n)) (slice T (2 * n) (2 * n))) as [sg3 cy3]. cbn [fst snd] in *.
    destruct SP3 as (Ls3 & Es3 & Hc3 & _). rewrite ERa in Es3. destruct OK as (ERES & Hc & FIT).
    pose proof (KAFTER KB_after_R FCELLS m1 m2 R T n sg3 _ 48%Z eq_refl I MUc ltac:(rewrite ERa, Es3; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls3 ltac:(rewrite Es3; clear; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa WRa HTb LTb ETb MUc WMc HS I D1 D2 D3 HEAP.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_mod c12 cy3) by (clear - Hc12 Hc3; lia).
    zstep. if_cases K; zify_cond K.
    { eapply B_epi; [exact I2|]. rewrite ERES. rewrite K. reflexivity. }
    specialize (FIT K). destruct (Z.eqb_spec (c12 + cy3) 0) as [E0|_]; [contradiction|].
    zstep. rewrite A2, (bn_swrap32_small (N + 2 * N)) by (clear - G; lia).
    do 2 zstep.

    remember (splice R n sg3) as R' eqn:ER'. pose proof ER as ERl.
    assert (Lpre : length (firstn (n + 2 * n) R') = (n + 2 * n)%nat) by (rewrite length_firstn; clear - ER; lia).
    destruct (skipn (n + 2 * n) R') as [|x l'] eqn:Esk.
    { exfalso. pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. clear - HH ER G. lia. }
    assert (ERpl : R' = firstn (n + 2 * n) R' ++ x :: l') by (rewrite <- Esk; symmetry; apply firstn_skipn).
    remember (firstn (n + 2 * n) R') as pre eqn:Epre.
    rewrite ERpl in I2, HR, LR. clear ERpl.
    pose proof (limbs_cons_lit x l' (proj2 (limbs_app_inv _ _ LR))) as (Hx & Ll').
    setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre)))
      ltac:(f_equal; rewrite ?land_m64, ?Z.mod_small by (clear - G; lia); rewrite Z.shiftl_mul_pow2 by lia; rewrite Lpre; clear; lia).
    pose proof (KACC KB_bounds _ _ _ _ I2 ltac:(clear - G; lia) ltac:(clear - G; lia)) as (BR0 & BR1 & _).
    assert (Hi : (length pre < 4 * n)%nat) by (rewrite Lpre; clear - G; lia).
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shR_rd _ m2 _ T (length pre) ad I2 Hi (conj BR0 BR1) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    ld_hd HR2.
    zstep.
    setreg 11%Z (Z_to_bv 64 (addw x (c12 + cy3))) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE FCELLS m2 (pre ++ x :: l') T (length pre) (addw x (c12 + cy3)) eq_refl I2 Hi (addw_limb _ _)) as (SOK0 & I3).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI MU WM I2 MIc STc HEAP BR0 BR1.
    kb_store SOK0 I3. rewrite upd_app_mid in I3.
    pose proof (addw_limb x (c12 + cy3)) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K2; zify_cond K2.
    - eapply B_epi; [exact I3|]. rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx).
      destruct (Z.ltb_spec (addw x (c12 + cy3)) x) as [HH|_]; [exfalso; clear - HH K2; lia|]. rewrite <- app_assoc. reflexivity.
    - do 4 zstep.
      setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x (c12 + cy3)])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      setreg 11%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x (c12 + cy3)])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      setreg 25%Z (Z_to_bv 64 (shad (rp + 8 * Z.of_nat (length (pre ++ [addw x (c12 + cy3)])))))
        ltac:(f_equal; unfold shad; rewrite length_app; cbn [length]; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; Z.div_mod_to_equations; lia).
      assert (TST : (addw x (c12 + cy3) <? x) = true) by (apply Z.ltb_lt; clear - K2; lia).
      eapply B_loop; [exact I3 | |].
      + eapply (add_carry_fit x l' (c12 + cy3)); [rewrite BW_lit; exact Hx | exact Ll' | rewrite BW_lit; clear - Hc; lia | | exact TST].
        replace (S (length l')) with n; [exact FIT|].
        pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. rewrite HH, ERl. clear. lia.
      + rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx). rewrite TST. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma B_sub : forall m1 R T c1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 F fc,
    KBK FCELLS m1 R T -> kc2_ok RES n true R T c1 -> (0 <= c1 <= 1)%Z ->
    evt bgasegs POST (ST F fc 0x230b54 m1 x1 x5 x6 x7 (Z_to_bv 64 c1) x11 x12 x13 x14 x15 x16 x17 a3 x21
                         (Z_to_bv 64 (16 * N)) x24 (Z_to_bv 64 SHB) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    zstep.
    zstep. setreg 22%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (2 * n))) ltac:(f_equal; clear; lia).
    do 5 zstep.
    pose proof SEPT as D3.
    eapply call_sub_wordsK with (a := slice T 0 (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -96)%Z)
                               (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP96 | ret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | exact LTa | exact LTb | rewrite ETa, ETb; reflexivity
      | rewrite ETa; clear - G; lia | ulit | ulit | ulit | rewrite ETa, A2; clear; lia
      | exact HTa | exact HTb | rewrite ETa; exact WTb
      | unfold alias_ok; rewrite ETa; clear; lia | unfold alias_ok; left; reflexivity
      | clear - G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia | kasan I G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (sub_words_spec _ _ LTa LTb ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (sub_words (slice T 0 (2 * n)) (slice T (2 * n) (2 * n))) as [sg2 bw]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hbw & _). rewrite ETa in Es2.
    pose proof (KAFTER KB_after_T FCELLS m1 m2 R T (2 * n)%nat sg2 _ 48%Z eq_refl I MUc ltac:(rewrite ETa, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep. rewrite (bn_swrap32_small (c1 - bw)) by (clear - Hc1 Hbw; lia).
    eapply B_fin; [exact I2 | exact OK | clear - Hc1 Hbw; lia].
  Qed.

  Lemma B_add1 : forall m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 F fc,
    KBK FCELLS m1 R T -> kc_ok RES n true R T ->
    evt bgasegs POST (ST F fc 0x230b40 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a3 (Z_to_bv 64 (rp + 8 * Z.of_nat (2 * n)))
                         (Z_to_bv 64 (16 * N)) x24 (Z_to_bv 64 SHB) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & _).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear; lia)) as (HRb & LRb & ERb & _).
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (_ & _ & _ & WTa).
    do 5 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply call_add_wordsK with (a := slice R 0 (2 * n)) (b := slice R (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -96)%Z)
                               (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (rp + 8 * Z.of_nat 0)%Z) (BP := (rp + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP96 | ret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | exact LRa | exact LRb | rewrite ERa, ERb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa, A2; clear; lia
      | exact HRa | exact HRb | rewrite ERa; exact WTa
      | unfold alias_ok; rewrite ERa; clear - D1 G; lia | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D3 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia | kasan I G | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LRb ltac:(rewrite ERa, ERb; reflexivity)) as SP1.
    unfold kc_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R 0 (2 * n)) (slice R (2 * n) (2 * n))) as [sg1 cy1]. cbn [fst snd] in *.
    destruct SP1 as (Ls1 & Es1 & Hc1 & _). rewrite ERa in Es1.
    pose proof (KAFTER KB_after_T FCELLS m1 m2 R T 0%nat sg1 _ 48%Z eq_refl I MUc ltac:(rewrite ERa, Es1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls1 ltac:(rewrite Es1; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa HRb LRb ERb WTa MUc WMc HS I D1 D2 D3.
    eapply B_sub; [exact I2 | exact OK | exact Hc1].
  Qed.

  Notation a_lo := (firstn n a).
  Notation a_hi := (slice a n n).

  Ltac kin := first [ exact INR | exact INT | exact INA | apply in_or_app; left; first [exact INR | exact INT] ].
  Ltac krng G := let r := fresh in let t := fresh in let a' := fresh in
    pose proof RGR as r; pose proof RGT as t; pose proof RGA as a'; clear - G r t a'; lia.
  Ltac kblocks G := klen; unfold kara_blocks; split; [kin|]; split; [kin|]; split; [kin|]; split; [kin|];
    split; [krng G|]; split; [krng G|]; split; [krng G|]; split; [krng G|];
    split; [kal8|]; split; [kal8|]; split; [kal8|]; kal8.
  Ltac kaside HEAP G :=
    split; [exact HEAP|]; split; [kblocks G|]; split; [exact CEIL|];
    split; [pose proof SPT16 as s16; clear - s16; lia|];
    split; [pose proof SP16 as s16; clear - s16; Z.div_mod_to_equations; lia | exact ETP].

  Lemma B_gen : forall m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc,
    KBK FCELLS m1 R T ->
    sgen2_ok RES k' n a R T ->
    evt bgasegs POST (ST F fc 0x230b14 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a3 a1 (Z_to_bv 64 (16 * N))
                         (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 SHB) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl.
    assert (Lal : length a_lo = n) by (rewrite length_firstn; clear - G; lia).
    pose proof sqr_scratch_tail as HSC.
    do 5 zstep.
    pose proof DRA as D1. pose proof DTA as D3. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof Hk' as HK.
    eapply call_sqr_recA with (CSL := CSL) (k := k') (a := a_lo) (R := slice R 0 (2 * n)) (T := skipn (4 * n) T)
                             (lo := lo) (SPz := (SP + -96)%Z) (bR := bR) (bT := bT) (bA := bA)
                             (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP96 | ret_even | exact ST | exact MI | exact IH
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
      | kaside HEAP G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (sqr_recursive_spec k' a_lo (slice R 0 (2 * n)) (skipn (4 * n) T) (limbs_firstn _ _ LA) LRa LTp
                  ltac:(rewrite Lal, pow_n; reflexivity) ltac:(rewrite ERa, pow_n; reflexivity) ltac:(rewrite ETp; exact HSC)) as MP.
    unfold sqr_post in MP. unfold SqrKaraX.sgen2_ok in OK.
    destruct (sqr_recursive k' a_lo (slice R 0 (2 * n)) (skipn (4 * n) T)) as [rl p1]. cbn [fst snd] in *.
    destruct MP as (Lrl & Erl & _ & Lp1 & Ep1). rewrite ERa in Erl. rewrite ETp in Ep1.
    assert (I2 : KBK FCELLS m2 (splice R 0 rl) (splice T (4 * n) p1)).
    { eapply (KK KB_cps) with (m1 := m1);
        [ reflexivity | exact I | exact HEAPc | rewrite Erl, Ep1; rewrite ERa, ETp in AGc; exact AGc | exact WMc | exact MIc | exact STc
        | exact Lrl | exact Lp1 | rewrite Erl; clear; lia | rewrite Ep1; clear - G; lia | exact HSR | exact HST ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HRa LRa ERa WRa HTp LTp ETp WTp HAl HEAPc AGc WMc HSR HST MIc STc I.
    remember (splice R 0 rl) as R1 eqn:ER1. remember (splice T (4 * n) p1) as T1 eqn:ET1. clear ER1 ET1 Lrl Erl Lp1 Ep1.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I2 ltac:(clear; lia)) as (HRb & LRb & ERb & WRb).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I2 ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n n I2 ltac:(clear - G; lia)) as HAh.
    assert (Lah : length a_hi = n) by (rewrite slice_length; clear - G; lia).
    zstep. setreg 21%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (2 * n))) ltac:(f_equal; clear; lia).
    do 5 zstep.
    eapply call_sqr_recA with (CSL := CSL) (k := k') (a := a_hi) (R := slice R1 (2 * n) (2 * n)) (T := skipn (4 * n) T1)
                             (lo := lo) (SPz := (SP + -96)%Z) (bR := bR) (bT := bT) (bA := bA)
                             (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP96 | ret_even | exact ST | exact MI | exact IH
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
      | kaside HEAP G | ].
    intros m3 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' F3 fc3 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (sqr_recursive_spec k' a_hi (slice R1 (2 * n) (2 * n)) (skipn (4 * n) T1) (slice_limbs _ _ _ LA) LRb LTp
                  ltac:(rewrite Lah, pow_n; reflexivity) ltac:(rewrite ERb, pow_n; reflexivity) ltac:(rewrite ETp; exact HSC)) as MP.
    unfold sqr_post in MP. unfold SqrKaraX.sgen3_ok in OK.
    destruct (sqr_recursive k' a_hi (slice R1 (2 * n) (2 * n)) (skipn (4 * n) T1)) as [rh p2]. cbn [fst snd] in *.
    destruct MP as (Lrh & Erh & _ & Lp2 & Ep2). rewrite ERb in Erh. rewrite ETp in Ep2.
    assert (I3 : KBK FCELLS m3 (splice R1 (2 * n) rh) (splice T1 (4 * n) p2)).
    { eapply (KK KB_cps) with (m1 := m2);
        [ reflexivity | exact I2 | exact HEAPc | rewrite Erh, Ep2; rewrite ERb, ETp in AGc; exact AGc | exact WMc | exact MIc | exact STc
        | exact Lrh | exact Lp2 | rewrite Erh; clear; lia | rewrite Ep2; clear - G; lia | exact HSR | exact HST ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HRb LRb ERb WRb HTp LTp ETp WTp HAh HEAPc AGc WMc HSR HST MIc STc I2.
    clear D1 D3 D5 D6 D7 D8 HK.
    eapply B_add1; [exact I3 | exact OK].
  Qed.

  Lemma B_join : forall m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 F fc,
    KBK FCELLS m1 R T ->
    sjoin_ok RES k' n a R T ->
    evt bgasegs POST (ST F fc 0x230ad0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a3 a1 (Z_to_bv 64 (16 * N)) x24 (Z_to_bv 64 SHB) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof sqr_scratch_tail as HSC.
    zstep. rewrite A2.
    replace ((2 * N) ≪ 1)%Z with (4 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    rewrite (bn_swrap32_small (4 * N)) by (clear - G; lia).
    do 2 zstep.
    setreg 24%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) ltac:(f_equal; rewrite ?land_m64, ?Z.shiftl_mul_pow2 by lia; clear - G; lia).
    zstep. setreg 10%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (2 * n))) ltac:(f_equal; clear; lia).
    do 4 zstep.
    pose proof SEPT as D7. pose proof Hk' as HK.
    eapply call_sqr_recA with (CSL := CSL) (k := k') (a := slice T 0 n) (R := slice T (2 * n) (2 * n)) (T := skipn (4 * n) T)
                             (lo := lo) (SPz := (SP + -96)%Z) (bR := bT) (bT := bT) (bA := bT)
                             (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP96 | ret_even | exact ST | exact MI | exact IH
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
      | kaside HEAP G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HSR HST STc.
    pose proof (sqr_recursive_spec k' (slice T 0 n) (slice T (2 * n) (2 * n)) (skipn (4 * n) T) LTa LTr LTp
                  ltac:(rewrite ETa, pow_n; reflexivity) ltac:(rewrite ETr, pow_n; reflexivity) ltac:(rewrite ETp; exact HSC)) as MP.
    unfold sqr_post in MP. unfold SqrKaraX.sjoin_ok in OK.
    destruct (sqr_recursive k' (slice T 0 n) (slice T (2 * n) (2 * n)) (skipn (4 * n) T)) as [tm p0]. cbn [fst snd] in *.
    destruct MP as (Ltm & Etm & _ & Lp0 & Ep0). rewrite ETr in Etm. rewrite ETp in Ep0.
    assert (I2 : KBK FCELLS m2 R (splice T (2 * n) (tm ++ p0))).
    { eapply (KK KB_cps_TT);
        [ reflexivity | exact I | exact HEAPc | rewrite Etm, Ep0; rewrite ETr, ETp in AGc; exact AGc | rewrite Etm; clear; lia
        | exact WMc | exact MIc | exact STc | exact Ltm | exact Lp0 | rewrite Ep0; clear - G; lia | exact HSR | exact HST ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HTa LTa ETa HTr LTr ETr WTr HTp LTp ETp WTp HEAPc AGc WMc HSR HST MIc STc I D7 HK.
    zstep.
    eapply B_gen; [exact I2 | exact OK].
  Qed.

  Lemma ms_stack : (lo + RT_STACK <= SP + -96 /\ SP + -96 + 16 <= USTACK_TOP /\ (SP + -96) mod 16 = 0)%Z.
  Proof.
    pose proof geom as G. pose proof SPT16 as S1. pose proof SP16 as S2. unfold RT_STACK.
    split; [clear - G; lia|]. split; [clear - S1; lia|]. clear - S2. Z.div_mod_to_equations. lia.
  Qed.

  Lemma B_zero : forall m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 F fc,
    KBK FCELLS m1 R T ->
    szero_ok RES k' n a R T ->
    evt bgasegs POST (ST F fc 0x230af8 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a3 a1 (Z_to_bv 64 (16 * N)) x24 (Z_to_bv 64 SHB) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
    zstep. rewrite A2.
    replace ((2 * N) ≪ 1)%Z with (4 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    rewrite (bn_swrap32_small (4 * N)) by (clear - G; lia).
    do 2 zstep.
    setreg 24%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) ltac:(f_equal; rewrite ?land_m64, ?Z.shiftl_mul_pow2 by lia; clear - G; lia).
    zstep. setreg 10%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (2 * n))) ltac:(f_equal; clear; lia).
    do 3 zstep.
    pose proof ms_stack as (MS1 & MS2 & MS3). pose proof RGT as RT'.
    eapply call_memset0A with (L := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -96)%Z) (D := (tq + 8 * Z.of_nat (2 * n))%Z) (bd := bT);
      [ exact ESP96 | ret_even | exact ST | exact MI | exact HEAP | exact CEIL | exact MS1 | exact MS2 | exact MS3 | exact ETP
      | apply in_or_app; left; exact INT | clear - RT' G; lia | rewrite ETr; clear - RT' G; lia | rewrite ETr; clear - G; lia
      | ulit | reflexivity | rewrite ETr; ulit | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HZ STc.
    rewrite ETr in HZ, AGc.
    assert (I2 : KBK FCELLS m2 R (splice T (2 * n) (repeat 0%Z (2 * n)))).
    { eapply (KK KB_cps_T);
        [ reflexivity | exact I | exact HEAPc | rewrite repeat_length; exact AGc | exact WMc | exact MIc | exact STc
        | exact (limbs_repeat _ _ limb_0) | rewrite repeat_length; clear - G; lia | exact HZ ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HTr LTr ETr WTr HEAPc AGc WMc HZ MIc STc I MS1 MS2 MS3 RT'.
    eapply B_gen; [exact I2 | exact OK].
  Qed.

  Lemma B_diff : forall (sw : bool) m1 R T x1 x5 x6 x7 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 F fc,
    KBK FCELLS m1 R T ->
    sjoin_ok RES k' n a R (splice T 0 (fst (if sw then sub_words a_hi a_lo else sub_words a_lo a_hi))) ->
    evt bgasegs POST (ST F fc 0x230ac8 m1 x1 x5 x6 x7 a3 (if sw then Z_to_bv 64 (ap + 8 * N) else a1) (if sw then a1 else Z_to_bv 64 (ap + 8 * N))
                         x13 x14 x15 x16 x17 a3 a1 (Z_to_bv 64 (16 * N)) x24 (Z_to_bv 64 SHB) x28 x29 x30 x31).
  Proof.
    intros until fc. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
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
      eapply call_sub_wordsK with (a := a_hi) (b := a_lo) (lo := lo) (SPz := (SP + -96)%Z)
                                 (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * N)%Z) (BP := (ap + 8 * Z.of_nat 0)%Z);
        [ exact ESP96 | ret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | apply slice_limbs; exact LA | apply limbs_firstn; exact LA
        | rewrite Lah, Lal; reflexivity | rewrite Lah; clear - G; lia | ulit | ulit | ulit | rewrite Lah; ulit
        | exact HAh | exact HAl | rewrite Lah; exact WTn
        | unfold alias_ok; rewrite Lah; clear - D3 G; lia | unfold alias_ok; rewrite Lah; clear - D3 G; lia
        | clear - G; lia | rewrite Lah; clear - D7 G; lia | rewrite Lah; clear - D8 G; lia | rewrite Lah; clear - D8 G; lia | kasan I G | ].
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (sub_words_spec _ _ (slice_limbs _ n n LA) (limbs_firstn n _ LA) ltac:(rewrite Lah, Lal; reflexivity)) as SPd.
      destruct (sub_words a_hi a_lo) as [d bw]. cbn [fst snd] in *.
      destruct SPd as (Ld & Ed & _ & _). rewrite Lah in Ed.
      pose proof (KAFTER KB_after_T FCELLS m1 m2 R T 0%nat d _ 48%Z eq_refl I MUc ltac:(rewrite Lah, Ed; reflexivity)
                    ltac:(clear - G; lia) WMc MIc HS STc Ld ltac:(rewrite Ed; clear - G; lia)) as I2.
      eapply B_join; [exact I2 | exact OK].
    - do 2 zstep.
      eapply call_sub_wordsK with (a := a_lo) (b := a_hi) (lo := lo) (SPz := (SP + -96)%Z)
                                 (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
        [ exact ESP96 | ret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
        | rewrite Lah, Lal; reflexivity | rewrite Lal; clear - G; lia | ulit | ulit | ulit | rewrite Lal; ulit
        | exact HAl | exact HAh | rewrite Lal; exact WTn
        | unfold alias_ok; rewrite Lal; clear - D3 G; lia | unfold alias_ok; rewrite Lal; clear - D3 G; lia
        | clear - G; lia | rewrite Lal; clear - D7 G; lia | rewrite Lal; clear - D8 G; lia | rewrite Lal; clear - D8 G; lia | kasan I G | ].
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (sub_words_spec _ _ (limbs_firstn n _ LA) (slice_limbs _ n n LA) ltac:(rewrite Lah, Lal; reflexivity)) as SPd.
      destruct (sub_words a_lo a_hi) as [d bw]. cbn [fst snd] in *.
      destruct SPd as (Ld & Ed & _ & _). rewrite Lal in Ed.
      pose proof (KAFTER KB_after_T FCELLS m1 m2 R T 0%nat d _ 48%Z eq_refl I MUc ltac:(rewrite Lal, Ed; reflexivity)
                    ltac:(clear - G; lia) WMc MIc HS STc Ld ltac:(rewrite Ed; clear - G; lia)) as I2.
      eapply B_join; [exact I2 | exact OK].
  Qed.

  Lemma kara_body : forall m1 R T x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 F fc,
    KBK FCELLS m1 R T ->
    (let c1 := cmp_words a_lo a_hi in
     if (0 <? c1)%Z then sjoin_ok RES k' n a R (splice T 0 (fst (sub_words a_lo a_hi)))
     else if (c1 <? 0)%Z then sjoin_ok RES k' n a R (splice T 0 (fst (sub_words a_hi a_lo)))
     else szero_ok RES k' n a R T) ->
    evt bgasegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 sp a2 (Z_to_bv 64 15) (Z_to_bv 64 8) a2 a3 x14 x15 x16 x17
               a0 a3 s4 a1 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x230a84) fc None m1 (seg_rom bgasegs)).
  Proof.
    intros until fc. intros I OK.
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & HEAP & _ & _).
    pose proof (KACC KB_shb _ _ _ _ I) as (G1 & G2).
    pose proof (KACC KB_shhi _ _ _ _ I) as CSH. unfold SHHI in CSH.
    do 6 zstep. rewrite A2, ?land_m64, half_n2 by (clear - G; lia).
    do 2 zstep. replace (N ≪ 3)%Z with (8 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    setreg 23%Z (Z_to_bv 64 (ap + 8 * N)) ltac:(f_equal; clear; lia).
    do 4 zstep.
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_a _ _ _ _ n n I ltac:(clear - G; lia)) as HAh.
    assert (Lal : length a_lo = n) by (rewrite length_firstn; clear - G; lia).
    assert (Lah : length a_hi = n) by (rewrite slice_length; clear - G; lia).
    pose proof SEPA as D8.
    eapply call_cmp_wordsA with (a := a_lo) (b := a_hi) (lo := lo) (SPz := (SP + -96)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
      [ exact ESP96 | ret_even | exact STK | exact MI | exact (AH_shb _ _ _ _ HEAP) | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
      | rewrite Lah, Lal; reflexivity | rewrite Lal; clear - G; lia | ulit | ulit | rewrite Lal; ulit
      | exact HAl | exact HAh | clear - G; lia
      | rewrite Lal; clear - D8 G; lia | rewrite Lal; clear - D8 G; lia | kasan2 I G | ].
    intros m3 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc STc.
    pose proof (KAFTER KB_after_ro FCELLS m1 m3 R T 16%Z eq_refl I MUc ltac:(clear - G; lia) WMc MIc STc) as I3.
    clear FR STK MI HEAP HAl HAh D8 MUc WMc MIc STc I G1 G2.
    pose proof I3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    remember (cmp_words a_lo a_hi) as c1 eqn:Ec1.
    zstep. rewrite A2. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    assert (Hc1 : (c1 = -1 \/ c1 = 0 \/ c1 = 1)%Z).
    { rewrite Ec1, (cmp_words_spec a_lo a_hi (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA)) by (rewrite Lal, Lah; reflexivity). apply sgn3_range. }
    clear Ec1.
    destruct Hc1 as [E1|[E1|E1]]; rewrite E1 in *; clear E1 c1; cbn [Z.ltb] in OK.
    -
      setreg 10%Z (Z_to_bv 64 (-1)) ltac:(vm_compute; reflexivity). zstep. if_true.
      zstep. if_true. do 4 zstep.
      eapply (B_diff true); [exact I3 | exact OK].
    -
      setreg 10%Z (Z_to_bv 64 0) ltac:(vm_compute; reflexivity). zstep. if_true.
      zstep. if_false.
      eapply B_zero; [exact I3 | exact OK].
    -
      setreg 10%Z (Z_to_bv 64 1) ltac:(vm_compute; reflexivity). zstep. if_false.
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

Definition stop_preA (CSL : Z) (N2 la lR lT : nat) (SK rp tq ap SP lo : Z) : Prop :=
  (1 <= Z.of_nat N2 <= 67108864)%Z /\ la = N2 /\ lR = (2 * N2)%nat /\ (2 * N2 <= lT)%nat /\ (65536 <= SK /\ CSL <= SK)%Z /\
  (rp + 8 * Z.of_nat lR <= ap \/ ap + 8 * Z.of_nat la <= rp)%Z /\
  (tq + 8 * Z.of_nat lT <= ap \/ ap + 8 * Z.of_nat la <= tq)%Z /\
  (rp + 8 * Z.of_nat lR <= tq \/ tq + 8 * Z.of_nat lT <= rp)%Z /\
  (rp + 8 * Z.of_nat lR <= SP - 96 - SK \/ SP <= rp)%Z /\
  (tq + 8 * Z.of_nat lT <= SP - 96 - SK \/ SP <= tq)%Z /\
  (ap + 8 * Z.of_nat la <= SP - 96 - SK \/ SP <= ap)%Z /\
  (lo <= SP - 96 - SK)%Z /\ (0 <= lo)%Z.

Section Top.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).
  Variables (CQ4 CQ8 CSL : Z).
  Hypothesis C4_0 : (0 <= CQ4)%Z.
  Hypothesis C8_0 : (0 <= CQ8)%Z.
  Hypothesis HC4 : (CQ4 <= CSL)%Z.
  Hypothesis HC8 : (CQ8 <= CSL)%Z.
  Hypothesis comba4_ok : sqr_comba4_aspec CQ4.
  Hypothesis comba8_ok : sqr_comba8_aspec CQ8.
  Variables (Σ : rts RT) (OW LB : list block) (bR bT bA : block).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : word -> option byte) (a R T : list Z) (lo : Z) (N2 : nat) (SK : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation tq := (bv_unsigned a3).
  Notation SP := (bv_unsigned sp).
  Hypothesis PRE : stop_preA CSL N2 (length a) (length R) (length T) SK (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned sp) lo.
  Hypothesis KBL : kara_blocks OW LB bR bT bA bA rp tq ap ap (length R) (length T) (length a) (length a).
  Hypothesis CEIL : (ACEIL <= lo)%Z.
  Hypothesis SPT16 : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis ETP : tp = wz TP_A.
  Hypothesis LA : limbs a.
  Hypothesis A2 : bv_unsigned a2 = Z.of_nat N2.
  Lemma tHN2 : (1 <= Z.of_nat N2 <= 67108864)%Z. Proof. apply PRE. Qed.
  Lemma tHLA : length a = N2. Proof. apply PRE. Qed.
  Lemma tHLR : length R = (2 * N2)%nat. Proof. apply PRE. Qed.
  Lemma tHLT : (2 * N2 <= length T)%nat. Proof. apply PRE. Qed.
  Lemma tHSK : (65536 <= SK /\ CSL <= SK)%Z. Proof. apply PRE. Qed.
  Lemma tDRA : (rp + 8 * Z.of_nat (length R) <= ap \/ ap + 8 * Z.of_nat (length a) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma tDTA : (tq + 8 * Z.of_nat (length T) <= ap \/ ap + 8 * Z.of_nat (length a) <= tq)%Z. Proof. apply PRE. Qed.
  Lemma tDRT : (rp + 8 * Z.of_nat (length R) <= tq \/ tq + 8 * Z.of_nat (length T) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma tSEPR : (rp + 8 * Z.of_nat (length R) <= SP - 96 - SK \/ SP <= rp)%Z. Proof. apply PRE. Qed.
  Lemma tSEPT : (tq + 8 * Z.of_nat (length T) <= SP - 96 - SK \/ SP <= tq)%Z. Proof. apply PRE. Qed.
  Lemma tSEPA : (ap + 8 * Z.of_nat (length a) <= SP - 96 - SK \/ SP <= ap)%Z. Proof. apply PRE. Qed.
  Lemma tLO : (lo <= SP - 96 - SK)%Z. Proof. apply PRE. Qed.
  Lemma tLO0 : (0 <= lo)%Z. Proof. apply PRE. Qed.
  Variable RES : list Z * list Z.

  Lemma tSK0 : (0 <= SK)%Z. Proof. pose proof tHSK as h. clear - h. lia. Qed.
  Lemma tFS0 : (0 <= 96)%Z. Proof. lia. Qed.
  Lemma tFBE : (SP + -96 = SP - 96)%Z. Proof. reflexivity. Qed.
  Lemma tSPTop : (SP <= USTACK_TOP)%Z. Proof. pose proof SPT16. lia. Qed.
  Lemma tINR : In bR OW. Proof. apply KBL. Qed.
  Lemma tINT : In bT OW. Proof. apply KBL. Qed.
  Lemma tINA : In bA (OW ++ LB). Proof. apply KBL. Qed.
  Lemma tRGR : (blk_addr bR <= rp /\ rp + 8 * Z.of_nat (length R) <= blk_addr bR + blk_size bR)%Z. Proof. apply KBL. Qed.
  Lemma tRGT : (blk_addr bT <= tq /\ tq + 8 * Z.of_nat (length T) <= blk_addr bT + blk_size bT)%Z. Proof. apply KBL. Qed.
  Lemma tRGA : (blk_addr bA <= ap /\ ap + 8 * Z.of_nat (length a) <= blk_addr bA + blk_size bA)%Z. Proof. apply KBL. Qed.
  Lemma tAL8 : (rp mod 8 = 0 /\ tq mod 8 = 0 /\ ap mod 8 = 0 /\ ap mod 8 = 0)%Z. Proof. apply KBL. Qed.

  Notation POST := (kpost Σ (ASTA RT Σ PMc (kr_apost ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo
                      (bv_unsigned a0) (Z.of_nat (length R)) (bv_unsigned a3) (Z.of_nat (length T)) (fst RES) (snd RES) m))).
  Notation KS L := (L Σ OW LB m (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a (length R) (length T)
                      96%Z SK (bv_unsigned sp + -96)%Z bR bT bA bA tFS0 tFBE tSK0 tDRA tDRA tDTA tDTA tDRT tSEPR tSEPT tSEPA tSEPA
                      tINR tINT tINA tINA tRGR tRGT tRGA tRGA CEIL tLO tSPTop).
  Notation KBS := (KB Σ OW LB m (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (bv_unsigned sp) lo a a (length R) (length T)
                      (bv_unsigned sp + -96)%Z).
  Notation FCELLS := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation ST0 F fc pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             a0 x19 s4 a1 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).

  Lemma tgeom : (1 <= Z.of_nat N2 <= 67108864 /\ 0 <= lo /\ lo <= SP - 96 - SK /\ 65536 <= SK /\ CSL <= SK /\ 0 <= CQ4 <= CSL /\ 0 <= CQ8 <= CSL /\
                 Z.of_nat (length a) = Z.of_nat N2 /\ Z.of_nat (length R) = 2 * Z.of_nat N2 /\ 2 * Z.of_nat N2 <= Z.of_nat (length T))%Z.
  Proof.
    pose proof tHN2 as h1. pose proof tLO as h2. pose proof tLO0 as h3. pose proof tHSK as h4.
    pose proof tHLA as h7. pose proof tHLR as h9. pose proof tHLT as h10. clear - h1 h2 h3 h4 h7 h9 h10 C4_0 C8_0 HC4 HC8. lia.
  Qed.

  Lemma T_leaf_post : forall (F : bvmap 5 word) (fc : bv 32) m1 CS res nn ms',
    KBS FCELLS m1 R T -> (0 <= CS <= SK)%Z -> length res = length R -> RES = (splice R 0 res, T) -> nn = Z.of_nat (length R) ->
    stk bgasegs m1 lo SP ->
    vl_post bgasegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp nn CS res lo m1 ms' ->
    kpost Σ (ASTA RT Σ PMc (kr_apost ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo
                      (bv_unsigned a0) (Z.of_nat (length R)) (bv_unsigned a3) (Z.of_nat (length T)) (fst RES) (snd RES) m)) ms'.
  Proof.
    intros F fc m1 CS res nn ms' I HCS Lres ERES -> STK PO.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof tgeom as G.
    pose proof tDRT as D6. pose proof tSEPT as D7.
    unfold W_mul_normal.vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
    assert (HW : Forall (kw_ok rp tq SP lo (length R) (length T)) [(rp, rp + 8 * Z.of_nat (length R)); (SP - CS, SP)]%Z).
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold kw_ok; cbn [fst snd].
      - right; left. clear. lia.
      - left. clear - G HCS. lia. }
    subst ms'. unfold kpost. apply cps_done. unfold kr_apost. rewrite ETP.
    do 18 eexists. split; [reflexivity|].
    split; [exact MIc|]. split; [exact STc|].
    split; [exact (KS kw_heap _ m1 m2 HEAP MUc WMc HW)|].
    split; [eapply wmono_trans; [exact WM | exact WMc]|].
    split. { eapply agree_on_trans; [exact MU|]. exact (KS kw_agree _ m1 m2 HEAP MUc HW). }
    rewrite ERES. cbn [fst snd].
    rewrite splice_all by (rewrite Lres; reflexivity).
    split; [exact HS|].
    eapply limbs_at_transport; [exact HT | exact MUc | cbn [disjoint_from]; clear - D6 D7 G HCS; lia].
  Qed.

  Lemma T_comba_pre : forall m1 (nl : nat), KBS FCELLS m1 R T -> N2 = nl ->
    length a = nl /\ limbs_at bgasegs m1 ap a /\ wr_at bgasegs m1 rp (8 * Z.of_nat (2 * nl)) /\
    (rp + 8 * Z.of_nat (2 * nl) <= ap \/ ap + 8 * Z.of_nat nl <= rp)%Z /\
    (rp + 8 * Z.of_nat (2 * nl) <= SP - SK \/ SP <= rp)%Z /\ (ap + 8 * Z.of_nat nl <= SP - SK \/ SP <= ap)%Z /\
    mem_inv bgasegs m1 /\ shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m1 /\
    acc bgasegs m1 rp (8 * Z.of_nat (2 * nl)) /\ acc bgasegs m1 ap (8 * Z.of_nat nl) /\
    aptrs2 rp ap (Z.of_nat (2 * nl)) lo /\ (0 < rp)%Z /\ (0 < ap)%Z /\ (rp + 8 * Z.of_nat (2 * nl) <= 65536 \/ 12345344 <= rp)%Z /\
    length R = (2 * nl)%nat.
  Proof.
    intros m1 nl I E.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof tgeom as G. pose proof tHLA as h1. pose proof tHLR as h2.
    pose proof tDRA as D1. pose proof tSEPR as D3. pose proof tSEPA as D4.
    pose proof (KS KB_offR _ _ _ _ I) as (OSH & OFI). pose proof (KS KB_shhi _ _ _ _ I) as CSH. pose proof (KS KB_pos _ _ _ _ I) as (P1 & _ & P3 & _).
    pose proof tAL8 as (AR8 & _ & AA8 & _).
    assert (ELR : length R = (2 * nl)%nat) by (clear - h2 E; lia).
    split; [clear - h1 E; lia|]. split; [exact HA|]. split; [rewrite <- ELR; exact WR|].
    split; [rewrite <- ELR; clear - D1 h1 E; lia|]. split; [rewrite <- ELR; clear - D3 G; lia|]. split; [clear - D4 h1 E G; lia|].
    split; [exact MI|]. split; [exact (AH_shb _ _ _ _ HEAP)|].
    split; [eapply (KS KB_accRz _ _ _ _ _ _ I); clear - ELR; lia|]. split; [eapply (KS KB_accaz _ _ _ _ _ _ I); clear - h1 E; lia|].
    split; [unfold aptrs2; split; [exact AR8|]; split; [exact AA8|]; split; [rewrite <- ELR; exact OSH | exact CSH]|].
    split; [exact P1|]. split; [exact P3|]. split; [rewrite <- ELR; exact OFI | exact ELR].
  Qed.

  Lemma T_comba8 : forall m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 F fc,
    KBS FCELLS m1 R T -> N2 = 8%nat -> RES = (splice R 0 (sqr_comba8 a), T) ->
    evt bgasegs POST (ST0 F fc 0x2309f0 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I E8 ERES.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof tgeom as G.
    destruct (T_comba_pre m1 8%nat I E8) as (La & HA' & WR' & D1 & D3 & D4 & _ & SHB' & ACR & ACA & APT & P1 & P3 & OFI & ELR).
    do 16 zstep.
    assert (LO1 : (lo <= SP + -96)%Z) by (clear - G; lia).
    release_frame FR ST (bv_unsigned sp).
    destruct (sqr_comba_spec a 8 LA La) as (_ & Lc & _).
    eapply evt_mono.
    { eapply comba8_ok with (a := a) (lo := lo);
        [ exact LA | exact La | exact HA' | exact WR' | clear - D1; lia | exact ST | clear - G; lia
        | clear - D3 G; lia | clear - D4 G; lia | exact MI | exact SHB' | exact ACR | exact ACA | exact APT | exact P1 | exact P3 | clear - OFI; lia ]. }
    intros ms' PO.
    eapply (T_leaf_post F fc m1 CQ8 (sqr_comba8 a) 16%Z ms' I); [ clear - G; lia | rewrite Lc, ELR; reflexivity | exact ERES | rewrite ELR; reflexivity | exact ST | exact PO ].
  Qed.

  Lemma T_comba4 : forall m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 F fc,
    KBS FCELLS m1 R T -> N2 = 4%nat -> RES = (splice R 0 (sqr_comba4 a), T) ->
    evt bgasegs POST (ST0 F fc 0x2309b0 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I E4 ERES.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof tgeom as G.
    destruct (T_comba_pre m1 4%nat I E4) as (La & HA' & WR' & D1 & D3 & D4 & _ & SHB' & ACR & ACA & APT & P1 & P3 & OFI & ELR).
    do 16 zstep.
    assert (LO1 : (lo <= SP + -96)%Z) by (clear - G; lia).
    release_frame FR ST (bv_unsigned sp).
    destruct (sqr_comba_spec a 4 LA La) as (_ & Lc & _).
    eapply evt_mono.
    { eapply comba4_ok with (a := a) (lo := lo);
        [ exact LA | exact La | exact HA' | exact WR' | clear - D1; lia | exact ST | clear - G; lia
        | clear - D3 G; lia | clear - D4 G; lia | exact MI | exact SHB' | exact ACR | exact ACA | exact APT | exact P1 | exact P3 | clear - OFI; lia ]. }
    intros ms' PO.
    eapply (T_leaf_post F fc m1 CQ4 (sqr_comba4 a) 8%Z ms' I); [ clear - G; lia | rewrite Lc, ELR; reflexivity | exact ERES | rewrite ELR; reflexivity | exact ST | exact PO ].
  Qed.

  Lemma T_small : forall m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc,
    KBS FCELLS m1 R T -> (Z.of_nat N2 <= 15)%Z ->
    RES = (let '(ro, tmp) := sqr_normal a R in (splice R 0 ro, splice T 0 tmp)) ->
    evt bgasegs POST (ST0 F fc 0x230a3c m1 x1 x5 x6 x7 a2 x10 x11 x12 x13 x14 x15 x16 x17 a3 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I K16 ERES.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof tgeom as G. pose proof tHLA as HLA'. pose proof tHLR as HLR'. pose proof tHLT as HT2.
    pose proof tDRA as DRA. pose proof tDTA as DTA. pose proof tDRT as DRT. pose proof tSEPR as SEPR. pose proof tSEPT as SEPT. pose proof tSEPA as SEPA.
    pose proof (KS KB_offR _ _ _ _ I) as (OSHR & OFIR). pose proof (KS KB_offT _ _ _ _ I) as (OSHT & OFIT).
    pose proof (KS KB_shhi _ _ _ _ I) as CSH. pose proof tAL8 as (AR8 & AT8 & AA8 & _).
    assert (ACR : acc bgasegs m1 rp (8 * (2 * Z.of_nat (length a)))) by (eapply (KS KB_accRz _ _ _ _ _ _ I); clear - G; lia).
    assert (ACA : acc bgasegs m1 ap (8 * Z.of_nat (length a))) by (eapply (KS KB_accaz _ _ _ _ _ _ I); clear - G; lia).
    assert (ACT : acc bgasegs m1 tq (8 * (2 * Z.of_nat (length a)))) by (eapply (KS KB_accTz _ _ _ _ _ _ I); clear - G; lia).
    assert (APT : sqn_ptrs rp ap tq (2 * Z.of_nat (length a)) lo).
    { unfold sqn_ptrs. split; [exact AR8|]. split; [exact AA8|]. split; [exact AT8|].
      split; [clear - OSHR G; lia|]. split; [clear - OSHT G; unfold SHLO, SHHI in *; lia|]. split; [exact CSH|].
      split; [clear - OFIR G; lia | clear - OFIT G; lia]. }
    clear OSHR OFIR OSHT OFIT DRA DTA DRT SEPR SEPT SEPA.
    do 18 zstep.
    assert (LO1 : (lo <= SP + -96)%Z) by (clear - G; lia).
    release_frame FR ST (bv_unsigned sp).
    pose proof tDRA as DRA. pose proof tDTA as DTA. pose proof tDRT as DRT. pose proof tSEPR as SEPR. pose proof tSEPT as SEPT. pose proof tSEPA as SEPA.
    pose proof (BgSqrCorrect.sqr_normal_spec a LA R ltac:(clear - HLA' G; lia) LR ltac:(clear - HLA' HLR'; lia)) as NSP.
    rewrite ERES. clear ERES.
    destruct (sqr_normal a R) as [ro tmp] eqn:Esn. destruct NSP as (Lro & Ero & _ & Etmp). cbn [fst snd].
    destruct (sqr_words_spec a LA) as (_ & Lsw & _).
    eapply evt_mono.
    { eapply (bn_sqr_normal_aspec ra sp gp tp) with (A := a) (r0 := R) (lo := lo);
        [ exact LA | exact LR | clear - HLA' HLR'; lia | clear - G; lia | clear - G K16; lia | rewrite A2, HLA'; reflexivity
        | exact HA | exact HR
        | replace (8 * (2 * Z.of_nat (length a)))%Z with (8 * Z.of_nat (length R))%Z by (clear - G; lia); exact WR
        | pose proof (wr_at_sub bgasegs m1 _ _ 0 (8 * (2 * Z.of_nat (length a))) WT ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - G; lia)) as X;
          rewrite Z.add_0_r in X; exact X
        | clear - DRA G; lia | clear - DRT G; lia | clear - DTA G; lia
        | exact ST | clear - G; lia
        | clear - SEPR G; lia | clear - SEPA G; lia | clear - SEPT G; lia | exact MI
        | exact (AH_shb _ _ _ _ HEAP) | exact ACR | exact ACA | exact ACT | exact APT ]. }
    intros ms' PO. unfold W_sqr_normal.vl_post2 in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & HTs & STc).
    assert (HW : Forall (kw_ok rp tq SP lo (length R) (length T))
                   [(rp, rp + 8 * (2 * Z.of_nat (length a))); (tq, tq + 8 * (2 * Z.of_nat (length a))); (SP - 208, SP)]%Z).
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold kw_ok; cbn [fst snd].
      - right; left. clear - G. lia.
      - right; right. clear - G. lia.
      - left. clear - G. lia. }
    subst ms'. unfold kpost. apply cps_done. unfold kr_apost. rewrite ETP.
    do 18 eexists. split; [reflexivity|].
    split; [exact MIc|]. split; [exact STc|].
    split; [exact (KS kw_heap _ m1 m2 HEAP MUc WMc HW)|].
    split; [eapply wmono_trans; [exact WM | exact WMc]|].
    split. { eapply agree_on_trans; [exact MU|]. exact (KS kw_agree _ m1 m2 HEAP MUc HW). }
    rewrite Esn in HS. cbn [fst snd] in HS.
    rewrite splice_all by (rewrite Ero, HLR', HLA'; reflexivity).
    split; [exact HS|].
    eapply (BnKaraMem.limbs_at_splice bgasegs _ m1 m2 tq T 0 tmp HT MUc).
    - rewrite Etmp, Lsw. clear - HT2 HLA'. lia.
    - change (Z.of_nat 0) with 0%Z. rewrite Z.mul_0_r, Z.add_0_r, Etmp. exact HTs.
    - cbn [disjoint_from]. split; [clear - DRT G; lia|]. split; [clear; lia|]. split; [clear - SEPT G; lia | exact Logic.I].
    - cbn [disjoint_from]. rewrite Etmp, Lsw.
      split; [clear - DRT G; lia|]. split; [clear - G; lia|]. split; [clear - SEPT G; lia | exact Logic.I].
  Qed.

  Lemma T_entry : forall F fc,
    limbs R -> limbs T ->
    limbs_at bgasegs m ap a -> limbs_at bgasegs m rp R -> limbs_at bgasegs m tq T ->
    wr_at bgasegs m rp (8 * Z.of_nat (length R)) -> wr_at bgasegs m tq (8 * Z.of_nat (length T)) ->
    stk bgasegs m lo SP -> mem_inv bgasegs m -> AHEAP Σ OW LB m ->
    (N2 = 8%nat -> RES = (splice R 0 (sqr_comba8 a), T)) ->
    (N2 = 4%nat -> RES = (splice R 0 (sqr_comba4 a), T)) ->
    (N2 <> 8%nat -> N2 <> 4%nat -> (Z.of_nat N2 <= 15)%Z ->
     RES = (let '(ro, tmp) := sqr_normal a R in (splice R 0 ro, splice T 0 tmp))) ->
    ((16 <= Z.of_nat N2)%Z ->
     forall m1 x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31,
       KBS FCELLS m1 R T ->
       evt bgasegs POST
         (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 sp a2 (Z_to_bv 64 15) (Z_to_bv 64 8) a2 a3 x14 x15 x16 x17
                  a0 a3 s4 a1 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x230a84) fc None m1 (seg_rom bgasegs))) ->
    evt bgasegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x23095c) fc None m (seg_rom bgasegs)).
  Proof.
    intros F fc LR LT RA RR RT' WR WT STK MI0 HEAP RES8 RES4 RESS KARA.
    pose proof tgeom as G.
    pose proof (AH_ceil _ _ _ _ HEAP) as (_ & CSH & _).
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - CSH CEIL; unfold SHHI in CSH; lia).
    assert (LO1 : (lo <= SP - 96)%Z) by (clear - G; lia).
    carve_frame 96%nat STK.
    pose proof (munch_refl [(SP + -96, SP + -96 + 96)]%Z m) as MUF. pose proof (wmono_refl bgasegs m) as WMF.
    assert (I0 : KBS [CB 96 junk] m R T).
    { unfold KB. split; [exact LR|]. split; [exact LT|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact RR|]. split; [exact RT'|]. split; [exact RA|]. split; [exact RA|]. split; [exact WR|]. split; [exact WT|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact HEAP|].
      split; [|exact WMF]. unfold KAG. intros x _. reflexivity. }
    clear RA RR RT' WR WT HEAP CSH.
    apply (rw_cells_split_CB bgasegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 14 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (KS KB_frame _ _ m mm R T I0 MUF WMF MI0 STK FR) as I end.
    clear I0 MUF WMF.
    do 3 zstep.
    zstep. if_cases K8; zify_cond K8.
    { assert (E8 : N2 = 8%nat) by (clear - K8 A2; lia).
      eapply T_comba8; [exact I | exact E8 | exact (RES8 E8)]. }
    do 2 zstep.
    zstep. if_cases K4; zify_cond K4.
    2: { assert (E4 : N2 = 4%nat) by (clear - K4 A2; lia).
         eapply T_comba4; [exact I | exact E4 | exact (RES4 E4)]. }
    do 2 zstep.
    assert (L15 : (bv_unsigned (Z_to_bv 64 15) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (L2 : (bv_unsigned a2 < 9223372036854775808)%Z) by (rewrite A2; clear - G; lia).
    zstep. rewrite (W_mul_normal.lts_words_small (Z_to_bv 64 15) a2 L15 L2). clear L15 L2.
    rewrite A2. if_cases K16; zify_cond K16.
    { eapply KARA; [clear - K16; lia | exact I]. }
    assert (NC : N2 <> 4%nat /\ N2 <> 8%nat) by (clear - K4 K8 A2; split; intros E; [apply K4 | apply K8]; rewrite A2, E; reflexivity).
    eapply T_small; [exact I | clear - K16; lia | apply RESS; [apply NC | apply NC | clear - K16; lia]].
  Qed.
End Top.

Section Main.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).
  Variables (CQ4 CQ8 CSL : Z).
  Hypothesis C4_0 : (0 <= CQ4)%Z.
  Hypothesis C8_0 : (0 <= CQ8)%Z.
  Hypothesis HC4 : (CQ4 <= CSL)%Z.
  Hypothesis HC8 : (CQ8 <= CSL)%Z.
  Hypothesis comba4_ok : sqr_comba4_aspec CQ4.
  Hypothesis comba8_ok : sqr_comba8_aspec CQ8.

  Lemma rec_body : forall k, (forall k', k = S k' -> sqr_rec_spec_atA CSL k') -> sqr_rec_spec_atA CSL k.
  Proof.
    intros k IHk. unfold sqr_rec_spec_atA.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB bR bT bA a R T lo
           LA LR LT Hk HLA HLR HLT A2 RA RR RT WR WT DRA DTA DRT STK LO SEPR SEPT SEPA MI0
           HEAP KBL CEIL SPT16 SP16 ETP.
    remember (Nat.pow 2 k) as N2 eqn:EN2.
    assert (HN2 : (1 <= Z.of_nat N2 <= 67108864)%Z) by (subst N2; apply pow2_bounds26; exact Hk).
    remember (srec_stackA CSL k - 96)%Z as SK eqn:ESK.
    assert (HSK : (65536 <= SK /\ CSL <= SK)%Z) by (subst SK; unfold srec_stackA; clear; lia).
    assert (ERS : srec_stackA CSL k = (96 + SK)%Z) by (subst SK; clear; lia).
    rewrite ERS in LO, SEPR, SEPT, SEPA.
    replace (bv_unsigned sp - (96 + SK))%Z with (bv_unsigned sp - 96 - SK)%Z in LO by (clear; lia).
    replace (bv_unsigned sp - (96 + SK))%Z with (bv_unsigned sp - 96 - SK)%Z in SEPR by (clear; lia).
    replace (bv_unsigned sp - (96 + SK))%Z with (bv_unsigned sp - 96 - SK)%Z in SEPT by (clear; lia).
    replace (bv_unsigned sp - (96 + SK))%Z with (bv_unsigned sp - 96 - SK)%Z in SEPA by (clear; lia).
    pose proof (proj1 STK) as LO0.
    pose proof (sqr_scratch_ge k) as HSG. rewrite <- EN2 in HSG.
    assert (PRE : stop_preA CSL N2 (length a) (length R) (length T) SK (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned sp) lo).
    { unfold stop_preA.
      split; [exact HN2|]. split; [exact HLA|]. split; [exact HLR|]. split; [clear - HSG HLT; lia|]. split; [exact HSK|].
      split; [exact DRA|]. split; [exact DTA|]. split; [exact DRT|].
      split; [exact SEPR|]. split; [exact SEPT|]. split; [exact SEPA|]. split; [exact LO | exact LO0]. }
    apply cps_from_evt'.
    eapply (T_entry CQ4 CQ8 CSL C4_0 C8_0 HC4 HC8 comba4_ok comba8_ok) with (N2 := N2) (SK := SK) (bR := bR) (bT := bT) (bA := bA);
      [ exact PRE | exact KBL | exact CEIL | exact SPT16 | exact ETP | exact LA | exact A2
      | exact LR | exact LT | exact RA | exact RR | exact RT | exact WR | exact WT | exact STK | exact MI0 | exact HEAP | | | | ].
    -
      intros E8. rewrite sqr_recursive_c8 by (rewrite <- EN2; exact E8).
      rewrite firstn_all2 by (clear - HLA E8; lia). reflexivity.
    -
      intros E4. rewrite sqr_recursive_c4 by (rewrite <- EN2; exact E4).
      rewrite firstn_all2 by (clear - HLA E4; lia). reflexivity.
    -
      intros N8 N4 K16. rewrite sqr_recursive_small by (rewrite <- EN2; first [clear - K16; lia | assumption]).
      cbv zeta. rewrite <- EN2. rewrite !firstn_all2 by (clear - HLA HLR; lia). reflexivity.
    -
      intros K16 m1 x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 I.
      destruct (pow2_ge16 k ltac:(rewrite <- EN2; clear - K16; lia)) as (k' & Ek & Hk3). subst k.
      remember (Nat.pow 2 k') as n eqn:En.
      assert (EN : N2 = (2 * n)%nat) by (rewrite EN2, En; cbn [Nat.pow]; clear; lia).
      assert (ELR : length R = (4 * n)%nat) by (clear - HLR EN; lia).
      assert (ESK' : SK = srec_stackA CSL k').
      { clear - ESK. unfold srec_stackA in *. rewrite !Nat2Z.inj_succ in *. lia. }
      assert (KPRE : sqr_preA CSL k' n (length a) (length T) SK (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned sp) lo).
      { unfold sqr_preA. rewrite <- ELR.
        split; [exact En|]. split; [clear - Hk Hk3; lia|]. split; [clear - K16 EN; lia|]. split; [clear - HN2 EN; lia|].
        split; [clear - HLA EN; lia|].
        split. { cbn [sqr_scratch] in HLT. rewrite <- EN2 in HLT. clear - HLT EN ELR. lia. }
        split; [exact ESK'|].
        split; [exact DRA|]. split; [exact DTA|]. split; [exact DRT|].
        split; [exact SEPR|]. split; [exact SEPT|]. split; [exact SEPA|].
        split; [exact LO | exact LO0]. }
      assert (KBL' : kara_blocks OW LB bR bT bA bA (bv_unsigned a0) (bv_unsigned a3) (bv_unsigned a1) (bv_unsigned a1) (4 * n) (length T) (length a) (length a))
        by (rewrite <- ELR; exact KBL).
      rewrite ELR in I. rewrite ELR.
      eapply (kara_body CSL k' (IHk k' eq_refl)) with (n := n) (nT := length T) (SK := SK);
        [ exact KPRE | exact KBL' | exact CEIL | exact SPT16 | exact SP16 | exact ETP | exact LA | rewrite A2, EN; clear; lia
        | exact I | ].
      rewrite En. apply srec_staged; try assumption; rewrite <- ?EN2; try assumption.
      clear - K16. lia.
  Qed.

  Theorem bn_sqr_recursive_aspec : forall k, sqr_rec_spec_atA CSL k.
  Proof.
    induction k as [|k IH]; apply rec_body; intros k' E; [discriminate|]. injection E as <-. exact IH.
  Qed.
End Main.
