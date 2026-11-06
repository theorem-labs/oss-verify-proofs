(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp BnKaraX BnKaraPX BnKaraMem.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require Import W_add_words W_sub_words W_cmp_words W_cmp_part_words W_sub_part_words W_mul_normal BnCalls W_mul_recursive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_mul_part_recursive_entry := 0xf89d4%Z.

Lemma munch_add_stack0 : forall (D L8 FB : Z) (m1 m2 : word -> option byte),
  munch [(D, D + L8)]%Z m1 m2 -> munch [(D, D + L8); (FB - 0, FB)]%Z m1 m2.
Proof.
  intros D L8 FB m1 m2 H. eapply munch_weaken; [|exact H]. unfold sub_fp. cbn [outside]. intros x (H1 & _ & H3). split; [exact H1 | exact H3].
Qed.

Lemma land_even_mask64 : forall x, (0 <= x < 1073741824)%Z -> Z.land (2 * x) 18446744071562067966 = (2 * x)%Z.
Proof.
  intros x Hx.
  replace (2 * x)%Z with (Z.shiftl x 1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  change 18446744071562067966%Z with (Z.shiftl 9223372035781033983 1).
  rewrite <- Z.shiftl_land. f_equal.
  assert (E : x = Z.land x (Z.ones 30)) by (rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 30)%Z with 1073741824%Z; lia).
  rewrite E at 1. rewrite <- Z.land_assoc. change (Z.land (Z.ones 30) 9223372035781033983) with (Z.ones 30). symmetry. exact E.
Qed.

Lemma srliw_half : forall x, (0 <= x < 1073741824)%Z -> bv_swrap 32 (bv_wrap 32 (2 * x) ≫ 1) = x.
Proof.
  intros x Hx.
  assert (E1 : bv_wrap 32 (2 * x) = (2 * x)%Z) by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32)%Z with 4294967296%Z; apply Z.mod_small; lia).
  rewrite E1, Z.shiftr_div_pow2 by lia. change (2 ^ 1)%Z with 2%Z. rewrite Z.mul_comm, Z.div_mul by lia.
  apply bn_swrap32_small. lia.
Qed.

Definition part_stack (CS8 : Z) (k : nat) : Z := (144 * Z.of_nat (S k) + rec_stack CS8 k)%Z.

Lemma rec_stack_mono : forall CS8 j k, (j <= k)%nat -> (rec_stack CS8 j <= rec_stack CS8 k)%Z.
Proof. intros CS8 j k H. unfold rec_stack. lia. Qed.
Lemma part_stack_S : forall CS8 j k, (S j <= k)%nat -> (part_stack CS8 j <= part_stack CS8 k - 144)%Z.
Proof. intros CS8 j k H. unfold part_stack, rec_stack. lia. Qed.
Lemma part_stack_rec : forall CS8 k, (rec_stack CS8 k <= part_stack CS8 k - 144)%Z.
Proof. intros CS8 k. unfold part_stack. lia. Qed.

Definition part_spec_at (CS8 : Z) (fuel : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (k tna tnb : nat) (R T : list Z) (lo : Z),
    limbs a -> limbs b -> limbs R -> limbs T ->
    (3 <= k)%nat -> (k <= fuel)%nat -> (k <= 26)%nat ->
    (tna < Nat.pow 2 k)%nat -> (tnb < Nat.pow 2 k)%nat -> (tna <= tnb + 1)%nat -> (tnb <= tna + 1)%nat ->
    length a = (Nat.pow 2 k + tna)%nat -> length b = (Nat.pow 2 k + tnb)%nat -> length R = (4 * Nat.pow 2 k)%nat ->
    (8 * Nat.pow 2 k <= length T)%nat ->
    bv_unsigned a3 = Z.of_nat (Nat.pow 2 k) -> bv_unsigned a4 = Z.of_nat tna -> bv_unsigned a5 = Z.of_nat tnb ->
    limbs_at bgpsegs m (bv_unsigned a1) a -> limbs_at bgpsegs m (bv_unsigned a2) b ->
    limbs_at bgpsegs m (bv_unsigned a0) R -> limbs_at bgpsegs m (bv_unsigned a6) T ->
    wr_at bgpsegs m (bv_unsigned a0) (8 * Z.of_nat (length R)) -> wr_at bgpsegs m (bv_unsigned a6) (8 * Z.of_nat (length T)) ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a0)%Z ->
    (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a6)%Z ->
    (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a6)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a6 \/ bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a0)%Z ->
    stk bgpsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - part_stack CS8 k)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned sp - part_stack CS8 k \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned sp - part_stack CS8 k \/ bv_unsigned sp <= bv_unsigned a6)%Z ->
    (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - part_stack CS8 k \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned sp - part_stack CS8 k \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    mem_inv bgpsegs m ->
    evt bgpsegs (kr_post bgpsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (bv_unsigned a0) (Z.of_nat (length R)) (bv_unsigned a6) (Z.of_nat (length T)) (part_stack CS8 k)
                 (fst (mul_part_recursive fuel k a b tna tnb R T)) (snd (mul_part_recursive fuel k a b tna tnb R T)) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xf89d4) fc None m (seg_rom bgpsegs)).

Section CallPart.
  Variable POST : machine_state -> Prop.
  Variables (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo SPz RET : Z).
  Hypothesis ESP : bv_unsigned wsp = SPz.
  Hypothesis ERET : ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET.
  Hypothesis STK : stk bgpsegs m lo SPz.
  Hypothesis MI0 : mem_inv bgpsegs m.

  Lemma call_part : forall (CS8 : Z) (fuel k : nat) (a b : list Z) (tna tnb : nat) (R T : list Z) (RP AP BP TQ : Z),
    part_spec_at CS8 fuel ->
    limbs a -> limbs b -> limbs R -> limbs T ->
    (3 <= k)%nat -> (k <= fuel)%nat -> (k <= 26)%nat ->
    (tna < Nat.pow 2 k)%nat -> (tnb < Nat.pow 2 k)%nat -> (tna <= tnb + 1)%nat -> (tnb <= tna + 1)%nat ->
    length a = (Nat.pow 2 k + tna)%nat -> length b = (Nat.pow 2 k + tnb)%nat -> length R = (4 * Nat.pow 2 k)%nat ->
    (8 * Nat.pow 2 k <= length T)%nat ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (Nat.pow 2 k) ->
    bv_unsigned w4 = Z.of_nat tna -> bv_unsigned w5 = Z.of_nat tnb -> bv_unsigned w6 = TQ ->
    limbs_at bgpsegs m AP a -> limbs_at bgpsegs m BP b -> limbs_at bgpsegs m RP R -> limbs_at bgpsegs m TQ T ->
    wr_at bgpsegs m RP (8 * Z.of_nat (length R)) -> wr_at bgpsegs m TQ (8 * Z.of_nat (length T)) ->
    (RP + 8 * Z.of_nat (length R) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (RP + 8 * Z.of_nat (length R) <= BP \/ BP + 8 * Z.of_nat (length b) <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= AP \/ AP + 8 * Z.of_nat (length a) <= TQ)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= BP \/ BP + 8 * Z.of_nat (length b) <= TQ)%Z ->
    (RP + 8 * Z.of_nat (length R) <= TQ \/ TQ + 8 * Z.of_nat (length T) <= RP)%Z ->
    (lo <= SPz - part_stack CS8 k)%Z ->
    (RP + 8 * Z.of_nat (length R) <= SPz - part_stack CS8 k \/ SPz <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= SPz - part_stack CS8 k \/ SPz <= TQ)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - part_stack CS8 k \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - part_stack CS8 k \/ SPz <= BP)%Z ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length R)); (TQ, TQ + 8 * Z.of_nat (length T)); (SPz - part_stack CS8 k, SPz)]%Z m m2 ->
       wmono bgpsegs m m2 -> mem_inv bgpsegs m2 ->
       limbs_at bgpsegs m2 RP (fst (mul_part_recursive fuel k a b tna tnb R T)) ->
       limbs_at bgpsegs m2 TQ (snd (mul_part_recursive fuel k a b tna tnb R T)) ->
       stk bgpsegs m2 lo SPz ->
       evt bgpsegs POST
         (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
             F (Z_to_bv 64 RET) fc None m2 (seg_rom bgpsegs))) ->
    evt bgpsegs POST
      (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xf89d4) fc None m (seg_rom bgpsegs)).
  Proof using ESP ERET STK MI0.
    intros CS8 fuel k a b tna tnb R T RP AP BP TQ SPEC LA LB LR LT Hk3 Hkf Hk26 Htna Htnb Hd1 Hd2 HLA HLB HLR HLT E0 E1 E2 E3 E4 E5 E6
           RA RB RR RT WR WT DRA DRB DTA DTB DRT LO SEPR SEPT SEPA SEPB K.
    subst RP AP BP TQ SPz.
    eapply evt_cut; [ eapply SPEC with (a := a) (b := b) (k := k) (tna := tna) (tnb := tnb) (R := R) (T := T) (lo := lo); eassumption | ].
    intros ms' PO. unfold kr_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & HT & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.
End CallPart.

Definition kpart_pre (CS8 : Z) (fuel' k n tna tnb la lb nT : nat) (SK rp tq ap bp SP lo : Z) : Prop :=
  n = Nat.pow 2 k /\ (3 <= k <= 26)%nat /\ (k <= S fuel')%nat /\ (8 <= n)%nat /\ (Z.of_nat n <= 67108864)%Z /\
  (tna < n)%nat /\ (tnb < n)%nat /\ (tna <= tnb + 1)%nat /\ (tnb <= tna + 1)%nat /\
  la = (n + tna)%nat /\ lb = (n + tnb)%nat /\ (8 * n <= nT)%nat /\ SK = (part_stack CS8 k - 144)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= ap \/ ap + 8 * Z.of_nat la <= rp)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= bp \/ bp + 8 * Z.of_nat lb <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat la <= tq)%Z /\
  (tq + 8 * Z.of_nat nT <= bp \/ bp + 8 * Z.of_nat lb <= tq)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= tq \/ tq + 8 * Z.of_nat nT <= rp)%Z /\
  (rp + 8 * Z.of_nat (4 * n) <= SP - 144 - SK \/ SP <= rp)%Z /\
  (tq + 8 * Z.of_nat nT <= SP - 144 - SK \/ SP <= tq)%Z /\
  (ap + 8 * Z.of_nat la <= SP - 144 - SK \/ SP <= ap)%Z /\
  (bp + 8 * Z.of_nat lb <= SP - 144 - SK \/ SP <= bp)%Z /\
  (lo <= SP - 144 - SK)%Z /\ (0 <= lo)%Z.

Section KaraP.
  Variable CS8 : Z.
  Hypothesis CS8_0 : (0 <= CS8)%Z.
  Hypothesis comba8_ok : comba8_spec CS8.
  Variable fuel' : nat.
  Hypothesis IHp : part_spec_at CS8 fuel'.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (k tna tnb : nat) (lo : Z) (n nT : nat) (SK : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a2).
  Notation tq := (bv_unsigned a6).
  Notation SP := (bv_unsigned sp).
  Notation N := (Z.of_nat n).
  Hypothesis PRE : kpart_pre CS8 fuel' k n tna tnb (length a) (length b) nT SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo.
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
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
  Lemma HSK : SK = (part_stack CS8 k - 144)%Z. Proof. apply PRE. Qed.
  Lemma DRA : (rp + 8 * Z.of_nat (4 * n) <= ap \/ ap + 8 * Z.of_nat (length a) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma DRB : (rp + 8 * Z.of_nat (4 * n) <= bp \/ bp + 8 * Z.of_nat (length b) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma DTA : (tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat (length a) <= tq)%Z. Proof. apply PRE. Qed.
  Lemma DTB : (tq + 8 * Z.of_nat nT <= bp \/ bp + 8 * Z.of_nat (length b) <= tq)%Z. Proof. apply PRE. Qed.
  Lemma DRT : (rp + 8 * Z.of_nat (4 * n) <= tq \/ tq + 8 * Z.of_nat nT <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPR : (rp + 8 * Z.of_nat (4 * n) <= SP - 144 - SK \/ SP <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPT : (tq + 8 * Z.of_nat nT <= SP - 144 - SK \/ SP <= tq)%Z. Proof. apply PRE. Qed.
  Lemma SEPA : (ap + 8 * Z.of_nat (length a) <= SP - 144 - SK \/ SP <= ap)%Z. Proof. apply PRE. Qed.
  Lemma SEPB : (bp + 8 * Z.of_nat (length b) <= SP - 144 - SK \/ SP <= bp)%Z. Proof. apply PRE. Qed.
  Lemma LO : (lo <= SP - 144 - SK)%Z. Proof. apply PRE. Qed.
  Lemma LO0 : (0 <= lo)%Z. Proof. apply PRE. Qed.
  Lemma SK_rec : (rec_stack CS8 k <= SK)%Z. Proof. rewrite HSK. apply part_stack_rec. Qed.
  Lemma SK_ge : (320 <= SK /\ CS8 <= SK)%Z. Proof. pose proof SK_rec. unfold rec_stack in *. lia. Qed.
  Lemma SK0 : (0 <= SK)%Z. Proof. pose proof SK_ge. lia. Qed.
  Lemma FS0 : (0 <= 144)%Z. Proof. lia. Qed.
  Lemma FBE : (SP + -144 = SP - 144)%Z. Proof. reflexivity. Qed.
  Lemma ESP144 : bv_unsigned (Z_to_bv 64 (SP + -144)) = (SP + -144)%Z.
  Proof.
    apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R.
    pose proof LO. pose proof LO0. pose proof SK0. lia.
  Qed.
  Lemma pow_n : Nat.pow 2 k = n. Proof. symmetry. exact Hn. Qed.

  Lemma geom : (8 <= N <= 67108864 /\ 0 <= lo /\ lo <= SP - 144 - SK /\ 320 <= SK /\ CS8 <= SK /\ 0 <= CS8 /\ rec_stack CS8 k <= SK /\
                8 * N <= Z.of_nat nT /\ Z.of_nat tna < N /\ Z.of_nat tnb < N /\ Z.of_nat tna <= Z.of_nat tnb + 1 /\ Z.of_nat tnb <= Z.of_nat tna + 1 /\
                Z.of_nat (length a) = N + Z.of_nat tna /\ Z.of_nat (length b) = N + Z.of_nat tnb)%Z.
  Proof.
    pose proof Hn8. pose proof HnB. pose proof LO. pose proof LO0. pose proof SK_ge. pose proof SK_rec. pose proof HnT. pose proof Htna.
    pose proof Htnb. pose proof Hd1. pose proof Hd2. pose proof HLA. pose proof HLB. lia.
  Qed.

  Notation POST := (kr_post bgpsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                      (bv_unsigned a0) (Z.of_nat (4 * n)) (bv_unsigned a6) (Z.of_nat nT) (144 + SK)%Z (fst RES) (snd RES) lo m).
  Notation KBK := (KB bgpsegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      144%Z SK (bv_unsigned sp + -144)%Z).
  Notation KFRAME := (KB_frame bgpsegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      144%Z SK (bv_unsigned sp + -144)%Z FS0 FBE SK0 SEPR SEPT SEPA SEPB).
  Notation KSTORE := (KB_storeR bgpsegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      144%Z SK (bv_unsigned sp + -144)%Z FS0 FBE SK0 DRA DRB DRT SEPR).
  Notation KAFTER L := (L bgpsegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      144%Z SK (bv_unsigned sp + -144)%Z FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB).
  Notation KACC L := (L bgpsegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      144%Z SK (bv_unsigned sp + -144)%Z).

  Notation TCELLS jb j1 j2 v120 v112 :=
    [CB 8 jb; CB 8 j1; CB 8 j2; C8 v120; C8 v112;
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 sp a3 x10 x11 x12 x13 x14 x15 x16 x17
             x18 a6 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).

  Ltac ret_even := apply ret_pc_even; [lia | reflexivity].
  Ltac ulit := first [ reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; lia); lia | lia ].
  Ltac kb_store SOK0 I2 :=
    lazymatch type of SOK0 with
    | store_ok _ ?m2 ?a0' _ = true =>
        let ad := cur_mem_addr in
        let SOK := fresh "SOK" in
        assert (SOK : store_ok bgpsegs m2 ad 8 = true) by (replace ad with a0' by (unfold wa; f_equal; lia); exact SOK0);
        replace a0' with ad in I2 by (unfold wa; f_equal; lia);
        zstep; clear SOK SOK0;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => let m' := fresh "m" in gen_mem mm m' end
    end.

  Lemma BP_epi : forall jb j1 j2 v120 v112 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KBK (TCELLS jb j1 j2 v120 v112) m1 R T -> RES = (R, T) ->
    evt bgpsegs POST (ST 0xf8e90 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM) E.
    do 15 zstep.
    assert (LO1 : (lo <= SP + -144)%Z) by (pose proof LO; pose proof SK0; lia).
    release_frame FR ST (bv_unsigned sp).
    subst RES. cbn [fst snd].
    assert (MU' : munch [(rp, rp + 8 * Z.of_nat (4 * n)); (tq, tq + 8 * Z.of_nat nT); (SP - (144 + SK), SP)]%Z m m1).
    { unfold KWfin in MU. replace (SP - (144 + SK))%Z with (SP - 144 - SK)%Z by (clear; lia). exact MU. }
    finish.
  Qed.

  Lemma BP_loop : forall (l pre : list Z) jb j1 j2 v120 v112 m1 T x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KBK (TCELLS jb j1 j2 v120 v112) m1 (pre ++ l) T -> cu_fit l -> RES = (pre ++ carry_up l, T) ->
    evt bgpsegs POST (ST 0xf8e7c m1 x1 x5 x6 x7 (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre))) x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction l as [|x l' IHl]; intros until x31; intros I FIT E.
    { exfalso. unfold cu_fit in FIT. cbn [lval length] in FIT. rewrite Bp_0 in FIT. clear - FIT. lia. }
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (cu_fit_cons (x :: l') (proj2 (limbs_app_inv _ _ LR)) FIT) as (x' & l'' & Ecs & Hx & Hl' & Hfit').
    injection Ecs as <- <-.
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    ld_hd HR2.
    zstep.
    setreg 11%Z (Z_to_bv 64 (addw x 1)) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    assert (Hi : (length pre < 4 * n)%nat) by (rewrite length_app in ER; cbn [length] in ER; clear - ER; lia).
    destruct (KSTORE (TCELLS jb j1 j2 v120 v112) m1 (pre ++ x :: l') T (length pre) (addw x 1) eq_refl I Hi (addw_limb _ _)) as (SOK0 & I2).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI MU WM.
    kb_store SOK0 I2.
    zstep.
    rewrite upd_app_mid in I2.
    pose proof (addw_limb x 1) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K; zify_cond K.
    - setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x 1])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      eapply IHl; [exact I2 | apply Hfit'; exact K |].
      rewrite E. cbn [carry_up]. rewrite K. cbn [Z.eqb]. rewrite <- app_assoc. reflexivity.
    - eapply BP_epi; [exact I2|].
      rewrite E. cbn [carry_up]. destruct (Z.eqb_spec (addw x 1) 0) as [E0|_]; [contradiction|]. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma BP_fin : forall jb j1 j2 v120 v112 m1 R T c12 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30 x31,
    KBK (TCELLS jb j1 j2 v120 v112) m1 R T -> kc3_ok RES n R T c12 -> (-1 <= c12 <= 2)%Z ->
    evt bgpsegs POST (ST 0xf8e40 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 (Z_to_bv 64 (tq + 16 * N)) (Z_to_bv 64 (2 * N))
                       (Z_to_bv 64 c12) (Z_to_bv 64 (8 * N)) x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK Hc12.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ n (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    do 5 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply call_add_words with (a := slice R n (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -144)%Z)
                               (RP := (rp + 8 * N)%Z) (AP := (rp + 8 * N)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact LRa | exact LTb | rewrite ERa, ETb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa; ulit
      | exact HRa | exact HTb | rewrite ERa; exact WRa
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D3 G; lia | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LTb ltac:(rewrite ERa, ETb; reflexivity)) as SP3.
    unfold kc3_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R n (2 * n)) (slice T (2 * n) (2 * n))) as [sg3 cy3]. cbn [fst snd] in *.
    destruct SP3 as (Ls3 & Es3 & Hc3 & _). rewrite ERa in Es3. destruct OK as (ERES & Hc & FIT).
    pose proof (KAFTER KB_after_R (TCELLS jb j1 j2 v120 v112) m1 m2 R T n sg3 _ 16%Z eq_refl I MUc ltac:(rewrite ERa, Es3; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls3 ltac:(rewrite Es3; clear; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa WRa HTb LTb ETb MUc WMc HS I D1 D2 D3.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    zstep. rewrite (bn_swrap32_mod c12 cy3) by (clear - Hc12 Hc3; lia).
    zstep. if_cases K; zify_cond K.
    { eapply BP_epi; [exact I2|]. rewrite ERES. rewrite K. reflexivity. }
    specialize (FIT K). destruct (Z.eqb_spec (c12 + cy3) 0) as [E0|_]; [contradiction|].
    zstep. rewrite A3, (bn_swrap32_small (2 * N + N)) by (clear - G; lia).
    do 2 zstep.

    remember (splice R n sg3) as R' eqn:ER'. pose proof ER as ERl.
    assert (Lpre : length (firstn (n + 2 * n) R') = (n + 2 * n)%nat) by (rewrite length_firstn; clear - ER; lia).
    destruct (skipn (n + 2 * n) R') as [|x l'] eqn:Esk.
    { exfalso. pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. clear - HH ER G. lia. }
    assert (ERpl : R' = firstn (n + 2 * n) R' ++ x :: l') by (rewrite <- Esk; symmetry; apply firstn_skipn).
    remember (firstn (n + 2 * n) R') as pre eqn:Epre.
    rewrite ERpl in I2, HR, LR. clear ERpl.
    pose proof (limbs_cons_lit x l' (proj2 (limbs_app_inv _ _ LR))) as (Hx & Ll').
    setreg 18%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre))) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; rewrite Lpre; clear; lia).
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    ld_hd HR2.
    zstep.
    setreg 10%Z (Z_to_bv 64 (addw x (c12 + cy3))) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE (TCELLS jb j1 j2 v120 v112) m2 (pre ++ x :: l') T (length pre) (addw x (c12 + cy3)) eq_refl I2 ltac:(rewrite Lpre; clear - G; lia) (addw_limb _ _)) as (SOK0 & I3).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI MU WM I2 MIc STc.
    kb_store SOK0 I3. rewrite upd_app_mid in I3.
    pose proof (addw_limb x (c12 + cy3)) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K2; zify_cond K2.
    - eapply BP_epi; [exact I3|]. rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx).
      destruct (Z.ltb_spec (addw x (c12 + cy3)) x) as [HH|_]; [exfalso; clear - HH K2; lia|]. rewrite <- app_assoc. reflexivity.
    - zstep.
      setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x (c12 + cy3)])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      assert (TST : (addw x (c12 + cy3) <? x) = true) by (apply Z.ltb_lt; clear - K2; lia).
      eapply BP_loop; [exact I3 | |].
      + eapply (add_carry_fit x l' (c12 + cy3)); [rewrite BW_lit; exact Hx | exact Ll' | rewrite BW_lit; clear - Hc; lia | | exact TST].
        replace (S (length l')) with n; [exact FIT|].
        pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. rewrite HH, ERl. clear. lia.
      + rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx). rewrite TST. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma BP_sub : forall jb j1 j2 v120 v112 m1 R T c1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30 x31,
    KBK (TCELLS jb j1 j2 v120 v112) m1 R T -> kc2_ok RES n true R T c1 -> (0 <= c1 <= 1)%Z ->
    evt bgpsegs POST (ST 0xf8e2c m1 x1 x5 x6 x7 (Z_to_bv 64 (tq + 16 * N)) x11 x12 x13 x14 x15 x16 x17 a0 (Z_to_bv 64 (tq + 16 * N)) (Z_to_bv 64 (2 * N))
                       (Z_to_bv 64 c1) (Z_to_bv 64 (8 * N)) x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    do 4 zstep.
    pose proof SEPT as D3.
    eapply call_sub_words with (a := slice T 0 (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -144)%Z)
                               (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact LTa | exact LTb | rewrite ETa, ETb; reflexivity
      | rewrite ETa; clear - G; lia | ulit | ulit | ulit | rewrite ETa; ulit
      | exact HTa | exact HTb | rewrite ETa; exact WTb
      | unfold alias_ok; rewrite ETa; clear; lia | unfold alias_ok; left; reflexivity
      | clear - G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (sub_words_spec _ _ LTa LTb ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (sub_words (slice T 0 (2 * n)) (slice T (2 * n) (2 * n))) as [sg2 bw]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hbw & _). rewrite ETa in Es2.
    pose proof (KAFTER KB_after_T (TCELLS jb j1 j2 v120 v112) m1 m2 R T (2 * n)%nat sg2 _ 16%Z eq_refl I MUc ltac:(rewrite ETa, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep. rewrite (bn_swrap32_small (c1 - bw)) by (clear - Hc1 Hbw; lia).
    eapply BP_fin; [exact I2 | exact OK | clear - Hc1 Hbw; lia].
  Qed.

  Lemma BP_add : forall jb j1 j2 v120 v112 m1 R T c1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30 x31,
    KBK (TCELLS jb j1 j2 v120 v112) m1 R T -> kc2_ok RES n false R T c1 -> (0 <= c1 <= 1)%Z ->
    evt bgpsegs POST (ST 0xf8e14 m1 x1 x5 x6 x7 (Z_to_bv 64 (tq + 16 * N)) x11 x12 x13 x14 x15 x16 x17 a0 (Z_to_bv 64 (tq + 16 * N)) (Z_to_bv 64 (2 * N))
                       (Z_to_bv 64 c1) (Z_to_bv 64 (8 * N)) x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    do 4 zstep.
    pose proof SEPT as D3.
    eapply call_add_words with (a := slice T (2 * n) (2 * n)) (b := slice T 0 (2 * n)) (lo := lo) (SPz := (SP + -144)%Z)
                               (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat (2 * n))%Z) (BP := (tq + 8 * Z.of_nat 0)%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact LTb | exact LTa | rewrite ETa, ETb; reflexivity
      | rewrite ETb; clear - G; lia | ulit | ulit | ulit | rewrite ETb; ulit
      | exact HTb | exact HTa | rewrite ETb; exact WTb
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ETb; clear; lia
      | clear - G; lia | rewrite ETb; clear - D3 G; lia | rewrite ETb; clear - D3 G; lia | rewrite ETb; clear - D3 G; lia | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LTb LTa ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (add_words (slice T (2 * n) (2 * n)) (slice T 0 (2 * n))) as [sg2 cy]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hcy & _). rewrite ETb in Es2.
    pose proof (KAFTER KB_after_T (TCELLS jb j1 j2 v120 v112) m1 m2 R T (2 * n)%nat sg2 _ 16%Z eq_refl I MUc ltac:(rewrite ETb, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep. setreg 22%Z (Z_to_bv 64 (c1 + cy)) ltac:(f_equal; clear; lia).
    zstep.
    eapply BP_fin; [exact I2 | exact OK | clear - Hc1 Hcy; lia].
  Qed.

  Lemma BP_tail : forall (neg : bool) jb j1 j2 v120 v112 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x25 x26 x28 x29 x30 x31,
    KBK (TCELLS jb j1 j2 v120 v112) m1 R T -> kc_ok RES n neg R T ->
    evt bgpsegs POST (ST 0xf8dec m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 (Z_to_bv 64 (2 * N)) (Z_to_bv 64 (2 * N))
                       x22 (Z_to_bv 64 (8 * N)) x24 x25 x26 (Z_to_bv 64 (if neg then 0 else 1)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & _).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear; lia)) as (HRb & LRb & ERb & _).
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (_ & _ & _ & WTa).
    zstep. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 5 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply call_add_words with (a := slice R 0 (2 * n)) (b := slice R (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -144)%Z)
                               (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (rp + 8 * Z.of_nat 0)%Z) (BP := (rp + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact LRa | exact LRb | rewrite ERa, ERb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa; ulit
      | exact HRa | exact HRb | rewrite ERa; exact WTa
      | unfold alias_ok; rewrite ERa; clear - D1 G; lia | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D3 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LRb ltac:(rewrite ERa, ERb; reflexivity)) as SP1.
    unfold kc_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R 0 (2 * n)) (slice R (2 * n) (2 * n))) as [sg1 cy1]. cbn [fst snd] in *.
    destruct SP1 as (Ls1 & Es1 & Hc1 & _). rewrite ERa in Es1.
    pose proof (KAFTER KB_after_T (TCELLS jb j1 j2 v120 v112) m1 m2 R T 0%nat sg1 _ 16%Z eq_refl I MUc ltac:(rewrite ERa, Es1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls1 ltac:(rewrite Es1; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa HRb LRb ERb WTa MUc WMc HS I D1 D2 D3 MIc STc.
    do 3 zstep.
    destruct neg.
    - zstep. if_true. eapply BP_sub; [exact I2 | exact OK | exact Hc1].
    - zstep. if_false. eapply BP_add; [exact I2 | exact OK | exact Hc1].
  Qed.

  Notation GCELLS jb v136 :=
    [CB 8 jb; C8 v136; C8 (Z_to_bv 64 (8 * Z.of_nat n)); C8 (Z_to_bv 64 (bv_unsigned a2 + 8 * Z.of_nat n)); C8 (Z_to_bv 64 (bv_unsigned a1 + 8 * Z.of_nat n));
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma to_tail : forall jb v136 m1 R T, KBK (GCELLS jb v136) m1 R T ->
    KBK (TCELLS jb (le8 v136) (le8 (Z_to_bv 64 (8 * N))) (Z_to_bv 64 (bp + 8 * N)) (Z_to_bv 64 (ap + 8 * N))) m1 R T.
  Proof.
    intros jb v136 m1 R T I. eapply (KACC KB_recell); [exact I|].
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
    apply (rw_cells_forget_C8 bgpsegs m1 _ [CB 8 jb]) in FR. cbn [app] in FR.
    apply (rw_cells_forget_C8 bgpsegs m1 _ [CB 8 jb; CB 8 (le8 v136)]) in FR. cbn [app] in FR. exact FR.
  Qed.

  Lemma BP_tail_cc : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x25 x26 x27 x28 x29 x30 x31,
    KBK (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T -> kc_ok RES n neg R T ->
    evt bgpsegs POST (ST 0xf8de8 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 (Z_to_bv 64 (2 * N)) (Z_to_bv 64 (2 * N))
                       x22 (Z_to_bv 64 (8 * N)) x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
    zstep.
    eapply (BP_tail neg); [apply to_tail; exact I | exact OK].
  Qed.

  Lemma BP_tail_c8 : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31,
    KBK (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T -> kc_ok RES n neg R T ->
    evt bgpsegs POST (ST 0xf8de4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 x20 (Z_to_bv 64 (2 * N))
                       x22 (Z_to_bv 64 (8 * N)) x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK. zstep. eapply (BP_tail_cc neg); [exact I | exact OK].
  Qed.

  Lemma BP_fill : forall (neg : bool) (off len : nat) jb m1 R T x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    (off + len <= 4 * n)%nat ->
    KBK (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T -> kc_ok RES n neg (splice R off (repeat 0%Z len)) T ->
    evt bgpsegs POST (ST 0xf8d28 m1 x1 x5 x6 x7 (Z_to_bv 64 (8 * Z.of_nat off)) x11 (Z_to_bv 64 (Z.of_nat len)) x13 x14 x15 x16 x17 a0 x20 (Z_to_bv 64 (2 * N))
                       x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hol I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ off len I Hol) as (HRz & LRz & ERz & WRz).
    zstep.
    zstep. replace ((Z.of_nat len) ≪ 3)%Z with (8 * Z.of_nat len)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 3 zstep.
    eapply call_memset0 with (L := slice R off len) (lo := lo) (SPz := (SP + -144)%Z) (D := (rp + 8 * Z.of_nat off)%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | ulit | reflexivity | rewrite ERz; ulit | exact HRz | rewrite ERz; exact WRz | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    rewrite ERz in HS.
    pose proof (KAFTER KB_after_R (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 m2 R T off (repeat 0%Z len) _ 0%Z eq_refl I (munch_add_stack0 _ _ _ _ _ MUc)
                  ltac:(rewrite ERz, repeat_length; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc (limbs_repeat _ _ limb_0) ltac:(rewrite repeat_length; exact Hol)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRz LRz ERz WRz MUc WMc HS MIc STc I.
    pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
    do 3 zstep.
    eapply (BP_tail_cc neg); [exact I2 | exact OK].
  Qed.

  Notation a_lo := (firstn n a).
  Notation a_hi := (slice a n tna).
  Notation b_lo := (firstn n b).
  Notation b_hi := (slice b n tnb).

  Notation JCELLS jb24 :=
    [CB 24 jb24; C8 (Z_to_bv 64 (bv_unsigned a2 + 8 * Z.of_nat n)); C8 (Z_to_bv 64 (bv_unsigned a1 + 8 * Z.of_nat n));
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma j_to_tail : forall jb24 m1 R T, KBK (JCELLS jb24) m1 R T ->
    KBK (TCELLS (firstn 8 jb24) (firstn 8 (skipn 8 jb24)) (firstn 8 (skipn 8 (skipn 8 jb24))) (Z_to_bv 64 (bp + 8 * N)) (Z_to_bv 64 (ap + 8 * N))) m1 R T.
  Proof.
    intros jb24 m1 R T I. eapply (KACC KB_recell); [exact I|].
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _).
    apply (rw_cells_split_CB bgpsegs m1 _ [] 24 jb24 _ [8; 8; 8]%nat) in FR; [|reflexivity]. exact FR.
  Qed.

  Lemma BP_comba : forall (neg : bool) jb24 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    n = 8%nat ->
    KBK (JCELLS jb24) m1 R T -> pcomba_ok RES n neg a b tna tnb R T ->
    evt bgpsegs POST (ST 0xf8bdc m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (2 * N))
                       x22 (Z_to_bv 64 (8 * N)) a4 a2 a1 (Z_to_bv 64 (if neg then 0 else 1)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros En I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat 16%nat I ltac:(clear - G En; lia)) as (_ & _ & _ & WTr).
    zstep. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 4 zstep.
    pose proof SEPT as D7.
    eapply call_comba8 with (CS8 := CS8) (a := slice T 0 n) (b := slice T n n) (lo := lo) (SPz := (SP + -144)%Z)
                            (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * N)%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact comba8_ok | exact LTa | exact LTb
      | rewrite ETa; exact En | rewrite ETb; exact En | ulit | ulit | ulit | exact HTa | exact HTb | exact WTr
      | clear - G En; lia | clear - G En; lia | clear - G; lia
      | clear - D7 G En; lia | clear - D7 G En; lia | clear - D7 G En; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (mul_comba8_spec (slice T 0 n) (slice T n n) LTa LTb ltac:(rewrite ETa; exact En) ltac:(rewrite ETb; exact En)) as (Lc & Ec & _).
    pose proof (KAFTER KB_after_T (JCELLS jb24) m1 m2 R T (2 * n)%nat _ _ CS8 eq_refl I MUc ltac:(rewrite Ec; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc ltac:(rewrite Ec; clear - G En; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTr MUc WMc HS MIc STc I D7.
    unfold pcomba_ok in OK. cbv zeta in OK.
    remember (splice T (2 * n) (mul_comba8 (slice T 0 n) (slice T n n))) as T1 eqn:ET1. clear ET1 Lc Ec.

    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (KACC KB_R _ _ _ _ 0%nat 16%nat I2 ltac:(clear - En; lia)) as (_ & _ & _ & WRa).
    pose proof (KACC KB_a _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HBl.
    assert (Lal : length a_lo = 8%nat) by (rewrite length_firstn; clear - G En; lia).
    assert (Lbl : length b_lo = 8%nat) by (rewrite length_firstn; clear - G En; lia).
    do 4 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof SEPR as D3. pose proof SEPA as D4. pose proof SEPB as D5.
    eapply call_comba8 with (CS8 := CS8) (a := a_lo) (b := b_lo) (lo := lo) (SPz := (SP + -144)%Z)
                            (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact comba8_ok | apply limbs_firstn; exact LA | apply limbs_firstn; exact LB
      | exact Lal | exact Lbl | ulit | ulit | ulit | exact HAl | exact HBl | exact WRa
      | clear - D1 G En; lia | clear - D2 G En; lia | clear - G; lia
      | clear - D3 G En; lia | clear - D4 G En; lia | clear - D5 G En; lia | ].
    intros m3 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HS STc.
    destruct (mul_comba8_spec a_lo b_lo (limbs_firstn _ _ LA) (limbs_firstn _ _ LB) Lal Lbl) as (Lc1 & Ec1 & _).
    pose proof (KAFTER KB_after_R (JCELLS jb24) m2 m3 R T1 0%nat (mul_comba8 a_lo b_lo) _ CS8 eq_refl I2 MUc ltac:(rewrite Ec1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc1 ltac:(rewrite Ec1; clear - En; lia)) as I3.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM WRa HAl HBl MUc WMc HS I2 MIc STc.
    remember (splice R 0 (mul_comba8 a_lo b_lo)) as R1 eqn:ER1. clear ER1 Lc1 Ec1.

    pose proof I3 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (tna + tnb)%nat I3 ltac:(clear - G; lia)) as (_ & _ & _ & WRn).
    pose proof (KACC KB_a _ _ _ _ n tna I3 ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n tnb I3 ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    do 6 zstep.
    eapply call_mul_normal with (a := a_hi) (b := b_hi) (lo := lo) (SPz := (SP + -144)%Z)
                                (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | apply slice_limbs; exact LA | apply slice_limbs; exact LB
      | rewrite Lah, Lbh; clear - G; lia
      | ulit | ulit | rewrite Lah; exact A4 | ulit | rewrite Lbh; exact A5
      | exact HAh | exact HBh
      | rewrite Lah, Lbh; replace (Z.of_nat tna + Z.of_nat tnb)%Z with (Z.of_nat (tna + tnb)) by (clear; lia); exact WRn
      | rewrite Lah, Lbh; clear - D1 G; lia | rewrite Lah, Lbh; clear - D2 G; lia | clear - G; lia
      | rewrite Lah, Lbh; clear - D3 G; lia | rewrite Lah; clear - D4 G; lia | rewrite Lbh; clear - D5 G; lia | ].
    intros m4 w0 w1 w2 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 MUc WMc MIc HS STc.
    destruct (mul_normal_spec a_hi b_hi (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB)) as (LMN & _ & EMN).
    assert (EMN' : length (mul_normal a_hi b_hi) = (tna + tnb)%nat).
    { rewrite EMN, Lah, Lbh. destruct (Nat.eqb_spec tna 0); destruct (Nat.eqb_spec tnb 0); cbn [orb]; clear - G e || clear - G e e0 || clear - G; lia. }
    clear EMN.
    pose proof (KAFTER KB_after_R (JCELLS jb24) m3 m4 R1 T1 (2 * n)%nat (mul_normal a_hi b_hi) _ 144%Z eq_refl I3 MUc
                  ltac:(rewrite Lah, Lbh, EMN'; clear; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc LMN ltac:(rewrite EMN'; clear - G; lia)) as I4.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM WRn HAh HBh MUc WMc HS I3 MIc STc D1 D2 D3 D4 D5.
    remember (splice R1 (2 * n) (mul_normal a_hi b_hi)) as R2 eqn:ER2. clear ER2 LMN EMN'.

    pose proof I4 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (KACC KB_R _ _ _ _ (2 * n + tna + tnb)%nat (2 * n - tna - tnb)%nat I4 ltac:(clear - G; lia)) as (HRz & LRz & ERz & WRz).
    zstep. rewrite A4, A5.
    do 2 zstep. rewrite (bn_swrap32_small (Z.of_nat tnb + Z.of_nat tna + 2 * N)) by (clear - G; lia).
    zstep. rewrite (bn_swrap32_small (16 - (Z.of_nat tnb + Z.of_nat tna))) by (clear - G; lia).
    do 6 zstep.
    setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (2 * n + tna + tnb))) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    setreg 12%Z (Z_to_bv 64 (8 * Z.of_nat (2 * n - tna - tnb))) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; clear - G En; lia).
    eapply call_memset0 with (L := slice R2 (2 * n + tna + tnb) (2 * n - tna - tnb)) (lo := lo) (SPz := (SP + -144)%Z)
                             (D := (rp + 8 * Z.of_nat (2 * n + tna + tnb))%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | ulit | reflexivity | rewrite ERz; ulit | exact HRz | rewrite ERz; exact WRz | ].
    intros m5 w0' w1' w2' y1' y2' y3' y4' y5' y6' y7' w3' w4' w5' w6' MUc WMc MIc HS STc.
    rewrite ERz in HS.
    pose proof (KAFTER KB_after_R (JCELLS jb24) m4 m5 R2 T1 (2 * n + tna + tnb)%nat (repeat 0%Z (2 * n - tna - tnb)) _ 0%Z eq_refl I4
                  (munch_add_stack0 _ _ _ _ _ MUc) ltac:(rewrite ERz, repeat_length; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc (limbs_repeat _ _ limb_0) ltac:(rewrite repeat_length; clear - G; lia)) as I5.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRz LRz ERz WRz MUc WMc HS MIc STc I4.
    zstep.
    replace (Z_to_bv 64 16) with (Z_to_bv 64 (2 * N)) by (f_equal; clear - En; lia).
    eapply (BP_tail neg); [apply j_to_tail; exact I5 | exact OK].
  Qed.

  Lemma pow2_le_n : forall j, (j <= k)%nat -> (Nat.pow 2 j * Nat.pow 2 (k - j) = n)%nat.
  Proof. intros j Hj. rewrite <- Nat.pow_add_r. rewrite Hn. f_equal. lia. Qed.

  Lemma BP_fpart : forall (kc : nat) (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    (kc + 2 <= k)%nat -> (3 <= kc)%nat -> (Nat.pow 2 kc <= tna)%nat -> (Nat.pow 2 kc <= tnb)%nat ->
    (tna < 2 * Nat.pow 2 kc)%nat -> (tnb < 2 * Nat.pow 2 kc)%nat ->
    KBK (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T -> pfpart_ok RES fuel' n neg a b tna tnb kc R T ->
    evt bgpsegs POST (ST 0xf8dc4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (2 * N))
                       x22 (Z_to_bv 64 (8 * N)) a4 (Z_to_bv 64 (Z.of_nat (Nat.pow 2 kc))) (Z_to_bv 64 (rp + 16 * N))
                       (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hkc Hkc3 Hia Hib Hta Htb I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    remember (Nat.pow 2 kc) as ic eqn:Eic.
    assert (Hic : (4 * ic <= n)%nat).
    { pose proof (pow2_le_n (kc + 2) Hkc) as HH. rewrite Nat.pow_add_r, <- Eic in HH. cbn [Nat.pow] in HH.
      pose proof (pow2_pos (k - (kc + 2))) as HP. clear - HH HP. nia. }
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (4 * ic)%nat I ltac:(clear - Hic; lia)) as (HRh & LRh & ERh & WRh).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n tna I ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n tnb I ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    zstep. rewrite A4, (bn_swrap32_small (Z.of_nat tna - Z.of_nat ic)) by (clear - G Hia; lia).
    zstep. rewrite A5, (bn_swrap32_small (Z.of_nat tnb - Z.of_nat ic)) by (clear - G Hib; lia).
    do 6 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9. pose proof Hk as HK. pose proof Hkf as HKF.
    pose proof Hd1 as HD1. pose proof Hd2 as HD2.
    assert (HPS : (part_stack CS8 kc <= SK)%Z) by (rewrite HSK; apply part_stack_S; clear - Hkc; lia).
    eapply call_part with (CS8 := CS8) (fuel := fuel') (k := kc) (a := a_hi) (b := b_hi) (tna := (tna - ic)%nat) (tnb := (tnb - ic)%nat)
                          (R := slice R (2 * n) (4 * ic)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -144)%Z)
                          (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact IHp
      | apply slice_limbs; exact LA | apply slice_limbs; exact LB | exact LRh | exact LTp
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
      | rewrite Lah; clear - D8 G HPS; lia | rewrite Lbh; clear - D9 G HPS; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HSR HST STc.
    pose proof (mul_part_recursive_spec fuel' kc a_hi b_hi (tna - ic)%nat (tnb - ic)%nat (slice R (2 * n) (4 * ic)) (skipn (4 * n) T)
                  (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB) LRh LTp Hkc3 ltac:(clear - Hkc HKF; lia)
                  ltac:(rewrite <- Eic; clear - Hta; lia) ltac:(rewrite <- Eic; clear - Htb; lia) ltac:(clear - HD1 Hia Hib; lia) ltac:(clear - HD2 Hia Hib; lia)
                  ltac:(rewrite Lah, <- Eic; clear - Hia; lia) ltac:(rewrite Lbh, <- Eic; clear - Hib; lia) ltac:(rewrite ERh, <- Eic; reflexivity)
                  ltac:(rewrite ETp, <- Eic; clear - G Hic; lia)) as MP.
    unfold mul_post in MP. unfold pfpart_ok in OK. cbv zeta in OK. rewrite <- Eic in OK.
    destruct (mul_part_recursive fuel' kc a_hi b_hi (tna - ic) (tnb - ic) (slice R (2 * n) (4 * ic)) (skipn (4 * n) T)) as [o p2]. cbn [fst snd] in *.
    destruct MP as (Lo & Eo & _ & Lp2 & Ep2). rewrite ERh in Eo. rewrite ETp in Ep2.
    pose proof (KAFTER KB_after_RT (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 m2 R T (2 * n)%nat o (4 * n)%nat p2 _ _ (part_stack CS8 kc) eq_refl I MUc
                  ltac:(rewrite ERh, Eo; reflexivity) ltac:(rewrite ETp, Ep2; reflexivity) ltac:(unfold part_stack, rec_stack in *; clear - HPS CS8_0; lia)
                  WMc MIc HSR HST STc Lo Lp2 ltac:(rewrite Eo; clear - Hic; lia) ltac:(rewrite Ep2; clear - G; lia)) as I2.
    eapply (BP_tail_c8 neg); [exact I2 | exact OK].
  Qed.

  Lemma BP_frec : forall (kc : nat) (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    (kc + 2 <= k)%nat -> (1 <= kc)%nat -> (tna <= Nat.pow 2 kc)%nat -> (tnb <= Nat.pow 2 kc)%nat ->
    (Nat.pow 2 kc <= tna + 1)%nat -> (Nat.pow 2 kc <= tnb + 1)%nat ->
    KBK (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T -> pfrec_ok RES n neg a b tna tnb kc R T ->
    evt bgpsegs POST (ST 0xf8da0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (2 * N))
                       x22 (Z_to_bv 64 (8 * N)) a4 (Z_to_bv 64 (Z.of_nat (Nat.pow 2 kc))) (Z_to_bv 64 (rp + 16 * N))
                       (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hkc Hkc1 Hia Hib Hta Htb I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    pose proof (scratch_rec_le kc) as HSC.
    remember (Nat.pow 2 kc) as ic eqn:Eic.
    assert (Hic : (4 * ic <= n)%nat).
    { pose proof (pow2_le_n (kc + 2) Hkc) as HH. rewrite Nat.pow_add_r, <- Eic in HH. cbn [Nat.pow] in HH.
      pose proof (pow2_pos (k - (kc + 2))) as HP. clear - HH HP. nia. }
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * ic)%nat I ltac:(clear - Hic; lia)) as (HRh & LRh & ERh & WRh).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n tna I ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n tnb I ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    zstep. rewrite A4, (bn_swrap32_small (Z.of_nat tna - Z.of_nat ic)) by (clear - G Hia Hic; lia).
    zstep. rewrite A5, (bn_swrap32_small (Z.of_nat tnb - Z.of_nat ic)) by (clear - G Hib Hic; lia).
    do 6 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9. pose proof Hk as HK.
    assert (HPS : (rec_stack CS8 kc <= SK)%Z) by (pose proof SK_rec; pose proof (rec_stack_mono CS8 kc k ltac:(clear - Hkc; lia)); lia).
    eapply call_rec with (CS8 := CS8) (k := kc) (a := a_hi) (b := b_hi) (da := (ic - tna)%nat) (db := (ic - tnb)%nat)
                         (R := slice R (2 * n) (2 * ic)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -144)%Z)
                         (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact (bn_mul_recursive_spec CS8 CS8_0 comba8_ok kc)
      | apply slice_limbs; exact LA | apply slice_limbs; exact LB | exact LRh | exact LTp
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
      | rewrite Lah; clear - D8 G HPS; lia | rewrite Lbh; clear - D9 G HPS; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec kc a_hi b_hi (ic - tna)%nat (ic - tnb)%nat (slice R (2 * n) (2 * ic)) (skipn (4 * n) T)
                  (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB) LRh LTp Hkc1 ltac:(clear - Hta; lia) ltac:(clear - Htb; lia)
                  ltac:(rewrite Lah, <- Eic; clear - Hia; lia) ltac:(rewrite Lbh, <- Eic; clear - Hib; lia) ltac:(rewrite ERh, <- Eic; reflexivity)
                  ltac:(rewrite ETp; clear - G Hic HSC; lia)) as MP.
    unfold mul_post in MP. unfold pfrec_ok in OK. cbv zeta in OK. rewrite <- Eic in OK.
    destruct (mul_recursive kc a_hi b_hi (ic - tna) (ic - tnb) (slice R (2 * n) (2 * ic)) (skipn (4 * n) T)) as [o p2]. cbn [fst snd] in *.
    destruct MP as (Lo & Eo & _ & Lp2 & Ep2). rewrite ERh in Eo. rewrite ETp in Ep2.
    pose proof (KAFTER KB_after_RT (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 m2 R T (2 * n)%nat o (4 * n)%nat p2 _ _ (rec_stack CS8 kc) eq_refl I MUc
                  ltac:(rewrite ERh, Eo; reflexivity) ltac:(rewrite ETp, Ep2; reflexivity) ltac:(unfold rec_stack in *; clear - HPS CS8_0; lia)
                  WMc MIc HSR HST STc Lo Lp2 ltac:(rewrite Eo; clear - Hic; lia) ltac:(rewrite Ep2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRh LRh ERh WRh HTp LTp ETp WTp HAh HBh MUc WMc HSR HST MIc STc I.
    zstep.
    eapply (BP_tail_c8 neg); [exact I2 | exact OK].
  Qed.

  Lemma pow2_gt8 : forall j, (8 < Nat.pow 2 j)%nat -> (4 <= j)%nat.
  Proof.
    intros j H. destruct (Nat.le_gt_cases 4 j) as [|Hlt]; [assumption|exfalso].
    assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3)%nat as [->|[->|[->| ->]]] by lia; cbn in H; lia.
  Qed.

  Lemma BP_find : forall (ki : nat) (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    (ki + 2 <= k)%nat -> (Nat.max tna tnb < 2 * Nat.pow 2 ki)%nat -> (16 <= Nat.max tna tnb)%nat ->
    KBK (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T -> pfind_ok RES fuel' n neg a b tna tnb ki R T ->
    evt bgpsegs POST (ST 0xf8d90 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (2 * N))
                       (Z_to_bv 64 (Z.of_nat (Nat.max tna tnb))) (Z_to_bv 64 (8 * N)) a4 (Z_to_bv 64 (Z.of_nat (2 * Nat.pow 2 ki)))
                       (Z_to_bv 64 (rp + 16 * N)) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) x28 x29 x30 x31).
  Proof.
    induction ki as [|ki' IHk]; intros until x31; intros Hki Hmx H16 I OK.
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
    {
      unfold pfind_ok in OK. rewrite kara_find_lt in OK by (rewrite <- Eic; clear - K1; lia).
      rewrite Eic. eapply (BP_fpart (S ki') neg); [exact Hki | assert (H4 : (4 <= S ki')%nat) by (apply pow2_gt8; rewrite <- Eic; clear - Hmx H16 Eic2; lia); clear - H4; lia
        | rewrite <- Eic; clear - K1 HD1 HD2; lia | rewrite <- Eic; clear - K1 HD1 HD2; lia
        | rewrite <- Eic; clear - Hmx; lia | rewrite <- Eic; clear - Hmx; lia | exact I | exact OK]. }
    zstep. if_cases K2; zify_cond K2.
    {
      unfold pfind_ok in OK. rewrite kara_find_eq in OK by (rewrite <- Eic; clear - K1 K2 A4; lia).
      rewrite Eic. eapply (BP_frec (S ki') neg); [exact Hki | clear; lia
        | rewrite <- Eic; clear - K1; lia | rewrite <- Eic; clear - K1; lia
        | rewrite <- Eic; clear - K2 A4; lia | rewrite <- Eic; clear - K2 A4 HD1 HD2; lia | exact I | exact OK]. }
    zstep. if_cases K3; zify_cond K3.
    {
      assert (Hlt : (tna < ic /\ tnb < ic)%nat) by (clear - K1 K2 K3 A4 A5; lia).
      unfold pfind_ok in OK. rewrite kara_find_S in OK by (rewrite <- Eic; clear - Hlt; lia).
      replace (Z_to_bv 64 (Z.of_nat ic)) with (Z_to_bv 64 (Z.of_nat (2 * Nat.pow 2 ki'))) by (rewrite Eic2; reflexivity).
      eapply (IHk neg); [clear - Hki; lia | rewrite <- Eic2; clear - Hlt; lia | exact H16 | exact I | exact OK]. }

    unfold pfind_ok in OK. rewrite kara_find_eq in OK by (rewrite <- Eic; clear - K1 K3 A5; lia).
    rewrite Eic. eapply (BP_frec (S ki') neg); [exact Hki | clear; lia
      | rewrite <- Eic; clear - K1; lia | rewrite <- Eic; clear - K1; lia
      | rewrite <- Eic; clear - K3 A5 HD1 HD2; lia | rewrite <- Eic; clear - K3 A5; lia | exact I | exact OK].
  Qed.

  Notation i_ := (Nat.pow 2 (k - 1)).
  Lemma n_2i : (4 <= k)%nat -> n = (2 * i_)%nat.
  Proof. intros H. rewrite Hn. replace k with (S (k - 1)) at 1 by lia. cbn [Nat.pow]. lia. Qed.

  Lemma BP_jneg : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    (4 <= k)%nat -> (Nat.max tna tnb < i_)%nat ->
    KBK (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T -> pjneg_ok RES fuel' k n neg a b tna tnb R T ->
    evt bgpsegs POST (ST 0xf8d48 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (2 * N))
                       (Z_to_bv 64 (Z.of_nat (Nat.max tna tnb))) (Z_to_bv 64 (16 * N)) a4 (Z_to_bv 64 (Z.of_nat i_))
                       (Z_to_bv 64 (rp + 16 * N)) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hk4 Hmx I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G. pose proof (n_2i Hk4) as En.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear; lia)) as (HRz & LRz & ERz & WRz).
    do 5 zstep.
    eapply call_memset0 with (L := slice R (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -144)%Z) (D := (rp + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | ulit | reflexivity | rewrite ERz; ulit | exact HRz | rewrite ERz; exact WRz | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    rewrite ERz in HS.
    pose proof (KAFTER KB_after_R (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 m2 R T (2 * n)%nat (repeat 0%Z (2 * n)) _ 0%Z eq_refl I
                  (munch_add_stack0 _ _ _ _ _ MUc) ltac:(rewrite ERz, repeat_length; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc (limbs_repeat _ _ limb_0) ltac:(rewrite repeat_length; clear; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRz LRz ERz WRz MUc WMc HS MIc STc I.
    unfold pjneg_ok in OK. cbv zeta in OK.
    remember (splice R (2 * n) (repeat 0%Z (2 * n))) as R2 eqn:ER2. clear ER2.
    assert (TOFIND : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
               ((tna <? 16)%nat && (tnb <? 16)%nat = false) ->
               evt bgpsegs POST (ST 0xf8d90 m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 a0 a5 (Z_to_bv 64 (2 * N))
                                  (Z_to_bv 64 (Z.of_nat (Nat.max tna tnb))) (Z_to_bv 64 (8 * N)) a4 (Z_to_bv 64 (Z.of_nat i_))
                                  (Z_to_bv 64 (rp + 16 * N)) (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) y28 y29 y30 y31)).
    { intros until y31. intros Esm. rewrite Esm in OK.
      assert (H16 : (16 <= Nat.max tna tnb)%nat).
      { apply andb_false_elim in Esm. destruct Esm as [E|E]; apply Nat.ltb_ge in E; clear - E; lia. }
      assert (Ei2 : i_ = (2 * Nat.pow 2 (k - 1 - 1))%nat).
      { replace (k - 1)%nat with (S (k - 1 - 1)) at 1 by (clear - Hk4; lia). cbn [Nat.pow]. clear. lia. }
      rewrite Ei2.
      eapply (BP_find (k - 1 - 1) neg); [clear - Hk4; lia | rewrite <- Ei2; exact Hmx | exact H16 | exact I2 | exact OK]. }
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    zstep.
    assert (L15 : (bv_unsigned (Z_to_bv 64 15) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (L4 : (bv_unsigned a4 < 9223372036854775808)%Z) by (rewrite A4; clear - G; lia).
    zstep. rewrite (lts_words_small (Z_to_bv 64 15) a4 L15 L4). rewrite A4.
    if_cases K1; zify_cond K1.
    { zstep. eapply TOFIND. destruct (Nat.ltb_spec tna 16) as [HH|_]; [exfalso; clear - HH K1; lia | reflexivity]. }
    do 2 zstep.
    assert (L16 : (bv_unsigned (Z_to_bv 64 16) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (L5 : (bv_unsigned a5 < 9223372036854775808)%Z) by (rewrite A5; clear - G; lia).
    zstep. rewrite (lts_words_small a5 (Z_to_bv 64 16) L5 L16). rewrite A5.
    if_cases K2; zify_cond K2.
    { eapply TOFIND. destruct (Nat.ltb_spec tnb 16) as [HH|_]; [exfalso; clear - HH K2; lia | apply andb_false_r]. }

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
    eapply call_mul_normal with (a := a_hi) (b := b_hi) (lo := lo) (SPz := (SP + -144)%Z)
                                (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | apply slice_limbs; exact LA | apply slice_limbs; exact LB
      | rewrite Lah, Lbh; clear - G; lia
      | ulit | ulit | rewrite Lah; exact A4 | ulit | rewrite Lbh; exact A5
      | exact HAh | exact HBh
      | rewrite Lah, Lbh; replace (Z.of_nat tna + Z.of_nat tnb)%Z with (Z.of_nat (tna + tnb)) by (clear; lia); exact WRn
      | rewrite Lah, Lbh; clear - D1 G; lia | rewrite Lah, Lbh; clear - D2 G; lia | clear - G; lia
      | rewrite Lah, Lbh; clear - D3 G; lia | rewrite Lah; clear - D4 G; lia | rewrite Lbh; clear - D5 G; lia | ].
    intros m4 w0 w1 w2 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 MUc WMc MIc' HS STc.
    destruct (mul_normal_spec a_hi b_hi (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB)) as (LMN & _ & EMN).
    assert (EMN' : length (mul_normal a_hi b_hi) = (tna + tnb)%nat).
    { rewrite EMN, Lah, Lbh. destruct (Nat.eqb_spec tna 0); destruct (Nat.eqb_spec tnb 0); cbn [orb]; clear - G e || clear - G e e0 || clear - G; lia. }
    clear EMN.
    pose proof (KAFTER KB_after_R (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m2 m4 R2 T (2 * n)%nat (mul_normal a_hi b_hi) _ 144%Z eq_refl I2 MUc
                  ltac:(rewrite Lah, Lbh, EMN'; clear; lia)
                  ltac:(clear - G; lia) WMc MIc' HS STc LMN ltac:(rewrite EMN'; clear - G; lia)) as I4.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM WRn HAh HBh MUc WMc HS I2 MIc' STc D1 D2 D3 D4 D5.
    zstep.
    eapply (BP_tail_c8 neg); [exact I4 | exact OK].
  Qed.

  Lemma BP_jpos : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31,
    (4 <= k)%nat -> (i_ < Nat.max tna tnb)%nat ->
    KBK (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T -> pjpos_ok RES fuel' k n neg a b tna tnb R T ->
    evt bgpsegs POST (ST 0xf8cf8 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (2 * N))
                       x22 x23 a4 (Z_to_bv 64 (Z.of_nat i_)) (Z_to_bv 64 (rp + 16 * N))
                       (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hk4 Hmx I OK.
    pose proof (n_2i Hk4) as En2i. pose proof Hd1 as HD1'. pose proof Hd2 as HD2'. pose proof Htna as HTA. pose proof Htnb as HTB.
    assert (Hkc : (k - 1 + 1 <= k)%nat) by (clear - Hk4; lia). assert (Hkc3 : (3 <= k - 1)%nat) by (clear - Hk4; lia).
    assert (Hia : (Nat.pow 2 (k - 1) <= tna)%nat) by (clear - Hmx HD1' HD2'; lia).
    assert (Hib : (Nat.pow 2 (k - 1) <= tnb)%nat) by (clear - Hmx HD1' HD2'; lia).
    assert (Hta : (tna < 2 * Nat.pow 2 (k - 1))%nat) by (clear - En2i HTA; lia).
    assert (Htb : (tnb < 2 * Nat.pow 2 (k - 1))%nat) by (clear - En2i HTB; lia).
    clear HD1' HD2' HTA HTB. set (kc := (k - 1)%nat) in *.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    remember (Nat.pow 2 kc) as ic eqn:Eic.
    assert (Hic : (2 * ic = n)%nat) by (clear - En2i; lia).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (4 * ic)%nat I ltac:(clear - Hic; lia)) as (HRh & LRh & ERh & WRh).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n tna I ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n tnb I ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    zstep. rewrite A4, (bn_swrap32_small (Z.of_nat tna - Z.of_nat ic)) by (clear - G Hia; lia).
    zstep. rewrite A5, (bn_swrap32_small (Z.of_nat tnb - Z.of_nat ic)) by (clear - G Hib; lia).
    do 6 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9. pose proof Hk as HK. pose proof Hkf as HKF.
    pose proof Hd1 as HD1. pose proof Hd2 as HD2.
    assert (HPS : (part_stack CS8 kc <= SK)%Z) by (rewrite HSK; apply part_stack_S; subst kc; clear - Hk4; lia).
    eapply call_part with (CS8 := CS8) (fuel := fuel') (k := kc) (a := a_hi) (b := b_hi) (tna := (tna - ic)%nat) (tnb := (tnb - ic)%nat)
                          (R := slice R (2 * n) (4 * ic)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -144)%Z)
                          (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact IHp
      | apply slice_limbs; exact LA | apply slice_limbs; exact LB | exact LRh | exact LTp
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
      | rewrite Lah; clear - D8 G HPS; lia | rewrite Lbh; clear - D9 G HPS; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HSR HST STc.
    pose proof (mul_part_recursive_spec fuel' kc a_hi b_hi (tna - ic)%nat (tnb - ic)%nat (slice R (2 * n) (4 * ic)) (skipn (4 * n) T)
                  (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB) LRh LTp Hkc3 ltac:(subst kc; clear - Hk4 HKF; lia)
                  ltac:(rewrite <- Eic; clear - Hta; lia) ltac:(rewrite <- Eic; clear - Htb; lia) ltac:(clear - HD1 Hia Hib; lia) ltac:(clear - HD2 Hia Hib; lia)
                  ltac:(rewrite Lah, <- Eic; clear - Hia; lia) ltac:(rewrite Lbh, <- Eic; clear - Hib; lia) ltac:(rewrite ERh, <- Eic; reflexivity)
                  ltac:(rewrite ETp, <- Eic; clear - G Hic; lia)) as MP.
    unfold mul_post in MP. unfold pjpos_ok in OK. cbv zeta in OK. fold kc in OK. rewrite <- Eic in OK.
    destruct (mul_part_recursive fuel' kc a_hi b_hi (tna - ic) (tnb - ic) (slice R (2 * n) (4 * ic)) (skipn (4 * n) T)) as [o p2]. cbn [fst snd] in *.
    destruct MP as (Lo & Eo & _ & Lp2 & Ep2). rewrite ERh in Eo. rewrite ETp in Ep2.
    pose proof (KAFTER KB_after_RT (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 m2 R T (2 * n)%nat o (4 * n)%nat p2 _ _ (part_stack CS8 kc) eq_refl I MUc
                  ltac:(rewrite ERh, Eo; reflexivity) ltac:(rewrite ETp, Ep2; reflexivity) ltac:(unfold part_stack, rec_stack in *; clear - HPS CS8_0; lia)
                  WMc MIc HSR HST STc Lo Lp2 ltac:(rewrite Eo; clear - Hic; lia) ltac:(rewrite Ep2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRh LRh ERh WRh HTp LTp ETp WTp HAh HBh MUc WMc HSR HST MIc STc I.
    zstep. rewrite A4, A5.
    zstep. rewrite (bn_swrap32_small (Z.of_nat tnb + Z.of_nat tna + 2 * N)) by (clear - G; lia).
    zstep. rewrite (bn_swrap32_small (2 * N - (Z.of_nat tnb + Z.of_nat tna))) by (clear - G; lia).
    zstep.
    setreg 10%Z (Z_to_bv 64 (8 * Z.of_nat (2 * n + tna + tnb))) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    setreg 12%Z (Z_to_bv 64 (Z.of_nat (2 * n - tna - tnb))) ltac:(f_equal; clear - G; lia).
    eapply (BP_fill neg (2 * n + tna + tnb) (2 * n - tna - tnb)); [clear - G; lia | exact I2 | exact OK].
  Qed.

  Lemma BP_j0 : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x28 x29 x30 x31,
    (4 <= k)%nat -> (Nat.max tna tnb = i_)%nat ->
    KBK (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T -> pj0_ok RES k n neg a b tna tnb R T ->
    evt bgpsegs POST (ST 0xf8cb4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (2 * N))
                       x22 (Z_to_bv 64 (16 * N)) a4 (Z_to_bv 64 (Z.of_nat i_)) x26
                       (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hk4 Hmx I OK.
    pose proof (n_2i Hk4) as En2i. pose proof Hd1 as HD1'. pose proof Hd2 as HD2'.
    assert (Hkc1 : (1 <= k - 1)%nat) by (clear - Hk4; lia).
    assert (Hia : (tna <= Nat.pow 2 (k - 1))%nat) by (clear - Hmx; lia).
    assert (Hib : (tnb <= Nat.pow 2 (k - 1))%nat) by (clear - Hmx; lia).
    assert (Hta : (Nat.pow 2 (k - 1) <= tna + 1)%nat) by (clear - Hmx HD1' HD2'; lia).
    assert (Htb : (Nat.pow 2 (k - 1) <= tnb + 1)%nat) by (clear - Hmx HD1' HD2'; lia).
    clear HD1' HD2'. set (kc := (k - 1)%nat) in *.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    pose proof (scratch_rec_le kc) as HSC.
    remember (Nat.pow 2 kc) as ic eqn:Eic.
    assert (Hic : (2 * ic = n)%nat) by (clear - En2i; lia).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * ic)%nat I ltac:(clear - Hic; lia)) as (HRh & LRh & ERh & WRh).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ n tna I ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n tnb I ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = tna) by (rewrite slice_length; clear - G; lia).
    assert (Lbh : length b_hi = tnb) by (rewrite slice_length; clear - G; lia).
    zstep.
    zstep. rewrite A4, (bn_swrap32_small (Z.of_nat tna - Z.of_nat ic)) by (clear - G Hia Hic; lia).
    zstep. rewrite A5, (bn_swrap32_small (Z.of_nat tnb - Z.of_nat ic)) by (clear - G Hib Hic; lia).
    do 5 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9. pose proof Hk as HK.
    assert (HPS : (rec_stack CS8 kc <= SK)%Z) by (pose proof SK_rec; pose proof (rec_stack_mono CS8 kc k ltac:(subst kc; clear; lia)); lia).
    eapply call_rec with (CS8 := CS8) (k := kc) (a := a_hi) (b := b_hi) (da := (ic - tna)%nat) (db := (ic - tnb)%nat)
                         (R := slice R (2 * n) (2 * ic)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -144)%Z)
                         (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact (bn_mul_recursive_spec CS8 CS8_0 comba8_ok kc)
      | apply slice_limbs; exact LA | apply slice_limbs; exact LB | exact LRh | exact LTp
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
      | rewrite Lah; clear - D8 G HPS; lia | rewrite Lbh; clear - D9 G HPS; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec kc a_hi b_hi (ic - tna)%nat (ic - tnb)%nat (slice R (2 * n) (2 * ic)) (skipn (4 * n) T)
                  (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB) LRh LTp Hkc1 ltac:(clear - Hta; lia) ltac:(clear - Htb; lia)
                  ltac:(rewrite Lah, <- Eic; clear - Hia; lia) ltac:(rewrite Lbh, <- Eic; clear - Hib; lia) ltac:(rewrite ERh, <- Eic; reflexivity)
                  ltac:(rewrite ETp; clear - G Hic HSC; lia)) as MP.
    unfold mul_post in MP. unfold pj0_ok in OK. cbv zeta in OK. fold kc in OK. rewrite <- Eic in OK.
    destruct (mul_recursive kc a_hi b_hi (ic - tna) (ic - tnb) (slice R (2 * n) (2 * ic)) (skipn (4 * n) T)) as [o p2]. cbn [fst snd] in *.
    destruct MP as (Lo & Eo & _ & Lp2 & Ep2). rewrite ERh in Eo. rewrite ETp in Ep2.
    pose proof (KAFTER KB_after_RT (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 m2 R T (2 * n)%nat o (4 * n)%nat p2 _ _ (rec_stack CS8 kc) eq_refl I MUc
                  ltac:(rewrite ERh, Eo; reflexivity) ltac:(rewrite ETp, Ep2; reflexivity) ltac:(unfold rec_stack in *; clear - HPS CS8_0; lia)
                  WMc MIc HSR HST STc Lo Lp2 ltac:(rewrite Eo; clear - Hic; lia) ltac:(rewrite Ep2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRh LRh ERh WRh HTp LTp ETp WTp HAh HBh MUc WMc HSR HST MIc STc I.
    do 3 zstep. rewrite A3. replace N with (2 * Z.of_nat ic)%Z by (clear - Hic; lia). rewrite land_even_mask64 by (clear - G Hic; lia).
    zstep. rewrite (bn_swrap32_small (2 * (2 * Z.of_nat ic) + 2 * Z.of_nat ic)) by (clear - G Hic; lia).
    zstep. rewrite (bn_swrap32_small (2 * (2 * Z.of_nat ic) - 2 * Z.of_nat ic)) by (clear - G Hic; lia).
    do 2 zstep.
    setreg 10%Z (Z_to_bv 64 (8 * Z.of_nat (2 * n + 2 * ic))) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; clear - Hic; lia).
    setreg 12%Z (Z_to_bv 64 (Z.of_nat (2 * n - 2 * ic))) ltac:(f_equal; clear - Hic; lia).
    replace (Z_to_bv 64 (2 * (2 * Z.of_nat ic))) with (Z_to_bv 64 (2 * N)) by (f_equal; clear - Hic; lia).
    eapply (BP_fill neg (2 * n + 2 * ic) (2 * n - 2 * ic)); [clear - Hic; lia | exact I2 | exact OK].
  Qed.

  Lemma BP_split : forall (neg : bool) jb m1 R T (w22 : word) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31,
    (4 <= k)%nat -> w22 = Z_to_bv 64 (Z.of_nat (Nat.max tna tnb)) ->
    KBK (GCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T -> pgen3_ok RES fuel' k n neg a b tna tnb R T ->
    evt bgpsegs POST (ST 0xf8cb0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (2 * N))
                       w22 (Z_to_bv 64 (16 * N)) a4 (Z_to_bv 64 (Z.of_nat i_)) x26
                       (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hk4 E22 I OK. subst w22.
    pose proof geom as G. pose proof (n_2i Hk4) as En2i.
    unfold pgen3_ok in OK. cbv zeta in OK.
    zstep. if_cases K1; zify_cond K1.
    -
      destruct (Nat.eqb_spec (Nat.max tna tnb) i_) as [E|_]; [exfalso; apply K1; rewrite E; reflexivity|].
      zstep.
      zstep. rewrite lts_small by (clear - G En2i; lia).
      if_cases K2; zify_cond K2.
      + destruct (Nat.ltb_spec i_ (Nat.max tna tnb)) as [HH|_]; [exfalso; clear - HH K2; lia|].
        eapply (BP_jneg neg); [exact Hk4 | clear - K1 K2; lia | exact I | exact OK].
      + destruct (Nat.ltb_spec i_ (Nat.max tna tnb)) as [HH|HH]; [|exfalso; clear - HH K2; lia].
        eapply (BP_jpos neg); [exact Hk4 | exact HH | exact I | exact OK].
    - destruct (Nat.eqb_spec (Nat.max tna tnb) i_) as [E|NE]; [|exfalso; apply NE; clear - K1; lia].
      eapply (BP_j0 neg); [exact Hk4 | exact E | exact I | exact OK].
  Qed.

  Lemma BP_gen : forall (neg : bool) jb24 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    (4 <= k)%nat ->
    KBK (JCELLS jb24) m1 R T ->
    (let '(tm, p0) := mul_recursive k (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) in
     pgen2_ok RES fuel' k n neg a b tna tnb R (splice T (2 * n) (tm ++ p0))) ->
    evt bgpsegs POST (ST 0xf8c44 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (2 * N))
                       x22 (Z_to_bv 64 (8 * N)) a4 a2 a1 (Z_to_bv 64 (if neg then 0 else 1)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hk4 I OK.
    pose proof geom as G. pose proof (n_2i Hk4) as En2i.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    pose proof (munch_refl [(SP + -144, SP + -144 + 144)]%Z m1) as MUF. pose proof (wmono_refl bgpsegs m1) as WMF.
    zstep.
    zstep. rewrite A3. replace (N ≪ 2)%Z with (4 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    rewrite (bn_swrap32_small (4 * N)) by (clear - G; lia).
    do 2 zstep. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 3 zstep.
    setreg 27%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) ltac:(f_equal; rewrite !Z.shiftl_mul_pow2 by lia; clear; lia).
    zstep.
    pose proof (KFRAME _ _ m1 _ R T I MUF WMF MI STK FR) as I1.
    clear I MUF WMF FR STK MI. clear m1.
    pose proof I1 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (KACC KB_T _ _ _ _ 0%nat n I1 ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ n n I1 ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I1 ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I1 ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    do 7 zstep.
    pose proof SEPT as D7. pose proof Hk as HK. pose proof (scratch_rec_le k) as HSC. rewrite pow_n in HSC.
    eapply call_rec with (CS8 := CS8) (k := k) (a := slice T 0 n) (b := slice T n n) (da := 0%nat) (db := 0%nat)
                         (R := slice T (2 * n) (2 * n)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -144)%Z)
                         (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact (bn_mul_recursive_spec CS8 CS8_0 comba8_ok k)
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
      | rewrite ETa; clear - D7 G; lia | rewrite ETb; clear - D7 G; lia | ].
    intros m3 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) LTa LTb LTr LTp
                  ltac:(clear - HK; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(rewrite ETa, pow_n; clear; lia) ltac:(rewrite ETb, pow_n; clear; lia) ltac:(rewrite ETr, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G HSC; lia)) as MP.
    unfold mul_post in MP.
    destruct (mul_recursive k (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T)) as [tm p0]. cbn [fst snd] in *.
    destruct MP as (Ltm & Etm & _ & Lp0 & Ep0). rewrite ETr in Etm. rewrite ETp in Ep0.
    lazymatch type of I1 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_TT cells mm m3 R T (2 * n)%nat (4 * n)%nat tm p0 _ _ (rec_stack CS8 k) eq_refl I1 MUc
                    ltac:(rewrite ETr, Etm; reflexivity) ltac:(rewrite ETp, Ep0; reflexivity) ltac:(rewrite Etm; clear; lia)
                    ltac:(unfold rec_stack in *; clear - G CS8_0; lia)
                    WMc MIc HSR HST STc Ltm Lp0 ltac:(rewrite Ep0; clear - G; lia)) as I2 end.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb HTr LTr ETr WTr HTp LTp ETp WTp MUc WMc HSR HST MIc STc I1 D7.
    remember (splice T (2 * n) (tm ++ p0)) as T1 eqn:ET1. clear ET1 Ltm Etm Lp0 Ep0.

    unfold pgen2_ok in OK.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I2 ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_Tskip _ _ _ _ (4 * n)%nat I2 ltac:(clear - G; lia)) as (HTp & LTp & ETp & WTp).
    pose proof (KACC KB_a _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HBl.
    assert (Lal : length a_lo = n) by (rewrite length_firstn; clear - G; lia).
    assert (Lbl : length b_lo = n) by (rewrite length_firstn; clear - G; lia).
    do 8 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9.
    eapply call_rec with (CS8 := CS8) (k := k) (a := a_lo) (b := b_lo) (da := 0%nat) (db := 0%nat) (R := slice R 0 (2 * n)) (T := skipn (4 * n) T1)
                         (lo := lo) (SPz := (SP + -144)%Z)
                         (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP144 | ret_even | exact ST | exact MI | exact (bn_mul_recursive_spec CS8 CS8_0 comba8_ok k)
      | apply limbs_firstn; exact LA | apply limbs_firstn; exact LB | exact LRa | exact LTp
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
      | rewrite Lal; clear - D8 G; lia | rewrite Lbl; clear - D9 G; lia | ].
    intros m4 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k a_lo b_lo 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T1) (limbs_firstn _ _ LA) (limbs_firstn _ _ LB) LRa LTp
                  ltac:(clear - HK; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(rewrite Lal, pow_n; clear; lia) ltac:(rewrite Lbl, pow_n; clear; lia) ltac:(rewrite ERa, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G HSC; lia)) as MP.
    unfold mul_post in MP.
    destruct (mul_recursive k a_lo b_lo 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T1)) as [rl p1]. cbn [fst snd] in *.
    destruct MP as (Lrl & Erl & _ & Lp1 & Ep1). rewrite ERa in Erl. rewrite ETp in Ep1.
    lazymatch type of I2 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_RT cells mm m4 R T1 0%nat rl (4 * n)%nat p1 _ _ (rec_stack CS8 k) eq_refl I2 MUc
                    ltac:(rewrite ERa, Erl; reflexivity) ltac:(rewrite ETp, Ep1; reflexivity) ltac:(unfold rec_stack in *; clear - G CS8_0; lia)
                    WMc MIc HSR HST STc Lrl Lp1 ltac:(rewrite Erl; clear; lia) ltac:(rewrite Ep1; clear - G; lia)) as I3 end.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa WRa HTp LTp ETp WTp HAl HBl MUc WMc HSR HST MIc STc I2.
    clear D1 D2 D3 D4 D5 D6 D7 D8 D9.
    remember (splice R 0 rl) as R1 eqn:ER1. remember (splice T1 (4 * n) p1) as T2 eqn:ET2. clear ER1 ET2 Lrl Erl Lp1 Ep1.
    zstep. rewrite A3.
    replace (bv_swrap 32 (bv_wrap 32 N ≫ 1)) with (Z.of_nat i_)
      by (replace N with (2 * Z.of_nat i_)%Z by (clear - En2i; lia); symmetry; apply srliw_half; clear - G En2i; lia).
    zstep.
    assert (L4 : (bv_unsigned a4 < 9223372036854775808)%Z) by (rewrite A4; clear - G; lia).
    assert (L5 : (bv_unsigned a5 < 9223372036854775808)%Z) by (rewrite A5; clear - G; lia).
    zstep. rewrite (lts_words_small a5 a4 L5 L4). rewrite A4, A5.
    if_cases K1; zify_cond K1.
    - eapply (BP_split neg); [exact Hk4 | | exact I3 | exact OK].
      rewrite <- (Z_to_bv_bv_unsigned a4), A4. f_equal. clear - K1. lia.
    - zstep.
      eapply (BP_split neg); [exact Hk4 | | exact I3 | exact OK].
      rewrite <- (Z_to_bv_bv_unsigned a5), A5. f_equal. clear - K1. lia.
  Qed.

  Lemma BP_join : forall (neg : bool) jb24 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31,
    KBK (JCELLS jb24) m1 R T -> pjoin_ok RES fuel' k n neg a b tna tnb R T ->
    evt bgpsegs POST (ST 0xf8bd0 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 x21
                       x22 (Z_to_bv 64 (8 * N)) a4 a2 a1 (Z_to_bv 64 (if neg then 0 else 1)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof geom as G.
    zstep.
    zstep. rewrite A3. replace (N ≪ 1)%Z with (2 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    rewrite (bn_swrap32_small (2 * N)) by (clear - G; lia).
    zstep. if_cases K1; zify_cond K1.
    - assert (Hk4 : (4 <= k)%nat).
      { pose proof Hk as HK. pose proof Hn as HN. destruct (Nat.eq_dec k 3) as [E3|NE]; [|clear - HK NE; lia].
        exfalso. rewrite E3 in HN. cbn in HN. clear - HN K1 A3. lia. }
      unfold pjoin_ok in OK. destruct (Nat.eqb_spec n 8) as [E8|_]; [exfalso; clear - E8 K1 A3; lia|].
      eapply (BP_gen neg); [exact Hk4 | exact I | exact OK].
    - assert (En : n = 8%nat) by (clear - K1 A3; lia).
      unfold pjoin_ok in OK. rewrite (proj2 (Nat.eqb_eq n 8) En) in OK.
      eapply (BP_comba neg); [exact En | exact I | exact OK].
  Qed.

  Notation t0_of sw := (fst (if sw then sub_part_words a_hi a_lo tna else sub_part_words a_lo a_hi tna)).
  Notation t1_of sw := (fst (if sw then sub_part_words b_hi b_lo tnb else sub_part_words b_lo b_hi tnb)).

  Ltac sp1_call I G BND sw :=
    let HAl := fresh "HAl" in let HAh := fresh "HAh" in let WTn := fresh "WTn" in
    let D3 := fresh "D3" in let D7 := fresh "D7" in let D8 := fresh "D8" in
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl;
    pose proof (KACC KB_a _ _ _ _ n tna I ltac:(clear - G; lia)) as HAh;
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (_ & _ & _ & WTn);
    pose proof DTA as D3; pose proof SEPT as D7; pose proof SEPA as D8;
    lazymatch goal with ST : stk bgpsegs ?m1 lo _, MI : mem_inv bgpsegs ?m1 |- _ =>
    lazymatch sw with
    | false =>
      eapply call_sub_part_words with (a := a_lo) (b := a_hi) (cl := tna) (da := (n - tna)%nat) (db := 0%nat) (lo := lo) (SPz := (SP + -144)%Z)
                                      (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
        [ exact ESP144 | ret_even | exact ST | exact MI | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
        | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
        | clear - G; lia | ulit | ulit | ulit | exact A4 | f_equal; clear - G; lia
        | exact HAl | exact HAh | replace (tna + (n - tna) + 0)%nat with n by (clear - G; lia); exact WTn
        | rewrite length_firstn; clear - D3 G; lia | rewrite slice_length by (clear - G; lia); clear - D3 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite length_firstn; clear - D8 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia | ]
    | true =>
      eapply call_sub_part_words with (a := a_hi) (b := a_lo) (cl := tna) (da := 0%nat) (db := (n - tna)%nat) (lo := lo) (SPz := (SP + -144)%Z)
                                      (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * N)%Z) (BP := (ap + 8 * Z.of_nat 0)%Z);
        [ exact ESP144 | ret_even | exact ST | exact MI | apply slice_limbs; exact LA | apply limbs_firstn; exact LA
        | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
        | clear - G; lia | ulit | ulit | ulit | exact A4 | f_equal; clear - G; lia
        | exact HAh | exact HAl | replace (tna + 0 + (n - tna))%nat with n by (clear - G; lia); exact WTn
        | rewrite slice_length by (clear - G; lia); clear - D3 G; lia | rewrite length_firstn; clear - D3 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia | rewrite length_firstn; clear - D8 G; lia | ]
    end end.

  Ltac sp2_call I G BND sw :=
    let HBl := fresh "HBl" in let HBh := fresh "HBh" in let WTn := fresh "WTn" in
    let D4 := fresh "D4" in let D7 := fresh "D7" in let D9 := fresh "D9" in
    pose proof (KACC KB_b _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HBl;
    pose proof (KACC KB_b _ _ _ _ n tnb I ltac:(clear - G; lia)) as HBh;
    destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (_ & _ & _ & WTn);
    pose proof DTB as D4; pose proof SEPT as D7; pose proof SEPB as D9;
    lazymatch goal with ST : stk bgpsegs ?m1 lo _, MI : mem_inv bgpsegs ?m1 |- _ =>
    lazymatch sw with
    | false =>
      eapply call_sub_part_words with (a := b_lo) (b := b_hi) (cl := tnb) (da := (n - tnb)%nat) (db := 0%nat) (lo := lo) (SPz := (SP + -144)%Z)
                                      (RP := (tq + 8 * N)%Z) (AP := (bp + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * N)%Z);
        [ exact ESP144 | ret_even | exact ST | exact MI | apply limbs_firstn; exact LB | apply slice_limbs; exact LB
        | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
        | clear - G; lia | ulit | ulit | ulit | exact A5 | f_equal; clear - G; lia
        | exact HBl | exact HBh | replace (tnb + (n - tnb) + 0)%nat with n by (clear - G; lia); exact WTn
        | rewrite length_firstn; clear - D4 G; lia | rewrite slice_length by (clear - G; lia); clear - D4 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite length_firstn; clear - D9 G; lia | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | ]
    | true =>
      eapply call_sub_part_words with (a := b_hi) (b := b_lo) (cl := tnb) (da := 0%nat) (db := (n - tnb)%nat) (lo := lo) (SPz := (SP + -144)%Z)
                                      (RP := (tq + 8 * N)%Z) (AP := (bp + 8 * N)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
        [ exact ESP144 | ret_even | exact ST | exact MI | apply slice_limbs; exact LB | apply limbs_firstn; exact LB
        | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
        | clear - G; lia | ulit | ulit | ulit | exact A5 | f_equal; clear - G; lia
        | exact HBh | exact HBl | replace (tnb + 0 + (n - tnb))%nat with n by (clear - G; lia); exact WTn
        | rewrite slice_length by (clear - G; lia); clear - D4 G; lia | rewrite length_firstn; clear - D4 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | rewrite length_firstn; clear - D9 G; lia | ]
    end end.

  Lemma t1_facts : forall sw : bool, limbs (t1_of sw) /\ length (t1_of sw) = n.
  Proof.
    intros sw. pose proof geom as G. destruct sw.
    - destruct (sub_part_words_fst b_hi b_lo tnb (slice_limbs _ _ _ LB) (limbs_firstn _ _ LB)
                  ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (L1 & E1 & _).
      rewrite slice_length, length_firstn in E1 by (clear - G; lia). split; [exact L1 | rewrite E1; clear - G; lia].
    - destruct (sub_part_words_fst b_lo b_hi tnb (limbs_firstn _ _ LB) (slice_limbs _ _ _ LB)
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

  Lemma BP_sp2_neg : forall (sw : bool) jb24 m1 R T x1 x5 x6 x7 x15 x16 x17 x22 x27 x28 x29 x30 x31,
    KBK (JCELLS jb24) m1 R T ->
    pjoin_ok RES fuel' k n true a b tna tnb R (splice T n (t1_of sw)) ->
    evt bgpsegs POST (ST 0xf8b58 m1 x1 x5 x6 x7 (Z_to_bv 64 (tq + 8 * N))
                       (if sw then Z_to_bv 64 (bp + 8 * N) else a2) (if sw then a2 else Z_to_bv 64 (bp + 8 * N))
                       a5 (if sw then Z_to_bv 64 (Z.of_nat tnb - N) else Z_to_bv 64 (N - Z.of_nat tnb))
                       x15 x16 x17 a0 a5 (Z_to_bv 64 (Z.of_nat tnb - N)) x22 (Z_to_bv 64 (8 * N)) a4 a2 a1 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t1_facts sw) as (Lt1 & Et1).
    destruct sw.
    - zstep. sp2_call I G BND true.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (KAFTER KB_after_T (JCELLS jb24) m1 m2 R T n _ _ 80%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      do 2 zstep. eapply (BP_join true); [exact I2 | exact OK].
    - zstep. sp2_call I G BND false.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (KAFTER KB_after_T (JCELLS jb24) m1 m2 R T n _ _ 80%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      do 2 zstep. eapply (BP_join true); [exact I2 | exact OK].
  Qed.

  Lemma BP_sp2_pos : forall (sw : bool) jb24 m1 R T x1 x5 x6 x7 x15 x16 x17 x22 x27 x28 x29 x30 x31,
    KBK (JCELLS jb24) m1 R T ->
    pjoin_ok RES fuel' k n false a b tna tnb R (splice T n (t1_of sw)) ->
    evt bgpsegs POST (ST 0xf8bc8 m1 x1 x5 x6 x7 (Z_to_bv 64 (tq + 8 * N))
                       (if sw then Z_to_bv 64 (bp + 8 * N) else a2) (if sw then a2 else Z_to_bv 64 (bp + 8 * N))
                       a5 (if sw then Z_to_bv 64 (Z.of_nat tnb - N) else Z_to_bv 64 (N - Z.of_nat tnb))
                       x15 x16 x17 a0 a5 (Z_to_bv 64 (Z.of_nat tnb - N)) x22 (Z_to_bv 64 (8 * N)) a4 a2 a1 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t1_facts sw) as (Lt1 & Et1).
    destruct sw.
    - zstep. sp2_call I G BND true.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (KAFTER KB_after_T (JCELLS jb24) m1 m2 R T n _ _ 80%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      zstep. eapply (BP_join false); [exact I2 | exact OK].
    - zstep. sp2_call I G BND false.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      pose proof (KAFTER KB_after_T (JCELLS jb24) m1 m2 R T n _ _ 80%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      zstep. eapply (BP_join false); [exact I2 | exact OK].
  Qed.

  Lemma BP_case_A : forall jb24 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    KBK (JCELLS jb24) m1 R T ->
    pjoin_ok RES fuel' k n true a b tna tnb R (splice (splice T 0 (t0_of false)) n (t1_of false)) ->
    evt bgpsegs POST (ST 0xf8aec m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (Z.of_nat tnb - N)) x22 (Z_to_bv 64 (8 * N))
                       a4 a2 a1 (Z_to_bv 64 (N - Z.of_nat tna)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t0_facts false) as (Lt0 & Et0).
    do 6 zstep. sp1_call I G BND false.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (KAFTER KB_after_T (JCELLS jb24) m1 m2 R T 0%nat _ _ 80%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    zstep.
    zstep. rewrite A3, A5, (bn_swrap32_small (N - Z.of_nat tnb)) by (clear - G; lia).
    do 4 zstep.
    eapply (BP_sp2_neg false); [exact I2 | exact OK].
  Qed.

  Lemma BP_case_B : forall jb24 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    KBK (JCELLS jb24) m1 R T ->
    pjoin_ok RES fuel' k n true a b tna tnb R (splice (splice T 0 (t0_of true)) n (t1_of true)) ->
    evt bgpsegs POST (ST 0xf8b2c m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (Z.of_nat tnb - N)) x22 (Z_to_bv 64 (8 * N))
                       a4 a2 a1 (Z_to_bv 64 (N - Z.of_nat tna)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t0_facts true) as (Lt0 & Et0).
    zstep. rewrite A4, A3, (bn_swrap32_small (Z.of_nat tna - N)) by (clear - G; lia).
    do 5 zstep. sp1_call I G BND true.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (KAFTER KB_after_T (JCELLS jb24) m1 m2 R T 0%nat _ _ 80%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 5 zstep.
    eapply (BP_sp2_neg true); [exact I2 | exact OK].
  Qed.

  Lemma BP_case_C : forall jb24 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    KBK (JCELLS jb24) m1 R T ->
    pjoin_ok RES fuel' k n false a b tna tnb R (splice (splice T 0 (t0_of false)) n (t1_of true)) ->
    evt bgpsegs POST (ST 0xf8b64 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (Z.of_nat tnb - N)) x22 (Z_to_bv 64 (8 * N))
                       a4 a2 a1 (Z_to_bv 64 (N - Z.of_nat tna)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t0_facts false) as (Lt0 & Et0).
    do 6 zstep. sp1_call I G BND false.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (KAFTER KB_after_T (JCELLS jb24) m1 m2 R T 0%nat _ _ 80%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 6 zstep.
    eapply (BP_sp2_pos true); [exact I2 | exact OK].
  Qed.

  Lemma BP_case_D : forall jb24 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    KBK (JCELLS jb24) m1 R T ->
    pjoin_ok RES fuel' k n false a b tna tnb R (splice (splice T 0 (t0_of true)) n (t1_of false)) ->
    evt bgpsegs POST (ST 0xf8b9c m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 a0 a5 (Z_to_bv 64 (Z.of_nat tnb - N)) x22 (Z_to_bv 64 (8 * N))
                       a4 a2 a1 (Z_to_bv 64 (N - Z.of_nat tna)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    destruct (t0_facts true) as (Lt0 & Et0).
    zstep. rewrite A4, A3, (bn_swrap32_small (Z.of_nat tna - N)) by (clear - G; lia).
    do 5 zstep. sp1_call I G BND true.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (KAFTER KB_after_T (JCELLS jb24) m1 m2 R T 0%nat _ _ 80%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    zstep.
    zstep. rewrite A3, A5, (bn_swrap32_small (N - Z.of_nat tnb)) by (clear - G; lia).
    do 3 zstep.
    eapply (BP_sp2_pos false); [exact I2 | exact OK].
  Qed.

  Notation PCELLS0 jb40 := [CB 40 jb40; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma kpart_body : forall jb40 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x19 x21 x23 x27 x28 x29 x30 x31,
    KBK (PCELLS0 jb40) m1 R T ->
    (let '(t0', t1', neg) := part_diffs a_lo a_hi b_lo b_hi tna tnb (cmp_part_words a_lo a_hi tna) (cmp_part_words b_hi b_lo tnb) in
     pjoin_ok RES fuel' k n neg a b tna tnb R (splice (splice T 0 t0') n t1')) ->
    evt bgpsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 sp a3 x10 x11 x12 x13 x14 x15 a6 x17
               a0 x19 a5 x21 (Z_to_bv 64 7) x23 a4 a2 a1 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xf8a80) fc None m1 (seg_rom bgpsegs)).
  Proof.
    intros until x31. intros I OK.
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof (KACC KB_bounds_ab _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND2.
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    pose proof (munch_refl [(SP + -144, SP + -144 + 144)]%Z m1) as MUF. pose proof (wmono_refl bgpsegs m1) as WMF.
    zstep.
    zstep. rewrite A3. replace (N ≪ 3)%Z with (8 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    zstep.
    zstep. rewrite A3, A4, (bn_swrap32_small (N - Z.of_nat tna)) by (clear - G; lia).
    do 5 zstep.
    pose proof (KFRAME _ _ m1 _ R T I MUF WMF MI STK FR) as I2.
    clear I MUF WMF. clear m1.
    pose proof (KACC KB_a _ _ _ _ 0%nat n I2 ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_a _ _ _ _ n tna I2 ltac:(clear - G; lia)) as HAh.
    pose proof SEPA as D8.
    eapply call_cmp_part_words with (a := a_lo) (b := a_hi) (cl := tna) (da := (n - tna)%nat) (db := 0%nat) (lo := lo) (SPz := (SP + -144)%Z)
                                    (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
      [ exact ESP144 | ret_even | exact STK | exact MI | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
      | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
      | clear - G; lia | ulit | ulit | exact A4 | f_equal; clear - G; lia
      | exact HAl | exact HAh | clear - G; lia
      | rewrite length_firstn; clear - D8 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia | ].
    intros m3 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc STc.
    lazymatch type of I2 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_ro cells mm m3 R T 16%Z eq_refl I2 MUc ltac:(clear - G; lia) WMc MIc STc) as I3 end.
    clear FR STK MI HAl HAh D8 MUc WMc MIc STc I2.
    pose proof I3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    lazymatch type of MI with mem_inv _ ?mm => pose proof (munch_refl [(SP + -144, SP + -144 + 144)]%Z mm) as MUF; pose proof (wmono_refl bgpsegs mm) as WMF end.
    remember (cmp_part_words a_lo a_hi tna) as c1 eqn:Ec1.
    do 2 zstep.
    zstep. rewrite A5, A3, (bn_swrap32_small (Z.of_nat tnb - N)) by (clear - G; lia).
    do 5 zstep.
    lazymatch type of I3 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ _ =>
      lazymatch type of MI with mem_inv _ ?mm' => pose proof (KFRAME _ _ mm mm' R T I3 MUF WMF MI STK FR) as I4 end end.
    clear I3 MUF WMF.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I4 ltac:(clear - G; lia)) as HBl.
    pose proof (KACC KB_b _ _ _ _ n tnb I4 ltac:(clear - G; lia)) as HBh.
    pose proof SEPB as D9.
    eapply call_cmp_part_words with (a := b_hi) (b := b_lo) (cl := tnb) (da := 0%nat) (db := (n - tnb)%nat) (lo := lo) (SPz := (SP + -144)%Z)
                                    (AP := (bp + 8 * N)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
      [ exact ESP144 | ret_even | exact STK | exact MI | apply slice_limbs; exact LB | apply limbs_firstn; exact LB
      | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
      | clear - G; lia | ulit | ulit | exact A5 | f_equal; clear - G; lia
      | exact HBh | exact HBl | clear - G; lia
      | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | rewrite length_firstn; clear - D9 G; lia | ].
    intros m5 u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc STc.
    lazymatch type of I4 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_ro cells mm m5 R T 16%Z eq_refl I4 MUc ltac:(clear - G; lia) WMc MIc STc) as I5 end.
    clear FR STK MI HBl HBh D9 MUc WMc MIc STc I4.
    remember (cmp_part_words b_hi b_lo tnb) as c2 eqn:Ec2.
    do 5 zstep. rewrite A3. replace (N ≪ 3)%Z with (8 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    assert (Hc1 : (c1 = -1 \/ c1 = 0 \/ c1 = 1)%Z).
    { rewrite Ec1, (cmp_part_words_spec a_lo a_hi tna (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA))
        by (right; rewrite slice_length, length_firstn; clear - G; lia). apply sgn3_range. }
    assert (Hc2 : (c2 = -1 \/ c2 = 0 \/ c2 = 1)%Z).
    { rewrite Ec2, (cmp_part_words_spec b_hi b_lo tnb (slice_limbs _ _ _ LB) (limbs_firstn _ _ LB))
        by (left; rewrite slice_length, length_firstn; clear - G; lia). apply sgn3_range. }
    clear Ec1 Ec2.
    pose proof I5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & _).
    destruct Hc1 as [E1|[E1|E1]]; destruct Hc2 as [E2|[E2|E2]]; rewrite E1, E2 in *; clear E1 E2 c1 c2.
    -
      setreg 10%Z (Z_to_bv 64 (-1)) ltac:(vm_compute; reflexivity). setreg 11%Z (Z_to_bv 64 (-4)) ltac:(vm_compute; reflexivity).
      zstep. if_true. zstep. zstep. if_false.
      rewrite part_diffs_m1_m1 in OK. eapply BP_case_D; [exact I5 | exact OK].
    -
      setreg 10%Z (Z_to_bv 64 0) ltac:(vm_compute; reflexivity). setreg 11%Z (Z_to_bv 64 (-3)) ltac:(vm_compute; reflexivity).
      zstep. if_false. do 3 zstep. zstep. if_true. do 3 zstep. zstep. if_false.
      rewrite part_diffs_m1_0 in OK. eapply BP_case_B; [exact I5 | exact OK].
    -
      setreg 10%Z (Z_to_bv 64 1) ltac:(vm_compute; reflexivity). setreg 11%Z (Z_to_bv 64 (-2)) ltac:(vm_compute; reflexivity).
      zstep. if_false. do 3 zstep. zstep. if_true. do 3 zstep. zstep. if_false.
      rewrite part_diffs_m1_p1 in OK. eapply BP_case_B; [exact I5 | exact OK].
    -
      setreg 10%Z (Z_to_bv 64 2) ltac:(vm_compute; reflexivity). setreg 11%Z (Z_to_bv 64 (-1)) ltac:(vm_compute; reflexivity).
      zstep. if_false. do 3 zstep. zstep. if_false.
      rewrite part_diffs_0_m1 in OK. eapply BP_case_A; [exact I5 | exact OK].
    -
      setreg 10%Z (Z_to_bv 64 3) ltac:(vm_compute; reflexivity). setreg 11%Z (Z_to_bv 64 0) ltac:(vm_compute; reflexivity).
      zstep. if_false. do 3 zstep. zstep. if_false.
      rewrite part_diffs_0_0 in OK. eapply BP_case_A; [exact I5 | exact OK].
    -
      setreg 10%Z (Z_to_bv 64 4) ltac:(vm_compute; reflexivity). setreg 11%Z (Z_to_bv 64 1) ltac:(vm_compute; reflexivity).
      zstep. if_false. do 3 zstep. zstep. if_false.
      rewrite part_diffs_0_p1 in OK. eapply BP_case_A; [exact I5 | exact OK].
    -
      setreg 10%Z (Z_to_bv 64 5) ltac:(vm_compute; reflexivity). setreg 11%Z (Z_to_bv 64 2) ltac:(vm_compute; reflexivity).
      zstep. if_false. do 3 zstep. zstep. if_false.
      rewrite part_diffs_p1_m1 in OK. eapply BP_case_A; [exact I5 | exact OK].
    -
      setreg 10%Z (Z_to_bv 64 6) ltac:(vm_compute; reflexivity). setreg 11%Z (Z_to_bv 64 3) ltac:(vm_compute; reflexivity).
      zstep. if_false. do 3 zstep. zstep. if_true. do 3 zstep. zstep. if_true.
      rewrite part_diffs_p1_0 in OK. eapply BP_case_C; [exact I5 | exact OK].
    -
      setreg 10%Z (Z_to_bv 64 7) ltac:(vm_compute; reflexivity). setreg 11%Z (Z_to_bv 64 4) ltac:(vm_compute; reflexivity).
      zstep. if_false. do 3 zstep. zstep. if_true. do 3 zstep. zstep. if_true.
      rewrite part_diffs_p1_p1 in OK. eapply BP_case_C; [exact I5 | exact OK].
  Qed.

End KaraP.

Section MainP.
  Variable CS8 : Z.
  Hypothesis CS8_0 : (0 <= CS8)%Z.
  Hypothesis comba8_ok : comba8_spec CS8.

  Lemma part_body : forall fuel', part_spec_at CS8 fuel' -> part_spec_at CS8 (S fuel').
  Proof.
    intros fuel' IHp. unfold part_spec_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a b k tna tnb R T lo
           LA LB LR LT Hk3 Hkf Hk26 Htna Htnb Hd1 Hd2 HLA HLB HLR HLT A3 A4 A5 RA RB RR RT WR WT DRA DRB DTA DTB DRT STK LO SEPR SEPT SEPA SEPB MI0.
    remember (Nat.pow 2 k) as n eqn:En.
    assert (HN : (2 <= Z.of_nat n <= 67108864)%Z) by (subst n; apply pow2_Z_bounds; clear - Hk3 Hk26; lia).
    assert (Hn8 : (8 <= n)%nat).
    { subst n. replace k with (3 + (k - 3))%nat by (clear - Hk3; lia). rewrite Nat.pow_add_r. pose proof (pow2_pos (k - 3)) as HP.
      cbn [Nat.pow] in *. clear - HP. lia. }
    remember (part_stack CS8 k - 144)%Z as SK eqn:ESK.
    assert (HSK : (320 <= SK)%Z) by (subst SK; unfold part_stack, rec_stack; lia).
    assert (ERS : part_stack CS8 k = (144 + SK)%Z) by (subst SK; lia).
    rewrite ERS in LO, SEPR, SEPT, SEPA, SEPB |- *.
    pose proof (proj1 STK) as LO0.
    rewrite HLR in WR.
    assert (GEO : hide ((bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0) /\
                        (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a0) /\
                        (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a6) /\
                        (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a6) /\
                        (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a6 \/ bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a0) /\
                        (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned sp - (144 + SK) \/ bv_unsigned sp <= bv_unsigned a0) /\
                        (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned sp - (144 + SK) \/ bv_unsigned sp <= bv_unsigned a6) /\
                        (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - (144 + SK) \/ bv_unsigned sp <= bv_unsigned a1) /\
                        (bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned sp - (144 + SK) \/ bv_unsigned sp <= bv_unsigned a2) /\
                        length a = (n + tna)%nat /\ length b = (n + tnb)%nat /\ length R = (4 * n)%nat /\ (8 * n <= length T)%nat /\
                        (tna < n)%nat /\ (tnb < n)%nat /\ (tna <= tnb + 1)%nat /\ (tnb <= tna + 1)%nat)%Z).
    { apply hide_intro. repeat split; assumption. }
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB HLA HLB HLR HLT Htna Htnb Hd1 Hd2.
    pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length R)); (bv_unsigned a6, bv_unsigned a6 + 8 * Z.of_nat (length T));
                            (bv_unsigned sp - (144 + SK), bv_unsigned sp)]%Z m) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUF. pose proof (wmono_refl bgpsegs m) as WM.
    assert (LO1 : (lo <= bv_unsigned sp - 144)%Z) by (clear - LO HSK; lia).
    carve_frame 144%nat STK.
    do 22 zstep.
    pose proof (hide_elim _ GEO) as (DRA & DRB & DTA & DTB & DRT & SEPR & SEPT & SEPA & SEPB & HLA' & HLB' & HLR' & HLT' & Htna & Htnb & Hd1 & Hd2).
    assert (RA1 : limbs_at bgpsegs m0 (bv_unsigned a1) a) by (eapply limbs_at_transport; [exact RA | exact MUF | cbn [disjoint_from]; clear - SEPA HSK; lia]).
    assert (RB1 : limbs_at bgpsegs m0 (bv_unsigned a2) b) by (eapply limbs_at_transport; [exact RB | exact MUF | cbn [disjoint_from]; clear - SEPB HSK; lia]).
    assert (RR1 : limbs_at bgpsegs m0 (bv_unsigned a0) R) by (eapply limbs_at_transport; [exact RR | exact MUF | cbn [disjoint_from]; clear - SEPR HSK; lia]).
    assert (RT1 : limbs_at bgpsegs m0 (bv_unsigned a6) T) by (eapply limbs_at_transport; [exact RT | exact MUF | cbn [disjoint_from]; clear - SEPT HSK; lia]).
    clear MUF RA RB RR RT.
    assert (PRE : kpart_pre CS8 fuel' k n tna tnb (length a) (length b) (length T) SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1)
                            (bv_unsigned a2) (bv_unsigned sp) lo).
    { unfold kpart_pre. rewrite <- HLR'.
      split; [exact En|]. split; [clear - Hk3 Hk26; lia|]. split; [exact Hkf|]. split; [exact Hn8|]. split; [clear - HN; lia|].
      split; [exact Htna|]. split; [exact Htnb|]. split; [exact Hd1|]. split; [exact Hd2|].
      split; [exact HLA'|]. split; [exact HLB'|]. split; [exact HLT'|]. split; [exact ESK|].
      split; [exact DRA|]. split; [exact DRB|]. split; [exact DTA|]. split; [exact DTB|]. split; [exact DRT|].
      split; [clear - SEPR; lia|]. split; [clear - SEPT; lia|]. split; [clear - SEPA; lia|]. split; [clear - SEPB; lia|].
      split; [clear - LO; lia | exact LO0]. }
    assert (KB0 : KB bgpsegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat (length T)
                     144%Z SK (bv_unsigned sp + -144)%Z
                     [CB 40 (firstn 40 (firstn 48 (firstn 56 (firstn 64 (firstn 72 (firstn 80 (firstn 88 (firstn 96 (firstn 104 (firstn 112 (firstn 120 (firstn 128 (firstn 136 junk)))))))))))));
                      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] m0 R T).
    { unfold KB. split; [exact LR|]. split; [exact LT|]. split; [exact HLR'|]. split; [reflexivity|].
      split; [exact RR1|]. split; [exact RT1|]. split; [exact RA1|]. split; [exact RB1|].
      split; [exact WR|]. split; [exact WT|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MI0|].
      split; [|exact WM]. unfold KWfin. rewrite <- HLR'. replace (bv_unsigned sp - 144 - SK)%Z with (bv_unsigned sp - (144 + SK))%Z by (clear; lia). exact MU. }
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB HLA' HLB' HLT' Htna Htnb Hd1 Hd2 FR STK MI0 MU WM WR WT RA1 RB1 RR1 RT1.
    assert (L7 : (bv_unsigned (Z_to_bv 64 7) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (L3 : (bv_unsigned a3 < 9223372036854775808)%Z) by (rewrite A3; clear - HN; lia).
    zstep. rewrite (lts_words_small (Z_to_bv 64 7) a3 L7 L3). rewrite A3.
    if_cases K8; zify_cond K8; [|exfalso; clear - K8 Hn8; lia].
    replace (Z.of_nat (length R)) with (Z.of_nat (4 * n)) by (rewrite HLR'; reflexivity).
    eapply (kpart_body CS8 CS8_0 comba8_ok fuel' IHp) with (n := n) (nT := length T) (SK := SK) (k := k) (tna := tna) (tnb := tnb);
      try (first [ exact PRE | exact LA | exact LB | exact A3 | exact A4 | exact A5 | exact KB0 ]).
    pose proof (hide_elim _ GEO) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HLA' & HLB' & _ & HLT' & Htna & Htnb & Hd1 & Hd2).
    rewrite En. apply part_staged; try assumption; rewrite <- ?En; try assumption.
  Qed.

  Theorem bn_mul_part_recursive_spec : forall fuel, part_spec_at CS8 fuel.
  Proof.
    induction fuel as [|fuel' IH]; [|apply part_body; exact IH].
    unfold part_spec_at. intros. exfalso. lia.
  Qed.
End MainP.
