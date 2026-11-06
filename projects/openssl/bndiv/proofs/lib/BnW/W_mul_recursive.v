(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp BnKaraX BnKaraMem
  W_add_words W_sub_words W_cmp_words W_cmp_part_words W_sub_part_words W_mul_normal BnCalls.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_mul_recursive_entry := 0x109a30%Z.

(* [comment removed for export] *)
Lemma land_even31 : forall x, (0 <= x < 1073741824)%Z -> Z.land (2 * x) 2147483646 = (2 * x)%Z.
Proof.
  intros x Hx.
  replace (2 * x)%Z with (Z.shiftl x 1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  change 2147483646%Z with (Z.shiftl 1073741823 1).
  rewrite <- Z.shiftl_land. f_equal. change 1073741823%Z with (Z.ones 30). rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2 ^ 30)%Z with 1073741824%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma lor_neg_zero : forall da db : nat, (da <= 1)%nat -> (db <= 1)%nat ->
  (Z.lor (bv_unsigned (Z_to_bv 64 (- Z.of_nat db))) (bv_unsigned (Z_to_bv 64 (- Z.of_nat da))) = 0 <-> (da = 0 /\ db = 0)%nat)%Z.
Proof.
  intros da db Hda Hdb. rewrite Z.lor_eq_0_iff.
  assert (Hd : (da = 0 \/ da = 1)%nat) by lia. assert (He : (db = 0 \/ db = 1)%nat) by lia.
  assert (E0 : bv_unsigned (Z_to_bv 64 (- Z.of_nat 0)) = 0%Z) by (vm_compute; reflexivity).
  assert (E1 : bv_unsigned (Z_to_bv 64 (- Z.of_nat 1)) = 18446744073709551615%Z) by (vm_compute; reflexivity).
  destruct Hd as [-> | ->]; destruct He as [-> | ->]; rewrite ?E0, ?E1; split; intros H; try (destruct H as [H1 H2]); try lia; try discriminate.
Qed.

(* [comment removed for export] *)
Lemma half_n2 : forall x, (0 <= x < 1073741824)%Z ->
  bv_swrap 32 (bv_swrap 32 ((2 * x + bv_swrap 32 (bv_wrap 32 (2 * x) ≫ 31)) mod 18446744073709551616) ≫ 1) = x.
Proof.
  intros x Hx.
  assert (E1 : bv_wrap 32 (2 * x) = (2 * x)%Z) by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32)%Z with 4294967296%Z; apply Z.mod_small; lia).
  rewrite E1. rewrite (Z.shiftr_div_pow2 (2 * x) 31) by lia. change (2 ^ 31)%Z with 2147483648%Z.
  rewrite (Z.div_small (2 * x) 2147483648) by lia. rewrite (bn_swrap32_small 0) by lia. rewrite Z.add_0_r.
  rewrite (Z.mod_small (2 * x)) by lia. rewrite (bn_swrap32_small (2 * x)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1)%Z with 2%Z. rewrite Z.mul_comm, Z.div_mul by lia.
  apply bn_swrap32_small. lia.
Qed.

(* [comment removed for export] *)
Lemma addw_dn : forall x (d : nat), (d <= 1)%nat -> (0 <= x < 1073741824)%Z ->
  bv_swrap 32 (x + bv_unsigned (Z_to_bv 64 (- Z.of_nat d))) = (x - Z.of_nat d)%Z.
Proof.
  intros x d Hd Hx. assert (E : (d = 0 \/ d = 1)%nat) by lia.
  assert (E0 : bv_unsigned (Z_to_bv 64 (- Z.of_nat 0)) = 0%Z) by (vm_compute; reflexivity).
  assert (E1 : bv_unsigned (Z_to_bv 64 (- Z.of_nat 1)) = 18446744073709551615%Z) by (vm_compute; reflexivity).
  destruct E as [-> | ->]; rewrite ?E0, ?E1.
  - rewrite Z.add_0_r. change (Z.of_nat 0) with 0%Z. rewrite Z.sub_0_r. apply bn_swrap32_small. lia.
  - unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z. change (Z.of_nat 1) with 1%Z.
    Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_dn : forall d : nat, (d <= 1)%nat -> bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 (- Z.of_nat d))) = Z.of_nat d.
Proof. intros d Hd. assert (E : (d = 0 \/ d = 1)%nat) by lia. destruct E as [-> | ->]; vm_compute; reflexivity. Qed.

Lemma upd_app_mid : forall (pre l : list Z) x v, upd (pre ++ x :: l) (length pre) v = (pre ++ [v]) ++ l.
Proof.
  intros pre l x v. unfold upd, splice. cbn [length].
  rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
  rewrite skipn_app, skipn_all2 by lia. replace (length pre + 1 - length pre)%nat with 1%nat by lia. cbn [skipn app].
  rewrite <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Definition kr_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp nr tq nt fs : Z) (r' t' : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(rp, rp + 8 * nr); (tq, tq + 8 * nt); (bv_unsigned sp - fs, bv_unsigned sp)]%Z m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ limbs_at segs m' rp r' /\ limbs_at segs m' tq t'
    /\ stk segs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition rec_stack (CS8 : Z) (k : nat) : Z := (176 * Z.of_nat (S k) + Z.max CS8 144)%Z.

Definition rec_spec_at (CS8 : Z) (k : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (da db : nat) (R T : list Z) (lo : Z),
    limbs a -> limbs b -> limbs R -> limbs T ->
    (1 <= k <= 26)%nat -> (da <= 1)%nat -> (db <= 1)%nat ->
    length a = (Nat.pow 2 k - da)%nat -> length b = (Nat.pow 2 k - db)%nat -> length R = (2 * Nat.pow 2 k)%nat ->
    (scratch_rec k <= length T)%nat ->
    bv_unsigned a3 = Z.of_nat (Nat.pow 2 k) -> a4 = Z_to_bv 64 (- Z.of_nat da) -> a5 = Z_to_bv 64 (- Z.of_nat db) ->
    limbs_at psegs m (bv_unsigned a1) a -> limbs_at psegs m (bv_unsigned a2) b ->
    limbs_at psegs m (bv_unsigned a0) R -> limbs_at psegs m (bv_unsigned a6) T ->
    wr_at psegs m (bv_unsigned a0) (8 * Z.of_nat (length R)) -> wr_at psegs m (bv_unsigned a6) (8 * Z.of_nat (length T)) ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a0)%Z ->
    (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a6)%Z ->
    (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a6)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a6 \/ bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a0)%Z ->
    stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - rec_stack CS8 k)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned sp - rec_stack CS8 k \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned sp - rec_stack CS8 k \/ bv_unsigned sp <= bv_unsigned a6)%Z ->
    (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - rec_stack CS8 k \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned sp - rec_stack CS8 k \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    mem_inv psegs m ->
    evt psegs (kr_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (bv_unsigned a0) (Z.of_nat (length R)) (bv_unsigned a6) (Z.of_nat (length T)) (rec_stack CS8 k)
                 (fst (mul_recursive k a b da db R T)) (snd (mul_recursive k a b da db R T)) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x109a30) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Section CallRec.
  Variable POST : machine_state -> Prop.
  Variables (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo SPz RET : Z).
  Hypothesis ESP : bv_unsigned wsp = SPz.
  Hypothesis ERET : ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET.
  Hypothesis STK : stk psegs m lo SPz.
  Hypothesis MI0 : mem_inv psegs m.

  Lemma call_rec : forall (CS8 : Z) (k : nat) (a b : list Z) (da db : nat) (R T : list Z) (RP AP BP TQ : Z),
    rec_spec_at CS8 k ->
    limbs a -> limbs b -> limbs R -> limbs T ->
    (1 <= k <= 26)%nat -> (da <= 1)%nat -> (db <= 1)%nat ->
    length a = (Nat.pow 2 k - da)%nat -> length b = (Nat.pow 2 k - db)%nat -> length R = (2 * Nat.pow 2 k)%nat ->
    (scratch_rec k <= length T)%nat ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (Nat.pow 2 k) ->
    w4 = Z_to_bv 64 (- Z.of_nat da) -> w5 = Z_to_bv 64 (- Z.of_nat db) -> bv_unsigned w6 = TQ ->
    limbs_at psegs m AP a -> limbs_at psegs m BP b -> limbs_at psegs m RP R -> limbs_at psegs m TQ T ->
    wr_at psegs m RP (8 * Z.of_nat (length R)) -> wr_at psegs m TQ (8 * Z.of_nat (length T)) ->
    (RP + 8 * Z.of_nat (length R) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (RP + 8 * Z.of_nat (length R) <= BP \/ BP + 8 * Z.of_nat (length b) <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= AP \/ AP + 8 * Z.of_nat (length a) <= TQ)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= BP \/ BP + 8 * Z.of_nat (length b) <= TQ)%Z ->
    (RP + 8 * Z.of_nat (length R) <= TQ \/ TQ + 8 * Z.of_nat (length T) <= RP)%Z ->
    (lo <= SPz - rec_stack CS8 k)%Z ->
    (RP + 8 * Z.of_nat (length R) <= SPz - rec_stack CS8 k \/ SPz <= RP)%Z ->
    (TQ + 8 * Z.of_nat (length T) <= SPz - rec_stack CS8 k \/ SPz <= TQ)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - rec_stack CS8 k \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - rec_stack CS8 k \/ SPz <= BP)%Z ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length R)); (TQ, TQ + 8 * Z.of_nat (length T)); (SPz - rec_stack CS8 k, SPz)]%Z m m2 ->
       wmono psegs m m2 -> mem_inv psegs m2 ->
       limbs_at psegs m2 RP (fst (mul_recursive k a b da db R T)) -> limbs_at psegs m2 TQ (snd (mul_recursive k a b da db R T)) ->
       stk psegs m2 lo SPz ->
       evt psegs POST
         (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
             F (Z_to_bv 64 RET) fc None m2 (seg_rom psegs))) ->
    evt psegs POST
      (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x109a30) fc None m (seg_rom psegs)).
  Proof using ESP ERET STK MI0.
    intros CS8 k a b da db R T RP AP BP TQ SPEC LA LB LR LT Hk Hda Hdb HLA HLB HLR HLT E0 E1 E2 E3 E4 E5 E6
           RA RB RR RT WR WT DRA DRB DTA DTB DRT LO SEPR SEPT SEPA SEPB K.
    subst RP AP BP TQ SPz.
    eapply evt_cut; [ eapply SPEC with (a := a) (b := b) (da := da) (db := db) (R := R) (T := T) (lo := lo); eassumption | ].
    intros ms' PO. unfold kr_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & HT & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.
End CallRec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kara_pre (CS8 : Z) (k' n da db la lb nT : nat) (SK rp tq ap bp SP lo : Z) : Prop :=
  n = Nat.pow 2 k' /\ (1 <= k' <= 25)%nat /\ (8 <= n)%nat /\ (Z.of_nat n <= 33554432)%Z /\ (da <= 1)%nat /\ (db <= 1)%nat /\
  la = (2 * n - da)%nat /\ lb = (2 * n - db)%nat /\ (4 * n + scratch_rec k' <= nT)%nat /\ SK = rec_stack CS8 k' /\
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
  Variable CS8 : Z.
  Hypothesis CS8_0 : (0 <= CS8)%Z.
  Hypothesis comba8_ok : comba8_spec CS8.
  Variable k' : nat.
  Hypothesis IH : rec_spec_at CS8 k'.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (da db : nat) (lo : Z) (n nT : nat) (SK : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a2).
  Notation tq := (bv_unsigned a6).
  Notation SP := (bv_unsigned sp).
  Notation N := (Z.of_nat n).
  Hypothesis PRE : kara_pre CS8 k' n da db (length a) (length b) nT SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo.
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
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
  Lemma HSK : SK = rec_stack CS8 k'. Proof. apply PRE. Qed.
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
  Lemma SK0 : (0 <= SK)%Z. Proof. rewrite HSK. unfold rec_stack. lia. Qed.
  Lemma SK_ge : (320 <= SK /\ CS8 <= SK)%Z. Proof. rewrite HSK. unfold rec_stack. lia. Qed.
  Lemma FS0 : (0 <= 176)%Z. Proof. lia. Qed.
  Lemma FBE : (SP + -176 = SP - 176)%Z. Proof. reflexivity. Qed.
  Lemma ESP176 : bv_unsigned (Z_to_bv 64 (SP + -176)) = (SP + -176)%Z.
  Proof.
    apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R.
    pose proof LO. pose proof LO0. pose proof SK0. lia.
  Qed.

  Notation POST := (kr_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                      (bv_unsigned a0) (Z.of_nat (4 * n)) (bv_unsigned a6) (Z.of_nat nT) (176 + SK)%Z (fst RES) (snd RES) lo m).
  Notation KBK := (KB psegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      176%Z SK (bv_unsigned sp + -176)%Z).
  Notation KUPD := (KB_upd psegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      176%Z SK (bv_unsigned sp + -176)%Z FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB).
  Notation KFRAME := (KB_frame psegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      176%Z SK (bv_unsigned sp + -176)%Z FS0 FBE SK0 SEPR SEPT SEPA SEPB).
  Notation KSTORE := (KB_storeR psegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      176%Z SK (bv_unsigned sp + -176)%Z FS0 FBE SK0 DRA DRB DRT SEPR).
  Notation KAFTER L := (L psegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      176%Z SK (bv_unsigned sp + -176)%Z FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB).
  Notation KACC L := (L psegs m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (4 * n)%nat nT
                      176%Z SK (bv_unsigned sp + -176)%Z).

  (* [comment removed for export] *)
  Notation FCELLS jb v144 :=
    [CB 8 jb; C8 (Z_to_bv 64 (Z.of_nat da)); C8 (Z_to_bv 64 (Z.of_nat n - Z.of_nat da)); C8 (Z_to_bv 64 (Z.of_nat n - Z.of_nat db));
     C8 v144; C8 (Z_to_bv 64 (bv_unsigned a2 + 8 * Z.of_nat n)); C8 (Z_to_bv 64 (bv_unsigned a1 + 8 * Z.of_nat n));
     C8 (Z_to_bv 64 (Z.of_nat n)); C8 (Z_to_bv 64 (8 * Z.of_nat n));
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             a3 a6 x20 (Z_to_bv 64 (16 * Z.of_nat n)) a2 a1 x24 a4 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma B_epi : forall jb v144 m1 R T x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb v144) m1 R T -> RES = (R, T) ->
    evt psegs POST (ST 0x109ed4 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM) E.
    do 15 zstep.
    assert (LO1 : (lo <= SP + -176)%Z) by (pose proof LO; pose proof SK0; lia).
    release_frame FR ST (bv_unsigned sp).
    subst RES. cbn [fst snd].
    assert (MU' : munch [(rp, rp + 8 * Z.of_nat (4 * n)); (tq, tq + 8 * Z.of_nat nT); (SP - (176 + SK), SP)]%Z m m1).
    { unfold KWfin in MU. replace (SP - (176 + SK))%Z with (SP - 176 - SK)%Z by (clear; lia). exact MU. }
    finish.
  Qed.

  (* [comment removed for export] *)
  Ltac kb_store SOK0 I2 :=
    lazymatch type of SOK0 with
    | store_ok _ ?m2 ?a0' _ = true =>
        let ad := cur_mem_addr in
        let SOK := fresh "SOK" in
        assert (SOK : store_ok psegs m2 ad 8 = true) by (replace ad with a0' by (unfold wa; f_equal; lia); exact SOK0);
        replace a0' with ad in I2 by (unfold wa; f_equal; lia);
        zstep; clear SOK SOK0;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => let m' := fresh "m" in gen_mem mm m' end
    end.

  (* [comment removed for export] *)
  Lemma B_loop : forall (l pre : list Z) jb v144 m1 T x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x24 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb v144) m1 (pre ++ l) T -> cu_fit l -> RES = (pre ++ carry_up l, T) ->
    evt psegs POST (ST 0x109ec0 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre))) x11 x12 x13 x14 x15 x16 x17 x20 x24 x26 x27 x28 x29 x30 x31).
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
    destruct (KSTORE (FCELLS jb v144) m1 (pre ++ x :: l') T (length pre) (addw x 1) eq_refl I Hi (addw_limb _ _)) as (SOK0 & I2).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI MU WM.
    kb_store SOK0 I2.
    zstep.
    rewrite upd_app_mid in I2.
    pose proof (addw_limb x 1) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K; zify_cond K.
    - setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x 1])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      eapply IHl; [exact I2 | apply Hfit'; exact K |].
      rewrite E. cbn [carry_up]. rewrite K. cbn [Z.eqb]. rewrite <- app_assoc. reflexivity.
    - eapply B_epi; [exact I2|].
      rewrite E. cbn [carry_up]. destruct (Z.eqb_spec (addw x 1) 0) as [E0|_]; [contradiction|]. rewrite <- app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma geom : (8 <= N <= 33554432 /\ 0 <= lo /\ lo <= SP - 176 - SK /\ 320 <= SK /\ CS8 <= SK /\ 0 <= CS8 /\
                Z.of_nat (4 * n + scratch_rec k') <= Z.of_nat nT /\ Z.of_nat da <= 1 /\ Z.of_nat db <= 1 /\
                Z.of_nat (length a) = 2 * N - Z.of_nat da /\ Z.of_nat (length b) = 2 * N - Z.of_nat db)%Z.
  Proof.
    pose proof Hn8. pose proof HnB. pose proof LO. pose proof LO0. pose proof SK_ge. pose proof HnT. pose proof Hda. pose proof Hdb.
    pose proof HLA. pose proof HLB. lia.
  Qed.

  Ltac ret_even := apply ret_pc_even; [lia | reflexivity].
  Ltac ulit := first [ reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; lia); lia | lia ].

  (* [comment removed for export] *)
  Lemma B_fin : forall jb v144 m1 R T c12 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb v144) m1 R T -> kc3_ok RES n R T c12 -> (-1 <= c12 <= 2)%Z ->
    evt psegs POST (ST 0x109e7c m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c12) x24 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK Hc12.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ n (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & WRa).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & _).
    do 6 zstep.
    pose proof DRT as D1. pose proof SEPR as D2. pose proof SEPT as D3.
    eapply call_add_words with (a := slice R n (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -176)%Z)
                               (RP := (rp + 8 * N)%Z) (AP := (rp + 8 * N)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact LRa | exact LTb | rewrite ERa, ETb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa, A3; clear; lia
      | exact HRa | exact HTb | rewrite ERa; exact WRa
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D3 G; lia | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LRa LTb ltac:(rewrite ERa, ETb; reflexivity)) as SP3.
    unfold kc3_ok in OK. cbv zeta in OK.
    destruct (add_words (slice R n (2 * n)) (slice T (2 * n) (2 * n))) as [sg3 cy3]. cbn [fst snd] in *.
    destruct SP3 as (Ls3 & Es3 & Hc3 & _). rewrite ERa in Es3. destruct OK as (ERES & Hc & FIT).
    pose proof (KAFTER KB_after_R (FCELLS jb v144) m1 m2 R T n sg3 _ 16%Z eq_refl I MUc ltac:(rewrite ERa, Es3; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls3 ltac:(rewrite Es3; clear; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRa LRa ERa WRa HTb LTb ETb MUc WMc HS I D1 D2 D3.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    zstep. rewrite (bn_swrap32_mod c12 cy3) by (clear - Hc12 Hc3; lia).
    zstep. if_cases K; zify_cond K.
    { eapply B_epi; [exact I2|]. rewrite ERES. rewrite K. reflexivity. }
    specialize (FIT K). destruct (Z.eqb_spec (c12 + cy3) 0) as [E0|_]; [contradiction|].
    do 2 zstep. rewrite A3, (bn_swrap32_small (N + 2 * N)) by (clear - G; lia).
    do 2 zstep.
    (* [comment removed for export] *)
    remember (splice R n sg3) as R' eqn:ER'. pose proof ER as ERl.
    assert (Lpre : length (firstn (n + 2 * n) R') = (n + 2 * n)%nat) by (rewrite length_firstn; clear - ER; lia).
    destruct (skipn (n + 2 * n) R') as [|x l'] eqn:Esk.
    { exfalso. pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. clear - HH ER G. lia. }
    assert (ERpl : R' = firstn (n + 2 * n) R' ++ x :: l') by (rewrite <- Esk; symmetry; apply firstn_skipn).
    remember (firstn (n + 2 * n) R') as pre eqn:Epre.
    rewrite ERpl in I2, HR, LR. clear ERpl.
    pose proof (limbs_cons_lit x l' (proj2 (limbs_app_inv _ _ LR))) as (Hx & Ll').
    setreg 9%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length pre))) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; rewrite Lpre; clear; lia).
    apply limbs_at_app in HR. destruct HR as [HR1 HR2].
    ld_hd HR2.
    zstep.
    setreg 10%Z (Z_to_bv 64 (addw x (c12 + cy3))) ltac:(unfold addw; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia).
    destruct (KSTORE (FCELLS jb v144) m2 (pre ++ x :: l') T (length pre) (addw x (c12 + cy3)) eq_refl I2 ltac:(rewrite Lpre; clear - G; lia) (addw_limb _ _)) as (SOK0 & I3).
    clear LR LT ER ET HR1 HR2 HT HA HB WR WT FR ST MI MU WM I2 MIc STc.
    kb_store SOK0 I3. rewrite upd_app_mid in I3.
    pose proof (addw_limb x (c12 + cy3)) as RL. unfold limb in RL. rewrite BW_lit in RL.
    zstep. if_cases K2; zify_cond K2.
    - eapply B_epi; [exact I3|]. rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx).
      destruct (Z.ltb_spec (addw x (c12 + cy3)) x) as [HH|_]; [exfalso; clear - HH K2; lia|]. rewrite <- app_assoc. reflexivity.
    - zstep.
      setreg 10%Z (Z_to_bv 64 (rp + 8 * Z.of_nat (length (pre ++ [addw x (c12 + cy3)])))) ltac:(f_equal; rewrite length_app; cbn [length]; clear; lia).
      assert (TST : (addw x (c12 + cy3) <? x) = true) by (apply Z.ltb_lt; clear - K2; lia).
      eapply B_loop; [exact I3 | |].
      + eapply (add_carry_fit x l' (c12 + cy3)); [rewrite BW_lit; exact Hx | exact Ll' | rewrite BW_lit; clear - Hc; lia | | exact TST].
        replace (S (length l')) with n; [exact FIT|].
        pose proof (length_skipn (n + 2 * n) R') as HH. rewrite Esk in HH. cbn [length] in HH. rewrite HH, ERl. clear. lia.
      + rewrite ERES. unfold add_carry. rewrite add_carry_test by (rewrite BW_lit; exact Hx). rewrite TST. rewrite <- app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma B_sub : forall jb v144 m1 R T c1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb v144) m1 R T -> kc2_ok RES n true R T c1 -> (0 <= c1 <= 1)%Z ->
    evt psegs POST (ST 0x109db4 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c1) x24 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    do 5 zstep.
    pose proof SEPT as D3.
    eapply call_sub_words with (a := slice T 0 (2 * n)) (b := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -176)%Z)
                               (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact LTa | exact LTb | rewrite ETa, ETb; reflexivity
      | rewrite ETa; clear - G; lia | ulit | ulit | ulit | rewrite ETa, A3; clear; lia
      | exact HTa | exact HTb | rewrite ETa; exact WTb
      | unfold alias_ok; rewrite ETa; clear; lia | unfold alias_ok; left; reflexivity
      | clear - G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia | rewrite ETa; clear - D3 G; lia | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (sub_words_spec _ _ LTa LTb ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (sub_words (slice T 0 (2 * n)) (slice T (2 * n) (2 * n))) as [sg2 bw]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hbw & _). rewrite ETa in Es2.
    pose proof (KAFTER KB_after_T (FCELLS jb v144) m1 m2 R T (2 * n)%nat sg2 _ 16%Z eq_refl I MUc ltac:(rewrite ETa, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep. rewrite (bn_swrap32_small (c1 - bw)) by (clear - Hc1 Hbw; lia).
    zstep.
    eapply B_fin; [exact I2 | exact OK | clear - Hc1 Hbw; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B_add : forall jb v144 m1 R T c1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb v144) m1 R T -> kc2_ok RES n false R T c1 -> (0 <= c1 <= 1)%Z ->
    evt psegs POST (ST 0x109e64 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c1) x24 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK Hc1.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTa & LTa & ETa & _).
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTb & LTb & ETb & WTb).
    do 5 zstep.
    pose proof SEPT as D3.
    eapply call_add_words with (a := slice T (2 * n) (2 * n)) (b := slice T 0 (2 * n)) (lo := lo) (SPz := (SP + -176)%Z)
                               (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat (2 * n))%Z) (BP := (tq + 8 * Z.of_nat 0)%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact LTb | exact LTa | rewrite ETa, ETb; reflexivity
      | rewrite ETb; clear - G; lia | ulit | ulit | ulit | rewrite ETb, A3; clear; lia
      | exact HTb | exact HTa | rewrite ETb; exact WTb
      | unfold alias_ok; left; reflexivity | unfold alias_ok; rewrite ETb; clear; lia
      | clear - G; lia | rewrite ETb; clear - D3 G; lia | rewrite ETb; clear - D3 G; lia | rewrite ETb; clear - D3 G; lia | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    pose proof (add_words_spec _ _ LTb LTa ltac:(rewrite ETa, ETb; reflexivity)) as SP2.
    unfold kc2_ok in OK. cbv zeta in OK.
    destruct (add_words (slice T (2 * n) (2 * n)) (slice T 0 (2 * n))) as [sg2 cy]. cbn [fst snd] in *.
    destruct SP2 as (Ls2 & Es2 & Hcy & _). rewrite ETb in Es2.
    pose proof (KAFTER KB_after_T (FCELLS jb v144) m1 m2 R T (2 * n)%nat sg2 _ 16%Z eq_refl I MUc ltac:(rewrite ETb, Es2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls2 ltac:(rewrite Es2; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTb MUc WMc HS I D3.
    zstep.
    eapply B_fin; [exact I2 | exact OK | clear - Hc1 Hcy; lia].
  Qed.

  Notation a_lo := (firstn n a).
  Notation a_hi := (slice a n (n - da)).
  Notation b_lo := (firstn n b).
  Notation b_hi := (slice b n (n - db)).

  (* [comment removed for export] *)
  Ltac first_add I OK G BND jb v144 :=
    let HRa := fresh "HRa" in let LRa := fresh "LRa" in let ERa := fresh "ERa" in
    let HRb := fresh "HRb" in let LRb := fresh "LRb" in let ERb := fresh "ERb" in
    let WTa := fresh "WTa" in let D1 := fresh "D1" in let D2 := fresh "D2" in let D3 := fresh "D3" in
    destruct (KACC KB_R _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear; lia)) as (HRa & LRa & ERa & _);
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear; lia)) as (HRb & LRb & ERb & _);
    destruct (KACC KB_T _ _ _ _ 0%nat (2 * n)%nat I ltac:(clear - G; lia)) as (_ & _ & _ & WTa);
    pose proof DRT as D1; pose proof SEPR as D2; pose proof SEPT as D3;
    lazymatch goal with ST : stk psegs ?m1 lo _, MI : mem_inv psegs ?m1 |- _ =>
    eapply call_add_words with (a := slice _ 0 (2 * n)) (b := slice _ (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -176)%Z)
                               (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (rp + 8 * Z.of_nat 0)%Z) (BP := (rp + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact LRa | exact LRb | rewrite ERa, ERb; reflexivity
      | rewrite ERa; clear - G; lia | ulit | ulit | ulit | rewrite ERa, A3; clear; lia
      | exact HRa | exact HRb | rewrite ERa; exact WTa
      | unfold alias_ok; rewrite ERa; clear - D1 G; lia | unfold alias_ok; rewrite ERa; clear - D1 G; lia
      | clear - G; lia | rewrite ERa; clear - D3 G; lia | rewrite ERa; clear - D2 G; lia | rewrite ERa; clear - D2 G; lia | ];
    let m4 := fresh "m" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIc" in
    let HS := fresh "HS" in let STc := fresh "STc" in let SP1 := fresh "SP1" in
    let sg1 := fresh "sg" in let cy1 := fresh "cy" in let Ls1 := fresh "Ls" in let Es1 := fresh "Es" in let Hc1 := fresh "Hcy" in
    intros m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MUc WMc MIc HS STc;
    pose proof (add_words_spec _ _ LRa LRb ltac:(rewrite ERa, ERb; reflexivity)) as SP1;
    unfold kc_ok in OK; cbv zeta in OK;
    lazymatch type of SP1 with (let '(_, _) := ?AW in _) => destruct AW as [sg1 cy1] end;
    cbn [fst snd] in *;
    destruct SP1 as (Ls1 & Es1 & Hc1 & _); rewrite ERa in Es1;
    pose proof (KAFTER KB_after_T (FCELLS jb v144) m1 m4 _ _ 0%nat sg1 _ 16%Z eq_refl I MUc ltac:(rewrite ERa, Es1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Ls1 ltac:(rewrite Es1; clear - G; lia));
    clear HRa LRa ERa HRb LRb ERb WTa D1 D2 D3 MUc WMc HS MIc STc
    end.

  (* [comment removed for export] *)
  Lemma B_comba : forall (neg : bool) jb v144 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x27 x28 x29 x30 x31,
    n = 8%nat -> da = 0%nat -> db = 0%nat ->
    KBK (FCELLS jb v144) m1 R T ->
    kc_ok RES n neg (splice (splice R 0 (mul_comba8 a_lo b_lo)) (2 * n) (mul_comba8 a_hi b_hi)) T ->
    evt psegs POST (ST 0x109d74 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 x20 (Z_to_bv 64 (if neg then 0 else 1)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros En Eda Edb I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_R _ _ _ _ 0%nat 16%nat I ltac:(clear - En; lia)) as (_ & _ & _ & WRa).
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HBl.
    do 4 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof SEPR as D3. pose proof SEPA as D4. pose proof SEPB as D5.
    assert (Lal : length a_lo = 8%nat) by (rewrite length_firstn; clear - G En; lia).
    assert (Lbl : length b_lo = 8%nat) by (rewrite length_firstn; clear - G En; lia).
    eapply call_comba8 with (CS8 := CS8) (a := a_lo) (b := b_lo) (lo := lo) (SPz := (SP + -176)%Z)
                            (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact comba8_ok | apply limbs_firstn; exact LA | apply limbs_firstn; exact LB
      | exact Lal | exact Lbl | ulit | ulit | ulit | exact HAl | exact HBl | exact WRa
      | clear - D1 G En; lia | clear - D2 G En; lia | clear - G; lia
      | clear - D3 G En; lia | clear - D4 G En; lia | clear - D5 G En; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (mul_comba8_spec a_lo b_lo (limbs_firstn _ _ LA) (limbs_firstn _ _ LB) Lal Lbl) as (Lc1 & Ec1 & _).
    pose proof (KAFTER KB_after_R (FCELLS jb v144) m1 m2 R T 0%nat (mul_comba8 a_lo b_lo) _ CS8 eq_refl I MUc ltac:(rewrite Ec1; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc1 ltac:(rewrite Ec1; clear - En; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM WRa HAl HBl MUc WMc HS I MIc STc.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    destruct (KACC KB_R _ _ _ _ (2 * n)%nat 16%nat I2 ltac:(clear - En; lia)) as (_ & _ & _ & WRb).
    pose proof (KACC KB_a _ _ _ _ n (n - da)%nat I2 ltac:(clear - G; lia)) as HAh.
    pose proof (KACC KB_b _ _ _ _ n (n - db)%nat I2 ltac:(clear - G; lia)) as HBh.
    assert (Lah : length a_hi = 8%nat) by (rewrite slice_length; clear - G En Eda; lia).
    assert (Lbh : length b_hi = 8%nat) by (rewrite slice_length; clear - G En Edb; lia).
    do 5 zstep.
    eapply call_comba8 with (CS8 := CS8) (a := a_hi) (b := b_hi) (lo := lo) (SPz := (SP + -176)%Z)
                            (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact comba8_ok | apply slice_limbs; exact LA | apply slice_limbs; exact LB
      | exact Lah | exact Lbh | ulit | ulit | ulit | exact HAh | exact HBh | exact WRb
      | clear - D1 G En Eda; lia | clear - D2 G En Edb; lia | clear - G; lia
      | clear - D3 G En; lia | clear - D4 G En Eda; lia | clear - D5 G En Edb; lia | ].
    intros m3 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HS STc.
    destruct (mul_comba8_spec a_hi b_hi (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB) Lah Lbh) as (Lc2 & Ec2 & _).
    pose proof (KAFTER KB_after_R (FCELLS jb v144) m2 m3 _ T (2 * n)%nat (mul_comba8 a_hi b_hi) _ CS8 eq_refl I2 MUc ltac:(rewrite Ec2; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc2 ltac:(rewrite Ec2; clear - En; lia)) as I3.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM WRb HAh HBh MUc WMc HS I2 MIc STc D1 D2 D3 D4 D5.
    pose proof I3 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 5 zstep.
    remember (splice (splice R 0 (mul_comba8 a_lo b_lo)) (2 * n) (mul_comba8 a_hi b_hi)) as R2 eqn:ER2. clear ER2.
    first_add I3 OK G BND jb v144.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM I3.
    zstep.
    destruct neg.
    - zstep. if_false. eapply B_sub; [eassumption | exact OK | assumption].
    - zstep. if_true. eapply B_add; [eassumption | exact OK | assumption].
  Qed.

  Lemma pow_n : Nat.pow 2 k' = n. Proof. symmetry. exact Hn. Qed.

  (* [comment removed for export] *)
  Lemma B_gen : forall (neg : bool) jb v144 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    KBK (FCELLS jb v144) m1 R T ->
    gen2_ok RES k' n neg a b da db R T ->
    evt psegs POST (ST 0x109e04 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) a5
                       (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) (Z_to_bv 64 (if neg then 0 else 1)) x28 x29 x30 x31).
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
    do 8 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof DTA as D3. pose proof DTB as D4. pose proof DRT as D5.
    pose proof SEPR as D6. pose proof SEPT as D7. pose proof SEPA as D8. pose proof SEPB as D9. pose proof Hk' as HK.
    eapply call_rec with (CS8 := CS8) (k := k') (a := a_lo) (b := b_lo) (da := 0%nat) (db := 0%nat) (R := slice R 0 (2 * n)) (T := skipn (4 * n) T)
                         (lo := lo) (SPz := (SP + -176)%Z)
                         (RP := (rp + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact IH
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
      | rewrite <- HSK, Lal; clear - D8 G; lia | rewrite <- HSK, Lbl; clear - D9 G; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k' a_lo b_lo 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T) (limbs_firstn _ _ LA) (limbs_firstn _ _ LB) LRa LTp
                  ltac:(clear - HK; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(rewrite Lal, pow_n; clear; lia) ltac:(rewrite Lbl, pow_n; clear; lia) ltac:(rewrite ERa, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G; lia)) as MP.
    unfold mul_post in MP. unfold gen2_ok in OK.
    destruct (mul_recursive k' a_lo b_lo 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T)) as [rl p1]. cbn [fst snd] in *.
    destruct MP as (Lrl & Erl & _ & Lp1 & Ep1). rewrite ERa in Erl. rewrite ETp in Ep1.
    pose proof (KAFTER KB_after_RT (FCELLS jb v144) m1 m2 R T 0%nat rl (4 * n)%nat p1 _ _ (rec_stack CS8 k') eq_refl I MUc
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
    do 9 zstep.
    pose proof Hda as HDA. pose proof Hdb as HDB.
    eapply call_rec with (CS8 := CS8) (k := k') (a := a_hi) (b := b_hi) (da := da) (db := db) (R := slice R1 (2 * n) (2 * n)) (T := skipn (4 * n) T1)
                         (lo := lo) (SPz := (SP + -176)%Z)
                         (RP := (rp + 8 * Z.of_nat (2 * n))%Z) (AP := (ap + 8 * N)%Z) (BP := (bp + 8 * N)%Z) (TQ := (tq + 8 * Z.of_nat (4 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact IH
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
      | rewrite <- HSK, Lah; clear - D8 G; lia | rewrite <- HSK, Lbh; clear - D9 G; lia | ].
    intros m3 u0' u1' u2' v0' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k' a_hi b_hi da db (slice R1 (2 * n) (2 * n)) (skipn (4 * n) T1) (slice_limbs _ _ _ LA) (slice_limbs _ _ _ LB) LRb LTp
                  ltac:(clear - HK; lia) HDA HDB
                  ltac:(rewrite Lah, pow_n; reflexivity) ltac:(rewrite Lbh, pow_n; reflexivity) ltac:(rewrite ERb, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G; lia)) as MP.
    unfold mul_post in MP. unfold gen3_ok in OK.
    destruct (mul_recursive k' a_hi b_hi da db (slice R1 (2 * n) (2 * n)) (skipn (4 * n) T1)) as [rh p2]. cbn [fst snd] in *.
    destruct MP as (Lrh & Erh & _ & Lp2 & Ep2). rewrite ERb in Erh. rewrite ETp in Ep2.
    pose proof (KAFTER KB_after_RT (FCELLS jb v144) m2 m3 R1 T1 (2 * n)%nat rh (4 * n)%nat p2 _ _ (rec_stack CS8 k') eq_refl I2 MUc
                  ltac:(rewrite ERb, Erh; reflexivity) ltac:(rewrite ETp, Ep2; reflexivity) ltac:(rewrite <- HSK; clear - G; lia)
                  WMc MIc HSR HST STc Lrh Lp2 ltac:(rewrite Erh; clear; lia) ltac:(rewrite Ep2; clear - G; lia)) as I3.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HRb LRb ERb WRb HTp LTp ETp WTp HAh HBh MUc WMc HSR HST MIc STc I2.
    clear D1 D2 D3 D4 D5 D6 D7 D8 D9 HK HDA HDB.
    remember (splice R1 (2 * n) rh) as R2 eqn:ER2. remember (splice T1 (4 * n) p2) as T2 eqn:ET2. clear ER2 ET2 Lrh Erh Lp2 Ep2.
    pose proof I3 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 5 zstep.
    first_add I3 OK G BND jb v144.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM I3.
    zstep.
    destruct neg.
    - zstep. if_true. eapply B_sub; [eassumption | exact OK | assumption].
    - zstep. if_false. eapply B_add; [eassumption | exact OK | assumption].
  Qed.

  (* [comment removed for export] *)
  Lemma B_join_gen : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T ->
    (let '(tm, p0) := mul_recursive k' (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) in
     gen2_ok RES k' n neg a b da db R (splice T (2 * n) (tm ++ p0))) ->
    evt psegs POST (ST 0x109dd0 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) a5 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
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
    setreg 26%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) ltac:(f_equal; rewrite !Z.shiftl_mul_pow2 by lia; clear; lia).
    do 8 zstep.
    pose proof SEPT as D7. pose proof Hk' as HK.
    eapply call_rec with (CS8 := CS8) (k := k') (a := slice T 0 n) (b := slice T n n) (da := 0%nat) (db := 0%nat)
                         (R := slice T (2 * n) (2 * n)) (T := skipn (4 * n) T) (lo := lo) (SPz := (SP + -176)%Z)
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
      | rewrite <- HSK, ETa; clear - D7 G; lia | rewrite <- HSK, ETb; clear - D7 G; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HSR HST STc.
    pose proof (mul_recursive_spec k' (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) LTa LTb LTr LTp
                  ltac:(clear - HK; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(rewrite ETa, pow_n; clear; lia) ltac:(rewrite ETb, pow_n; clear; lia) ltac:(rewrite ETr, pow_n; reflexivity)
                  ltac:(rewrite ETp; clear - G; lia)) as MP.
    unfold mul_post in MP.
    destruct (mul_recursive k' (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T)) as [tm p0]. cbn [fst snd] in *.
    destruct MP as (Ltm & Etm & _ & Lp0 & Ep0). rewrite ETr in Etm. rewrite ETp in Ep0.
    pose proof (KAFTER KB_after_TT (FCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 m2 R T (2 * n)%nat (4 * n)%nat tm p0 _ _ (rec_stack CS8 k') eq_refl I MUc
                  ltac:(rewrite ETr, Etm; reflexivity) ltac:(rewrite ETp, Ep0; reflexivity) ltac:(rewrite Etm; clear; lia)
                  ltac:(rewrite <- HSK; clear - G; lia)
                  WMc MIc HSR HST STc Ltm Lp0 ltac:(rewrite Ep0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb HTr LTr ETr WTr HTp LTp ETp WTp MUc WMc HSR HST MIc STc I D7 HK.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    zstep.
    eapply B_gen; [exact I2 | exact OK].
  Qed.

  (* [comment removed for export] *)
  Lemma B_join : forall (neg : bool) jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x27 x28 x29 x30 x31,
    KBK (FCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 R T ->
    join_ok RES k' n neg a b da db R T ->
    evt psegs POST (ST 0x109d40 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 3 zstep. rewrite A3, land_even31 by (clear - G; lia).
    do 2 zstep.
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
    pose proof SEPT as D7.
    eapply call_comba8 with (CS8 := CS8) (a := slice T 0 n) (b := slice T n n) (lo := lo) (SPz := (SP + -176)%Z)
                            (RP := (tq + 8 * Z.of_nat (2 * n))%Z) (AP := (tq + 8 * Z.of_nat 0)%Z) (BP := (tq + 8 * N)%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | exact comba8_ok | exact LTa | exact LTb
      | rewrite ETa; exact En | rewrite ETb; exact En | ulit | ulit | ulit | exact HTa | exact HTb | exact WTr
      | clear - G En; lia | clear - G En; lia | clear - G; lia
      | clear - D7 G En; lia | clear - D7 G En; lia | clear - D7 G En; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (mul_comba8_spec (slice T 0 n) (slice T n n) LTa LTb ltac:(rewrite ETa; exact En) ltac:(rewrite ETb; exact En)) as (Lc & Ec & _).
    pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 (if neg then 0 else 1))) m1 m2 R T (2 * n)%nat _ _ CS8 eq_refl I MUc ltac:(rewrite Ec; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc Lc ltac:(rewrite Ec; clear - G En; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTa LTa ETa HTb LTb ETb WTr MUc WMc HS MIc STc I D7.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    zstep.
    eapply B_comba; [exact En | exact Eda | exact Edb | exact I2 | exact OK].
  Qed.

  (* [comment removed for export] *)
  Lemma munch_add_stack : forall (D L8 FB : Z) m1 m2, munch [(D, D + L8)]%Z m1 m2 -> munch [(D, D + L8); (FB - 0, FB)]%Z m1 m2.
  Proof. intros D L8 FB m1 m2 H. eapply munch_weaken; [|exact H]. unfold sub_fp. cbn [outside]. intros x Hx. tauto. Qed.

  (* [comment removed for export] *)
  Lemma B_zero_gen : forall jb v144 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31,
    KBK (FCELLS jb v144) m1 R T ->
    gen2_ok RES k' n false a b da db R (splice T (2 * n) (repeat 0%Z (2 * n))) ->
    evt psegs POST (ST 0x109c40 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) a5 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct (KACC KB_T _ _ _ _ (2 * n)%nat (2 * n)%nat I ltac:(clear - G; lia)) as (HTr & LTr & ETr & WTr).
    zstep. rewrite A3.
    replace ((2 * N) ≪ 1)%Z with (4 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    rewrite (bn_swrap32_small (4 * N)) by (clear - G; lia).
    do 2 zstep.
    setreg 26%Z (Z_to_bv 64 (tq + 8 * Z.of_nat (4 * n))) ltac:(f_equal; rewrite !Z.shiftl_mul_pow2 by lia; clear; lia).
    do 5 zstep.
    eapply call_memset0 with (L := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -176)%Z) (D := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | ulit | reflexivity | rewrite ETr; ulit | exact HTr | rewrite ETr; exact WTr | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    rewrite ETr in HS.
    pose proof (KAFTER KB_after_T (FCELLS jb v144) m1 m2 R T (2 * n)%nat (repeat 0%Z (2 * n)) _ 0%Z eq_refl I (munch_add_stack _ _ _ _ _ MUc)
                  ltac:(rewrite ETr, repeat_length; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc (limbs_repeat _ _ limb_0) ltac:(rewrite repeat_length; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTr LTr ETr WTr MUc WMc HS MIc STc I.
    do 2 zstep.
    eapply (B_gen false); [exact I2 | exact OK].
  Qed.

  (* [comment removed for export] *)
  Lemma B_zero : forall jb v144 m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x27 x28 x29 x30 x31,
    KBK (FCELLS jb v144) m1 R T ->
    zero_ok RES k' n a b da db R T ->
    evt psegs POST (ST 0x109c08 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 3 zstep. rewrite A3, land_even31 by (clear - G; lia).
    do 2 zstep.
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
    do 5 zstep.
    eapply call_memset0 with (L := slice T (2 * n) (2 * n)) (lo := lo) (SPz := (SP + -176)%Z) (D := (tq + 8 * Z.of_nat (2 * n))%Z);
      [ exact ESP176 | ret_even | exact ST | exact MI | ulit | reflexivity | rewrite ETr, En; reflexivity | exact HTr | rewrite ETr; exact WTr | ].
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    rewrite ETr in HS.
    pose proof (KAFTER KB_after_T (FCELLS jb v144) m1 m2 R T (2 * n)%nat (repeat 0%Z (2 * n)) _ 0%Z eq_refl I (munch_add_stack _ _ _ _ _ MUc)
                  ltac:(rewrite ETr, repeat_length; reflexivity)
                  ltac:(clear - G; lia) WMc MIc HS STc (limbs_repeat _ _ limb_0) ltac:(rewrite repeat_length; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HTr LTr ETr WTr MUc WMc HS MIc STc I.
    do 2 zstep.
    eapply (B_comba false); [exact En | exact Eda | exact Edb | exact I2 | exact OK].
  Qed.

  (* [comment removed for export] *)
  Notation t1_of sw := (fst (if sw then sub_part_words b_hi b_lo (n - db) else sub_part_words b_lo b_hi (n - db))).

  Ltac sp2_call I G BND sw :=
    let HBl := fresh "HBl" in let HBh := fresh "HBh" in let WTn := fresh "WTn" in
    let D4 := fresh "D4" in let D7 := fresh "D7" in let D9 := fresh "D9" in
    pose proof (KACC KB_b _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HBl;
    pose proof (KACC KB_b _ _ _ _ n (n - db)%nat I ltac:(clear - G; lia)) as HBh;
    destruct (KACC KB_T _ _ _ _ n n I ltac:(clear - G; lia)) as (_ & _ & _ & WTn);
    pose proof DTB as D4; pose proof SEPT as D7; pose proof SEPB as D9;
    lazymatch goal with ST : stk psegs ?m1 lo _, MI : mem_inv psegs ?m1 |- _ =>
    lazymatch sw with
    | false =>
      eapply call_sub_part_words with (a := b_lo) (b := b_hi) (cl := (n - db)%nat) (da := db) (db := 0%nat) (lo := lo) (SPz := (SP + -176)%Z)
                                      (RP := (tq + 8 * N)%Z) (AP := (bp + 8 * Z.of_nat 0)%Z) (BP := (bp + 8 * N)%Z);
        [ exact ESP176 | ret_even | exact ST | exact MI | apply limbs_firstn; exact LB | apply slice_limbs; exact LB
        | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | f_equal; clear; lia
        | exact HBl | exact HBh | replace (n - db + db + 0)%nat with n by (clear - G; lia); exact WTn
        | rewrite length_firstn; clear - D4 G; lia | rewrite slice_length by (clear - G; lia); clear - D4 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite length_firstn; clear - D9 G; lia | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | ]
    | true =>
      eapply call_sub_part_words with (a := b_hi) (b := b_lo) (cl := (n - db)%nat) (da := 0%nat) (db := db) (lo := lo) (SPz := (SP + -176)%Z)
                                      (RP := (tq + 8 * N)%Z) (AP := (bp + 8 * N)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
        [ exact ESP176 | ret_even | exact ST | exact MI | apply slice_limbs; exact LB | apply limbs_firstn; exact LB
        | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | rewrite A5; f_equal; clear; lia
        | exact HBh | exact HBl | replace (n - db + 0 + db)%nat with n by (clear - G; lia); exact WTn
        | rewrite slice_length by (clear - G; lia); clear - D4 G; lia | rewrite length_firstn; clear - D4 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | rewrite length_firstn; clear - D9 G; lia | ]
    end end.

  (* [comment removed for export] *)
  Lemma B_sp2_pos : forall (sw : bool) jb m1 R T x1 x5 x6 x7 x15 x16 x17 x20 x28 x29 x30 x31,
    KBK (FCELLS jb (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n false a b da db R (splice T n (t1_of sw)) ->
    evt psegs POST (ST 0x109d3c m1 x1 x5 x6 x7 a0 (Z_to_bv 64 (tq + 8 * N))
                       (if sw then Z_to_bv 64 (bp + 8 * N) else a2) (if sw then a2 else Z_to_bv 64 (bp + 8 * N))
                       (Z_to_bv 64 (N - Z.of_nat db)) (if sw then a5 else Z_to_bv 64 (Z.of_nat db))
                       x15 x16 x17 x20 a5 (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct sw.
    - zstep. sp2_call I G BND true.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      destruct (sub_part_words_fst b_hi b_lo (n - db) (slice_limbs _ _ _ LB) (limbs_firstn _ _ LB)
                  ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
      rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
      pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 1)) m1 m2 R T n _ _ 80%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      eapply (B_join false); [exact I2 | exact OK].
    - zstep. sp2_call I G BND false.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      destruct (sub_part_words_fst b_lo b_hi (n - db) (limbs_firstn _ _ LB) (slice_limbs _ _ _ LB)
                  ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
      rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
      pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 1)) m1 m2 R T n _ _ 80%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      eapply (B_join false); [exact I2 | exact OK].
  Qed.

  (* [comment removed for export] *)
  Lemma B_sp2_neg : forall (sw : bool) jb m1 R T x1 x5 x6 x7 x15 x16 x17 x20 x28 x29 x30 x31,
    KBK (FCELLS jb (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n true a b da db R (splice T n (t1_of sw)) ->
    evt psegs POST (ST 0x109d00 m1 x1 x5 x6 x7 a0 (Z_to_bv 64 (tq + 8 * N))
                       (if sw then Z_to_bv 64 (bp + 8 * N) else a2) (if sw then a2 else Z_to_bv 64 (bp + 8 * N))
                       (Z_to_bv 64 (N - Z.of_nat db)) (if sw then a5 else Z_to_bv 64 (Z.of_nat db))
                       x15 x16 x17 x20 a5 (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    assert (CONT : forall m2 T' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
               KBK (FCELLS jb (Z_to_bv 64 1)) m2 R T' -> join_ok RES k' n true a b da db R T' ->
               evt psegs POST (ST 0x109d04 m2 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5
                                  (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31)).
    { clear I OK. intros m2 T' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 I2 OK2.
      pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & ST & MI & _ & _).
      pose proof (munch_refl [(SP + -176, SP + -176 + 176)]%Z m2) as MUF. pose proof (wmono_refl psegs m2) as WMF.
      zstep. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store.
      pose proof (KFRAME _ _ m2 _ R T' I2 MUF WMF MI ST FR) as I3.
      zstep.
      eapply (B_join true); [exact I3 | exact OK2]. }
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    destruct sw.
    - zstep. sp2_call I G BND true.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      destruct (sub_part_words_fst b_hi b_lo (n - db) (slice_limbs _ _ _ LB) (limbs_firstn _ _ LB)
                  ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
      rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
      pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 1)) m1 m2 R T n _ _ 80%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      eapply CONT; [exact I2 | exact OK].
    - zstep. sp2_call I G BND false.
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
      destruct (sub_part_words_fst b_lo b_hi (n - db) (limbs_firstn _ _ LB) (slice_limbs _ _ _ LB)
                  ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt1 & Et1 & _).
      rewrite slice_length, length_firstn in Et1 by (clear - G; lia).
      pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 1)) m1 m2 R T n _ _ 80%Z eq_refl I MUc ltac:(rewrite Et1; f_equal; clear - G; lia)
                    ltac:(clear - G; lia) WMc MIc HS STc Lt1 ltac:(rewrite Et1; clear - G; lia)) as I2.
      eapply CONT; [exact I2 | exact OK].
  Qed.

  (* [comment removed for export] *)
  Notation t0_of sw := (fst (if sw then sub_part_words a_hi a_lo (n - da) else sub_part_words a_lo a_hi (n - da))).

  Ltac sp1_call I G BND sw :=
    let HAl := fresh "HAl" in let HAh := fresh "HAh" in let WTn := fresh "WTn" in
    let D3 := fresh "D3" in let D7 := fresh "D7" in let D8 := fresh "D8" in
    pose proof (KACC KB_a _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as HAl;
    pose proof (KACC KB_a _ _ _ _ n (n - da)%nat I ltac:(clear - G; lia)) as HAh;
    destruct (KACC KB_T _ _ _ _ 0%nat n I ltac:(clear - G; lia)) as (_ & _ & _ & WTn);
    pose proof DTA as D3; pose proof SEPT as D7; pose proof SEPA as D8;
    lazymatch goal with ST : stk psegs ?m1 lo _, MI : mem_inv psegs ?m1 |- _ =>
    lazymatch sw with
    | false =>
      eapply call_sub_part_words with (a := a_lo) (b := a_hi) (cl := (n - da)%nat) (da := da) (db := 0%nat) (lo := lo) (SPz := (SP + -176)%Z)
                                      (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
        [ exact ESP176 | ret_even | exact ST | exact MI | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
        | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | f_equal; clear; lia
        | exact HAl | exact HAh | replace (n - da + da + 0)%nat with n by (clear - G; lia); exact WTn
        | rewrite length_firstn; clear - D3 G; lia | rewrite slice_length by (clear - G; lia); clear - D3 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite length_firstn; clear - D8 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia | ]
    | true =>
      eapply call_sub_part_words with (a := a_hi) (b := a_lo) (cl := (n - da)%nat) (da := 0%nat) (db := da) (lo := lo) (SPz := (SP + -176)%Z)
                                      (RP := (tq + 8 * Z.of_nat 0)%Z) (AP := (ap + 8 * N)%Z) (BP := (ap + 8 * Z.of_nat 0)%Z);
        [ exact ESP176 | ret_even | exact ST | exact MI | apply slice_limbs; exact LA | apply limbs_firstn; exact LA
        | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
        | clear - G; lia | ulit | ulit | ulit | ulit | rewrite A4; f_equal; clear; lia
        | exact HAh | exact HAl | replace (n - da + 0 + da)%nat with n by (clear - G; lia); exact WTn
        | rewrite slice_length by (clear - G; lia); clear - D3 G; lia | rewrite length_firstn; clear - D3 G; lia
        | clear - G; lia
        | clear - D7 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia | rewrite length_firstn; clear - D8 G; lia | ]
    end end.

  (* [comment removed for export] *)
  Lemma B_case_p2 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31,
    KBK (FCELLS jb (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n true a b da db R (splice (splice T 0 (t0_of false)) n (t1_of false)) ->
    evt psegs POST (ST 0x109c68 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 6 zstep. sp1_call I G BND false.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_lo a_hi (n - da) (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA)
                ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 1)) m1 m2 R T 0%nat _ _ 80%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 3 zstep. replace (bv_swrap 32 (0 - bv_unsigned a5)) with (Z.of_nat db) by (rewrite A5; symmetry; apply negw_dn; exact Hdb).
    do 4 zstep.
    eapply (B_sp2_neg false); [exact I2 | exact OK].
  Qed.

  (* [comment removed for export] *)
  Lemma B_case_m4 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31,
    KBK (FCELLS jb (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n false a b da db R (splice (splice T 0 (t0_of true)) n (t1_of false)) ->
    evt psegs POST (ST 0x109c9c m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 6 zstep. sp1_call I G BND true.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_hi a_lo (n - da) (slice_limbs _ _ _ LA) (limbs_firstn _ _ LA)
                ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 1)) m1 m2 R T 0%nat _ _ 80%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 3 zstep. replace (bv_swrap 32 (0 - bv_unsigned a5)) with (Z.of_nat db) by (rewrite A5; symmetry; apply negw_dn; exact Hdb).
    do 4 zstep.
    eapply (B_sp2_pos false); [exact I2 | exact OK].
  Qed.

  (* [comment removed for export] *)
  Lemma B_case_m2 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31,
    KBK (FCELLS jb (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n true a b da db R (splice (splice T 0 (t0_of true)) n (t1_of true)) ->
    evt psegs POST (ST 0x109cd0 m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 6 zstep. sp1_call I G BND true.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_hi a_lo (n - da) (slice_limbs _ _ _ LA) (limbs_firstn _ _ LA)
                ltac:(left; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 1)) m1 m2 R T 0%nat _ _ 80%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 6 zstep.
    eapply (B_sp2_neg true); [exact I2 | exact OK].
  Qed.

  (* [comment removed for export] *)
  Lemma B_case_p4 : forall jb m1 R T x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31,
    KBK (FCELLS jb (Z_to_bv 64 1)) m1 R T ->
    join_ok RES k' n false a b da db R (splice (splice T 0 (t0_of false)) n (t1_of true)) ->
    evt psegs POST (ST 0x109d0c m1 x1 x5 x6 x7 a0 x10 x11 x12 x13 x14 x15 x16 x17 x20 a5
                       (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) (Z_to_bv 64 (bp + 8 * N)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I OK.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    do 6 zstep. sp1_call I G BND false.
    intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (sub_part_words_fst a_lo a_hi (n - da) (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA)
                ltac:(right; rewrite slice_length, length_firstn; clear - G; lia)) as (Lt0 & Et0 & _).
    rewrite slice_length, length_firstn in Et0 by (clear - G; lia).
    pose proof (KAFTER KB_after_T (FCELLS jb (Z_to_bv 64 1)) m1 m2 R T 0%nat _ _ 80%Z eq_refl I MUc ltac:(rewrite Et0; f_equal; clear - G; lia)
                  ltac:(clear - G; lia) WMc MIc HS STc Lt0 ltac:(rewrite Et0; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM MUc WMc HS MIc STc I.
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM).
    do 6 zstep.
    eapply (B_sp2_pos true); [exact I2 | exact OK].
  Qed.

  (* [comment removed for export] *)
  Notation FCELLS0 jb72 := [CB 72 jb72; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma kara_body : forall jb72 m1 R T x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x27 x28 x29 x30 x31,
    KBK (FCELLS0 jb72) m1 R T ->
    match rec_diffs a_lo a_hi b_lo b_hi (n - da) (n - db) (cmp_part_words a_lo a_hi (n - da)) (cmp_part_words b_hi b_lo (n - db)) with
    | Some (t0', t1', neg) => join_ok RES k' n neg a b da db R (splice (splice T 0 t0') n t1')
    | None => zero_ok RES k' n a b da db R T
    end ->
    evt psegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp x5 x6 x7 sp a0 (Z_to_bv 64 15) x11 x12 x13 x14 x15 x16 x17
               a3 a6 x20 x21 a2 a1 a5 a4 (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x109b68) fc None m1 (seg_rom psegs)).
  Proof.
    intros until x31. intros I OK.
    pose proof geom as G.
    pose proof (KACC KB_bounds _ _ _ _ I ltac:(clear - G; lia) ltac:(clear - G; lia)) as BND.
    pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    pose proof (munch_refl [(SP + -176, SP + -176 + 176)]%Z m1) as MUF. pose proof (wmono_refl psegs m1) as WMF.
    do 3 zstep. rewrite A3, half_n2 by (clear - G; lia).
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
    eapply call_cmp_part_words with (a := a_lo) (b := a_hi) (cl := (n - da)%nat) (da := da) (db := 0%nat) (lo := lo) (SPz := (SP + -176)%Z)
                                    (AP := (ap + 8 * Z.of_nat 0)%Z) (BP := (ap + 8 * N)%Z);
      [ exact ESP176 | ret_even | exact STK | exact MI | apply limbs_firstn; exact LA | apply slice_limbs; exact LA
      | rewrite length_firstn; clear - G; lia | rewrite slice_length; clear - G; lia | right; reflexivity
      | clear - G; lia | ulit | ulit | ulit | f_equal; clear; lia
      | exact HAl | exact HAh | clear - G; lia
      | rewrite length_firstn; clear - D8 G; lia | rewrite slice_length by (clear - G; lia); clear - D8 G; lia | ].
    intros m3 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc STc.
    lazymatch type of I2 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_ro cells mm m3 R T 16%Z eq_refl I2 MUc ltac:(clear - G; lia) WMc MIc STc) as I3 end.
    clear FR STK MI HAl HAh D8 MUc WMc MIc STc I2.
    pose proof I3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    lazymatch type of MI with mem_inv _ ?mm => pose proof (munch_refl [(SP + -176, SP + -176 + 176)]%Z mm) as MUF; pose proof (wmono_refl psegs mm) as WMF end.
    remember (cmp_part_words a_lo a_hi (n - da)) as c1 eqn:Ec1.
    do 9 zstep.
    lazymatch type of I3 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ _ =>
      lazymatch type of MI with mem_inv _ ?mm' => pose proof (KFRAME _ _ mm mm' R T I3 MUF WMF MI STK FR) as I4 end end.
    clear I3 MUF WMF.
    pose proof (KACC KB_b _ _ _ _ 0%nat n I4 ltac:(clear - G; lia)) as HBl.
    pose proof (KACC KB_b _ _ _ _ n (n - db)%nat I4 ltac:(clear - G; lia)) as HBh.
    pose proof SEPB as D9.
    eapply call_cmp_part_words with (a := b_hi) (b := b_lo) (cl := (n - db)%nat) (da := 0%nat) (db := db) (lo := lo) (SPz := (SP + -176)%Z)
                                    (AP := (bp + 8 * N)%Z) (BP := (bp + 8 * Z.of_nat 0)%Z);
      [ exact ESP176 | ret_even | exact STK | exact MI | apply slice_limbs; exact LB | apply limbs_firstn; exact LB
      | rewrite slice_length; clear - G; lia | rewrite length_firstn; clear - G; lia | left; reflexivity
      | clear - G; lia | ulit | ulit | ulit | rewrite A5; f_equal; clear; lia
      | exact HBh | exact HBl | clear - G; lia
      | rewrite slice_length by (clear - G; lia); clear - D9 G; lia | rewrite length_firstn; clear - D9 G; lia | ].
    intros m5 u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' MUc WMc MIc STc.
    lazymatch type of I4 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cells ?mm _ _ =>
      pose proof (KAFTER KB_after_ro cells mm m5 R T 16%Z eq_refl I4 MUc ltac:(clear - G; lia) WMc MIc STc) as I5 end.
    clear FR STK MI HBl HBh D9 MUc WMc MIc STc I4.
    pose proof I5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & STK & MI & _ & _).
    pose proof (munch_refl [(SP + -176, SP + -176 + 176)]%Z m5) as MUF. pose proof (wmono_refl psegs m5) as WMF.
    remember (cmp_part_words b_hi b_lo (n - db)) as c2 eqn:Ec2.
    do 4 zstep. change (Z_to_le_bytes 8 1) with (le8 (Z_to_bv 64 1)). mem_after_store.
    do 3 zstep.
    zstep. rewrite A3. replace ((2 * N) ≪ 3)%Z with (16 * N)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    zstep.
    lazymatch type of I5 with KB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ _ =>
      lazymatch type of MI with mem_inv _ ?mm' => pose proof (KFRAME _ _ mm mm' R T I5 MUF WMF MI STK FR) as I6 end end.
    clear I5 MUF WMF FR STK.
    assert (Hc1 : (c1 = -1 \/ c1 = 0 \/ c1 = 1)%Z).
    { rewrite Ec1, (cmp_part_words_spec a_lo a_hi (n - da) (limbs_firstn _ _ LA) (slice_limbs _ _ _ LA))
        by (right; rewrite slice_length, length_firstn; clear - G; lia). apply sgn3_range. }
    assert (Hc2 : (c2 = -1 \/ c2 = 0 \/ c2 = 1)%Z).
    { rewrite Ec2, (cmp_part_words_spec b_hi b_lo (n - db) (slice_limbs _ _ _ LB) (limbs_firstn _ _ LB))
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma addw_dn_dn : forall da db : nat, (da <= 1)%nat -> (db <= 1)%nat ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 (- Z.of_nat db)) + bv_unsigned (Z_to_bv 64 (- Z.of_nat da))) = (- (Z.of_nat da + Z.of_nat db))%Z.
Proof.
  intros da db Hda Hdb. assert (Ea : (da = 0 \/ da = 1)%nat) by lia. assert (Eb : (db = 0 \/ db = 1)%nat) by lia.
  destruct Ea as [-> | ->]; destruct Eb as [-> | ->]; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fill_len : forall da db : nat, (da <= 1)%nat -> (db <= 1)%nat ->
  ((bv_swrap 32 (0 - (- (Z.of_nat da + Z.of_nat db)) mod 18446744073709551616) mod 18446744073709551616) ≪ 3 = 8 * Z.of_nat (da + db))%Z.
Proof.
  intros da db Hda Hdb. assert (Ea : (da = 0 \/ da = 1)%nat) by lia. assert (Eb : (db = 0 \/ db = 1)%nat) by lia.
  destruct Ea as [-> | ->]; destruct Eb as [-> | ->]; vm_compute; reflexivity.
Qed.

Lemma fill_off : forall x (da db : nat), (da <= 1)%nat -> (db <= 1)%nat -> (2 <= x < 268435456)%Z ->
  ((bv_swrap 32 (x ≪ 1 mod 18446744073709551616 +
                 (bv_unsigned (Z_to_bv 64 (- Z.of_nat da)) + bv_unsigned (Z_to_bv 64 (- Z.of_nat db))) mod 18446744073709551616)
    mod 18446744073709551616) ≪ 3 = 8 * (2 * x - Z.of_nat da - Z.of_nat db))%Z.
Proof.
  intros x da db Hda Hdb Hx. assert (Ea : (da = 0 \/ da = 1)%nat) by lia. assert (Eb : (db = 0 \/ db = 1)%nat) by lia.
  assert (E0 : bv_unsigned (Z_to_bv 64 (- Z.of_nat 0)) = 0%Z) by (vm_compute; reflexivity).
  assert (E1 : bv_unsigned (Z_to_bv 64 (- Z.of_nat 1)) = 18446744073709551615%Z) by (vm_compute; reflexivity).
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z. change (2 ^ 3)%Z with 8%Z.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z.
  destruct Ea as [-> | ->]; destruct Eb as [-> | ->]; rewrite ?E0, ?E1; change (Z.of_nat 0) with 0%Z; change (Z.of_nat 1) with 1%Z;
    Z.div_mod_to_equations; lia.
Qed.

Lemma pow2_Z_bounds : forall k, (1 <= k <= 26)%nat -> (2 <= Z.of_nat (Nat.pow 2 k) <= 67108864)%Z.
Proof.
  intros k Hk. rewrite Nat2Z.inj_pow. change (Z.of_nat 2) with 2%Z. split.
  - change 2%Z with (2 ^ 1)%Z at 1. apply Z.pow_le_mono_r; lia.
  - change 67108864%Z with (2 ^ 26)%Z. apply Z.pow_le_mono_r; lia.
Qed.

Section Main.
  Variable CS8 : Z.
  Hypothesis CS8_0 : (0 <= CS8)%Z.
  Hypothesis comba8_ok : comba8_spec CS8.

  Lemma rec_body : forall k, (forall k', k = S k' -> rec_spec_at CS8 k') -> rec_spec_at CS8 k.
  Proof.
    intros k IHk. unfold rec_spec_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a b da db R T lo
           LA LB LR LT Hk Hda Hdb HLA HLB HLR HLT A3 A4 A5 RA RB RR RT WR WT DRA DRB DTA DTB DRT STK LO SEPR SEPT SEPA SEPB MI0.
    remember (Nat.pow 2 k) as N2 eqn:EN2.
    assert (HN2 : (2 <= Z.of_nat N2 <= 67108864)%Z) by (subst N2; apply pow2_Z_bounds; exact Hk).
    remember (rec_stack CS8 k - 176)%Z as SK eqn:ESK.
    assert (HSK : (320 <= SK /\ CS8 <= SK)%Z) by (subst SK; unfold rec_stack; lia).
    assert (ERS : rec_stack CS8 k = (176 + SK)%Z) by (subst SK; lia).
    rewrite ERS in LO, SEPR, SEPT, SEPA, SEPB |- *.
    pose proof (proj1 STK) as LO0.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA. pose proof (limbs_at_bound _ _ _ _ RB) as BB.
    pose proof (wr_at_below psegs m _ _ MI0 WR ltac:(rewrite HLR; lia)) as BR. pose proof (wr_at_below psegs m _ _ MI0 WT) as BT.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *. unfold UTOP in *.
    (* [comment removed for export] *)
    assert (GEO : hide ((bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0) /\
                        (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a0) /\
                        (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a6) /\
                        (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a6) /\
                        (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned a6 \/ bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned a0) /\
                        (bv_unsigned a0 + 8 * Z.of_nat (length R) <= bv_unsigned sp - (176 + SK) \/ bv_unsigned sp <= bv_unsigned a0) /\
                        (bv_unsigned a6 + 8 * Z.of_nat (length T) <= bv_unsigned sp - (176 + SK) \/ bv_unsigned sp <= bv_unsigned a6) /\
                        (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - (176 + SK) \/ bv_unsigned sp <= bv_unsigned a1) /\
                        (bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned sp - (176 + SK) \/ bv_unsigned sp <= bv_unsigned a2) /\
                        length a = (N2 - da)%nat /\ length b = (N2 - db)%nat /\ length R = (2 * N2)%nat /\ (scratch_rec k <= length T)%nat)%Z).
    { apply hide_intro. repeat split; assumption. }
    rewrite HLR in WR.
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB HLA HLB HLR HLT.
    pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length R)); (bv_unsigned a6, bv_unsigned a6 + 8 * Z.of_nat (length T));
                            (bv_unsigned sp - (176 + SK), bv_unsigned sp)]%Z m) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MUF. pose proof (wmono_refl psegs m) as WM.
    assert (LO1 : (lo <= bv_unsigned sp - 176)%Z) by (clear - LO HSK; lia).
    carve_frame 176%nat STK.
    do 24 zstep.
    (* [comment removed for export] *)
    pose proof (hide_elim _ GEO) as (DRA & DRB & DTA & DTB & DRT & SEPR & SEPT & SEPA & SEPB & HLA' & HLB' & HLR' & HLT').
    assert (RA1 : limbs_at psegs m0 (bv_unsigned a1) a) by (eapply limbs_at_transport; [exact RA | exact MUF | cbn [disjoint_from]; clear - SEPA HSK; lia]).
    assert (RB1 : limbs_at psegs m0 (bv_unsigned a2) b) by (eapply limbs_at_transport; [exact RB | exact MUF | cbn [disjoint_from]; clear - SEPB HSK; lia]).
    assert (RR1 : limbs_at psegs m0 (bv_unsigned a0) R) by (eapply limbs_at_transport; [exact RR | exact MUF | cbn [disjoint_from]; clear - SEPR HSK; lia]).
    assert (RT1 : limbs_at psegs m0 (bv_unsigned a6) T) by (eapply limbs_at_transport; [exact RT | exact MUF | cbn [disjoint_from]; clear - SEPT HSK; lia]).
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
          | clear - DRA LR16 La8; lia | clear - DRB LR16 Lb8; lia | exact STK | clear - LO HSK; lia
          | clear - SEPR LR16 HSK; lia | clear - SEPA La8 HSK; lia | clear - SEPB Lb8 HSK; lia | exact MI0 ]. }
      intros ms' PO. unfold vl_post in PO.
      destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
      exists u0, u1, u2, v0, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m2.
      split; [exact E|].
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx.
               clear - Hx LR16 HSK. lia. }
      split; [eapply wmono_trans; [exact WM | exact WMc]|]. split; [exact MIc|].
      rewrite mul_recursive_comba by (rewrite <- EN2; exact E8). cbn [fst snd].
      destruct (mul_comba8_spec a b LA LB La8 Lb8) as (_ & Lc & _).
      rewrite !firstn_all2 by (clear - La8 Lb8; lia). rewrite splice_all by (rewrite Lc, LR16; reflexivity).
      split; [exact HS|]. split; [|exact STc].
      eapply limbs_at_transport; [exact RT1 | exact MUc | cbn [disjoint_from]; clear - DRT SEPT LR16 HSK; lia]. }
    intros NC.
    zstep.
    zstep.

    assert (L15 : (bv_unsigned (Z_to_bv 64 15) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (L3 : (bv_unsigned a3 < 9223372036854775808)%Z) by (rewrite A3; clear - HN2; lia).
    rewrite (lts_words_small (Z_to_bv 64 15) a3 L15 L3). clear L15 L3.
    rewrite A3. if_cases K16; zify_cond K16.
    { (* [comment removed for export] *)
      destruct k as [|k']; [exfalso; cbn in EN2; clear - EN2 K16; lia|].
      remember (Nat.pow 2 k') as n eqn:En.
      assert (EN : N2 = (2 * n)%nat) by (rewrite EN2, En; cbn [Nat.pow]; clear; lia).
      pose proof (hide_elim _ GEO) as (DRA & DRB & DTA & DTB & DRT & SEPR & SEPT & SEPA & SEPB & HLA' & HLB' & HLR' & HLT').
      assert (ELR : length R = (4 * n)%nat) by (clear - HLR' EN; lia).
      assert (ESK' : SK = rec_stack CS8 k').
      { clear - ESK. unfold rec_stack in *. rewrite !Nat2Z.inj_succ in *. lia. }
      assert (PRE : kara_pre CS8 k' n da db (length a) (length b) (length T) SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1)
                             (bv_unsigned a2) (bv_unsigned sp) lo).
      { unfold kara_pre. rewrite <- ELR.
        assert (Hk1 : (1 <= k')%nat) by (destruct k' as [|k'']; [cbn in En; exfalso; clear - En EN K16; lia | clear; lia]).
        split; [exact En|]. split; [clear - Hk Hk1; lia|]. split; [clear - K16 EN; lia|]. split; [clear - HN2 EN; lia|].
        split; [exact Hda|]. split; [exact Hdb|]. split; [clear - HLA' EN; lia|]. split; [clear - HLB' EN; lia|].
        split. { rewrite scratch_rec_S in HLT' by (rewrite <- EN2; clear - K16; lia). rewrite <- EN2 in HLT'. clear - HLT' EN ELR. lia. }
        split; [exact ESK'|].
        split; [exact DRA|]. split; [exact DRB|]. split; [exact DTA|]. split; [exact DTB|]. split; [exact DRT|].
        split; [clear - SEPR; lia|]. split; [clear - SEPT; lia|]. split; [clear - SEPA; lia|]. split; [clear - SEPB; lia|].
        split; [clear - LO; lia | exact LO0]. }
      replace (Z.of_nat (length R)) with (Z.of_nat (4 * n)) by (rewrite ELR; reflexivity).
      eapply (kara_body CS8 CS8_0 comba8_ok k' (IHk k' eq_refl)) with (n := n) (nT := length T) (SK := SK) (da := da) (db := db);
        [ exact PRE | exact LA | exact LB | rewrite A3, EN; clear; lia | exact A4 | exact A5 | | ].
      - unfold KB. split; [exact LR|]. split; [exact LT|]. split; [exact ELR|]. split; [reflexivity|].
        split; [exact RR1|]. split; [exact RT1|]. split; [exact RA1|]. split; [exact RB1|].
        split; [rewrite EN in WR; replace (4 * n)%nat with (2 * (2 * n))%nat by (clear; lia); exact WR|]. split; [exact WT|].
        split; [exact FR|]. split; [exact STK|]. split; [exact MI0|].
        split; [|exact WM]. unfold KWfin. rewrite <- ELR. replace (bv_unsigned sp - 176 - SK)%Z with (bv_unsigned sp - (176 + SK))%Z by (clear; lia). exact MU.
      - rewrite En. apply rec_staged; try assumption; rewrite <- ?EN2; try assumption.
        clear - K16. lia. }
    clear IHk.
    (* [comment removed for export] *)
    do 2 zstep.
    replace (bv_swrap 32 (bv_unsigned a4 + bv_unsigned a3)) with (Z.of_nat N2 - Z.of_nat da)%Z
      by (rewrite A4, A3, Z.add_comm; symmetry; apply addw_dn; [exact Hda | clear - HN2; lia]).
    replace (bv_swrap 32 (bv_unsigned a5 + bv_unsigned a3)) with (Z.of_nat N2 - Z.of_nat db)%Z
      by (rewrite A5, A3, Z.add_comm; symmetry; apply addw_dn; [exact Hdb | clear - HN2; lia]).
    do 4 zstep.
    pose proof (hide_elim _ GEO) as (DRA & DRB & DTA & DTB & DRT & SEPR & SEPT & SEPA & SEPB & HLA' & HLB' & HLR' & HLT').
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = (bv_unsigned sp + -176)%Z).
    { apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
      pose proof (zr_word sp) as RS. unfold inr64 in RS. change (2 ^ 64)%Z with 18446744073709551616%Z in RS. clear - RS LO0 LO1. lia. }
    assert (Lab : (Z.of_nat (length a) = Z.of_nat N2 - Z.of_nat da /\ Z.of_nat (length b) = Z.of_nat N2 - Z.of_nat db /\ Z.of_nat (length R) = 2 * Z.of_nat N2)%Z)
      by (clear - HLA' HLB' HLR' HN2 Hda Hdb; lia).
    eapply call_mul_normal with (a := a) (b := b) (lo := lo) (SPz := (bv_unsigned sp + -176)%Z)
                                (RP := bv_unsigned a0) (AP := bv_unsigned a1) (BP := bv_unsigned a2);
      [ exact ESP | apply ret_pc_even; [lia | reflexivity] | exact STK | exact MI0 | exact LA | exact LB | clear - Lab HN2; lia
      | reflexivity | reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - HN2 Hda; lia); clear - Lab; lia
      | reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - HN2 Hdb; lia); clear - Lab; lia
      | exact RA1 | exact RB1
      | pose proof (wr_at_sub psegs m0 _ _ 0 (8 * (Z.of_nat (length a) + Z.of_nat (length b))) WR ltac:(lia) ltac:(lia) ltac:(clear - Lab Hda Hdb; lia)) as X;
        rewrite Z.add_0_r in X; exact X
      | clear - DRA Lab; lia | clear - DRB Lab; lia | clear - LO HSK; lia
      | clear - SEPR Lab HSK; lia | clear - SEPA HSK; lia | clear - SEPB HSK; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (mul_normal_spec a b LA LB) as (LMN & _ & EMN).
    assert (EMN' : length (mul_normal a b) = (length a + length b)%nat).
    { rewrite EMN. destruct (Nat.eqb_spec (length a) 0) as [E|_]; [exfalso; clear - E Lab HN2 Hda; lia|].
      destruct (Nat.eqb_spec (length b) 0) as [E|_]; [exfalso; clear - E Lab HN2 Hdb; lia|]. reflexivity. }
    clear EMN.
    (* [comment removed for export] *)
    assert (RR2 : limbs_at psegs m2 (bv_unsigned a0) (splice R 0 (mul_normal a b))).
    { eapply (limbs_at_splice psegs _ m0 m2 (bv_unsigned a0) R 0 (mul_normal a b) RR1 MUc).
      - rewrite EMN'. clear - Lab Hda Hdb. lia.
      - change (Z.of_nat 0) with 0%Z. rewrite Z.mul_0_r, Z.add_0_r. exact HS.
      - cbn [disjoint_from]. clear - SEPR Lab HSK. lia.
      - cbn [disjoint_from]. rewrite EMN'. clear - SEPR Lab HSK Hda Hdb. lia. }
    assert (RT2 : limbs_at psegs m2 (bv_unsigned a6) T)
      by (eapply limbs_at_transport; [exact RT1 | exact MUc | cbn [disjoint_from]; clear - DRT SEPT Lab HSK; lia]).
    assert (WR2 : wr_at psegs m2 (bv_unsigned a0) (8 * Z.of_nat (2 * N2))) by (eapply wr_at_transport; [exact WR | exact WMc]).
    assert (FR2 := rw_cells_transport psegs _ m0 m2 _ _ FR MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - SEPR Lab HSK; lia)).
    assert (MU2 : munch [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (length R)); (bv_unsigned a6, bv_unsigned a6 + 8 * Z.of_nat (length T));
                         (bv_unsigned sp - (176 + SK), bv_unsigned sp)]%Z m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx Lab HSK Hda Hdb. lia. }
    assert (WM2 := wmono_trans psegs _ _ _ WM WMc).
    assert (Lab2 : length a = (N2 - da)%nat /\ length b = (N2 - db)%nat) by (split; assumption).
    clear MU WM MUc WMc FR WR RR1 RT1 RA1 RB1 STK MI0 HS. rename FR2 into FR.
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB HLA' HLB' HLR' HLT'.
    assert (EMOD : mul_recursive k a b da db R T =
                   ((if (0 <? da + db)%nat then splice (splice R 0 (mul_normal a b)) (2 * N2 - da - db) (repeat 0%Z (da + db))
                     else splice R 0 (mul_normal a b)), T)).
    { rewrite mul_recursive_small.
      - cbv zeta. rewrite <- EN2. rewrite !firstn_all2 by (clear - Lab2; lia). reflexivity.
      - rewrite <- EN2. clear - K16. lia.
      - rewrite <- EN2. destruct (Nat.eqb_spec N2 8) as [E1|_]; [|reflexivity].
        destruct (Nat.eqb_spec da 0) as [E2|_]; [|reflexivity]. destruct (Nat.eqb_spec db 0) as [E3|_]; [|reflexivity].
        exfalso. apply NC. repeat split; assumption. }
    rewrite EMOD. cbn [fst snd]. clear EMOD.
    zstep. replace (bv_swrap 32 (bv_unsigned a5 + bv_unsigned a4)) with (- (Z.of_nat da + Z.of_nat db))%Z
      by (rewrite A4, A5; symmetry; apply addw_dn_dn; [exact Hda | exact Hdb]).
    zstep. rewrite lts_signed by (clear - Hda Hdb; lia).
    if_cases KZ; zify_cond KZ.
    { (* [comment removed for export] *)
      destruct (Nat.ltb_spec 0 (da + db)) as [HH|_]; [exfalso; clear - HH KZ; lia|].
      do 15 zstep. release_frame FR STc (bv_unsigned sp).
      finish. }
    destruct (Nat.ltb_spec 0 (da + db)) as [_|HH]; [|exfalso; clear - HH KZ; lia].
    do 8 zstep.
    rewrite fill_len by assumption.
    rewrite A3, A4, A5, fill_off by (try assumption; clear - HN2 K16; lia).
    rewrite <- A4, <- A5.
    do 16 zstep.
    release_frame FR STc (bv_unsigned sp).
    pose proof (hide_elim _ GEO) as (DRA & DRB & DTA & DTB & DRT & SEPR & SEPT & SEPA & SEPB & HLA' & HLB' & HLR' & HLT').
    remember (splice R 0 (mul_normal a b)) as R1 eqn:ER1.
    assert (LR1 : length R1 = (2 * N2)%nat) by (rewrite ER1, splice_length; [exact HLR' | rewrite EMN'; clear - HLA' HLB' HLR'; lia]).
    assert (Hoff : (2 * N2 - da - db + (da + db) <= length R1)%nat) by (rewrite LR1; clear - HN2 Hda Hdb; lia).
    pose proof (limbs_at_slice psegs m2 _ R1 (2 * N2 - da - db) (da + db) RR2 Hoff) as HL.
    assert (LL : length (slice R1 (2 * N2 - da - db) (da + db)) = (da + db)%nat) by (apply slice_length; exact Hoff).
    assert (ED : (bv_unsigned a0 + 8 * (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db) = bv_unsigned a0 + 8 * Z.of_nat (2 * N2 - da - db))%Z)
      by (clear - HN2 Hda Hdb; lia).
    rewrite ED.
    pose proof (zr_word a0) as R0. unfold inr64 in R0.
    eapply evt_mono.
    { eapply memset0_limbs_spec with (L := slice R1 (2 * N2 - da - db) (da + db)) (D := (bv_unsigned a0 + 8 * Z.of_nat (2 * N2 - da - db))%Z)
                                     (lo := lo) (SPz := bv_unsigned sp);
        [ apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - R0 BR HLR' HN2 Hda Hdb; lia
        | reflexivity
        | rewrite LL; apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - Hda Hdb; lia
        | exact HL
        | rewrite LL; pose proof (wr_at_sub psegs m2 _ _ (8 * Z.of_nat (2 * N2 - da - db)) (8 * Z.of_nat (da + db)) WR2 ltac:(lia) ltac:(lia)
                                    ltac:(clear - HN2 Hda Hdb; lia)) as X; exact X
        | exact STc | exact MIc ]. }
    intros ms' PO. unfold memset0_post in PO.
    destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m3 & E & MUm & WMm & MIm & HZ & STm).
    rewrite LL in MUm, HZ.
    eexists w0, w1, w2, _, y1, y2, y3, y4, y5, y6, y7, w3, w4, w5, w6, m3.
    split; [exact E|].
    split. { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [|exact MUm]. unfold sub_fp. cbn [outside]. intros x Hx.
             clear - Hx HLR' HN2 Hda Hdb. lia. }
    split; [eapply wmono_trans; [exact WM2 | exact WMm]|]. split; [exact MIm|].
    split.
    { eapply (limbs_at_splice psegs _ m2 m3 (bv_unsigned a0) R1 (2 * N2 - da - db) (repeat 0%Z (da + db)) RR2 MUm).
      - rewrite repeat_length. exact Hoff.
      - exact HZ.
      - cbn [disjoint_from]. clear. lia.
      - cbn [disjoint_from]. rewrite repeat_length. clear. lia. }
    split; [|exact STm].
    eapply limbs_at_transport; [exact RT2 | exact MUm | cbn [disjoint_from]; clear - DRT HLR' HN2 Hda Hdb; lia].
  Qed.

  (* [comment removed for export] *)
  Theorem bn_mul_recursive_spec : forall k, rec_spec_at CS8 k.
  Proof.
    induction k as [|k IH]; apply rec_body; intros k' E; [discriminate|]. injection E as <-. exact IH.
  Qed.
End Main.


