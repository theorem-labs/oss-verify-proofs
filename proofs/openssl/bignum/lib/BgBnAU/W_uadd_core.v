(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnWordsCorrect BnModel BnAddSpec BnMInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import BnCalls.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_add_words BnCallsU.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnKaraMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition uadd_lists (la lb : list Z) : list Z * Z :=
  let '(s, c) := add_words (firstn (length lb) la) lb in
  let '(s2, c2) := add_carry_words (skipn (length lb) la) c in (s ++ s2, c2).

Lemma add_carry_words_facts : forall a c, limbs a -> (0 <= c <= 1)%Z ->
  limbs (fst (add_carry_words a c)) /\ length (fst (add_carry_words a c)) = length a /\ (0 <= snd (add_carry_words a c) <= 1)%Z.
Proof.
  intros a c Ha Hc. pose proof (add_carry_words_spec a c Ha Hc) as H. destruct (add_carry_words a c) as [r c']. cbn [fst snd]. tauto.
Qed.

Lemma add_carry_words_cons : forall t a c,
  add_carry_words (t :: a) c =
  (addw t c :: fst (add_carry_words a (if addw t c =? 0 then c else 0)%Z), snd (add_carry_words a (if addw t c =? 0 then c else 0)%Z)).
Proof. intros. cbn [add_carry_words]. destruct (add_carry_words a _). reflexivity. Qed.

Lemma uadd_lists_facts : forall la lb, limbs la -> limbs lb -> (length lb <= length la)%nat ->
  limbs (fst (uadd_lists la lb)) /\ length (fst (uadd_lists la lb)) = length la /\ (0 <= snd (uadd_lists la lb) <= 1)%Z.
Proof.
  intros la lb Ha Hb Hl. unfold uadd_lists.
  pose proof (add_words_spec (firstn (length lb) la) lb (limbs_firstn _ _ Ha) Hb ltac:(rewrite firstn_length_le; lia)) as H1.
  destruct (add_words (firstn (length lb) la) lb) as [s c]. destruct H1 as (L1 & N1 & C1 & _).
  pose proof (add_carry_words_facts (skipn (length lb) la) c (limbs_skipn _ _ Ha) C1) as H2.
  destruct (add_carry_words (skipn (length lb) la) c) as [s2 c2]. cbn [fst snd] in *. destruct H2 as (L2 & N2 & C2).
  split; [apply limbs_app; assumption|]. split; [|exact C2].
  rewrite length_app, N1, N2, firstn_length_le, length_skipn by lia. lia.
Qed.

Ltac store_bundle I2 :=
  unfold wa in I2;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad ?bs) _) =>
      let m' := fresh "m" in
      gen_mem (write_to_mem m ad bs) m';
      repeat match goal with H : context [m] |- _ => clear H end; try clear m
  end.

Section Core.

  Variables (ra0 sp gp tp s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).

  Variables (m1 : word -> option byte) (lo R A B Dr Da Db : Z) (br : bignum bptr) (la lb : list Z).
  Notation SP := (bv_unsigned sp).
  Notation max := (length la).
  Notation min := (length lb).
  Notation mx := (Z.of_nat (length la)).
  Notation mn := (Z.of_nat (length lb)).
  Notation dmx := (Z.of_nat (bn_dmax br)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -64)).

  Definition uadd_pre : Prop :=
    limbs la /\ limbs lb /\ (min <= max)%nat /\ bn_okm br /\ (max + 1 <= bn_dmax br)%nat /\
    (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * mx <= lo /\ 0 <= Db /\ Db + 8 * mn <= lo /\ lo <= SP - 80 /\ SP < 2^64)%Z /\

    (A = R \/ A + 8 <= R \/ R + 24 <= A)%Z /\ (B = R \/ B + 8 <= R \/ R + 24 <= B)%Z /\

    (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * mx <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * mn <= R)%Z /\

    (Da = Dr \/ Dr + 8 * dmx <= Da \/ Da + 8 * mx <= Dr)%Z /\ (Db = Dr \/ Dr + 8 * dmx <= Db \/ Db + 8 * mn <= Dr)%Z.
  Hypothesis PRE : uadd_pre.

  Notation Wfin := [(Dr, Dr + 8 * (mx + 1)); (R, R + 24); (SP - 80, SP)]%Z.
  Notation FRAME := [C8 s6_; C8 s5_; C8 s4_; C8 s3_; C8 s2_; C8 s1_; C8 s0_; C8 ra0].

  Definition uadd_top : nat := if (max =? 0)%nat then 0%nat else (max + Z.to_nat (snd (uadd_lists la lb)))%nat.
  Definition uadd_buf : list Z := if (max =? 0)%nat then bn_buf br else splice (bn_buf br) 0 (fst (uadd_lists la lb) ++ [snd (uadd_lists la lb)]).
  Definition uadd_bn : bignum bptr := mkBN (bn_d br) uadd_buf uadd_top false (bn_flags br).

  Definition uadd_post : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m2,
      ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0_ s1_ (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2_ s3_ s4_ s5_ s6_ s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra0) fc None m2 (seg_rom bgusegs)
      /\ munch Wfin m1 m2 /\ wmono bgusegs m1 m2 /\ mem_inv bgusegs m2
      /\ rw_cells bgusegs m2 R (bn_cells Dr uadd_bn) /\ u64arr bgusegs m2 Dr (wlimbs uadd_buf)
      /\ stk bgusegs m2 lo SP.

  Notation ST pc mm x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 :=
    (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  Definition core_mem : Prop :=
    rw_cells bgusegs m1 R (bn_cells Dr br) /\ u64arr bgusegs m1 Dr (wlimbs (bn_buf br)) /\
    rw_cells bgusegs m1 A [C8 (wz Da)] /\ rw_cells bgusegs m1 B [C8 (wz Db)] /\
    limbs_at bgusegs m1 Da la /\ limbs_at bgusegs m1 Db lb /\
    rw_cells bgusegs m1 (SP + -64) FRAME /\ stk bgusegs m1 lo (SP + -64) /\ mem_inv bgusegs m1.
  Hypothesis MEM : core_mem.

  Definition UB (m2 : word -> option byte) (pre l : list Z) (topv negv : word) : Prop :=
    rw_cells bgusegs m2 R [C8 (wz Dr); C4 topv; C4 (wz dmx); C4 negv; C4 (wz (bn_flags br))] /\
    limbs_at bgusegs m2 Dr pre /\ wr_at bgusegs m2 Dr (8 * dmx) /\
    limbs_at bgusegs m2 (Da + 8 * Z.of_nat (length pre)) l /\
    rw_cells bgusegs m2 (SP + -64) FRAME /\ stk bgusegs m2 lo (SP + -64) /\ mem_inv bgusegs m2 /\
    munch Wfin m1 m2 /\ wmono bgusegs m1 m2.

  End Core.

Lemma uadd_buf_length : forall (br : bignum bptr) la lb, limbs la -> limbs lb -> (length lb <= length la)%nat ->
  (length la + 1 <= bn_dmax br)%nat -> length (uadd_buf br la lb) = bn_dmax br.
Proof.
  intros br la lb HA HB HL HD. unfold uadd_buf. destruct (length la =? 0)%nat; [reflexivity|].
  pose proof (uadd_lists_facts la lb HA HB HL) as (_ & N & _).
  apply splice_length. rewrite length_app, N. cbn [length]. unfold bn_dmax in HD. lia.
Qed.

Lemma uadd_bn_okm : forall (br : bignum bptr) la lb, limbs la -> limbs lb -> (length lb <= length la)%nat ->
  (length la + 1 <= bn_dmax br)%nat -> bn_okm br -> bn_okm (uadd_bn br la lb).
Proof.
  intros br la lb HA HB HL HD (L1 & L2 & L3 & L4).
  pose proof (uadd_buf_length br la lb HA HB HL HD) as LU.
  pose proof (uadd_lists_facts la lb HA HB HL) as (LW & NW & CW).
  unfold bn_okm, uadd_bn, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. rewrite LU.
  split.
  - unfold uadd_buf. destruct (length la =? 0)%nat; [exact L1|]. apply splice_limbs; [exact L1|].
    apply limbs_app; [exact LW|]. constructor; [|constructor]. pose proof BW_pos. unfold limb. rewrite BW_lit in *. lia.
  - split; [|split; [exact L3 | exact L4]]. unfold uadd_top. destruct (length la =? 0)%nat; lia.
Qed.

