(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnWordsCorrect BnModel BnAddSpec BnMInv.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require Import W_sub_words BnCalls.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnKaraMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnRep.
From OSSVerify.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnA Require Import W_uadd_core.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition usub_list (la lb : list Z) : list Z :=
  let '(s, c) := sub_words (firstn (length lb) la) lb in
  let '(s2, _) := sub_part_pos (skipn (length lb) la) c in s ++ s2.

Lemma sub_part_pos_cons : forall t a c,
  sub_part_pos (t :: a) c =
  (((t - c) mod BW)%Z :: fst (sub_part_pos a (if t =? 0 then c else 0)%Z), snd (sub_part_pos a (if t =? 0 then c else 0)%Z)).
Proof. intros. cbn [sub_part_pos]. destruct (sub_part_pos a _). reflexivity. Qed.

Lemma sub_part_pos_facts : forall a c, limbs (fst (sub_part_pos a c)) /\ length (fst (sub_part_pos a c)) = length a.
Proof.
  induction a as [|t a IH]; intros c; [split; [constructor | reflexivity]|].
  rewrite sub_part_pos_cons. cbn [fst length]. destruct (IH (if t =? 0 then c else 0)%Z) as [L N].
  split; [constructor; [unfold limb; apply Z.mod_pos_bound; pose proof BW_pos; lia | exact L] | rewrite N; reflexivity].
Qed.

Lemma usub_list_facts : forall la lb, limbs la -> limbs lb -> (length lb <= length la)%nat ->
  limbs (usub_list la lb) /\ length (usub_list la lb) = length la.
Proof.
  intros la lb Ha Hb Hl. unfold usub_list.
  pose proof (sub_words_spec (firstn (length lb) la) lb (limbs_firstn _ _ Ha) Hb ltac:(rewrite firstn_length_le; lia)) as H1.
  destruct (sub_words (firstn (length lb) la) lb) as [s c]. destruct H1 as (L1 & N1 & C1 & _).
  pose proof (sub_part_pos_facts (skipn (length lb) la) c) as H2.
  destruct (sub_part_pos (skipn (length lb) la) c) as [s2 c2]. cbn [fst snd] in *. destruct H2 as (L2 & N2).
  split; [apply limbs_app; assumption|].
  rewrite length_app, N1, N2, firstn_length_le, length_skipn by lia. lia.
Qed.

Lemma strip_top_le : forall d t, (strip_top d t <= t)%nat.
Proof. intros d. induction t as [|t IH]; cbn [strip_top]; [lia|]. destruct (nth t d 0 =? 0)%Z; lia. Qed.

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

  Definition usub_pre : Prop :=
    limbs la /\ limbs lb /\ (min <= max)%nat /\ bn_okm br /\ (max <= bn_dmax br)%nat /\
    (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * mx <= lo /\ 0 <= Db /\ Db + 8 * mn <= lo /\ lo <= SP - 80 /\ SP < 2^64)%Z /\
    (A = R \/ A + 8 <= R \/ R + 24 <= A)%Z /\ (B = R \/ B + 8 <= R \/ R + 24 <= B)%Z /\
    (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * mx <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * mn <= R)%Z /\
    (Da = Dr \/ Dr + 8 * dmx <= Da \/ Da + 8 * mx <= Dr)%Z /\ (Db = Dr \/ Dr + 8 * dmx <= Db \/ Db + 8 * mn <= Dr)%Z.
  Hypothesis PRE : usub_pre.

  Lemma P_lists : limbs la /\ limbs lb /\ (min <= max)%nat /\ bn_okm br /\ (max <= bn_dmax br)%nat.
  Proof. destruct PRE as (H1 & H2 & H3 & H4 & H5 & _). auto. Qed.

  Notation Wfin := [(Dr, Dr + 8 * mx); (R, R + 24); (SP - 80, SP)]%Z.
  Notation FRAME := [C8 s6_; C8 s5_; C8 s4_; C8 s3_; C8 s2_; C8 s1_; C8 s0_; C8 ra0].

  Definition usub_buf : list Z := if (max =? 0)%nat then bn_buf br else splice (bn_buf br) 0 (usub_list la lb).
  Definition usub_top : nat := strip_top usub_buf max.
  Definition usub_bn : bignum bptr := mkBN (bn_d br) usub_buf usub_top false (bn_flags br).

  Lemma usub_buf_len : length usub_buf = bn_dmax br.
  Proof.
    pose proof P_lists as (LA & LB & HMM & _ & HD). unfold usub_buf. destruct (max =? 0)%nat; [reflexivity|].
    pose proof (usub_list_facts la lb LA LB HMM) as (_ & N). apply splice_length. unfold bn_dmax in HD. lia.
  Qed.

  Lemma usub_buf_limbs : limbs usub_buf.
  Proof.
    pose proof P_lists as (LA & LB & HMM & (LBR & _) & HD). unfold usub_buf. destruct (max =? 0)%nat; [exact LBR|].
    apply splice_limbs; [exact LBR|]. apply (usub_list_facts la lb LA LB HMM).
  Qed.

  Definition usub_post : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m2,
      ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0_ s1_ (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2_ s3_ s4_ s5_ s6_ s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra0) fc None m2 (seg_rom bgpsegs)
      /\ munch Wfin m1 m2 /\ wmono bgpsegs m1 m2 /\ mem_inv bgpsegs m2
      /\ rw_cells bgpsegs m2 R (bn_cells Dr usub_bn) /\ u64arr bgpsegs m2 Dr (wlimbs usub_buf)
      /\ stk bgpsegs m2 lo SP.

  Notation ST pc mm x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 :=
    (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).

  Definition core_mem : Prop :=
    rw_cells bgpsegs m1 R (bn_cells Dr br) /\ u64arr bgpsegs m1 Dr (wlimbs (bn_buf br)) /\
    rw_cells bgpsegs m1 A [C8 (wz Da)] /\ rw_cells bgpsegs m1 B [C8 (wz Db)] /\
    limbs_at bgpsegs m1 Da la /\ limbs_at bgpsegs m1 Db lb /\
    rw_cells bgpsegs m1 (SP + -64) FRAME /\ stk bgpsegs m1 lo (SP + -64) /\ mem_inv bgpsegs m1.
  Hypothesis MEM : core_mem.

  Definition UB (m2 : word -> option byte) (pre l : list Z) (topv negv : word) : Prop :=
    rw_cells bgpsegs m2 R [C8 (wz Dr); C4 topv; C4 (wz dmx); C4 negv; C4 (wz (bn_flags br))] /\
    limbs_at bgpsegs m2 Dr pre /\ wr_at bgpsegs m2 Dr (8 * dmx) /\
    limbs_at bgpsegs m2 (Da + 8 * Z.of_nat (length pre)) l /\
    rw_cells bgpsegs m2 (SP + -64) FRAME /\ stk bgpsegs m2 lo (SP + -64) /\ mem_inv bgpsegs m2 /\
    munch Wfin m1 m2 /\ wmono bgpsegs m1 m2.

  End Core.

Lemma usub_bn_okm : forall sp lo R A B Dr Da Db (br : bignum bptr) la lb, usub_pre sp lo R A B Dr Da Db br la lb -> bn_okm (usub_bn br la lb).
Proof.
  intros sp lo R A B Dr Da Db br la lb PRE.
  pose proof (usub_buf_len sp lo R A B Dr Da Db br la lb PRE) as LU.
  pose proof (usub_buf_limbs sp lo R A B Dr Da Db br la lb PRE) as LL.
  pose proof PRE as (_ & _ & _ & (_ & _ & L3 & L4) & HD & _).
  unfold bn_okm, usub_bn, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. rewrite LU.
  split; [exact LL|]. split; [|split; [exact L3 | exact L4]].
  unfold usub_top. pose proof (strip_top_le (usub_buf br la lb) (length la)). lia.
Qed.
