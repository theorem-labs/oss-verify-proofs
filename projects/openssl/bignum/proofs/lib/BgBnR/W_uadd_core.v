(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnWordsCorrect BnModel BnAddSpec BnMInv.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require Import W_add_words BnCalls.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnKaraMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnRep.

From OSSVerify.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
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
    (0 < R /\ R + 24 <= lo /\ 0 < A /\ (A + 8 <= lo \/ (SP <= A /\ A + 24 < 2^63)) /\ 0 < B /\ (B + 8 <= lo \/ (SP <= B /\ B + 24 < 2^63)) /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ (Da + 8 * mx <= lo \/ (SP <= Da /\ Da + 8 * mx < 2^63)) /\ 0 <= Db /\ (Db + 8 * mn <= lo \/ (SP <= Db /\ Db + 8 * mn < 2^63)) /\ lo <= SP - 80 /\ SP < 2^63)%Z /\

    (A = R \/ A + 8 <= R \/ R + 24 <= A)%Z /\ (B = R \/ B + 8 <= R \/ R + 24 <= B)%Z /\

    (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * mx <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * mn <= R)%Z /\

    (Da = Dr \/ Dr + 8 * dmx <= Da \/ Da + 8 * mx <= Dr)%Z /\ (Db = Dr \/ Dr + 8 * dmx <= Db \/ Db + 8 * mn <= Dr)%Z.
  Hypothesis PRE : uadd_pre.

  Lemma P_lists : limbs la /\ limbs lb /\ (min <= max)%nat /\ bn_okm br /\ (max + 1 <= bn_dmax br)%nat.
  Proof. destruct PRE as (H1 & H2 & H3 & H4 & H5 & _). auto. Qed.
  Lemma P_rng : (0 < R /\ R + 24 <= lo /\ 0 < A /\ (A + 8 <= lo \/ (SP <= A /\ A + 24 < 2^63)) /\ 0 < B /\ (B + 8 <= lo \/ (SP <= B /\ B + 24 < 2^63)) /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ (Da + 8 * mx <= lo \/ (SP <= Da /\ Da + 8 * mx < 2^63)) /\ 0 <= Db /\ (Db + 8 * mn <= lo \/ (SP <= Db /\ Db + 8 * mn < 2^63)) /\ lo <= SP - 80 /\ SP < 2^63)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma P_lo : (lo <= SP - 80 /\ SP < 18446744073709551616)%Z.
  Proof. pose proof P_rng as H. change (2^64)%Z with 18446744073709551616%Z in H. lia. Qed.
  Lemma P_structs : (A = R \/ A + 8 <= R \/ R + 24 <= A)%Z /\ (B = R \/ B + 8 <= R \/ R + 24 <= B)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & H1 & H2 & _). auto. Qed.
  Lemma P_sarr : (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * mx <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * mn <= R)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _). auto. Qed.
  Lemma P_alias : (Da = Dr \/ Dr + 8 * dmx <= Da \/ Da + 8 * mx <= Dr)%Z /\ (Db = Dr \/ Dr + 8 * dmx <= Db \/ Db + 8 * mn <= Dr)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2). auto. Qed.

  Notation Wfin := [(Dr, Dr + 8 * (mx + 1)); (R, R + 24); (SP - 80, SP)]%Z.
  Notation FRAME := [C8 s6_; C8 s5_; C8 s4_; C8 s3_; C8 s2_; C8 s1_; C8 s0_; C8 ra0].

  Definition uadd_top : nat := if (max =? 0)%nat then 0%nat else (max + Z.to_nat (snd (uadd_lists la lb)))%nat.
  Definition uadd_buf : list Z := if (max =? 0)%nat then bn_buf br else splice (bn_buf br) 0 (fst (uadd_lists la lb) ++ [snd (uadd_lists la lb)]).
  Definition uadd_bn : bignum bptr := mkBN (bn_d br) uadd_buf uadd_top false (bn_flags br).

  Definition uadd_post : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m2,
      ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0_ s1_ (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2_ s3_ s4_ s5_ s6_ s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra0) fc None m2 (seg_rom bgpsegs)
      /\ munch Wfin m1 m2 /\ wmono bgpsegs m1 m2 /\ mem_inv bgpsegs m2
      /\ rw_cells bgpsegs m2 R (bn_cells Dr uadd_bn) /\ u64arr bgpsegs m2 Dr (wlimbs uadd_buf)
      /\ stk bgpsegs m2 lo SP.

  Notation ST pc mm x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 :=
    (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).

  Lemma ua_epi : forall m2 x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6,
    rw_cells bgpsegs m2 (SP + -64) FRAME -> stk bgpsegs m2 lo (SP + -64) -> mem_inv bgpsegs m2 ->
    munch Wfin m1 m2 -> wmono bgpsegs m1 m2 ->
    rw_cells bgpsegs m2 R (bn_cells Dr uadd_bn) -> u64arr bgpsegs m2 Dr (wlimbs uadd_buf) ->
    evt bgpsegs uadd_post (ST 0xff6c4 m2 x1 t0 t1 t2 x8 x9 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6).
  Proof.
    intros m2 x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 FR ST MI MU WM SR UR.
    unfold bn_cells in SR.
    do 8 zstep.
    pose proof P_lo as PLO.
    release_frame FR ST (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold uadd_post. do 14 eexists. exists m2. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [unfold bn_cells; exact SR|]. split; [exact UR | exact ST].
  Qed.

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

  Lemma UB_store : forall m2 pre x l topv negv v,
    UB m2 pre (x :: l) topv negv -> (length pre + S (length l) <= max)%nat ->
    store_ok bgpsegs m2 (wa (Dr + 8 * Z.of_nat (length pre))) 8 = true /\
    UB (write_to_mem m2 (wa (Dr + 8 * Z.of_nat (length pre))) (le8 (Z_to_bv 64 v))) (pre ++ [v]) l topv negv.
  Proof.
    intros m2 pre x l topv negv v (SR & HP & HW & HL & FR & ST & MI & MU & WM) Hlen.
    pose proof P_lists as (_ & _ & _ & _ & HD). pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _). pose proof P_alias as (AL & _).
    pose proof (limbs_at_bound _ _ _ _ HL) as BL. cbn [length] in BL.
    assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
    change (2^64)%Z with 18446744073709551616%Z in *.
    assert (SOK : store_ok bgpsegs m2 (wa (Dr + 8 * Z.of_nat (length pre))) 8 = true).
    { apply (wr_at_store_ok bgpsegs m2 Dr (8 * dmx)); [exact HW | lia | lia]. }
    split; [exact SOK|]. unfold UB.
    split. { apply rw_cells_frame; [exact SR | lia | rewrite L8; lia | rewrite L8; cbn [cells_size csize Nat.add]; lia]. }
    split. { apply limbs_at_snoc_write; [exact HP | change (2^64)%Z with 18446744073709551616%Z; lia]. }
    split. { apply wr_at_write. exact HW. }
    split. { rewrite length_app. cbn [length]. replace (Da + 8 * Z.of_nat (length pre + 1))%Z with (Da + 8 * Z.of_nat (length pre) + 8)%Z by lia.
             apply limbs_at_write_other; [eapply limbs_at_cons_inv; exact HL | lia | rewrite L8; change (2^64)%Z with 18446744073709551616%Z; lia | rewrite L8; lia]. }
    split. { apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8; cbn [cells_size csize Nat.add]; lia]. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; change (2^64)%Z with 18446744073709551616%Z; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; change (2^64)%Z with 18446744073709551616%Z; lia | rewrite L8; cbn [inside]; left; lia]. }
    apply wmono_write. exact WM.
  Qed.

  Lemma UB_store_last : forall m2 pre topv negv v,
    UB m2 pre [] topv negv -> length pre = max ->
    store_ok bgpsegs m2 (wa (Dr + 8 * Z.of_nat (length pre))) 8 = true /\
    UB (write_to_mem m2 (wa (Dr + 8 * Z.of_nat (length pre))) (le8 (Z_to_bv 64 v))) (pre ++ [v]) [] topv negv.
  Proof.
    intros m2 pre topv negv v (SR & HP & HW & HL & FR & ST & MI & MU & WM) Hlen.
    pose proof P_lists as (_ & _ & _ & _ & HD). pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _).
    assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
    change (2^64)%Z with 18446744073709551616%Z in *.
    assert (SOK : store_ok bgpsegs m2 (wa (Dr + 8 * Z.of_nat (length pre))) 8 = true).
    { apply (wr_at_store_ok bgpsegs m2 Dr (8 * dmx)); [exact HW | lia | lia]. }
    split; [exact SOK|]. unfold UB.
    split. { apply rw_cells_frame; [exact SR | lia | rewrite L8; lia | rewrite L8; cbn [cells_size csize Nat.add]; lia]. }
    split. { apply limbs_at_snoc_write; [exact HP | change (2^64)%Z with 18446744073709551616%Z; lia]. }
    split. { apply wr_at_write. exact HW. }
    split. { apply limbs_at_nil. change (2^64)%Z with 18446744073709551616%Z. rewrite length_app. cbn [length]. lia. }
    split. { apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8; cbn [cells_size csize Nat.add]; lia]. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; change (2^64)%Z with 18446744073709551616%Z; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; change (2^64)%Z with 18446744073709551616%Z; lia | rewrite L8; cbn [inside]; left; lia]. }
    apply wmono_write. exact WM.
  Qed.

  Lemma ua_final_arr : forall m2 w, munch Wfin m1 m2 -> wmono bgpsegs m1 m2 -> limbs_at bgpsegs m2 Dr w -> length w = (max + 1)%nat ->
    u64arr bgpsegs m2 Dr (wlimbs (splice (bn_buf br) 0 w)).
  Proof.
    intros m2 w MU WM HWL Hlen.
    destruct MEM as (_ & UR1 & _).
    pose proof P_lists as (_ & _ & _ & _ & HD). pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _).
    unfold bn_dmax in *.
    apply (limbarr_limbs_at bgpsegs) in UR1. destruct UR1 as [HL1 HW1].
    assert (LS : length (splice (bn_buf br) 0 w) = length (bn_buf br)) by (apply splice_length; lia).
    apply u64arr_of_limbs_at.
    - replace Dr with (Dr + 8 * Z.of_nat 0)%Z in HWL by lia.
      replace Dr with (Dr + 8 * Z.of_nat 0)%Z at 1 by lia. rewrite Z.add_0_r.
      eapply (limbs_at_splice bgpsegs Wfin m1 m2 Dr (bn_buf br) 0 w HL1 MU); [lia | exact HWL | |].
      + cbn [disjoint_from]. lia.
      + cbn [disjoint_from]. lia.
    - rewrite LS. eapply wr_at_transport; [exact HW1 | exact WM].
  Qed.

  Lemma ua_neg : forall m2 negv x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6,
    rw_cells bgpsegs m2 R [C8 (wz Dr); C4 (wz (Z.of_nat uadd_top)); C4 (wz dmx); C4 negv; C4 (wz (bn_flags br))] ->
    u64arr bgpsegs m2 Dr (wlimbs uadd_buf) -> length uadd_buf = bn_dmax br ->
    rw_cells bgpsegs m2 (SP + -64) FRAME -> stk bgpsegs m2 lo (SP + -64) -> mem_inv bgpsegs m2 ->
    munch Wfin m1 m2 -> wmono bgpsegs m1 m2 ->
    evt bgpsegs uadd_post (ST 0xff6bc m2 x1 t0 t1 t2 x8 (Z_to_bv 64 R) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6).
  Proof.
    intros m2 negv x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 SR UR LU FR ST MI MU WM.
    pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _). change (2^64)%Z with 18446744073709551616%Z in RNG.
    assert (LW : length (wlimbs uadd_buf) = bn_dmax br) by (rewrite wlimbs_len; exact LU).
    step. zstep.
    eapply ua_epi; try eassumption.
    unfold bn_cells, uadd_bn, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags Z.b2z]. rewrite LU. exact SR.
  Qed.

  Lemma ua_fin : forall m2 negv x1 t0 t1 t2 x8 a1 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6,
    (0 < max)%nat ->
    UB m2 (fst (uadd_lists la lb)) [] (wz mx) negv ->
    evt bgpsegs uadd_post (ST 0xff6ac m2 x1 t0 t1 t2 x8 (Z_to_bv 64 R) (Z_to_bv 64 (snd (uadd_lists la lb))) a1 (Z_to_bv 64 (Dr + 8 * mx))
                            a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6).
  Proof.
    intros m2 negv x1 t0 t1 t2 x8 a1 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 Hmax I.
    pose proof P_lists as (LLA & LLB & HMM & OKR & HD).
    pose proof (uadd_lists_facts la lb LLA LLB HMM) as (LW & NW & CW).
    destruct (UB_store_last m2 _ _ _ (snd (uadd_lists la lb)) I NW) as [SOK I2]. rewrite NW in SOK, I2.
    destruct I as (SR & _).
    destruct OKR as (_ & _ & DMR & _). unfold BN_WORDS_MAX in DMR.
    zstep. unfold wz at 1. rewrite (sx32_small mx) by (clear - HD DMR; lia).
    zstep. store_bundle I2.
    destruct I2 as (SR & HP & HW & _ & FR & ST & MI & MU & WM).
    pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _). change (2^64)%Z with 18446744073709551616%Z in RNG.
    pose proof (munch_refl [(R, R + 24)]%Z m) as MUt.
    zstep. zstep.
    apply (limbs_at_transport bgpsegs [(R, R + 24)]%Z m m0) in HP;
      [| exact MUt | cbn [disjoint_from]; rewrite length_app, NW; cbn [length]; clear - SA1 HD; lia].
    clear MUt.
    assert (ETOP : uadd_top = (max + Z.to_nat (snd (uadd_lists la lb)))%nat).
    { unfold uadd_top. destruct (Nat.eqb_spec max 0) as [E0|_]; [exfalso; clear - E0 Hmax; lia | reflexivity]. }
    assert (EBUF : uadd_buf = splice (bn_buf br) 0 (fst (uadd_lists la lb) ++ [snd (uadd_lists la lb)])).
    { unfold uadd_buf. destruct (Nat.eqb_spec max 0) as [E0|_]; [exfalso; clear - E0 Hmax; lia | reflexivity]. }
    assert (LWW : length (fst (uadd_lists la lb) ++ [snd (uadd_lists la lb)]) = (max + 1)%nat) by (rewrite length_app, NW; reflexivity).
    eapply (ua_neg m0 negv); [ | | | exact FR | exact ST | exact MI | exact MU | exact WM].
    - rewrite ETOP. unfold wz at 2. rewrite Nat2Z.inj_add, Z2Nat.id by (clear - CW; lia). exact SR.
    - rewrite EBUF. apply ua_final_arr; [exact MU | exact WM | exact HP | exact LWW].
    - rewrite EBUF. apply splice_length. rewrite LWW. clear - HD. unfold bn_dmax in *. lia.
  Qed.

  Lemma ua_loop : forall l pre c m2 negv x1 t0 t1 t2 x8 a2 a3 a4 a5 a6 a7 x18 x21 x22 t3 t4 t5 t6,
    UB m2 pre l (Z_to_bv 64 mx) negv -> l <> [] -> (length pre + length l = max)%nat -> limbs l -> (0 <= c <= 1)%Z ->
    fst (uadd_lists la lb) = pre ++ fst (add_carry_words l c) -> snd (uadd_lists la lb) = snd (add_carry_words l c) ->
    evt bgpsegs uadd_post
      (ST 0xff67c m2 x1 t0 t1 t2 x8 (Z_to_bv 64 R) (Z_to_bv 64 c) (Z_to_bv 64 (- Z.of_nat (length l))) a2 a3 a4 a5 a6 a7
          x18 (Z_to_bv 64 (Da + 8 * Z.of_nat (length pre))) (Z_to_bv 64 (Dr + 8 * Z.of_nat (length pre))) x21 x22 t3 t4 t5 t6).
  Proof.
    induction l as [|x l IH]; intros pre c m2 negv x1 t0 t1 t2 x8 a2 a3 a4 a5 a6 a7 x18 x21 x22 t3 t4 t5 t6 I NE HLEN LL HC E1 E2;
      [exfalso; apply NE; reflexivity|]. clear NE.
    pose proof P_lists as (_ & _ & _ & OKR & HD). pose proof OKR as (_ & _ & DMR & _). unfold BN_WORDS_MAX in DMR.
    apply limbs_cons_lit in LL. destruct LL as [RX LL].
    pose proof I as (_ & _ & _ & HL & _).
    cbn [length] in HLEN.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_hd bgpsegs m2 _ x l ad HL ltac:(unfold wa; reflexivity)) as RD); zstep; clear RD.
    do 3 zstep.
    setreg 13%Z (Z_to_bv 64 (addw x c)) ltac:(unfold addw; apply Z_to_bv_eqm; rewrite BW_lit; clear; Z.div_mod_to_equations; lia).
    destruct (UB_store m2 pre x l _ negv (addw x c) I ltac:(clear - HLEN; lia)) as [SOK I2].
    assert (RT : (0 <= addw x c < 18446744073709551616)%Z) by (unfold addw; rewrite BW_lit; apply Z.mod_pos_bound; clear; lia).
    zstep. store_bundle I2.
    do 2 zstep.
    setreg 11%Z (Z_to_bv 64 (- Z.of_nat (length l)))
      ltac:(f_equal; cbn [length]; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia;
            change (2^64)%Z with 18446744073709551616%Z; rewrite bn_swrap32_mod by (clear - HLEN HD DMR; lia); clear; lia).
    zstep.
    setreg 10%Z (Z_to_bv 64 (if addw x c =? 0 then c else 0)%Z)
      ltac:(f_equal; clear - HC RT; destruct (Z.eqb_spec (addw x c) 0) as [E0|N0];
            [rewrite E0; cbn [Z.ltb Z.compare Z.b2z]; assert (c = 0 \/ c = 1)%Z as [->| ->] by lia; reflexivity
            |replace (addw x c <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity]).
    zstep.
    assert (E1' : fst (uadd_lists la lb) = (pre ++ [addw x c]) ++ fst (add_carry_words l (if addw x c =? 0 then c else 0)%Z)).
    { rewrite E1, add_carry_words_cons. cbn [fst]. rewrite <- app_assoc. reflexivity. }
    assert (E2' : snd (uadd_lists la lb) = snd (add_carry_words l (if addw x c =? 0 then c else 0)%Z)).
    { rewrite E2, add_carry_words_cons. reflexivity. }
    assert (HC' : (0 <= (if addw x c =? 0 then c else 0) <= 1)%Z) by (clear - HC; destruct (addw x c =? 0)%Z; lia).
    assert (LP : length (pre ++ [addw x c]) = (length pre + 1)%nat) by (rewrite length_app; reflexivity).
    zstep. if_cases KZ; zify_cond KZ.
    -
      assert (NE : l <> []) by (intros ->; apply KZ; reflexivity).
      setreg 19%Z (Z_to_bv 64 (Da + 8 * Z.of_nat (length (pre ++ [addw x c])))) ltac:(f_equal; rewrite LP; clear; lia).
      setreg 20%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (length (pre ++ [addw x c])))) ltac:(f_equal; rewrite LP; clear; lia).
      eapply IH; [exact I2 | exact NE | rewrite LP; clear - HLEN; lia | exact LL | exact HC' | exact E1' | exact E2'].
    -
      rewrite land64_zero_iff in KZ by (clear - HLEN HD DMR; lia).
      assert (EL : l = []) by (clear - KZ; destruct l; [reflexivity | cbn [length] in KZ; lia]). subst l.
      cbn [add_carry_words fst snd] in E1', E2'. rewrite app_nil_r in E1'.
      zstep.
      setreg 12%Z (Z_to_bv 64 (Dr + 8 * mx)) ltac:(f_equal; clear - HLEN; cbn [length] in HLEN; lia).
      rewrite <- E2'. rewrite <- E1' in I2.
      eapply ua_fin; [clear - HLEN; lia | exact I2].
  Qed.

  Lemma uadd_core : forall x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6,
    evt bgpsegs uadd_post
      (ST 0xff63c m1 x1 t0 t1 t2 x8 (Z_to_bv 64 R) (Z_to_bv 64 R) a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 mn) (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 mx) x22 t3 t4 t5 t6).
  Proof.
    intros x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & FR & ST & MI).
    pose proof P_lists as (LLA & LLB & HMM & OKR & HD).
    pose proof P_rng as RNG. change (2^64)%Z with 18446744073709551616%Z in RNG.
    pose proof OKR as (_ & _ & DMR & _). unfold BN_WORDS_MAX in DMR.
    pose proof (munch_refl Wfin m1) as MU. pose proof (wmono_refl bgpsegs m1) as WM.
    pose proof (munch_refl [(R, R + 24)]%Z m1) as MUt.
    unfold bn_cells in SR.
    zstep. if_cases K; zify_cond K; [exfalso; clear - K RNG; lia|]. clear K.
    pose proof P_structs as (SAR & SBR). pose proof P_sarr as (SA1 & SA2 & SA3).
    assert (LWR : length (wlimbs (bn_buf br)) = bn_dmax br) by (apply wlimbs_len).
    step.
    zstep. if_cases K0; zify_cond K0.
    {
      assert (E0 : max = 0%nat) by (clear - K0; lia).
      assert (ETOP : uadd_top = 0%nat) by (unfold uadd_top; rewrite E0; reflexivity).
      assert (EBUF : uadd_buf = bn_buf br) by (unfold uadd_buf; rewrite E0; reflexivity).
      eapply (ua_neg m); [ | | | exact FR | exact ST | exact MI | exact MU | exact WM].
      - rewrite ETOP. rewrite E0 in SR. exact SR.
      - rewrite EBUF. exact UR.
      - rewrite EBUF. reflexivity. }
    assert (Hmax : (0 < max)%nat) by (clear - K0; lia). clear K0.
    do 4 zstep. rewrite (bn_swrap32_small (mx - mn)) by (clear - HMM HD DMR; lia).
    do 3 zstep.

    pose proof P_alias as (ALA & ALB).
    assert (HLAm : limbs_at bgpsegs m Da la).
    { eapply limbs_at_transport; [exact HLA | exact MUt | cbn [disjoint_from]; clear - SA2; lia]. }
    assert (HLBm : limbs_at bgpsegs m Db lb).
    { eapply limbs_at_transport; [exact HLB | exact MUt | cbn [disjoint_from]; clear - SA3; lia]. }
    clear HLA HLB MUt.
    assert (HW : wr_at bgpsegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at bgpsegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    assert (LF : length (firstn min la) = min) by (apply firstn_length_le; exact HMM).
    assert (ESPF : bv_unsigned SPF = (SP + -64)%Z) by (apply unsigned_lit; clear - RNG; lia).
    zstep.
    eapply (call_add_words uadd_post) with (a := firstn min la) (b := lb) (RP := Dr) (AP := Da) (BP := Db) (lo := lo) (SPz := (SP + -64)%Z);
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI
      | apply limbs_firstn; exact LLA | exact LLB | rewrite LF; reflexivity | rewrite LF; clear - HMM HD DMR; lia
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia
      | rewrite LF; apply unsigned_lit; clear - HMM HD DMR; lia
      | apply (limbs_at_firstn bgpsegs); exact HLAm | exact HLBm
      | rewrite LF; replace Dr with (Dr + 0)%Z by lia; eapply wr_at_sub; [exact HW | lia | lia | clear - HMM HD; lia]
      | rewrite LF; unfold alias_ok; clear - ALA HMM HD; lia | rewrite LF; unfold alias_ok; clear - ALB HMM HD; lia
      | clear - RNG; lia | rewrite LF; clear - RNG HMM HD; lia | rewrite LF; clear - RNG HMM; lia | rewrite LF; clear - RNG; lia | ].
    rewrite LF. intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HRc STc.

    pose proof (add_words_spec (firstn min la) lb (limbs_firstn _ _ LLA) LLB LF) as AWS.
    assert (ELS : uadd_lists la lb = (fst (add_words (firstn min la) lb) ++ fst (add_carry_words (skipn min la) (snd (add_words (firstn min la) lb))),
                                      snd (add_carry_words (skipn min la) (snd (add_words (firstn min la) lb))))).
    { unfold uadd_lists. destruct (add_words (firstn min la) lb) as [sv cv]. cbn [fst snd]. destruct (add_carry_words (skipn min la) cv). reflexivity. }
    destruct (add_words (firstn min la) lb) as [sv cv]. cbn [fst snd] in *. destruct AWS as (LSV & NSV & CV & _). rewrite LF in NSV.
    assert (HL2 : limbs_at bgpsegs m2 (Da + 8 * Z.of_nat (length sv)) (skipn min la)).
    { rewrite NSV. eapply limbs_at_transport; [apply (limbs_at_skipn bgpsegs); [exact HLAm | exact HMM] | exact MUc |].
      cbn [disjoint_from]. rewrite length_skipn. clear - ALA RNG HMM HD. lia. }
    assert (I : UB m2 sv (skipn min la) (Z_to_bv 64 mx) (wz (Z.b2z (bn_neg br)))).
    { unfold UB. split.
      { eapply rw_cells_transport; [exact SR | exact MUc | exact WMc | cbn; clear - SA1 RNG HMM HD; lia]. }
      split; [exact HRc|]. split; [eapply wr_at_transport; [exact HW | exact WMc]|]. split; [exact HL2|].
      split. { eapply rw_cells_transport; [exact FR | exact MUc | exact WMc | cbn; clear - RNG HMM HD; lia]. }
      split; [exact STc|]. split; [exact MIc|].
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HMM. lia. }
      eapply wmono_trans; [exact WM | exact WMc]. }
    clear SR UR HAd HBd FR ST MI MU WM HLAm HLBm HW MUc WMc MIc HRc STc HL2 m.
    do 2 zstep.
    assert (LSK : length (skipn min la) = (max - min)%nat) by apply length_skipn.
    zstep. if_cases KD; zify_cond KD.
    {
      assert (ESK : skipn min la = []) by (clear - KD LSK; destruct (skipn min la); [reflexivity | cbn [length] in LSK; lia]).
      rewrite ESK in ELS, I. cbn [add_carry_words fst snd] in ELS. rewrite app_nil_r in ELS.
      zstep.
      setreg 12%Z (Z_to_bv 64 (Dr + 8 * mx)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; clear - KD; lia).
      replace (Z_to_bv 64 cv) with (Z_to_bv 64 (snd (uadd_lists la lb))) by (rewrite ELS; reflexivity).
      eapply ua_fin; [exact Hmax | rewrite ELS; exact I]. }
    do 2 zstep.
    rewrite (bn_swrap32_small (mn - mx)) by (clear - HMM HD DMR; lia).
    setreg 11%Z (Z_to_bv 64 (- Z.of_nat (length (skipn min la)))) ltac:(f_equal; rewrite LSK; clear - HMM; lia).
    setreg 19%Z (Z_to_bv 64 (Da + 8 * Z.of_nat (length sv))) ltac:(f_equal; rewrite NSV, Z.shiftl_mul_pow2 by lia; clear; lia).
    setreg 20%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (length sv))) ltac:(f_equal; rewrite NSV, Z.shiftl_mul_pow2 by lia; clear; lia).
    eapply ua_loop; [exact I | | rewrite NSV, LSK; clear - HMM; lia | apply limbs_skipn; exact LLA | exact CV
                    | rewrite ELS; reflexivity | rewrite ELS; reflexivity].
    intros E0. rewrite E0 in LSK. cbn [length] in LSK. clear - LSK KD HMM. lia.
  Qed.
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

