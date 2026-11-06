(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import ShiftPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition RINVG (m : word -> option byte) (f : list Z) (fp T rb : Z) (m1 : word -> option byte) (i : nat) : Prop :=
  limbs_at bgpsegs m1 T (map (rsh_at f rb) (seq 0 i)) /\
  ((S i <= length f)%nat -> limbs_at bgpsegs m1 (fp + 8 * Z.of_nat (S i)) (skipn (S i) f)) /\
  wr_at bgpsegs m1 T (8 * Z.of_nat (length f)) /\ mem_inv bgpsegs m1 /\
  munch [(T, T + 8 * Z.of_nat (length f))]%Z m m1 /\ wmono bgpsegs m m1.

Lemma RINVG_store : forall m f fp T rb m1 i v,
  (T <= fp \/ fp + 8 * Z.of_nat (length f) <= T)%Z -> (0 <= fp)%Z ->
  RINVG m f fp T rb m1 i -> (i < length f)%nat -> v = rsh_at f rb i ->
  store_ok bgpsegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true /\
  RINVG m f fp T rb (write_to_mem m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v))) (S i).
Proof.
  intros m f fp T rb m1 i v DISJ FP0 (HW & HS & WT & MI & MU & WM) Hi ->.
  assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
  pose proof (wr_at_below bgpsegs m1 T (8 * Z.of_nat (length f)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
  assert (L8 : length (le8 (Z_to_bv 64 (rsh_at f rb i))) = 8%nat) by apply length_le8.
  assert (SOK : store_ok bgpsegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true).
  { change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)). apply (wr_at_store_ok bgpsegs m1 T (8 * Z.of_nat (length f))); [exact WT | lia | lia]. }
  split; [exact SOK|].
  change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)).
  unfold RINVG.
  split. { rewrite seq_S, map_app. cbn [map Nat.add].
           replace (T + 8 * Z.of_nat i)%Z with (T + 8 * Z.of_nat (length (map (rsh_at f rb) (seq 0 i))))%Z by (rewrite length_map, length_seq; reflexivity).
           apply limbs_at_snoc_write; [exact HW | rewrite length_map, length_seq; lia]. }
  split. { intros HSS. specialize (HS ltac:(lia)).
           rewrite <- (firstn_skipn 1 (skipn (S i) f)) in HS. apply limbs_at_app in HS. destruct HS as [_ HS2].
           rewrite skipn_skipn in HS2. rewrite length_firstn, length_skipn in HS2.
           replace (Nat.min 1 (length f - S i)) with 1%nat in HS2 by lia.
           replace (fp + 8 * Z.of_nat (S i) + 8 * Z.of_nat 1)%Z with (fp + 8 * Z.of_nat (S (S i)))%Z in HS2 by lia.
           replace (1 + S i)%nat with (S (S i)) in HS2 by lia.
           pose proof (limbs_at_bound _ _ _ _ HS2) as BS.
           apply limbs_at_write_other; [exact HS2 | lia | rewrite L8; lia | rewrite L8, length_skipn; lia]. }
  split. { apply wr_at_write. exact WT. }
  split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
  split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
  apply wmono_write. exact WM.
Qed.

Section Block.
  Variables (ra sp gp tp s0 s1 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (Dx nwz T n rb : Z).
  Notation top := (Z.of_nat (length f)).
  Notation fp := (Dx + 8 * nwz)%Z.
  Hypothesis Hn : (0 <= n < 2147483648)%Z.
  Hypothesis Hrb : (0 <= rb < 64)%Z.
  Hypothesis Erb : Z.land n 63 = rb.
  Hypothesis Enn : Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63 = ((64 - rb) mod 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis HDx : (0 <= Dx)%Z.
  Hypothesis Hnw : (0 <= nwz < 2147483648)%Z.
  Hypothesis DISJ : (T <= fp \/ fp + 8 * top <= T)%Z.

  Notation lbm := ((64 - rb) mod 64)%Z.
  Notation rmask := (if (rb =? 0)%Z then 0 else 18446744073709551615)%Z.

  Notation SH pc mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 (Z_to_bv 64 top) (Z_to_bv 64 n) x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).

  Notation HEAD mm i x6 x7 :=
    (SH 0xff49c mm (Z_to_bv 64 (T + 8 * Z.of_nat i)) x6 x7 (Z_to_bv 64 T) (Z_to_bv 64 rb) (Z_to_bv 64 (nth i f 0%Z)) (Z_to_bv 64 (top - 1))
        (Z_to_bv 64 (fp + 8 * Z.of_nat (S i))) (Z_to_bv 64 lbm) (Z_to_bv 64 rmask) (Z_to_bv 64 (T + 8 * (top - 1))) (Z_to_bv 64 (8 * nwz))).
  Notation KEXIT :=
    (forall m2 x5 x6 x7 x14,
       RINVG m f fp T rb m2 (length f - 1) ->
       evt bgpsegs POST (SH 0xff4c4 m2 x5 x6 x7 (Z_to_bv 64 T) (Z_to_bv 64 rb) (Z_to_bv 64 (nth (length f - 1) f 0%Z)) (Z_to_bv 64 (top - 1))
                          x14 (Z_to_bv 64 lbm) (Z_to_bv 64 rmask) (Z_to_bv 64 (T + 8 * (top - 1))) (Z_to_bv 64 (8 * nwz)))).

  Lemma rshg_round : forall (i : nat) m1 x6 x7,
    (S i < length f)%nat -> RINVG m f fp T rb m1 i ->
    ((S (S i) = length f)%nat -> KEXIT) ->
    ((S (S i) < length f)%nat -> forall m2 x6 x7, RINVG m f fp T rb m2 (S i) -> evt bgpsegs POST (HEAD m2 (S i) x6 x7)) ->
    evt bgpsegs POST (HEAD m1 i x6 x7).
  Proof.
    intros i m1 x6 x7 Hi I KE KL.
    pose proof I as (_ & HS & WT & MI & _). specialize (HS ltac:(lia)).
    pose proof (limbs_at_bound _ _ _ _ HS) as BF. rewrite length_skipn in BF.
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below bgpsegs m1 T (8 * top) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (RI : (0 <= nth i f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (RS : (0 <= nth (S i) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (NS : nth_error (skipn (S i) f) 0 = Some (nth (S i) f 0%Z)).
    { rewrite nth_error_skipn, Nat.add_0_r. apply nth_error_nth'. lia. }
    zstep.
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgpsegs m1 (fp + 8 * Z.of_nat (S i)) (skipn (S i) f) 0 _ ad HS NS ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 4 zstep.
    setreg 6%Z (Z_to_bv 64 (rsh_at f rb i))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (rsh_hi_machine rb _ Hrb), (shrw_machine rb _ Hrb), (rsh_at_mid f rb i Hi); reflexivity).
    destruct (RINVG_store m f fp T rb m1 i _ DISJ ltac:(lia) I ltac:(lia) eq_refl) as [SOK I1].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    clear SOK I HS WT MI BF. try clear m1.
    do 2 zstep.
    zstep. if_cases KB; zify_cond KB.
    -
      replace (T + 8 * Z.of_nat i + 8)%Z with (T + 8 * Z.of_nat (S i))%Z by lia.
      replace (fp + 8 * Z.of_nat (S i) + 8)%Z with (fp + 8 * Z.of_nat (S (S i)))%Z by lia.
      eapply KL; [clear - KB Hi; lia | exact I1].
    -
      assert (E : (S (S i) = length f)%nat) by (clear - KB Hi; lia).
      replace (S i) with (length f - 1)%nat in * by lia.
      eapply KE; [exact E | exact I1].
  Qed.

  Lemma rshg_loop : forall (k i : nat) m1 x6 x7,
    (S i + k = length f - 1)%nat -> (S i < length f)%nat -> RINVG m f fp T rb m1 i -> KEXIT -> evt bgpsegs POST (HEAD m1 i x6 x7).
  Proof.
    induction k as [|k IH]; intros i m1 x6 x7 Hk Hi I K.
    - eapply rshg_round; [exact Hi | exact I | intros _; exact K | intros C; exfalso; lia].
    - eapply rshg_round; [exact Hi | exact I | intros C; exfalso; lia | ].
      intros _ m2 y6 y7 I2. eapply IH; [lia | lia | exact I2 | exact K].
  Qed.

  Lemma rshg_block : forall x5 x6 x7 x11 x12 x13 x15 x16 x17,
    limbs_at bgpsegs m fp f -> wr_at bgpsegs m T (8 * top) -> mem_inv bgpsegs m ->
    (forall m2 x5 x6 x7 x12 x14 x15 x16 x17,
       RINVG m f fp T rb m2 (length f - 1) ->
       evt bgpsegs POST (SH 0xff4e0 m2 x5 x6 x7 (Z_to_bv 64 T) (Z_to_bv 64 (rsh_at f rb (length f - 1))) x12 (Z_to_bv 64 (8 * (top - 1))) x14 x15 x16 x17 (Z_to_bv 64 (8 * nwz)))) ->
    evt bgpsegs POST (SH 0xff458 m x5 x6 x7 (Z_to_bv 64 T) x11 x12 x13 (Z_to_bv 64 Dx) x15 x16 x17 (Z_to_bv 64 nwz)).
  Proof.
    intros x5 x6 x7 x11 x12 x13 x15 x16 x17 HF WT MI K.
    pose proof (limbs_at_bound _ _ _ _ HF) as BF.
    pose proof (wr_at_below bgpsegs m T (8 * top) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    zstep. replace (nwz ≪ 3)%Z with (8 * nwz)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    assert (N0 : nth_error f 0 = Some (nth 0 f 0%Z)) by (apply nth_error_nth'; lia).
    assert (R0 : (0 <= nth 0 f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgpsegs m fp f 0 _ ad HF N0 ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 2 zstep.
    setreg 11%Z (Z_to_bv 64 rb) ltac:(f_equal; symmetry; exact Erb).
    assert (I0 : RINVG m f fp T rb m 0).
    { unfold RINVG. cbn [seq map]. split; [apply limbs_at_nil; lia|].
      split. { intros _. rewrite <- (firstn_skipn 1 f) in HF. apply limbs_at_app in HF. destruct HF as [_ HF2].
               rewrite length_firstn in HF2. replace (Nat.min 1 (length f)) with 1%nat in HF2 by lia. exact HF2. }
      split; [exact WT|]. split; [exact MI|].
      split; [apply munch_refl | apply wmono_refl]. }
    zstep. rewrite lts_signed by lia. if_cases KT; zify_cond KT.
    -
      do 3 zstep.
      assert (E1 : (length f - 1 = 0)%nat) by lia. rewrite E1 in K.
      setreg 11%Z (Z_to_bv 64 (rsh_at f rb 0)) ltac:(f_equal; rewrite (shrw_machine rb _ Hrb), (rsh_at_last f rb 0 ltac:(lia)); reflexivity).
      replace (8 * (top - 1))%Z with 0%Z in K by lia.
      apply K. exact I0.
    - do 2 zstep.
      rewrite (bn_swrap32_small (top + -1)) by lia.
      do 9 zstep.
      rewrite Enn.
      change (Z.lor (((0 - lbm) mod 18446744073709551616) ≫ 8) ((0 - lbm) mod 18446744073709551616)) with (rmask_m lbm).
      rewrite (rmask_m_eq rb Hrb).
      rewrite (shl32_shr29 (top + -1)) by lia.
      replace (top + -1)%Z with (top - 1)%Z by lia.
      replace (Z_to_bv 64 (fp + 8)) with (Z_to_bv 64 (fp + 8 * Z.of_nat 1)) by (f_equal; lia).
      eapply evt_eq; [ | eapply (rshg_loop (length f - 2) 0 m x6 x7); [lia | lia | exact I0 | ] ].
      + replace (T + 8 * Z.of_nat 0)%Z with T by lia. reflexivity.
      + intros m2 y5 y6 y7 y14 I2.
        assert (RLl : (0 <= nth (length f - 1) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
        do 3 zstep.
        setreg 11%Z (Z_to_bv 64 (rsh_at f rb (length f - 1)))
          ltac:(f_equal; rewrite (shrw_machine rb _ Hrb), (rsh_at_last f rb (length f - 1) ltac:(lia)); reflexivity).
        replace ((top - 1) ≪ 3)%Z with (8 * (top - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
        apply K. exact I2.
  Qed.

  Lemma rshg_last : forall m1 x5 x6 x7 x12 x14 x15 x16 x17 x21,
    RINVG m f fp T rb m1 (length f - 1) ->
    (forall m2 x10,
       limbs_at bgpsegs m2 T (map (rsh_at f rb) (seq 0 (length f))) -> mem_inv bgpsegs m2 ->
       munch [(T, T + 8 * top)]%Z m m2 -> wmono bgpsegs m m2 ->
       evt bgpsegs POST (SH 0xff4ec m2 x5 x6 x7 x10 (Z_to_bv 64 (rsh_at f rb (length f - 1))) x12 (Z_to_bv 64 (8 * (top - 1))) x14 x15 x16 x17 x21)) ->
    evt bgpsegs POST (SH 0xff4e4 m1 x5 x6 x7 (Z_to_bv 64 T) (Z_to_bv 64 (rsh_at f rb (length f - 1))) x12 (Z_to_bv 64 (8 * (top - 1))) x14 x15 x16 x17 x21).
  Proof.
    intros m1 x5 x6 x7 x12 x14 x15 x16 x17 x21 I K.
    pose proof I as (_ & _ & WT & MI & _).
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below bgpsegs m1 T (8 * top) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    zstep.
    destruct (RINVG_store m f fp T rb m1 (length f - 1) _ DISJ ltac:(lia) I ltac:(lia) eq_refl) as [SOK I1].
    replace (T + 8 * Z.of_nat (length f - 1))%Z with (T + 8 * (top - 1))%Z in SOK, I1 by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    destruct I1 as (HW & _ & WT2 & MI2 & MU2 & WM2).
    replace (S (length f - 1)) with (length f) in HW by lia.
    apply K; assumption.
  Qed.
End Block.
