(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import ShiftPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition RINVG (m : word -> option byte) (f : list Z) (fp T rb : Z) (m1 : word -> option byte) (i : nat) : Prop :=
  limbs_at bgusegs m1 T (map (rsh_at f rb) (seq 0 i)) /\
  ((S i <= length f)%nat -> limbs_at bgusegs m1 (fp + 8 * Z.of_nat (S i)) (skipn (S i) f)) /\
  wr_at bgusegs m1 T (8 * Z.of_nat (length f)) /\ mem_inv bgusegs m1 /\
  munch [(T, T + 8 * Z.of_nat (length f))]%Z m m1 /\ wmono bgusegs m m1.

Lemma RINVG_store : forall m f fp T rb m1 i v,
  (T <= fp \/ fp + 8 * Z.of_nat (length f) <= T)%Z -> (0 <= fp)%Z ->
  RINVG m f fp T rb m1 i -> (i < length f)%nat -> v = rsh_at f rb i ->
  store_ok bgusegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true /\
  RINVG m f fp T rb (write_to_mem m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v))) (S i).
Proof.
  intros m f fp T rb m1 i v DISJ FP0 (HW & HS & WT & MI & MU & WM) Hi ->.
  assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
  pose proof (wr_at_below bgusegs m1 T (8 * Z.of_nat (length f)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
  assert (L8 : length (le8 (Z_to_bv 64 (rsh_at f rb i))) = 8%nat) by apply length_le8.
  assert (SOK : store_ok bgusegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true).
  { change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)). apply (wr_at_store_ok bgusegs m1 T (8 * Z.of_nat (length f))); [exact WT | lia | lia]. }
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

Lemma lxor_signbit63 : forall x, (0 <= x < 9223372036854775808)%Z -> Z.lxor x 9223372036854775808 = (x + 9223372036854775808)%Z.
Proof.
  intros x H. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec, Z.bits_0. change 9223372036854775808%Z with (2 ^ 63)%Z. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 k) as [<-|NE]; [|apply andb_false_r]. rewrite andb_true_r.
  destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma max0_m : forall x, (0 <= x < 2147483648)%Z ->
  Z.land ((0 - Z.b2z (9223372036854775808 <? Z.lxor x 9223372036854775808)) mod 18446744073709551616) x = x.
Proof.
  intros x H. rewrite lxor_signbit63 by lia.
  destruct (Z.ltb_spec 9223372036854775808 (x + 9223372036854775808)) as [P|P]; cbn [Z.b2z].
  - change ((0 - 1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - assert (x = 0)%Z by lia. subst x. reflexivity.
Qed.

Section Block.
  Variables (ra sp gp tp s0 s2 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp T RS n rb : Z).
  Notation top := (Z.of_nat (length f)).
  Hypothesis Hn : (0 <= n < 2147483648)%Z.
  Hypothesis Hrb : (0 <= rb < 64)%Z.
  Hypothesis Erb : Z.land n 63 = rb.
  Hypothesis Enn : Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63 = ((64 - rb) mod 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis DISJ : (T <= fp \/ fp + 8 * top <= T)%Z.
  Hypothesis UBT : (0 < T /\ T mod 8 = 0 /\ 0 < fp /\ fp mod 8 = 0)%Z.

  Notation lbm := ((64 - rb) mod 64)%Z.
  Notation rmask := (if (rb =? 0)%Z then 0 else 18446744073709551615)%Z.
  Notation SH pc mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 (Z_to_bv 64 RS) x10 x11 x12 x13 x14 x15 x16 x17 s2 (Z_to_bv 64 top) (Z_to_bv 64 n) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).
  Notation ND := (Z.lxor fp 18446744073709551615).

  Notation HEAD mm i x28 x30 x31 :=
    (SH 0x10a67c mm (Z_to_bv 64 lbm) (Z_to_bv 64 1) (Z_to_bv 64 rmask) (Z_to_bv 64 rb) (Z_to_bv 64 T) (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (nth i f 0%Z))
        (Z_to_bv 64 (fp + 8)) (Z_to_bv 64 ND) (Z_to_bv 64 (8 * Z.of_nat i)) (Z_to_bv 64 1) x28 (Z_to_bv 64 (top - 1 - Z.of_nat i)) x30 x31).
  Notation KEXIT :=
    (forall m2 x14 x16 x29 x30 x31,
       RINVG m f fp T rb m2 (length f - 1) ->
       evt bgusegs POST (SH 0x10a6dc m2 (Z_to_bv 64 lbm) (Z_to_bv 64 1) (Z_to_bv 64 rmask) (Z_to_bv 64 rb) (Z_to_bv 64 T) (Z_to_bv 64 (top - 1))
                          (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x14 (Z_to_bv 64 ND) x16 (Z_to_bv 64 1) (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x29 x30 x31)).

  Lemma rshg_round : forall (i : nat) m1 x28 x30 x31,
    (S i < length f)%nat -> RINVG m f fp T rb m1 i ->
    ((S (S i) = length f)%nat -> KEXIT) ->
    ((S (S i) < length f)%nat -> forall m2 x28 x30 x31, RINVG m f fp T rb m2 (S i) -> evt bgusegs POST (HEAD m2 (S i) x28 x30 x31)) ->
    evt bgusegs POST (HEAD m1 i x28 x30 x31).
  Proof.
    intros i m1 x28 x30 x31 Hi I KE KL.
    pose proof I as (_ & HS & WT & MI & _). specialize (HS ltac:(lia)).
    pose proof (limbs_at_bound _ _ _ _ HS) as BF. rewrite length_skipn in BF. try change (2 ^ 64)%Z with 18446744073709551616%Z in BF.
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below bgusegs m1 T (8 * top) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (RI : (0 <= nth i f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (RSl : (0 <= nth (S i) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (NS : nth_error (skipn (S i) f) 0 = Some (nth (S i) f 0%Z)).
    { rewrite nth_error_skipn, Nat.add_0_r. apply nth_error_nth'. lia. }
    assert (END : (Z.lxor fp 18446744073709551615 = 18446744073709551615 - fp)%Z) by (apply zb_lxor_ones; lia).
    zstep.
    chk ltac:(fun C => rewrite END in C; clear - C BF Hi; lia).
    zstep.
    chk ltac:(fun C => clear - C T0 TOPB Hi; lia).
    zstep. replace (T + 8 * Z.of_nat i <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - UBT; lia).
    cbn [Z.b2z]. zstep. cbn [Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep.
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgusegs m1 (fp + 8 * Z.of_nat (S i)) (skipn (S i) f) 0 _ ad HS NS ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 5 zstep.
    setreg 13%Z (Z_to_bv 64 (rsh_at f rb i))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (rsh_hi_machine rb _ Hrb), (shrw_machine rb _ Hrb), (rsh_at_mid f rb i Hi); reflexivity).
    destruct (RINVG_store m f fp T rb m1 i _ DISJ ltac:(lia) I ltac:(lia) eq_refl) as [SOK I1].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    clear SOK I HS WT MI BF. try clear m1.
    do 2 zstep.
    zstep. if_cases KB; zify_cond KB.
    -
      replace (8 * Z.of_nat i + 8)%Z with (8 * Z.of_nat (S i))%Z by (clear; lia).
      replace (top - 1 - Z.of_nat i + -1)%Z with (top - 1 - Z.of_nat (S i))%Z by (clear; lia).
      eapply KL; [ | exact I1].
      rewrite ?unsigned_lit in KB by (clear - Hi Htop; lia). clear - KB Hi. lia.
    -
      assert (E : (S (S i) = length f)%nat) by (rewrite ?unsigned_lit in KB by (clear - Hi Htop; lia); clear - KB Hi; lia).
      zstep.
      replace (S i) with (length f - 1)%nat in * by (clear - E; lia).
      eapply KE; [exact E | exact I1].
  Qed.

  Lemma rshg_loop : forall (k i : nat) m1 x28 x30 x31,
    (S i + k = length f - 1)%nat -> (S i < length f)%nat -> RINVG m f fp T rb m1 i -> KEXIT -> evt bgusegs POST (HEAD m1 i x28 x30 x31).
  Proof.
    induction k as [|k IH]; intros i m1 x28 x30 x31 Hk Hi I K.
    - eapply rshg_round; [exact Hi | exact I | intros _; exact K | intros C; exfalso; lia].
    - eapply rshg_round; [exact Hi | exact I | intros C; exfalso; lia | ].
      intros _ m2 y28 y30 y31 I2. eapply IH; [lia | lia | exact I2 | exact K].
  Qed.

  Lemma rshg_addr : forall m2 x5 x6 x7 x13 x14 x15 x16 x17 x29 x30 x31,
    RINVG m f fp T rb m2 (length f - 1) ->
    (forall x11 x13 x14,
       evt bgusegs POST (SH 0x10a704 m2 x5 x6 x7 (Z_to_bv 64 rb) x11 (Z_to_bv 64 (T + 8 * (top - 1))) x13 x14 x15 x16 x17 (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x29 x30 x31)) ->
    evt bgusegs POST (SH 0x10a6dc m2 x5 x6 x7 (Z_to_bv 64 rb) (Z_to_bv 64 T) (Z_to_bv 64 (top - 1)) x13 x14 x15 x16 x17 (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x29 x30 x31).
  Proof.
    intros m2 x5 x6 x7 x13 x14 x15 x16 x17 x29 x30 x31 I K.
    pose proof I as (_ & _ & WT & MI & _).
    pose proof (wr_at_below bgusegs m2 T (8 * top) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    zstep. replace ((top - 1) ≪ 3)%Z with (8 * (top - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    chk ltac:(fun C => clear - C UBT TOPB Htop; lia).
    zstep. replace (0 <? T)%Z with true by (symmetry; apply Z.ltb_lt; clear - UBT; lia).
    zstep. replace (T + 8 * (top - 1) <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - UBT Htop; lia).
    cbn [Z.b2z]. zstep. cbn [Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    chk ltac:(fun C => clear - C UBT TOPB Htop; lia).
    zstep. rewrite (land7 (T + 8 * (top - 1))) by (clear - UBT; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
    apply K.
  Qed.

  Lemma rshg_block : forall x5 x6 x7 x10 x11 x12 x13 x16 x17 x28 x29 x30 x31 (r1 r2 r3 r4 : word),
    limbs_at bgusegs m fp f -> wr_at bgusegs m T (8 * top) -> mem_inv bgusegs m ->
    rw_cells bgusegs m RS [C8 (Z_to_bv 64 T); C4 r1; C4 r2; C4 r3; C4 r4] ->
    (forall m2 x5 x6 x7 x11 x13 x14 x15 x16 x17 x29 x30 x31,
       RINVG m f fp T rb m2 (length f - 1) ->
       evt bgusegs POST (SH 0x10a704 m2 x5 x6 x7 (Z_to_bv 64 rb) x11 (Z_to_bv 64 (T + 8 * (top - 1))) x13 x14 x15 x16 x17 (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x29 x30 x31)) ->
    evt bgusegs POST (SH 0x10a62c m x5 x6 x7 x10 x11 x12 x13 (Z_to_bv 64 fp) (Z_to_bv 64 (top - 1)) x16 x17 x28 x29 x30 x31).
  Proof.
    intros x5 x6 x7 x10 x11 x12 x13 x16 x17 x28 x29 x30 x31 r1 r2 r3 r4 HF WT MI RSC K.
    pose proof (limbs_at_bound _ _ _ _ HF) as BF. change (2 ^ 64)%Z with 18446744073709551616%Z in BF.
    pose proof (wr_at_below bgusegs m T (8 * top) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    zstep.
    rewrite Erb.
    step. clear RSC.
    assert (N0 : nth_error f 0 = Some (nth 0 f 0%Z)) by (apply nth_error_nth'; lia).
    assert (R0 : (0 <= nth 0 f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgusegs m fp f 0 _ ad HF N0 ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 3 zstep.
    rewrite (max0_m (top - 1)) by (clear - Htop; lia).
    assert (I0 : RINVG m f fp T rb m 0).
    { unfold RINVG. cbn [seq map]. split; [apply limbs_at_nil; lia|]. split. { intros _. rewrite <- (firstn_skipn 1 f) in HF. apply limbs_at_app in HF. destruct HF as [_ HF2]. rewrite length_firstn in HF2. replace (Nat.min 1 (length f)) with 1%nat in HF2 by lia. exact HF2. } split; [exact WT|]. split; [exact MI|].
      split; [apply munch_refl | apply wmono_refl]. }
    zstep. if_cases KT; zify_cond KT.
    -
      assert (E1 : (length f - 1 = 0)%nat) by (apply andb_false_iff in KT; destruct KT as [KT|KT]; apply Z.ltb_ge in KT; lia).
      zstep.
      replace (nth 0 f 0%Z) with (nth (length f - 1) f 0%Z) by (rewrite E1; reflexivity).
      assert (I0' : RINVG m f fp T rb m (length f - 1)) by (rewrite E1; exact I0).
      eapply rshg_addr; [exact I0' | ].
      intros y11 y13 y14. apply K. exact I0'.
    - do 13 zstep.
      rewrite Enn.
      change (Z.lor (((0 - lbm) mod 18446744073709551616) ≫ 8) ((0 - lbm) mod 18446744073709551616)) with (rmask_m lbm).
      rewrite (rmask_m_eq rb Hrb).
      rewrite (land7 T) by (clear - UBT; lia).
      replace (0 <? T)%Z with true by (symmetry; apply Z.ltb_lt; clear - UBT; lia).
      cbn [Z.ltb Z.compare Z.b2z]. change (Z.land 1 1) with 1%Z.
      eapply evt_eq; [ | eapply (rshg_loop (length f - 2) 0 m _ _ _); [lia | lia | exact I0 | ] ].
      + replace (8 * Z.of_nat 0)%Z with 0%Z by lia. replace (top - 1 - Z.of_nat 0)%Z with (top - 1)%Z by lia. reflexivity.
      + intros m2 y14 y16 y29 y30 y31 I2.
        eapply rshg_addr; [exact I2 | ].
        intros y11 y13 z14. apply K. exact I2.
  Qed.

  Lemma rshg_last : forall m1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x29 x30 x31,
    RINVG m f fp T rb m1 (length f - 1) ->
    (forall m2 x10,
       limbs_at bgusegs m2 T (map (rsh_at f rb) (seq 0 (length f))) -> mem_inv bgusegs m2 ->
       munch [(T, T + 8 * top)]%Z m m2 -> wmono bgusegs m m2 ->
       evt bgusegs POST (SH 0x10a710 m2 x5 x6 x7 x10 x11 (Z_to_bv 64 (T + 8 * (top - 1))) x13 x14 x15 x16 x17 (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x29 x30 x31)) ->
    evt bgusegs POST (SH 0x10a708 m1 x5 x6 x7 (Z_to_bv 64 rb) x11 (Z_to_bv 64 (T + 8 * (top - 1))) x13 x14 x15 x16 x17 (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x29 x30 x31).
  Proof.
    intros m1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x29 x30 x31 I K.
    pose proof I as (_ & _ & WT & MI & _).
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below bgusegs m1 T (8 * top) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (RLl : (0 <= nth (length f - 1) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    zstep.
    setreg 10%Z (Z_to_bv 64 (rsh_at f rb (length f - 1)))
      ltac:(f_equal; rewrite (shrw_machine rb _ Hrb), (rsh_at_last f rb (length f - 1) ltac:(lia)); reflexivity).
    destruct (RINVG_store m f fp T rb m1 (length f - 1) _ DISJ ltac:(lia) I ltac:(lia) eq_refl) as [SOK I1].
    replace (T + 8 * Z.of_nat (length f - 1))%Z with (T + 8 * (top - 1))%Z in SOK, I1 by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    destruct I1 as (HW & HF1 & WT1 & MI1 & MU1 & WM1).
    replace (S (length f - 1)) with (length f) in HW by lia.
    apply K; assumption.
  Qed.
End Block.
