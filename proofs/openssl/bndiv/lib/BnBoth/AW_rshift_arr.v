(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA ZBridge.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import ShiftPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import AW_lshift_arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2248904 => 2
  | 2248916 => 1
  | 2248920 => 2
  | 2248988 => 1
  | 2248992 => 2
  | 2249016 => 2
  | 2249020 => 1
  | 2249024 => 2
  | 2249072 => 1
  | 2249076 => 1
  | 2249080 => 2
  | 2249084 => 1
  | 2249088 => 1
  | 2249092 => 1
  | 2249096 => 1
  | 2249100 => 2
  | 2249104 => 2
  | 2249108 => 1
  | 2249112 => 2
  | 2249120 => 2
  | 2249176 => 1
  | 2249180 => 1
  | 2249184 => 1
  | 2249192 => 1
  | 2249200 => 1
  | 2249224 => 2
  | 2249252 => 2
  | 2249256 => 1
  | 2249260 => 1
  | 2249264 => 2
  | 2249268 => 2
  | 2249356 => 2
  | 2249360 => 1
  | 2249364 => 1
  | 2249368 => 1
  | 2249372 => 2
  | 2249376 => 2
  | 2249380 => 1
  | 2249384 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

(* [comment removed for export] *)
Definition RINVA (m : word -> option byte) (f : list Z) (fp T n : Z) (m1 : word -> option byte) (i : nat) : Prop :=
  limbs_at bsegs m1 T (map (rsh_at f n) (seq 0 i)) /\ limbs_at bsegs m1 fp f /\
  wr_at bsegs m1 T (8 * Z.of_nat (length f)) /\ mem_inv bsegs m1 /\
  munch [(T, T + 8 * Z.of_nat (length f))]%Z m m1 /\ wmono bsegs m m1.

Lemma RINVA_store : forall m f fp T n m1 i v,
  (fp + 8 * Z.of_nat (length f) <= T \/ T + 8 * Z.of_nat (length f) <= fp)%Z ->
  RINVA m f fp T n m1 i -> (i < length f)%nat -> v = rsh_at f n i ->
  store_ok bsegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true /\
  RINVA m f fp T n (write_to_mem m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v))) (S i).
Proof.
  intros m f fp T n m1 i v DISJ (HW & HF & WT & MI & MU & WM) Hi ->.
  pose proof (limbs_at_bound _ _ _ _ HF) as BF.
  assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
  pose proof (wr_at_below bsegs m1 T (8 * Z.of_nat (length f)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
  assert (L8 : length (le8 (Z_to_bv 64 (rsh_at f n i))) = 8%nat) by apply length_le8.
  assert (SOK : store_ok bsegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true).
  { change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)). apply (wr_at_store_ok bsegs m1 T (8 * Z.of_nat (length f))); [exact WT | lia | lia]. }
  split; [exact SOK|].
  change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)).
  unfold RINVA.
  split. { rewrite seq_S, map_app. cbn [map Nat.add].
           replace (T + 8 * Z.of_nat i)%Z with (T + 8 * Z.of_nat (length (map (rsh_at f n) (seq 0 i))))%Z by (rewrite length_map, length_seq; reflexivity).
           apply limbs_at_snoc_write; [exact HW | rewrite length_map, length_seq; lia]. }
  split. { apply limbs_at_write_other; [exact HF | lia | rewrite L8; lia | rewrite L8; lia]. }
  split. { apply wr_at_write. exact WT. }
  split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
  split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
  apply wmono_write. exact WM.
Qed.

Section Block.
  Variables (ra sp gp tp s0 s1 s3 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp T n : Z).
  Notation top := (Z.of_nat (length f)).
  Hypothesis Hn : (0 <= n < 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis DISJ : (fp + 8 * top <= T \/ T + 8 * top <= fp)%Z.
  (* [comment removed for export] *)
  Hypothesis ACF : acc bsegs m fp (8 * top).
  Hypothesis ACT : acc bsegs m T (8 * top).
  Hypothesis ALF : (fp mod 8 = 0)%Z.
  Hypothesis ALT : (T mod 8 = 0)%Z.
  Hypothesis OFFT : offshW [(T, T + 8 * top)]%Z.
  Hypothesis UBF : (0 < fp)%Z.
  Hypothesis UBT : (0 < T)%Z.

  Notation lbm := ((64 - n) mod 64)%Z.
  Notation rmask := (if (n =? 0)%Z then 0 else 18446744073709551615)%Z.
  (* [comment removed for export] *)
  Notation SH pc mm x5 x6 x7 x10 x11 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 (Z_to_bv 64 n) (Z_to_bv 64 T) x14 x15 x16 x17 (Z_to_bv 64 top) x19 x20 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Definition BNDR : Prop := ((0 <= fp /\ fp + 8 * top <= 140737488355328) /\ (0 <= T /\ T + 8 * top <= 140737488355328))%Z.

  Lemma shF : forall m1 i (k : nat) ad, BNDR -> RINVA m f fp T n m1 i -> (k < length f)%nat -> ad = wa (shad (fp + 8 * Z.of_nat k)) ->
    ov_read_bytes bsegs m1 ad 1 = Some [z8].
  Proof using ACF ALF OFFT.
    intros m1 i k ad (BF & _) (_ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bsegs _ m m1 fp top 0 (Z.of_nat k) _ ACF MU OFFT ALF BF); [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.
  Lemma shT : forall m1 i (k : nat) ad, BNDR -> RINVA m f fp T n m1 i -> (k < length f)%nat -> ad = wa (shad (T + 8 * Z.of_nat k)) ->
    ov_read_bytes bsegs m1 ad 1 = Some [z8].
  Proof using ACT ALT OFFT.
    intros m1 i k ad (_ & BT) (_ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bsegs _ m m1 T top 0 (Z.of_nat k) _ ACT MU OFFT ALT BT); [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Notation HEAD mm i x20 x30 x31 :=
    (SH 0x225204 mm (Z_to_bv 64 lbm) (Z_to_bv 64 1) (Z_to_bv 64 rmask) (Z_to_bv 64 fp) (Z_to_bv 64 (8 * Z.of_nat i))
        (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (nth i f 0%Z)) (Z_to_bv 64 (18446744073709551615 - fp)) (Z_to_bv 64 1) s3 x20
        (Z_to_bv 64 (fp + 8)) (Z_to_bv 64 (top - 1 - Z.of_nat i)) x30 x31).
  Notation KTAIL :=
    (forall m2 x5 x6 x7 x10 x11 x16 x17 x20 x28 x29 x31,
       RINVA m f fp T n m2 (length f - 1) ->
       evt bsegs POST (SH 0x225284 m2 x5 x6 x7 x10 x11 (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x16 x17 s3 x20 x28 x29
                          (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x31)).

  Lemma rsh_round : forall (i : nat) m1 x20 x30 x31,
    BNDR -> (S i < length f)%nat -> RINVA m f fp T n m1 i ->
    ((S (S i) = length f)%nat -> KTAIL) ->
    ((S (S i) < length f)%nat -> forall m2 x20 x30 x31, RINVA m f fp T n m2 (S i) -> evt bsegs POST (HEAD m2 (S i) x20 x30 x31)) ->
    evt bsegs POST (HEAD m1 i x20 x30 x31).
  Proof.
    intros i m1 x20 x30 x31 B Hi I KE KL.
    pose proof I as (_ & HF & WT & MI & _).
    pose proof B as (BF & BT).
    assert (RI : (0 <= nth i f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (RS : (0 <= nth (S i) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (NS : nth_error f (S i) = Some (nth (S i) f 0%Z)) by (apply nth_error_nth'; lia).
    assert (Hi' : (Z.of_nat i + 1 < top)%Z) by (clear - Hi; lia).
    zstep. ub. zstep.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shF m1 _ (S i) ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    zstep. ub.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shT m1 _ i ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bsegs m1 fp f (S i) _ ad HF NS ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 4 zstep.
    setreg 15%Z (Z_to_bv 64 (rsh_at f n i))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (rsh_hi_machine n _ Hn), (shrw_machine n _ Hn), (rsh_at_mid f n i Hi); reflexivity).
    zstep.
    destruct (RINVA_store m f fp T n m1 i _ DISJ I ltac:(lia) eq_refl) as [SOK I1].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    clear SOK I HF WT MI. try clear m1.
    do 2 zstep.
    zstep. if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      replace (8 * Z.of_nat i + 8)%Z with (8 * Z.of_nat (S i))%Z by lia.
      replace (top - 1 - Z.of_nat i + -1)%Z with (top - 1 - Z.of_nat (S i))%Z by lia.
      eapply KL; [clear - KB Hi; lia | exact I1].
    - (* [comment removed for export] *)
      assert (E : (S (S i) = length f)%nat) by (clear - KB Hi; lia).
      replace (S i) with (length f - 1)%nat in * by lia.
      zstep.
      eapply KE; [exact E | exact I1].
  Qed.

  Lemma rsh_loop : forall (k i : nat) m1 x20 x30 x31,
    BNDR -> (S i + k = length f - 1)%nat -> (S i < length f)%nat -> RINVA m f fp T n m1 i -> KTAIL -> evt bsegs POST (HEAD m1 i x20 x30 x31).
  Proof.
    induction k as [|k IH]; intros i m1 x20 x30 x31 B Hk Hi I K.
    - eapply rsh_round; [exact B | exact Hi | exact I | intros _; exact K | intros C; exfalso; lia].
    - eapply rsh_round; [exact B | exact Hi | exact I | intros C; exfalso; lia | ].
      intros _ m2 y20 y30 y31 I2. eapply IH; [exact B | lia | lia | exact I2 | exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma rsh_tail : forall m1 x5 x6 x7 x10 x11 x16 x17 x20 x28 x29 x31,
    BNDR -> RINVA m f fp T n m1 (length f - 1) ->
    (forall m2 x5 x6 x7 x10 x11 x14 x15 x16 x17 x20 x28 x29 x30 x31,
       limbs_at bsegs m2 T (map (rsh_at f n) (seq 0 (length f))) -> limbs_at bsegs m2 fp f -> mem_inv bsegs m2 ->
       munch [(T, T + 8 * top)]%Z m m2 -> wmono bsegs m m2 ->
       evt bsegs POST (SH 0x2252c8 m2 x5 x6 x7 x10 x11 x14 x15 x16 x17 (Z_to_bv 64 (bv_unsigned s3 + 16)) x20 x28 x29 x30 x31)) ->
    evt bsegs POST (SH 0x225284 m1 x5 x6 x7 x10 x11 (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x16 x17 s3 x20 x28 x29
                       (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x31).
  Proof.
    intros m1 x5 x6 x7 x10 x11 x16 x17 x20 x28 x29 x31 B I K.
    pose proof I as (_ & _ & WT & MI & _).
    pose proof B as (BF & BT).
    assert (RLl : (0 <= nth (length f - 1) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    pose proof (zr_word s3) as Z3. unfold inr64 in Z3.
    zstep.
    replace ((top - 1) ≪ 3)%Z with (8 * (top - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    ub.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shT m1 _ (length f - 1)%nat ad B I ltac:(lia) ltac:(unfold wa, shad; f_equal; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear - Htop; Z.div_mod_to_equations; lia)) as RD); zstep; clear RD. chk0.
    zstep.
    setreg 11%Z (Z_to_bv 64 (rsh_at f n (length f - 1)))
      ltac:(f_equal; rewrite (shrw_machine n _ Hn), (rsh_at_last f n (length f - 1) ltac:(lia)); reflexivity).
    zstep.
    destruct (RINVA_store m f fp T n m1 (length f - 1) _ DISJ I ltac:(lia) eq_refl) as [SOK I1].
    replace (T + 8 * Z.of_nat (length f - 1))%Z with (T + 8 * (top - 1))%Z in SOK, I1 by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    destruct I1 as (HW & HF2 & WT2 & MI2 & MU2 & WM2).
    replace (S (length f - 1)) with (length f) in HW by lia.
    apply K; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rsh_blockA : forall x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31,
    limbs_at bsegs m fp f -> wr_at bsegs m T (8 * top) -> mem_inv bsegs m ->
    (forall m2 x5 x6 x7 x10 x11 x14 x15 x16 x17 x20 x28 x29 x30 x31,
       limbs_at bsegs m2 T (map (rsh_at f n) (seq 0 (length f))) -> limbs_at bsegs m2 fp f -> mem_inv bsegs m2 ->
       munch [(T, T + 8 * top)]%Z m m2 -> wmono bsegs m m2 ->
       evt bsegs POST (SH 0x2252c8 m2 x5 x6 x7 x10 x11 x14 x15 x16 x17 (Z_to_bv 64 (bv_unsigned s3 + 16)) x20 x28 x29 x30 x31)) ->
    evt bsegs POST (SH 0x2251bc m x5 x6 x7 (Z_to_bv 64 fp) (Z_to_bv 64 (top - 1)) x14 x15 x16 x17 s3 (Z_to_bv 64 n) x28 x29 x30 x31).
  Proof.
    intros x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 HF WT MI K.
    assert (B : BNDR).
    { split; [exact (limbs_at_b47 bsegs m fp f HF MI ltac:(lia)) |].
      pose proof (wr_at_b47 bsegs m T (8 * top) WT MI ltac:(lia)) as H. lia. }
    pose proof B as (BF & BT).
    assert (N0 : nth_error f 0 = Some (nth 0 f 0%Z)) by (apply nth_error_nth'; lia).
    assert (R0 : (0 <= nth 0 f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bsegs m fp f 0 _ ad HF N0 ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 3 zstep.
    setreg 14%Z (Z_to_bv 64 (top - 1))
      ltac:(f_equal; symmetry; rewrite ub_lxor_sign63 by lia;
            destruct (Z.ltb_spec 9223372036854775808 (top - 1 + 9223372036854775808)) as [L|L]; cbn [Z.b2z];
            [ change ((0 - 1) mod 18446744073709551616)%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; lia
            | change ((0 - 0) mod 18446744073709551616)%Z with 0%Z; rewrite Z.land_0_l; lia ]).
    assert (I0 : RINVA m f fp T n m 0).
    { unfold RINVA. cbn [seq map]. split; [apply limbs_at_nil; lia|]. split; [exact HF|]. split; [exact WT|]. split; [exact MI|].
      split; [apply munch_refl | apply wmono_refl]. }
    zstep. rewrite lts_signed by lia. if_cases KT; zify_cond KT.
    - (* [comment removed for export] *)
      zstep.
      assert (E1 : (length f - 1 = 0)%nat) by lia.
      eapply evt_eq; [ | eapply rsh_tail; [exact B | rewrite E1; exact I0 | exact K] ].
      rewrite E1. replace (top - 1)%Z with 0%Z by lia. reflexivity.
    - zstep. zstep. ub. zstep.
      change (Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63) with (negn_mA n). rewrite (negn_mA_eq n Hn).
      ub. zstep. ub. do 2 zstep.
      change (Z.lor (((0 - lbm) mod 18446744073709551616) ≫ 8) ((0 - lbm) mod 18446744073709551616)) with (rmask_m lbm).
      rewrite (rmask_m_eq n Hn).
      do 2 zstep.
      setreg 6%Z (Z_to_bv 64 1) ltac:(f_equal; symmetry; rewrite (land7 _ ALT); replace (0 <? T)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      setreg 17%Z (Z_to_bv 64 1) ltac:(f_equal; symmetry; replace (0 <? T)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      setreg 16%Z (Z_to_bv 64 (18446744073709551615 - fp)) ltac:(f_equal; symmetry; apply zb_lxor_ones; lia).
      eapply evt_eq; [ | eapply (rsh_loop (length f - 2) 0 m _ x30 x31); [exact B | lia | lia | exact I0 | ] ].
      + replace (8 * Z.of_nat 0)%Z with 0%Z by lia. replace (top - 1 - Z.of_nat 0)%Z with (top - 1)%Z by lia. reflexivity.
      + intros m2 y5 y6 y7 y10 y11 y16 y17 y20 y28 y29 y31 I2. eapply rsh_tail; [exact B | exact I2 | exact K].
  Qed.
End Block.
