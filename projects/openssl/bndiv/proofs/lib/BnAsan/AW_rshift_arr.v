(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Layout Shadow.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import ShiftPure.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf AW_lshift_arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition RINVA (m : word -> option byte) (f : list Z) (fp T n : Z) (m1 : word -> option byte) (i : nat) : Prop :=
  limbs_at asegs m1 T (map (rsh_at f n) (seq 0 i)) /\ limbs_at asegs m1 fp f /\
  wr_at asegs m1 T (8 * Z.of_nat (length f)) /\ mem_inv asegs m1 /\
  munch [(T, T + 8 * Z.of_nat (length f))]%Z m m1 /\ wmono asegs m m1.

Lemma RINVA_store : forall m f fp T n m1 i v,
  (fp + 8 * Z.of_nat (length f) <= T \/ T + 8 * Z.of_nat (length f) <= fp)%Z ->
  RINVA m f fp T n m1 i -> (i < length f)%nat -> v = rsh_at f n i ->
  store_ok asegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true /\
  RINVA m f fp T n (write_to_mem m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v))) (S i).
Proof.
  intros m f fp T n m1 i v DISJ (HW & HF & WT & MI & MU & WM) Hi ->.
  pose proof (limbs_at_bound _ _ _ _ HF) as BF.
  assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
  pose proof (wr_at_below asegs m1 T (8 * Z.of_nat (length f)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
  assert (L8 : length (le8 (Z_to_bv 64 (rsh_at f n i))) = 8%nat) by apply length_le8.
  assert (SOK : store_ok asegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true).
  { change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)). apply (wr_at_store_ok asegs m1 T (8 * Z.of_nat (length f))); [exact WT | lia | lia]. }
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
  Variables (ra sp gp tp s0 s1 s3 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp T n : Z).
  Notation top := (Z.of_nat (length f)).
  Hypothesis Hn : (0 <= n < 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis DISJ : (fp + 8 * top <= T \/ T + 8 * top <= fp)%Z.
  (* [comment removed for export] *)
  Hypothesis ACF : acc asegs m fp (8 * top).
  Hypothesis ACT : acc asegs m T (8 * top).
  Hypothesis ALF : (fp mod 8 = 0)%Z.
  Hypothesis ALT : (T mod 8 = 0)%Z.
  Hypothesis OFFT : offshW [(T, T + 8 * top)]%Z.

  Notation lbm := ((64 - n) mod 64)%Z.
  Notation rmask := (if (n =? 0)%Z then 0 else 18446744073709551615)%Z.
  (* [comment removed for export] *)
  Notation SH pc mm x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x28 x29 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 (Z_to_bv 64 T) x14 x15 x16 x17 (Z_to_bv 64 top) s3 (Z_to_bv 64 n) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Definition BNDR : Prop := ((0 <= fp /\ fp + 8 * top <= 140737488355328) /\ (0 <= T /\ T + 8 * top <= 140737488355328))%Z.

  Lemma shF : forall m1 i (k : nat) ad, BNDR -> RINVA m f fp T n m1 i -> (k < length f)%nat -> ad = wa (shad (fp + 8 * Z.of_nat k)) ->
    ov_read_bytes asegs m1 ad 1 = Some [z8].
  Proof using ACF ALF OFFT.
    intros m1 i k ad (BF & _) (_ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb asegs _ m m1 fp top 0 (Z.of_nat k) _ ACF MU OFFT ALF BF); [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.
  Lemma shT : forall m1 i (k : nat) ad, BNDR -> RINVA m f fp T n m1 i -> (k < length f)%nat -> ad = wa (shad (T + 8 * Z.of_nat k)) ->
    ov_read_bytes asegs m1 ad 1 = Some [z8].
  Proof using ACT ALT OFFT.
    intros m1 i k ad (_ & BT) (_ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb asegs _ m m1 T top 0 (Z.of_nat k) _ ACT MU OFFT ALT BT); [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Notation HEAD mm i x28 x29 :=
    (SH 0x226cdc mm (Z_to_bv 64 rmask) (Z_to_bv 64 (top - 1 - Z.of_nat i)) (Z_to_bv 64 (T + 8 * Z.of_nat i)) (Z_to_bv 64 (fp + 8 * Z.of_nat (S i)))
        (Z_to_bv 64 (T + 8 * Z.of_nat i)) (Z_to_bv 64 n) (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (nth i f 0%Z)) (Z_to_bv 64 (fp + 8 * Z.of_nat (S i)))
        (Z_to_bv 64 lbm) x28 x29).
  Notation KTAIL :=
    (forall m2 x5 x6 x7 x10 x11 x16 x17 x28 x29,
       RINVA m f fp T n m2 (length f - 1) ->
       evt asegs POST (SH 0x226d48 m2 x5 x6 x7 x10 x11 (Z_to_bv 64 n) (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x16 x17 x28 x29)).

  Lemma rsh_round : forall (i : nat) m1 x28 x29,
    BNDR -> (S i < length f)%nat -> RINVA m f fp T n m1 i ->
    ((S (S i) = length f)%nat -> KTAIL) ->
    ((S (S i) < length f)%nat -> forall m2 x28 x29, RINVA m f fp T n m2 (S i) -> evt asegs POST (HEAD m2 (S i) x28 x29)) ->
    evt asegs POST (HEAD m1 i x28 x29).
  Proof.
    intros i m1 x28 x29 B Hi I KE KL.
    pose proof I as (_ & HF & WT & MI & _).
    pose proof B as (BF & BT).
    assert (RI : (0 <= nth i f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (RS : (0 <= nth (S i) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (NS : nth_error f (S i) = Some (nth (S i) f 0%Z)) by (apply nth_error_nth'; lia).
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shF m1 _ (S i) ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shT m1 _ i ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth asegs m1 fp f (S i) _ ad HF NS ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 7 zstep.
    setreg 15%Z (Z_to_bv 64 (rsh_at f n i))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (rsh_hi_machine n _ Hn), (shrw_machine n _ Hn), (rsh_at_mid f n i Hi); reflexivity).
    destruct (RINVA_store m f fp T n m1 i _ DISJ I ltac:(lia) eq_refl) as [SOK I1].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    clear SOK I HF WT MI. try clear m1.
    do 3 zstep.
    zstep. if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      replace (T + 8 * Z.of_nat i + 8)%Z with (T + 8 * Z.of_nat (S i))%Z by lia.
      replace (fp + 8 * Z.of_nat (S i) + 8)%Z with (fp + 8 * Z.of_nat (S (S i)))%Z by lia.
      replace (top - 1 - Z.of_nat i + -1)%Z with (top - 1 - Z.of_nat (S i))%Z by lia.
      eapply KL; [clear - KB Hi; lia | exact I1].
    - (* [comment removed for export] *)
      assert (E : (S (S i) = length f)%nat) by (clear - KB Hi; lia).
      replace (S i) with (length f - 1)%nat in * by lia.
      do 2 zstep.
      eapply KE; [exact E | exact I1].
  Qed.

  Lemma rsh_loop : forall (k i : nat) m1 x28 x29,
    BNDR -> (S i + k = length f - 1)%nat -> (S i < length f)%nat -> RINVA m f fp T n m1 i -> KTAIL -> evt asegs POST (HEAD m1 i x28 x29).
  Proof.
    induction k as [|k IH]; intros i m1 x28 x29 B Hk Hi I K.
    - eapply rsh_round; [exact B | exact Hi | exact I | intros _; exact K | intros C; exfalso; lia].
    - eapply rsh_round; [exact B | exact Hi | exact I | intros C; exfalso; lia | ].
      intros _ m2 y28 y29 I2. eapply IH; [exact B | lia | lia | exact I2 | exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma rsh_tail : forall m1 x5 x6 x7 x10 x11 x16 x17 x28 x29,
    BNDR -> RINVA m f fp T n m1 (length f - 1) ->
    (forall m2 x5 x6 x7 x11 x12 x14 x15 x16 x17 x28 x29,
       limbs_at asegs m2 T (map (rsh_at f n) (seq 0 (length f))) -> limbs_at asegs m2 fp f -> mem_inv asegs m2 ->
       munch [(T, T + 8 * top)]%Z m m2 -> wmono asegs m m2 ->
       evt asegs POST (SH 0x226d6c m2 x5 x6 x7 (Z_to_bv 64 (bv_unsigned s3 + 16)) x11 x12 x14 x15 x16 x17 x28 x29)) ->
    evt asegs POST (SH 0x226d48 m1 x5 x6 x7 x10 x11 (Z_to_bv 64 n) (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x16 x17 x28 x29).
  Proof.
    intros m1 x5 x6 x7 x10 x11 x16 x17 x28 x29 B I K.
    pose proof I as (_ & HF & WT & MI & _).
    pose proof B as (BF & BT).
    assert (RLl : (0 <= nth (length f - 1) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    zstep.
    replace ((top - 1) ≪ 3)%Z with (8 * (top - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    do 3 zstep.
    (let ad := cur_mem_addr in pose proof (shT m1 _ (length f - 1)%nat ad B I ltac:(lia) ltac:(unfold wa, shad; f_equal; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear - Htop; Z.div_mod_to_equations; lia)) as RD); zstep; clear RD. chk0.
    do 2 zstep.
    setreg 12%Z (Z_to_bv 64 (rsh_at f n (length f - 1)))
      ltac:(f_equal; rewrite (shrw_machine n _ Hn), (rsh_at_last f n (length f - 1) ltac:(lia)); reflexivity).
    destruct (RINVA_store m f fp T n m1 (length f - 1) _ DISJ I ltac:(lia) eq_refl) as [SOK I1].
    replace (T + 8 * Z.of_nat (length f - 1))%Z with (T + 8 * (top - 1))%Z in SOK, I1 by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    destruct I1 as (HW & HF2 & WT2 & MI2 & MU2 & WM2).
    replace (S (length f - 1)) with (length f) in HW by lia.
    apply K; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rsh_blockA : forall x5 x6 x7 x11 x12 x14 x15 x16 x17 x28 x29,
    limbs_at asegs m fp f -> wr_at asegs m T (8 * top) -> mem_inv asegs m ->
    (forall m2 x5 x6 x7 x11 x12 x14 x15 x16 x17 x28 x29,
       limbs_at asegs m2 T (map (rsh_at f n) (seq 0 (length f))) -> limbs_at asegs m2 fp f -> mem_inv asegs m2 ->
       munch [(T, T + 8 * top)]%Z m m2 -> wmono asegs m m2 ->
       evt asegs POST (SH 0x226d6c m2 x5 x6 x7 (Z_to_bv 64 (bv_unsigned s3 + 16)) x11 x12 x14 x15 x16 x17 x28 x29)) ->
    evt asegs POST (SH 0x226c9c m x5 x6 x7 (Z_to_bv 64 fp) x11 x12 x14 x15 x16 x17 x28 x29).
  Proof.
    intros x5 x6 x7 x11 x12 x14 x15 x16 x17 x28 x29 HF WT MI K.
    assert (B : BNDR).
    { split; [exact (limbs_at_b47 asegs m fp f HF MI ltac:(lia)) |].
      pose proof (wr_at_b47 asegs m T (8 * top) WT MI ltac:(lia)) as H. lia. }
    pose proof B as (BF & BT).
    assert (N0 : nth_error f 0 = Some (nth 0 f 0%Z)) by (apply nth_error_nth'; lia).
    assert (R0 : (0 <= nth 0 f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth asegs m fp f 0 _ ad HF N0 ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 2 zstep.
    setreg 12%Z (Z_to_bv 64 n) ltac:(f_equal; change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 6)%Z with 64%Z; lia).
    assert (I0 : RINVA m f fp T n m 0).
    { unfold RINVA. cbn [seq map]. split; [apply limbs_at_nil; lia|]. split; [exact HF|]. split; [exact WT|]. split; [exact MI|].
      split; [apply munch_refl | apply wmono_refl]. }
    zstep. rewrite lts_signed by lia. if_cases KT; zify_cond KT.
    - (* [comment removed for export] *)
      zstep.
      assert (E1 : (length f - 1 = 0)%nat) by lia.
      eapply evt_eq; [ | eapply rsh_tail; [exact B | rewrite E1; exact I0 | exact K] ].
      rewrite E1. replace (top - 1)%Z with 0%Z by lia. reflexivity.
    - do 2 zstep.
      rewrite (bn_swrap32_small (top + -1)) by lia.
      do 10 zstep.
      change (Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63) with (negn_mA n). rewrite (negn_mA_eq n Hn).
      change (Z.lor (((0 - lbm) mod 18446744073709551616) ≫ 8) ((0 - lbm) mod 18446744073709551616)) with (rmask_m lbm).
      rewrite (rmask_m_eq n Hn).
      rewrite (Z.mod_small (top + -1) 4294967296) by lia.
      replace (top + -1)%Z with (top - 1)%Z by lia.
      replace (Z_to_bv 64 (fp + 8)) with (Z_to_bv 64 (fp + 8 * Z.of_nat 1)) by (f_equal; lia).
      eapply evt_eq; [ | eapply (rsh_loop (length f - 2) 0 m x28 x29); [exact B | lia | lia | exact I0 | ] ].
      + replace (T + 8 * Z.of_nat 0)%Z with T by lia. replace (top - 1 - Z.of_nat 0)%Z with (top - 1)%Z by lia. reflexivity.
      + intros m2 y5 y6 y7 y10 y11 y16 y17 y28 y29 I2. eapply rsh_tail; [exact B | exact I2 | exact K].
  Qed.
End Block.
