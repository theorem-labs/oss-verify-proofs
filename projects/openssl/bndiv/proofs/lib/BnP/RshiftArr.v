(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import ShiftPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition RINV (m : word -> option byte) (f : list Z) (fp T n : Z) (m1 : word -> option byte) (i : nat) : Prop :=
  limbs_at psegs m1 T (map (rsh_at f n) (seq 0 i)) /\ limbs_at psegs m1 fp f /\
  wr_at psegs m1 T (8 * Z.of_nat (length f)) /\ mem_inv psegs m1 /\
  munch [(T, T + 8 * Z.of_nat (length f))]%Z m m1 /\ wmono psegs m m1.

Lemma RINV_store : forall m f fp T n m1 i v,
  (fp + 8 * Z.of_nat (length f) <= T \/ T + 8 * Z.of_nat (length f) <= fp)%Z ->
  RINV m f fp T n m1 i -> (i < length f)%nat -> v = rsh_at f n i ->
  store_ok psegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true /\
  RINV m f fp T n (write_to_mem m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v))) (S i).
Proof.
  intros m f fp T n m1 i v DISJ (HW & HF & WT & MI & MU & WM) Hi ->.
  pose proof (limbs_at_bound _ _ _ _ HF) as BF.
  assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
  pose proof (wr_at_below psegs m1 T (8 * Z.of_nat (length f)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
  assert (L8 : length (le8 (Z_to_bv 64 (rsh_at f n i))) = 8%nat) by apply length_le8.
  assert (SOK : store_ok psegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true).
  { change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)). apply (wr_at_store_ok psegs m1 T (8 * Z.of_nat (length f))); [exact WT | lia | lia]. }
  split; [exact SOK|].
  change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)).
  unfold RINV.
  split. { rewrite seq_S, map_app. cbn [map Nat.add].
           replace (T + 8 * Z.of_nat i)%Z with (T + 8 * Z.of_nat (length (map (rsh_at f n) (seq 0 i))))%Z by (rewrite length_map, length_seq; reflexivity).
           apply limbs_at_snoc_write; [exact HW | rewrite length_map, length_seq; lia]. }
  split. { apply limbs_at_write_other; [exact HF | lia | rewrite L8; lia | rewrite L8; lia]. }
  split. { apply wr_at_write. exact WT. }
  split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
  split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
  apply wmono_write. exact WM.
Qed.

(* [comment removed for export] *)
Definition negn_m (n : Z) : Z := Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63.
Lemma negn_chk : forallb (fun n => negn_m n =? (64 - n) mod 64)%Z (map Z.of_nat (seq 0 64)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma negn_m_eq : forall n, (0 <= n < 64)%Z -> negn_m n = ((64 - n) mod 64)%Z.
Proof.
  intros n H. pose proof negn_chk as A. rewrite forallb_forall in A. specialize (A n). rewrite Z.eqb_eq in A. apply A.
  apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia.
Qed.

Section Block.
  Variables (ra sp gp tp s0 s1 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp T n : Z).
  Notation top := (Z.of_nat (length f)).
  Hypothesis Hn : (0 <= n < 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis DISJ : (fp + 8 * top <= T \/ T + 8 * top <= fp)%Z.

  Notation lbm := ((64 - n) mod 64)%Z.
  Notation rmask := (if (n =? 0)%Z then 0 else 18446744073709551615)%Z.
  (* [comment removed for export] *)
  Notation SH pc mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 (Z_to_bv 64 top) (Z_to_bv 64 n) x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Notation HEAD mm i x6 x7 x11 :=
    (SH 0xf6674 mm (Z_to_bv 64 (T + 8 * Z.of_nat i)) x6 x7 (Z_to_bv 64 T) (Z_to_bv 64 n) (Z_to_bv 64 (nth i f 0%Z)) (Z_to_bv 64 (top - 1))
        (Z_to_bv 64 (fp + 8 * Z.of_nat (S i))) (Z_to_bv 64 lbm) (Z_to_bv 64 rmask) (Z_to_bv 64 (T + 8 * (top - 1))) (Z_to_bv 64 0)).
  Notation KEXIT :=
    (forall m2 x5 x6 x7 x14,
       RINV m f fp T n m2 (length f - 1) ->
       evt psegs POST (SH 0xf669c m2 x5 x6 x7 (Z_to_bv 64 T) (Z_to_bv 64 n) (Z_to_bv 64 (nth (length f - 1) f 0%Z)) (Z_to_bv 64 (top - 1))
                          x14 (Z_to_bv 64 lbm) (Z_to_bv 64 rmask) (Z_to_bv 64 (T + 8 * (top - 1))) (Z_to_bv 64 0))).

  Lemma rsh_round : forall (i : nat) m1 x6 x7,
    (S i < length f)%nat -> RINV m f fp T n m1 i ->
    ((S (S i) = length f)%nat -> KEXIT) ->
    ((S (S i) < length f)%nat -> forall m2 x6 x7, RINV m f fp T n m2 (S i) -> evt psegs POST (HEAD m2 (S i) x6 x7 (Z_to_bv 64 n))) ->
    evt psegs POST (HEAD m1 i x6 x7 (Z_to_bv 64 n)).
  Proof.
    intros i m1 x6 x7 Hi I KE KL.
    pose proof I as (_ & HF & WT & MI & _).
    pose proof (limbs_at_bound _ _ _ _ HF) as BF.
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below psegs m1 T (8 * top) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (RI : (0 <= nth i f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (RS : (0 <= nth (S i) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (NS : nth_error f (S i) = Some (nth (S i) f 0%Z)) by (apply nth_error_nth'; lia).
    zstep.
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth psegs m1 fp f (S i) _ ad HF NS ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 4 zstep.
    setreg 6%Z (Z_to_bv 64 (rsh_at f n i))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (rsh_hi_machine n _ Hn), (shrw_machine n _ Hn), (rsh_at_mid f n i Hi); reflexivity).
    destruct (RINV_store m f fp T n m1 i _ DISJ I ltac:(lia) eq_refl) as [SOK I1].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    clear SOK I HF WT MI. try clear m1.
    do 2 zstep.
    zstep. if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      replace (T + 8 * Z.of_nat i + 8)%Z with (T + 8 * Z.of_nat (S i))%Z by lia.
      replace (fp + 8 * Z.of_nat (S i) + 8)%Z with (fp + 8 * Z.of_nat (S (S i)))%Z by lia.
      eapply KL; [clear - KB Hi; lia | exact I1].
    - (* [comment removed for export] *)
      assert (E : (S (S i) = length f)%nat) by (clear - KB Hi; lia).
      replace (S i) with (length f - 1)%nat in * by lia.
      eapply KE; [exact E | exact I1].
  Qed.

  Lemma rsh_loop : forall (k i : nat) m1 x6 x7,
    (S i + k = length f - 1)%nat -> (S i < length f)%nat -> RINV m f fp T n m1 i -> KEXIT -> evt psegs POST (HEAD m1 i x6 x7 (Z_to_bv 64 n)).
  Proof.
    induction k as [|k IH]; intros i m1 x6 x7 Hk Hi I K.
    - eapply rsh_round; [exact Hi | exact I | intros _; exact K | intros C; exfalso; lia].
    - eapply rsh_round; [exact Hi | exact I | intros C; exfalso; lia | ].
      intros _ m2 y6 y7 I2. eapply IH; [lia | lia | exact I2 | exact K].
  Qed.

  Lemma rsh_block : forall x5 x6 x7 x11 x12 x13 x15 x16 x17,
    limbs_at psegs m fp f -> wr_at psegs m T (8 * top) -> mem_inv psegs m ->
    (forall m2 x5 x6 x7 x12 x14 x15 x16 x17 x21,
       RINV m f fp T n m2 (length f - 1) ->
       evt psegs POST (SH 0xf66b8 m2 x5 x6 x7 (Z_to_bv 64 T) (Z_to_bv 64 (rsh_at f n (length f - 1))) x12 (Z_to_bv 64 (8 * (top - 1))) x14 x15 x16 x17 x21)) ->
    evt psegs POST (SH 0xf6630 m x5 x6 x7 (Z_to_bv 64 T) x11 x12 x13 (Z_to_bv 64 fp) x15 x16 x17 (Z_to_bv 64 0)).
  Proof.
    intros x5 x6 x7 x11 x12 x13 x15 x16 x17 HF WT MI K.
    pose proof (limbs_at_bound _ _ _ _ HF) as BF.
    pose proof (wr_at_below psegs m T (8 * top) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    do 2 zstep.
    assert (N0 : nth_error f 0 = Some (nth 0 f 0%Z)) by (apply nth_error_nth'; lia).
    assert (R0 : (0 <= nth 0 f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth psegs m fp f 0 _ ad HF N0 ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 2 zstep.
    setreg 11%Z (Z_to_bv 64 n) ltac:(f_equal; change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 6)%Z with 64%Z; lia).
    assert (I0 : RINV m f fp T n m 0).
    { unfold RINV. cbn [seq map]. split; [apply limbs_at_nil; lia|]. split; [exact HF|]. split; [exact WT|]. split; [exact MI|].
      split; [apply munch_refl | apply wmono_refl]. }
    zstep. rewrite lts_signed by lia. if_cases KT; zify_cond KT.
    - (* [comment removed for export] *)
      do 3 zstep.
      assert (E1 : (length f - 1 = 0)%nat) by lia. rewrite E1 in K.
      setreg 11%Z (Z_to_bv 64 (rsh_at f n 0)) ltac:(f_equal; rewrite (shrw_machine n _ Hn), (rsh_at_last f n 0 ltac:(lia)); reflexivity).
      replace (8 * (top - 1))%Z with 0%Z in K by lia.
      apply K. exact I0.
    - do 2 zstep.
      rewrite (bn_swrap32_small (top + -1)) by lia.
      do 9 zstep.
      change (Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63) with (negn_m n). rewrite (negn_m_eq n Hn).
      change (Z.lor (((0 - lbm) mod 18446744073709551616) ≫ 8) ((0 - lbm) mod 18446744073709551616)) with (rmask_m lbm).
      rewrite (rmask_m_eq n Hn).
      rewrite (shl32_shr29 (top + -1)) by lia.
      replace (top + -1)%Z with (top - 1)%Z by lia.
      replace (Z_to_bv 64 (fp + 8)) with (Z_to_bv 64 (fp + 8 * Z.of_nat 1)) by (f_equal; lia).
      eapply evt_eq; [ | eapply (rsh_loop (length f - 2) 0 m x6 x7); [lia | lia | exact I0 | ] ].
      + replace (T + 8 * Z.of_nat 0)%Z with T by lia. reflexivity.
      + intros m2 y5 y6 y7 y14 I2.
        assert (RLl : (0 <= nth (length f - 1) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
        do 3 zstep.
        setreg 11%Z (Z_to_bv 64 (rsh_at f n (length f - 1)))
          ltac:(f_equal; rewrite (shrw_machine n _ Hn), (rsh_at_last f n (length f - 1) ltac:(lia)); reflexivity).
        replace ((top - 1) ≪ 3)%Z with (8 * (top - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
        apply K. exact I2.
  Qed.

  (* [comment removed for export] *)
  Lemma rsh_last : forall m1 x5 x6 x7 x12 x14 x15 x16 x17 x21,
    RINV m f fp T n m1 (length f - 1) ->
    (forall m2 x10,
       limbs_at psegs m2 T (map (rsh_at f n) (seq 0 (length f))) -> limbs_at psegs m2 fp f -> mem_inv psegs m2 ->
       munch [(T, T + 8 * top)]%Z m m2 -> wmono psegs m m2 ->
       evt psegs POST (SH 0xf66c4 m2 x5 x6 x7 x10 (Z_to_bv 64 (rsh_at f n (length f - 1))) x12 (Z_to_bv 64 (8 * (top - 1))) x14 x15 x16 x17 x21)) ->
    evt psegs POST (SH 0xf66bc m1 x5 x6 x7 (Z_to_bv 64 T) (Z_to_bv 64 (rsh_at f n (length f - 1))) x12 (Z_to_bv 64 (8 * (top - 1))) x14 x15 x16 x17 x21).
  Proof.
    intros m1 x5 x6 x7 x12 x14 x15 x16 x17 x21 I K.
    pose proof I as (_ & HF & WT & MI & _).
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below psegs m1 T (8 * top) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    zstep.
    destruct (RINV_store m f fp T n m1 (length f - 1) _ DISJ I ltac:(lia) eq_refl) as [SOK I1].
    replace (T + 8 * Z.of_nat (length f - 1))%Z with (T + 8 * (top - 1))%Z in SOK, I1 by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    destruct I1 as (HW & HF2 & WT2 & MI2 & MU2 & WM2).
    replace (S (length f - 1)) with (length f) in HW by lia.
    apply K; assumption.
  Qed.
End Block.
