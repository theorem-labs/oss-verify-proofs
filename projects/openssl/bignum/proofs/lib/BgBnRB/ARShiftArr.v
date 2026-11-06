(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop AsLeaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2318964 => 2
  | 2318976 => 1
  | 2318980 => 2
  | 2319048 => 1
  | 2319052 => 2
  | 2319076 => 2
  | 2319080 => 1
  | 2319084 => 2
  | 2319132 => 1
  | 2319136 => 1
  | 2319140 => 2
  | 2319144 => 1
  | 2319148 => 1
  | 2319152 => 1
  | 2319156 => 1
  | 2319160 => 2
  | 2319164 => 2
  | 2319168 => 1
  | 2319172 => 2
  | 2319180 => 2
  | 2319236 => 1
  | 2319240 => 1
  | 2319244 => 1
  | 2319252 => 1
  | 2319260 => 1
  | 2319284 => 2
  | 2319312 => 2
  | 2319316 => 1
  | 2319320 => 1
  | 2319324 => 2
  | 2319328 => 2
  | 2319416 => 2
  | 2319420 => 1
  | 2319424 => 1
  | 2319428 => 1
  | 2319432 => 2
  | 2319436 => 2
  | 2319440 => 1
  | 2319444 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition negn_mR (n : Z) : Z := Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63.

Lemma negn_mR_gen : forall n rb, (0 <= n < 2147483648)%Z -> Z.land n 63 = rb -> negn_mR n = ((64 - rb) mod 64)%Z.
Proof.
  intros n rb Hn <-. unfold negn_mR. change 63%Z with (Z.ones 6). rewrite !Z.land_ones by lia. change (2 ^ 6)%Z with 64%Z.
  assert (E : bv_swrap 32 (0 - n) = (0 - n)%Z).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (2 ^ (Z.of_N 32 - 1))%Z with 2147483648%Z.
    destruct (Z.eq_dec n 0) as [->|NZ]; [reflexivity|]. rewrite Z.mod_small by lia. lia. }
  rewrite E. rewrite Z.mod_mod_divide by (exists (2^58)%Z; reflexivity).
  replace (64 - n mod 64)%Z with (- (n mod 64) + 1 * 64)%Z by lia. rewrite Z.mod_add by lia.
  replace (0 - n)%Z with (- n)%Z by lia. rewrite <- (Z.sub_0_l n), <- (Z.sub_0_l (n mod 64)). rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Definition RINVGA (m : word -> option byte) (f : list Z) (fp T n : Z) (m1 : word -> option byte) (i : nat) : Prop :=
  limbs_at bgbsegs m1 T (map (rsh_at f n) (seq 0 i)) /\
  ((S i <= length f)%nat -> limbs_at bgbsegs m1 (fp + 8 * Z.of_nat (S i)) (skipn (S i) f)) /\
  wr_at bgbsegs m1 T (8 * Z.of_nat (length f)) /\ mem_inv bgbsegs m1 /\
  munch [(T, T + 8 * Z.of_nat (length f))]%Z m m1 /\ wmono bgbsegs m m1.

Lemma RINVGA_store : forall m f fp T n m1 i v,
  (T <= fp \/ fp + 8 * Z.of_nat (length f) <= T)%Z -> (0 <= fp)%Z ->
  RINVGA m f fp T n m1 i -> (i < length f)%nat -> v = rsh_at f n i ->
  store_ok bgbsegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true /\
  RINVGA m f fp T n (write_to_mem m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v))) (S i).
Proof.
  intros m f fp T n m1 i v DISJ FP0 (HW & HS & WT & MI & MU & WM) Hi ->.
  assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
  pose proof (wr_at_below bgbsegs m1 T (8 * Z.of_nat (length f)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
  assert (L8 : length (le8 (Z_to_bv 64 (rsh_at f n i))) = 8%nat) by apply length_le8.
  assert (SOK : store_ok bgbsegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true).
  { change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)). apply (wr_at_store_ok bgbsegs m1 T (8 * Z.of_nat (length f))); [exact WT | lia | lia]. }
  split; [exact SOK|].
  change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)).
  unfold RINVGA.
  split. { rewrite seq_S, map_app. cbn [map Nat.add].
           replace (T + 8 * Z.of_nat i)%Z with (T + 8 * Z.of_nat (length (map (rsh_at f n) (seq 0 i))))%Z by (rewrite length_map, length_seq; reflexivity).
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
  Variables (ra sp gp tp s0 s1 s3 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp T n rb : Z).
  Notation top := (Z.of_nat (length f)).
  Hypothesis Hn : (0 <= n < 2147483648)%Z.
  Hypothesis Hrb : (0 <= rb < 64)%Z.
  Hypothesis Erb : Z.land n 63 = rb.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis DISJ : (T <= fp \/ fp + 8 * top <= T)%Z.

  Hypothesis ACF : acc bgbsegs m fp (8 * top).
  Hypothesis ACT : acc bgbsegs m T (8 * top).
  Hypothesis ALF : (fp mod 8 = 0)%Z.
  Hypothesis ALT : (T mod 8 = 0)%Z.
  Hypothesis OFFT : offshW [(T, T + 8 * top)]%Z.

  Hypothesis UBF : (0 < fp)%Z.
  Hypothesis UBT : (0 < T)%Z.

  Notation lbm := ((64 - rb) mod 64)%Z.
  Notation rmask := (if (rb =? 0)%Z then 0 else 18446744073709551615)%Z.

  Notation SH pc mm x5 x6 x7 x10 x11 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 (Z_to_bv 64 rb) (Z_to_bv 64 T) x14 x15 x16 x17 (Z_to_bv 64 top) x19 x20 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgbsegs)).
  Definition BNDR : Prop := ((0 <= fp /\ fp + 8 * top <= 140737488355328) /\ (0 <= T /\ T + 8 * top <= 140737488355328))%Z.

  Lemma shF : forall m1 i (k : nat) ad, BNDR -> RINVGA m f fp T rb m1 i -> (k < length f)%nat -> ad = wa (shad (fp + 8 * Z.of_nat k)) ->
    ov_read_bytes bgbsegs m1 ad 1 = Some [z8].
  Proof using ACF ALF OFFT.
    intros m1 i k ad (BF & _) (_ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bgbsegs _ m m1 fp top 0 (Z.of_nat k) _ ACF MU OFFT ALF BF); [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.
  Lemma shT : forall m1 i (k : nat) ad, BNDR -> RINVGA m f fp T rb m1 i -> (k < length f)%nat -> ad = wa (shad (T + 8 * Z.of_nat k)) ->
    ov_read_bytes bgbsegs m1 ad 1 = Some [z8].
  Proof using ACT ALT OFFT.
    intros m1 i k ad (_ & BT) (_ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bgbsegs _ m m1 T top 0 (Z.of_nat k) _ ACT MU OFFT ALT BT); [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.

  Notation HEAD mm i x20 x30 x31 :=
    (SH 0x2363b0 mm (Z_to_bv 64 lbm) (Z_to_bv 64 1) (Z_to_bv 64 rmask) (Z_to_bv 64 fp) (Z_to_bv 64 (8 * Z.of_nat i))
        (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (nth i f 0%Z)) (Z_to_bv 64 (18446744073709551615 - fp)) (Z_to_bv 64 1) s3 x20
        (Z_to_bv 64 (fp + 8)) (Z_to_bv 64 (top - 1 - Z.of_nat i)) x30 x31).
  Notation KTAIL :=
    (forall m2 x5 x6 x7 x10 x11 x16 x17 x20 x28 x29 x31,
       RINVGA m f fp T rb m2 (length f - 1) ->
       evt bgbsegs POST (SH 0x236430 m2 x5 x6 x7 x10 x11 (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x16 x17 s3 x20 x28 x29
                          (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x31)).

  Lemma rshg_round : forall (i : nat) m1 x20 x30 x31,
    BNDR -> (S i < length f)%nat -> RINVGA m f fp T rb m1 i ->
    ((S (S i) = length f)%nat -> KTAIL) ->
    ((S (S i) < length f)%nat -> forall m2 x20 x30 x31, RINVGA m f fp T rb m2 (S i) -> evt bgbsegs POST (HEAD m2 (S i) x20 x30 x31)) ->
    evt bgbsegs POST (HEAD m1 i x20 x30 x31).
  Proof.
    intros i m1 x20 x30 x31 B Hi I KE KL.
    pose proof I as (_ & HS & WT & MI & _). specialize (HS ltac:(lia)).
    pose proof B as (BF & BT).
    assert (RI : (0 <= nth i f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (RS : (0 <= nth (S i) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (NS : nth_error (skipn (S i) f) 0 = Some (nth (S i) f 0%Z)).
    { rewrite nth_error_skipn, Nat.add_0_r. apply nth_error_nth'. lia. }
    assert (Hi' : (Z.of_nat i + 1 < top)%Z) by (clear - Hi; lia).
    zstep. ub. zstep.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shF m1 _ (S i) ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    zstep. ub.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shT m1 _ i ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgbsegs m1 (fp + 8 * Z.of_nat (S i)) (skipn (S i) f) 0 _ ad HS NS ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 4 zstep.
    setreg 15%Z (Z_to_bv 64 (rsh_at f rb i))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (rsh_hi_machine rb _ Hrb), (shrw_machine rb _ Hrb), (rsh_at_mid f rb i Hi); reflexivity).
    zstep.
    destruct (RINVGA_store m f fp T rb m1 i _ DISJ ltac:(clear - BF; lia) I ltac:(lia) eq_refl) as [SOK I1].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    clear SOK I HS WT MI. try clear m1.
    do 2 zstep.
    zstep. if_cases KB; zify_cond KB.
    -
      replace (8 * Z.of_nat i + 8)%Z with (8 * Z.of_nat (S i))%Z by lia.
      replace (top - 1 - Z.of_nat i + -1)%Z with (top - 1 - Z.of_nat (S i))%Z by lia.
      eapply KL; [clear - KB Hi; lia | exact I1].
    -
      assert (E : (S (S i) = length f)%nat) by (clear - KB Hi; lia).
      replace (S i) with (length f - 1)%nat in * by lia.
      zstep.
      eapply KE; [exact E | exact I1].
  Qed.

  Lemma rshg_loop : forall (k i : nat) m1 x20 x30 x31,
    BNDR -> (S i + k = length f - 1)%nat -> (S i < length f)%nat -> RINVGA m f fp T rb m1 i -> KTAIL -> evt bgbsegs POST (HEAD m1 i x20 x30 x31).
  Proof.
    induction k as [|k IH]; intros i m1 x20 x30 x31 B Hk Hi I K.
    - eapply rshg_round; [exact B | exact Hi | exact I | intros _; exact K | intros C; exfalso; lia].
    - eapply rshg_round; [exact B | exact Hi | exact I | intros C; exfalso; lia | ].
      intros _ m2 y20 y30 y31 I2. eapply IH; [exact B | lia | lia | exact I2 | exact K].
  Qed.

  Lemma rshg_tail : forall m1 x5 x6 x7 x10 x11 x16 x17 x20 x28 x29 x31,
    BNDR -> RINVGA m f fp T rb m1 (length f - 1) ->
    (forall m2 x5 x6 x7 x10 x11 x14 x15 x16 x17 x20 x28 x29 x30 x31,
       limbs_at bgbsegs m2 T (map (rsh_at f rb) (seq 0 (length f))) -> mem_inv bgbsegs m2 ->
       munch [(T, T + 8 * top)]%Z m m2 -> wmono bgbsegs m m2 ->
       evt bgbsegs POST (SH 0x236474 m2 x5 x6 x7 x10 x11 x14 x15 x16 x17 (Z_to_bv 64 (bv_unsigned s3 + 16)) x20 x28 x29 x30 x31)) ->
    evt bgbsegs POST (SH 0x236430 m1 x5 x6 x7 x10 x11 (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (nth (length f - 1) f 0%Z)) x16 x17 s3 x20 x28 x29
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
    setreg 11%Z (Z_to_bv 64 (rsh_at f rb (length f - 1)))
      ltac:(f_equal; rewrite (shrw_machine rb _ Hrb), (rsh_at_last f rb (length f - 1) ltac:(lia)); reflexivity).
    zstep.
    destruct (RINVGA_store m f fp T rb m1 (length f - 1) _ DISJ ltac:(clear - BF; lia) I ltac:(lia) eq_refl) as [SOK I1].
    replace (T + 8 * Z.of_nat (length f - 1))%Z with (T + 8 * (top - 1))%Z in SOK, I1 by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    destruct I1 as (HW & _ & WT2 & MI2 & MU2 & WM2).
    replace (S (length f - 1)) with (length f) in HW by lia.
    apply K; assumption.
  Qed.

  Lemma rshg_blockA : forall x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31,
    limbs_at bgbsegs m fp f -> wr_at bgbsegs m T (8 * top) -> mem_inv bgbsegs m ->
    (forall m2 x5 x6 x7 x10 x11 x14 x15 x16 x17 x20 x28 x29 x30 x31,
       limbs_at bgbsegs m2 T (map (rsh_at f rb) (seq 0 (length f))) -> mem_inv bgbsegs m2 ->
       munch [(T, T + 8 * top)]%Z m m2 -> wmono bgbsegs m m2 ->
       evt bgbsegs POST (SH 0x236474 m2 x5 x6 x7 x10 x11 x14 x15 x16 x17 (Z_to_bv 64 (bv_unsigned s3 + 16)) x20 x28 x29 x30 x31)) ->
    evt bgbsegs POST (SH 0x236368 m x5 x6 x7 (Z_to_bv 64 fp) (Z_to_bv 64 (top - 1)) x14 x15 x16 x17 s3 (Z_to_bv 64 n) x28 x29 x30 x31).
  Proof.
    intros x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 HF WT MI K.
    assert (B : BNDR).
    { split; [exact (limbs_at_b47 bgbsegs m fp f HF MI ltac:(lia)) |].
      pose proof (wr_at_b47 bgbsegs m T (8 * top) WT MI ltac:(lia)) as H. lia. }
    pose proof B as (BF & BT).
    assert (N0 : nth_error f 0 = Some (nth 0 f 0%Z)) by (apply nth_error_nth'; lia).
    assert (R0 : (0 <= nth 0 f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgbsegs m fp f 0 _ ad HF N0 ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 3 zstep.
    setreg 14%Z (Z_to_bv 64 (top - 1))
      ltac:(f_equal; symmetry; rewrite ub_lxor_sign63 by lia;
            destruct (Z.ltb_spec 9223372036854775808 (top - 1 + 9223372036854775808)) as [L|L]; cbn [Z.b2z];
            [ change ((0 - 1) mod 18446744073709551616)%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; lia
            | change ((0 - 0) mod 18446744073709551616)%Z with 0%Z; rewrite Z.land_0_l; lia ]).
    assert (I0 : RINVGA m f fp T rb m 0).
    { unfold RINVGA. cbn [seq map]. split; [apply limbs_at_nil; lia|].
      split. { intros _. pose proof HF as HF'. rewrite <- (firstn_skipn 1 f) in HF'. apply limbs_at_app in HF'. destruct HF' as [_ HF2].
               rewrite length_firstn in HF2. replace (Nat.min 1 (length f)) with 1%nat in HF2 by lia. exact HF2. }
      split; [exact WT|]. split; [exact MI|].
      split; [apply munch_refl | apply wmono_refl]. }
    zstep. rewrite lts_signed by lia. if_cases KT; zify_cond KT.
    -
      zstep.
      assert (E1 : (length f - 1 = 0)%nat) by lia.
      eapply evt_eq; [ | eapply rshg_tail; [exact B | rewrite E1; exact I0 | exact K] ].
      rewrite E1. replace (top - 1)%Z with 0%Z by lia. reflexivity.
    - zstep. zstep. ub. zstep.
      change (Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63) with (negn_mR n). rewrite (negn_mR_gen n rb Hn Erb).
      ub. zstep. ub. do 2 zstep.
      change (Z.lor (((0 - lbm) mod 18446744073709551616) ≫ 8) ((0 - lbm) mod 18446744073709551616)) with (rmask_m lbm).
      rewrite (rmask_m_eq rb Hrb).
      do 2 zstep.
      setreg 6%Z (Z_to_bv 64 1) ltac:(f_equal; symmetry; rewrite (land7 _ ALT); replace (0 <? T)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      setreg 17%Z (Z_to_bv 64 1) ltac:(f_equal; symmetry; replace (0 <? T)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      setreg 16%Z (Z_to_bv 64 (18446744073709551615 - fp)) ltac:(f_equal; symmetry; apply zb_lxor_ones; lia).
      eapply evt_eq; [ | eapply (rshg_loop (length f - 2) 0 m _ x30 x31); [exact B | lia | lia | exact I0 | ] ].
      + replace (8 * Z.of_nat 0)%Z with 0%Z by lia. replace (top - 1 - Z.of_nat 0)%Z with (top - 1)%Z by lia. reflexivity.
      + intros m2 y5 y6 y7 y10 y11 y16 y17 y20 y28 y29 y31 I2. eapply rshg_tail; [exact B | exact I2 | exact K].
  Qed.

End Block.
