(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BgWords BgExp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU2 Require Import WU_from_mont_loops.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition gfin (R M : list Z) (j : nat) : list Z := splice R 0 (neg_limbs (firstn j M)).

Lemma neg_limbs_length : forall l, length (neg_limbs l) = length l.
Proof. intros [|x l]; [reflexivity|]. cbn [neg_limbs length]. rewrite length_map. reflexivity. Qed.

Lemma neg_limbs_limbs : forall l, limbs l -> limbs (neg_limbs l).
Proof.
  intros [|x l] H; [constructor|]. cbn [neg_limbs]. apply Forall_cons_iff in H. destruct H as [Hx Hl].
  constructor.
  - unfold limb, negw. apply Z.mod_pos_bound. unfold BW. lia.
  - apply Forall_map. eapply Forall_impl; [|exact Hl]. intros y Hy. unfold limb in *. cbv beta. lia.
Qed.

Lemma neg_limbs_nth0 : forall l, (0 < length l)%nat -> nth 0 (neg_limbs l) 0%Z = negw (nth 0 l 0%Z).
Proof. intros [|x l] H; [cbn in H; lia|]. reflexivity. Qed.

Lemma neg_limbs_nth : forall l i, (0 < i < length l)%nat -> nth i (neg_limbs l) 0%Z = (BW - 1 - nth i l 0)%Z.
Proof.
  intros [|x l] i H; [cbn in H; lia|]. destruct i as [|i]; [lia|]. cbn [neg_limbs nth]. cbn [length] in H.
  rewrite (nth_indep _ 0%Z ((fun y : Z => (BW - 1 - y)%Z) 0%Z)) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

Lemma g_to_bv_mod64 : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 18446744073709551616)%Z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma g_lxor_ones64 : forall x, (0 <= x < 2^64)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof.
  intros x H. change 18446744073709551615%Z with (Z.ones 64).
  assert (L : Z.land x (Z.lxor x (Z.ones 64)) = 0%Z).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.ltb_spec n 64) as [Hlt|Hge].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
    - rewrite (Z.bits_above_log2 x n); [reflexivity| lia|].
      destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. assert (Z.log2 x < 64)%Z by (apply Z.log2_lt_pow2; lia). lia. }
  pose proof (Z.add_nocarry_lxor _ _ L) as E.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in E. change (Z.ones 64) with 18446744073709551615%Z in *. lia.
Qed.

Section Fin.
  Variables (R M : list Z) (j : nat).
  Hypothesis JR : (j <= length R)%nat.
  Hypothesis JM : (j <= length M)%nat.

  Lemma gfin_length : length (gfin R M j) = length R.
  Proof using JR JM. unfold gfin. apply splice_length. rewrite neg_limbs_length, length_firstn. lia. Qed.

  Lemma gfin_limbs : limbs R -> limbs M -> limbs (gfin R M j).
  Proof. intros LR LM. unfold gfin. apply splice_limbs; [exact LR|]. apply neg_limbs_limbs. apply limbs_firstn. exact LM. Qed.

  Lemma gfin_nth0 : (1 <= j)%nat -> nth 0 (gfin R M j) 0%Z = negw (nth 0 M 0%Z).
  Proof using JR JM.
    intros J1. unfold gfin. rewrite (nth_splice_same R 0 _ 0) by (rewrite ?neg_limbs_length, ?length_firstn; lia).
    rewrite neg_limbs_nth0 by (rewrite length_firstn; lia). rewrite nth_firstn. destruct (Nat.ltb_spec 0 j); [reflexivity| lia].
  Qed.

  Lemma gfin_nth : forall i, (0 < i < j)%nat -> nth i (gfin R M j) 0%Z = (BW - 1 - nth i M 0)%Z.
  Proof using JR JM.
    intros i Hi. unfold gfin. rewrite (nth_splice_same R 0 _ i) by (rewrite ?neg_limbs_length, ?length_firstn; lia).
    rewrite neg_limbs_nth by (rewrite length_firstn; lia). rewrite nth_firstn. destruct (Nat.ltb_spec i j); [reflexivity| lia].
  Qed.

  Lemma gfin_mixl : mixl j (gfin R M j) R = gfin R M j.
  Proof using JR JM.
    pose proof gfin_length as HL.
    apply (nth_ext _ _ 0%Z 0%Z); [rewrite mixl_length; lia|]. intros i Hi. rewrite mixl_length in Hi by lia.
    rewrite mixl_nth by lia. destruct (Nat.ltb_spec i j) as [L|G]; [reflexivity|].
    unfold gfin. symmetry. apply nth_splice_other; rewrite neg_limbs_length, length_firstn; lia.
  Qed.
End Fin.

Section WithRegs.
  Variables (sp gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Notation SP := (bv_unsigned sp).
  Variables (ra t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
            (m : word -> option byte) (lo RD MD : Z) (R M : list Z) (j : nat).
  Hypothesis LR : limbs R.
  Hypothesis LM : limbs M.
  Hypothesis J1 : (1 <= j)%nat.
  Hypothesis JR : (j <= length R)%nat.
  Hypothesis JM : (j <= length M)%nat.
  Hypothesis J31 : (Z.of_nat j < 2^31)%Z.
  Hypothesis DJ : (MD + 8 * Z.of_nat (length M) <= RD \/ RD + 8 * Z.of_nat (length R) <= MD)%Z.

  Definition gf_post : machine_state -> Prop :=
    fun ms' => exists x12 x13 x14 x15 x16 x17 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 MD) (Z_to_bv 64 RD) x12 x13 x14 x15 x16 x17
                    s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (Z.of_nat j)) s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x150514) fc None m' (seg_rom bgusegs)
      /\ munch [(RD, RD + 8 * Z.of_nat j)]%Z m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
      /\ u64arr bgusegs m' RD (wlimbs (gfin R M j)) /\ u64arr bgusegs m' MD (wlimbs M) /\ stk bgusegs m' lo SP.

  Definition GINV (m1 : word -> option byte) (i : nat) : Prop :=
    u64arr bgusegs m1 RD (wlimbs (mixl i (gfin R M j) R)) /\ u64arr bgusegs m1 MD (wlimbs M) /\ mem_inv bgusegs m1
    /\ munch [(RD, RD + 8 * Z.of_nat j)]%Z m m1 /\ wmono bgusegs m m1 /\ stk bgusegs m1 lo SP.

  Lemma gueron_loop : forall K i m1 (x16 x17 : word),
    (j - i = K)%nat -> (1 <= i < j)%nat -> GINV m1 i ->
    evt bgusegs gf_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 MD) (Z_to_bv 64 RD)
                (Z_to_bv 64 (18446744073709551615 - MD)) (Z_to_bv 64 (18446744073709551615 - RD))
                (Z_to_bv 64 (8 * Z.of_nat j)) (Z_to_bv 64 (8 * Z.of_nat i)) x16 x17
                s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (Z.of_nat j)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1504f0) fc None m1 (seg_rom bgusegs)).
  Proof.
    intros K. induction K as [|K IH]; intros i m1 x16 x17 HK Hi (UR & UM & MI & MU & WM & ST); [lia|].
    pose proof (gfin_length R M j JR JM) as LS.
    pose proof (u64arr_bound _ _ _ _ UR) as BR. rewrite wlimbs_len, mixl_length in BR by lia.
    pose proof (u64arr_bound _ _ _ _ UM) as BM. rewrite wlimbs_len in BM.
    pose proof (wr_at_below bgusegs m1 RD _ MI (proj2 UR) ltac:(rewrite wlimbs_len, mixl_length by lia; lia)) as TOPR.
    rewrite wlimbs_len, mixl_length in TOPR by lia. unfold UTOP in TOPR.
    assert (Rx : (0 <= nth i M 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LM).
    assert (NTHM : nth_error (wlimbs M) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i M 0%Z))).
    { rewrite Nat2Z.id. unfold wlimbs. erewrite map_nth_error; [reflexivity|]. rewrite (nth_error_nth' _ 0%Z) by lia. reflexivity. }
    ub_chk. ub_chk.
    zstep.
    (let ad := cur_mem_addr in
     pose proof (u64arr_read bgusegs m1 MD _ (Z.of_nat i) _ ad UM NTHM ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0); zstep; clear RD0.
    zstep. zstep.
    rewrite (g_lxor_ones64 (nth i M 0%Z)) by lia.
    set (v := (18446744073709551615 - nth i M 0)%Z).
    assert (Ev : v = nth i (gfin R M j) 0%Z) by (subst v; rewrite gfin_nth by lia; unfold BW; lia).
    zstep.
    assert (IDXR : (0 <= Z.of_nat i < Z.of_nat (length (wlimbs (mixl i (gfin R M j) R))))%Z) by (rewrite wlimbs_len, mixl_length by lia; lia).
    pose proof (u64arr_store_ok bgusegs m1 RD _ (Z.of_nat i) (wa (RD + 8 * Z.of_nat i)) UR IDXR eq_refl) as SOKW.
    pose proof (u64arr_write bgusegs m1 RD _ (Z.of_nat i) (Z_to_bv 64 v) UR IDXR) as UR2.
    pose proof (u64arr_frame bgusegs m1 MD _ (RD + 8 * Z.of_nat i) (le8 (Z_to_bv 64 v)) UM ltac:(lia) ltac:(rewrite length_le8; lia)
                  ltac:(rewrite length_le8, wlimbs_len; lia)) as UM2.
    clear UR UM.
    zstep. store_done.
    rewrite Nat2Z.id, Ev, mixl_step in UR2 by lia.
    clear NTHM IDXR Ev Rx. subst v.
    replace (8 * Z.of_nat i + 8)%Z with (8 * Z.of_nat (S i))%Z by lia.
    zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit, ?Z.mod_small in KB by lia.
    - eapply (IH (S i)); [lia| lia|]. split; [exact UR2|]. split; [exact UM2|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact ST].
    - assert (EJ : S i = j) by lia. rewrite EJ. apply evt_done.
      unfold gf_post. do 7 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      rewrite EJ, gfin_mixl in UR2 by lia.
      split; [exact UR2|]. split; [exact UM2| exact ST].
  Qed.

  Lemma gueron_fill_walk : forall (x13 x14 x15 x16 x17 : word),
    u64arr bgusegs m RD (wlimbs R) -> u64arr bgusegs m MD (wlimbs M) -> mem_inv bgusegs m -> stk bgusegs m lo SP ->
    evt bgusegs gf_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 MD) (Z_to_bv 64 RD) (Z_to_bv 64 (nth 0 M 0%Z)) x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (Z.of_nat j)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1504d0) fc None m (seg_rom bgusegs)).
  Proof.
    intros x13 x14 x15 x16 x17 UR UM MI ST.
    pose proof (gfin_length R M j JR JM) as LS.
    pose proof (u64arr_bound _ _ _ _ UR) as BR. rewrite wlimbs_len in BR.
    pose proof (u64arr_bound _ _ _ _ UM) as BM. rewrite wlimbs_len in BM.
    pose proof (wr_at_below bgusegs m RD _ MI (proj2 UR) ltac:(rewrite wlimbs_len; lia)) as TOPR.
    rewrite wlimbs_len in TOPR. unfold UTOP in TOPR.
    pose proof (munch_refl [(RD, RD + 8 * Z.of_nat j)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    assert (Rx : (0 <= nth 0 M 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LM).
    zstep.
    rewrite (g_to_bv_mod64 (0 - nth 0 M 0%Z)). change ((0 - nth 0 M 0) mod 18446744073709551616)%Z with (negw (nth 0 M 0%Z)).
    set (v := negw (nth 0 M 0%Z)).
    assert (Ev : v = nth 0 (gfin R M j) 0%Z) by (subst v; rewrite gfin_nth0 by lia; reflexivity).
    zstep.
    assert (IDXR : (0 <= Z.of_nat 0 < Z.of_nat (length (wlimbs R)))%Z) by (rewrite wlimbs_len; lia).
    pose proof (u64arr_store_ok bgusegs m RD _ (Z.of_nat 0) (wa RD) UR IDXR ltac:(unfold wa; f_equal; lia)) as SOKW.
    pose proof (u64arr_write bgusegs m RD _ (Z.of_nat 0) (Z_to_bv 64 v) UR IDXR) as UR2.
    pose proof (u64arr_frame bgusegs m MD _ RD (le8 (Z_to_bv 64 v)) UM ltac:(lia) ltac:(rewrite length_le8; lia)
                  ltac:(rewrite length_le8, wlimbs_len; lia)) as UM2.
    replace (wa (RD + 8 * Z.of_nat 0)) with (wa RD) in UR2 by (unfold wa; f_equal; lia).
    clear UR UM.
    zstep. store_done.
    rewrite Nat2Z.id, Ev in UR2. replace (wlimbs R) with (wlimbs (mixl 0 (gfin R M j) R)) in UR2 by (rewrite mixl_0; reflexivity).
    rewrite mixl_step in UR2 by lia.
    clear IDXR Ev Rx. subst v.
    zstep. rewrite lts_signed by lia.
    destruct (Z.ltb_spec (Z.of_nat j) 2) as [J2|J2].
    -
      assert (EJ : j = 1%nat) by lia.
      apply evt_done. unfold gf_post. do 7 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      replace 1%nat with j in UR2 by lia. rewrite gfin_mixl in UR2 by lia.
      split; [exact UR2|]. split; [exact UM2| exact ST].
    - zstep. zstep. zstep. zstep.
      rewrite ?(unsigned_lit MD), ?(unsigned_lit RD), ?(unsigned_lit (Z.of_nat j)) by lia.
      rewrite (g_lxor_ones64 MD) by lia. rewrite (g_lxor_ones64 RD) by lia.
      rewrite Z.shiftl_mul_pow2 by lia. replace (Z.of_nat j * 2 ^ 3)%Z with (8 * Z.of_nat j)%Z by lia.
      change (Z_to_bv 64 8) with (Z_to_bv 64 (8 * Z.of_nat 1)).
      eapply (gueron_loop (j - 1)%nat 1%nat); [lia| lia|].
      split; [exact UR2|]. split; [exact UM2|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact ST].
  Qed.
End WithRegs.
