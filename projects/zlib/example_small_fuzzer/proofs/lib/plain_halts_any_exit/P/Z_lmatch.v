(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_lmatch_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz LmatchModel FillWinModel RefDeflFastM RefDeflFast6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_LONGEST_MATCH : Z := 0x19d24.

Definition lm_post_gen (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (dF : deflate_state) (res lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ DST m' L dF.

Section LM.
Variables (L : dlay) (d : deflate_state) (lo : Z).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Let W := ds_window d.
Let ss := ds_strstart d.
Let la := ds_lookahead d.
Hypothesis Hwb : forall i, 0 <= i < 65536 -> 0 <= arr_get (ds_window d) i < 256.
Hypothesis Hpb : forall i, 0 <= i < 32768 -> 0 <= arr_get (ds_prev d) i < 65536.
Hypothesis Hss : 0 <= ds_strstart d /\ ds_strstart d + 258 < 65536.
Hypothesis Hla : 0 <= ds_lookahead d < 2^31.
Hypothesis HREST : forall m' ms, munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] me m' -> wmono psegs me m' ->
  dsA m' L (set_match_start d ms) -> DST m' L (set_match_start d ms).
Hypothesis LOsp : lo <= bv_unsigned sp + -64.
Hypothesis Bs : dl_As L + 5968 <= lo.
Hypothesis Rs : 0 < dl_As L.

Lemma lm_exit : forall (msF bF : Z) (x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word) (m : mem)
    (j8 h1 h2 h3 h4 h5 : list byte),
  rw_cells psegs m (dl_As L) (dsA_cells L (set_match_start d msF) h1 h2 h3 h4 h5) ->
  rw_cells psegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] ->
  stk psegs m lo (bv_unsigned sp + -64) ->
  munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] me m -> wmono psegs me m -> mem_inv psegs m ->
  0 <= bF <= 258 ->
  evt psegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (set_match_start d msF) (if bF <=? ds_lookahead d then bF else ds_lookahead d) lo me)
    (MS (mkR ra (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 (wz (dl_As L)) x11 (wz bF) (wz (ds_lookahead d)) x14 x15 x16 x17 x18 x19 x20 x21 x22
             s7 s8 s9 s10 s11 x28 x29 x30 x31) F (wz 0x19f44) fc None m (seg_rom psegs)).
Proof.
  intros until h5. intros GA FR STK MU WM MI HB.
  unfold dsA_cells in GA.
  do 8 zs.
  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { zs. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - replace (wz bF) with (wz (if bF <=? ds_lookahead d then bF else ds_lookahead d))
        by (f_equal; destruct (Z.leb_spec bF (ds_lookahead d)); lia).
      apply evt_done. reflexivity.
    - zs. apply evt_done. repeat f_equal. destruct (Z.leb_spec bF (ds_lookahead d)); lia. }
  intros ms' ->.
  do 2 zs.
  release_frame FR STK (bv_unsigned sp).
  apply evt_done. unfold lm_post_gen. do 14 eexists. exists m.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
  apply HREST; [exact MU| exact WM|]. exists h1, h2, h3, h4, h5. exact GA.
Qed.

Variables (nice limit : Z).
Definition lmR (x8 x9 x11 x12 x18 x19 x20 x21 x22 x28 x31 : word) : bvmap 5 word :=
  mkR ra (wz (bv_unsigned sp + -64)) gp tp (wz (ds_w_mask d)) (wz (dl_Ap L)) (wz (dl_Aw L + ds_strstart d + 258)) x8 x9 (wz (dl_As L)) x11 x12
      (wz (ds_lookahead d)) (wz (dl_Aw L)) (wz (dl_Aw L + ds_strstart d)) (wz nice) (wz limit) x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28
      (wz (dl_Aw L + 5)) (wz 250) x31.

Hypothesis RAw : 0 < dl_Aw L /\ dl_Aw L + 65536 < 2^62.

Ltac lm_cmp Gwin i cur k :=
  pose proof (Hwb (ds_strstart d + i + k) ltac:(lia)); pose proof (Hwb (cur + i + k) ltac:(lia));
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + i + k) ltac:(assumption);
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (cur + i + k) ltac:(assumption).

Ltac lm_mis HN HU LEN ptr lenv flip :=
  rewrite ?swrap32_mod64 by lia;
  replace (wz (ptr - (dl_Aw L + ds_strstart d + 258) + 258)) with (wz lenv) by (f_equal; lia);
  replace (wz (ptr - (dl_Aw L + ds_strstart d + 258))) with (wz (lenv - 258)) by (f_equal; lia);
  rewrite <- LEN;
  zs; let KB := fresh "KB" in if_cases KB;
  [ zify_cond KB; rewrite ?signed_wz in KB by lia;
    lazymatch flip with false => apply HU; lia | true => apply HN; lia end
  | zify_cond KB; rewrite ?signed_wz in KB by lia;
    lazymatch flip with false => zs; apply HN; lia | true => apply HU; lia end ].

Lemma lm_inner : forall (Q : machine_state -> Prop) (cur best : Z) (x8 x28 x31 : word) (m : mem),
  u8arr psegs m (dl_Aw L) (av8 (ds_window d) 65536) -> 0 <= cur < ds_strstart d -> 1 <= best <= 258 ->
  (forall v9 v18 v19 v20 v21 v22, ~ best < lm_len (ds_window d) (ds_strstart d) cur ->
     evt psegs Q (MS (lmR x8 v9 (wz cur) (wz best) v18 v19 v20 v21 v22 x28 x31) F (wz 0x19f28) fc None m (seg_rom psegs))) ->
  (forall v19 v20 v21 v22, best < lm_len (ds_window d) (ds_strstart d) cur ->
     evt psegs Q (MS (lmR x8 (wz (lm_len (ds_window d) (ds_strstart d) cur)) (wz cur) (wz best) (wz (lm_len (ds_window d) (ds_strstart d) cur - 258)) v19 v20 v21 v22 x28 x31)
                     F (wz 0x19f08) fc None m (seg_rom psegs))) ->
  forall (n : nat) (i : Z) (v19 v20 v21 v22 : word), (1 <= n <= 32)%nat -> i = 8 * (32 - Z.of_nat n) ->
  lm_cmp_loop (S n) (ds_window d) (ds_strstart d + 2 + i) (cur + 2 + i) (ds_strstart d + 258) = lm_len (ds_window d) (ds_strstart d) cur + ds_strstart d ->
  evt psegs Q (MS (lmR x8 (wz (dl_Aw L + 5 + cur)) (wz cur) (wz best) (wz i) v19 v20 v21 v22 x28 x31) F (wz 0x19df0) fc None m (seg_rom psegs)).
Proof.
  intros Q cur best x8 x28 x31 m Gwin Hcur Hbest HN HU.
  induction n as [|n IH]; intros i v19 v20 v21 v22 Hn Hi RES; [lia|].
  pose proof (lm_len_bound (ds_window d) (ds_strstart d) cur) as LB.
  unfold lmR in *.
  do 2 zs.
  lm_cmp Gwin i cur 3. zs. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 3).
    { rewrite (cmp_round_mis _ _ _ _ _ 1%nat) in RES; [change (Z.of_nat 1) with 1 in RES; lia| lia| change (Z.of_nat 1) with 1; intros t Ht; lia|].
      change (Z.of_nat 1) with 1. replace (ds_strstart d + 2 + i + 1) with (ds_strstart d + i + 3) by lia. replace (cur + 2 + i + 1) with (cur + i + 3) by lia. exact K1. }
    do 3 zs. lm_mis HN HU LEN (dl_Aw L + ds_strstart d + i + 3) (i + 3) false. }
  assert (E1 : arr_get (ds_window d) (ds_strstart d + 2 + i + 1) = arr_get (ds_window d) (cur + 2 + i + 1))
    by (replace (ds_strstart d + 2 + i + 1) with (ds_strstart d + i + 3) by lia; replace (cur + 2 + i + 1) with (cur + i + 3) by lia; exact K1).
  lm_cmp Gwin i cur 4. zs. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 4).
    { rewrite (cmp_round_mis _ _ _ _ _ 2%nat) in RES; [change (Z.of_nat 2) with 2 in RES; lia| lia| change (Z.of_nat 2) with 2; intros t Ht; assert (C : t = 1) by lia; subst t; assumption|].
      change (Z.of_nat 2) with 2. replace (ds_strstart d + 2 + i + 2) with (ds_strstart d + i + 4) by lia. replace (cur + 2 + i + 2) with (cur + i + 4) by lia. exact K2. }
    do 3 zs. lm_mis HN HU LEN (dl_Aw L + ds_strstart d + i + 4) (i + 4) false. }
  assert (E2 : arr_get (ds_window d) (ds_strstart d + 2 + i + 2) = arr_get (ds_window d) (cur + 2 + i + 2))
    by (replace (ds_strstart d + 2 + i + 2) with (ds_strstart d + i + 4) by lia; replace (cur + 2 + i + 2) with (cur + i + 4) by lia; exact K2).
  lm_cmp Gwin i cur 5. zs. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 5).
    { rewrite (cmp_round_mis _ _ _ _ _ 3%nat) in RES; [change (Z.of_nat 3) with 3 in RES; lia| lia| change (Z.of_nat 3) with 3; intros t Ht; assert (C : t = 1 \/ t = 2) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 3) with 3. replace (ds_strstart d + 2 + i + 3) with (ds_strstart d + i + 5) by lia. replace (cur + 2 + i + 3) with (cur + i + 5) by lia. exact K3. }
    do 3 zs. lm_mis HN HU LEN (dl_Aw L + ds_strstart d + i + 5) (i + 5) false. }
  assert (E3 : arr_get (ds_window d) (ds_strstart d + 2 + i + 3) = arr_get (ds_window d) (cur + 2 + i + 3))
    by (replace (ds_strstart d + 2 + i + 3) with (ds_strstart d + i + 5) by lia; replace (cur + 2 + i + 3) with (cur + i + 5) by lia; exact K3).
  lm_cmp Gwin i cur 6. zs. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 6).
    { rewrite (cmp_round_mis _ _ _ _ _ 4%nat) in RES; [change (Z.of_nat 4) with 4 in RES; lia| lia| change (Z.of_nat 4) with 4; intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 4) with 4. replace (ds_strstart d + 2 + i + 4) with (ds_strstart d + i + 6) by lia. replace (cur + 2 + i + 4) with (cur + i + 6) by lia. exact K4. }
    do 3 zs. lm_mis HN HU LEN (dl_Aw L + ds_strstart d + i + 6) (i + 6) false. }
  assert (E4 : arr_get (ds_window d) (ds_strstart d + 2 + i + 4) = arr_get (ds_window d) (cur + 2 + i + 4))
    by (replace (ds_strstart d + 2 + i + 4) with (ds_strstart d + i + 6) by lia; replace (cur + 2 + i + 4) with (cur + i + 6) by lia; exact K4).
  lm_cmp Gwin i cur 7. zs. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 7).
    { rewrite (cmp_round_mis _ _ _ _ _ 5%nat) in RES; [change (Z.of_nat 5) with 5 in RES; lia| lia| change (Z.of_nat 5) with 5; intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3 \/ t = 4) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 5) with 5. replace (ds_strstart d + 2 + i + 5) with (ds_strstart d + i + 7) by lia. replace (cur + 2 + i + 5) with (cur + i + 7) by lia. exact K5. }
    do 3 zs. lm_mis HN HU LEN (dl_Aw L + ds_strstart d + i + 7) (i + 7) false. }
  assert (E5 : arr_get (ds_window d) (ds_strstart d + 2 + i + 5) = arr_get (ds_window d) (cur + 2 + i + 5))
    by (replace (ds_strstart d + 2 + i + 5) with (ds_strstart d + i + 7) by lia; replace (cur + 2 + i + 5) with (cur + i + 7) by lia; exact K5).
  lm_cmp Gwin i cur 8. zs. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 8).
    { rewrite (cmp_round_mis _ _ _ _ _ 6%nat) in RES; [change (Z.of_nat 6) with 6 in RES; lia| lia| change (Z.of_nat 6) with 6; intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 6) with 6. replace (ds_strstart d + 2 + i + 6) with (ds_strstart d + i + 8) by lia. replace (cur + 2 + i + 6) with (cur + i + 8) by lia. exact K6. }
    do 3 zs. lm_mis HN HU LEN (dl_Aw L + ds_strstart d + i + 8) (i + 8) false. }
  assert (E6 : arr_get (ds_window d) (ds_strstart d + 2 + i + 6) = arr_get (ds_window d) (cur + 2 + i + 6))
    by (replace (ds_strstart d + 2 + i + 6) with (ds_strstart d + i + 8) by lia; replace (cur + 2 + i + 6) with (cur + i + 8) by lia; exact K6).
  lm_cmp Gwin i cur 9. zs. if_cases K7; zify_cond K7; rewrite ?unsigned_lit in K7 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 9).
    { rewrite (cmp_round_mis _ _ _ _ _ 7%nat) in RES; [change (Z.of_nat 7) with 7 in RES; lia| lia| change (Z.of_nat 7) with 7; intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 7) with 7. replace (ds_strstart d + 2 + i + 7) with (ds_strstart d + i + 9) by lia. replace (cur + 2 + i + 7) with (cur + i + 9) by lia. exact K7. }
    do 3 zs. lm_mis HN HU LEN (dl_Aw L + ds_strstart d + i + 9) (i + 9) true. }
  assert (E7 : arr_get (ds_window d) (ds_strstart d + 2 + i + 7) = arr_get (ds_window d) (cur + 2 + i + 7))
    by (replace (ds_strstart d + 2 + i + 7) with (ds_strstart d + i + 9) by lia; replace (cur + 2 + i + 7) with (cur + i + 9) by lia; exact K7).
  lm_cmp Gwin i cur 10. do 2 zs. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by lia.
  { assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 10).
    { rewrite (cmp_round_mis _ _ _ _ _ 8%nat) in RES; [change (Z.of_nat 8) with 8 in RES; lia| lia| change (Z.of_nat 8) with 8; intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption|].
      change (Z.of_nat 8) with 8. replace (ds_strstart d + 2 + i + 8) with (ds_strstart d + i + 10) by lia. replace (cur + 2 + i + 8) with (cur + i + 10) by lia. exact K8. }
    do 4 zs. lm_mis HN HU LEN (dl_Aw L + ds_strstart d + (i + 8) + 2) (i + 10) false. }
  assert (E8 : arr_get (ds_window d) (ds_strstart d + 2 + i + 8) = arr_get (ds_window d) (cur + 2 + i + 8))
    by (replace (ds_strstart d + 2 + i + 8) with (ds_strstart d + i + 10) by lia; replace (cur + 2 + i + 8) with (cur + i + 10) by lia; exact K8).
  rewrite cmp_round_all in RES
    by (intros t Ht; assert (C : t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8) by lia; repeat (destruct C as [C|C]; [subst t; assumption|]); subst t; assumption).
  do 3 zs. if_cases KL; zify_cond KL; rewrite ?unsigned_lit in KL by lia.
  -
    replace (i + 10 <? 258) with true in RES by (symmetry; apply Z.ltb_lt; lia).
    apply (IH (i + 8)); [lia| lia| exact RES].
  -
    replace (i + 10 <? 258) with false in RES by (symmetry; apply Z.ltb_ge; lia).
    assert (LEN : lm_len (ds_window d) (ds_strstart d) cur = i + 10) by lia.
    do 4 zs. lm_mis HN HU LEN (dl_Aw L + ds_strstart d + (i + 8) + 2) (i + 10) false.
Qed.

Hypothesis Hnice : 0 <= nice <= 258.
Hypothesis Hlimit : 0 <= limit < 65536.
Hypothesis Hwm : ds_w_mask d = 32767.
Hypothesis LAY : dlay_ok L.
Hypothesis LW : Z.of_nat (length (av8 (ds_window d) 65536)) = 65536.
Hypothesis L16 : Z.of_nat (length (u16s (av16 (ds_prev d) 32768))) = 2 * 32768.

Notation Kloop := (fun s' c ch b e1 e => longest_match_loop _ s' c ch b nice limit e1 e).

Lemma lm_loop : forall (f : nat) (msk cur chain best se1 se : Z) (v9 v18 v19 v20 v21 v22 : word) (m : mem) (j8 h1 h2 h3 h4 h5 : list byte),
  rw_cells psegs m (dl_As L) (dsA_cells L (set_match_start d msk) h1 h2 h3 h4 h5) ->
  rw_cells psegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] ->
  stk psegs m lo (bv_unsigned sp + -64) ->
  munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] me m -> wmono psegs me m -> mem_inv psegs m ->
  u8arr psegs m (dl_Aw L) (av8 (ds_window d) 65536) -> u8arr psegs m (dl_Ap L) (u16s (av16 (ds_prev d) 32768)) ->
  f = Z.to_nat chain -> 1 <= chain < 2^31 -> 1 <= best <= 258 -> 0 <= se1 < 256 -> 0 <= se < 256 ->
  Forall (fun c => 0 <= c < ds_strstart d) (lm_curs f (set_match_start d msk) cur chain best nice limit se1 se) ->
  evt psegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L
               (fst (longest_match_loop f (set_match_start d msk) cur chain best nice limit se1 se))
               (if snd (longest_match_loop f (set_match_start d msk) cur chain best nice limit se1 se) <=? ds_lookahead d
                then snd (longest_match_loop f (set_match_start d msk) cur chain best nice limit se1 se) else ds_lookahead d) lo me)
    (MS (lmR (wz se) v9 (wz cur) (wz best) v18 v19 v20 v21 v22 (wz chain) (wz se1)) F (wz 0x19db8) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until h5; intros GA FR STK MU WM MI Gwin Gprev Hf Hchain Hbest Hse1 Hse VIS; [lia|].
  rewrite lm_loop_S. rewrite lm_curs_S in VIS. apply Forall_cons_iff in VIS. destruct VIS as [Hcur VIS].
  remember (lm_tripG (fun s' c ch b e1 e => longest_match_loop f s' c ch b nice limit e1 e) (fun s' b => (s', b))
                     (set_match_start d msk) cur chain best nice limit se1 se) as R eqn:ER.
  unfold lm_tripG in ER, VIS. cbv zeta in ER, VIS.
  change (ds_window (set_match_start d msk)) with (ds_window d) in *. change (ds_strstart (set_match_start d msk)) with (ds_strstart d) in *.
  change (ds_prev (set_match_start d msk)) with (ds_prev d) in *. change (ds_w_mask (set_match_start d msk)) with (ds_w_mask d) in *.
  change (set_match_start (set_match_start d msk) cur) with (set_match_start d cur) in *.
  assert (HNEXT : forall (msk' best' se1' se' : Z) (w9 w18 w19 w20 w21 w22 : word) (m' : mem) (k1 k2 k3 k4 k5 : list byte),
    rw_cells psegs m' (dl_As L) (dsA_cells L (set_match_start d msk') k1 k2 k3 k4 k5) ->
    rw_cells psegs m' (bv_unsigned sp + -64) [CB 8 j8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] ->
    stk psegs m' lo (bv_unsigned sp + -64) ->
    munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] me m' -> wmono psegs me m' -> mem_inv psegs m' ->
    u8arr psegs m' (dl_Aw L) (av8 (ds_window d) 65536) -> u8arr psegs m' (dl_Ap L) (u16s (av16 (ds_prev d) 32768)) ->
    1 <= best' <= 258 -> 0 <= se1' < 256 -> 0 <= se' < 256 ->
    R = lm_restG (fun s' c ch b e1 e => longest_match_loop f s' c ch b nice limit e1 e) (fun s' b => (s', b))
                 (ds_prev d) (ds_w_mask d) limit (set_match_start d msk') cur chain best' se1' se' ->
    Forall (fun c => 0 <= c < ds_strstart d)
      (lm_restG (fun s' c ch b e1 e => lm_curs f s' c ch b nice limit e1 e) (fun _ _ => []) (ds_prev d) (ds_w_mask d) limit (set_match_start d msk') cur chain best' se1' se') ->
    evt psegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L R.1 (if R.2 <=? ds_lookahead d then R.2 else ds_lookahead d) lo me)
      (MS (lmR (wz se') w9 (wz cur) (wz best') w18 w19 w20 w21 w22 (wz chain) (wz se1')) F (wz 0x19f28) fc None m' (seg_rom psegs))).
  { intros until k5. intros GA' FR' STK' MU' WM' MI' Gwin' Gprev' Hb' He1' He' ER' VIS'.
    unfold lmR.
    assert (RL : 0 <= Z.land cur (ds_w_mask d) < 32768).
    { rewrite Hwm. change 32767 with (Z.ones 15). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
    pose proof (Hpb (Z.land cur (ds_w_mask d)) RL) as RPV.
    assert (RWM : 0 <= ds_w_mask d < 2^31) by (rewrite Hwm; lia).
    do 3 zs. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    ld16 Gprev' (ds_prev d) 32768 (dl_Ap L) (Z.land cur (ds_w_mask d)) ltac:(assumption).
    unfold lm_restG in ER', VIS'. cbv zeta in ER', VIS'.
    zs. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by lia.
    -
      replace (limit <? arr_get (ds_prev d) (Z.land cur (ds_w_mask d))) with false in ER' by (symmetry; apply Z.ltb_ge; lia).
      rewrite ER'. cbn [fst snd].
      eapply lm_exit; [exact GA'| exact FR'| exact STK'| exact MU'| exact WM'| exact MI'| lia].
    - replace (limit <? arr_get (ds_prev d) (Z.land cur (ds_w_mask d))) with true in ER', VIS' by (symmetry; apply Z.ltb_lt; lia).
      rewrite wrap32_id in ER', VIS' by lia.
      do 2 zs. if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by lia.
      +
        replace (chain - 1 =? 0) with false in ER', VIS' by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in ER', VIS'.
        rewrite ER'. replace (wz (chain + -1)) with (wz (chain - 1)) by (f_equal; lia).
        eapply (IH msk' (arr_get (ds_prev d) (Z.land cur (ds_w_mask d))) (chain - 1) best' se1' se');
          [exact GA'| exact FR'| exact STK'| exact MU'| exact WM'| exact MI'| exact Gwin'| exact Gprev'| lia| lia| lia| lia| lia| exact VIS'].
      + replace (chain - 1 =? 0) with true in ER' by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in ER'.
        rewrite ER'. cbn [fst snd].
        eapply lm_exit; [exact GA'| exact FR'| exact STK'| exact MU'| exact WM'| exact MI'| lia]. }
  assert (LB := lm_len_bound (ds_window d) (ds_strstart d) cur).
  assert (HUPD : forall w19 w20 w21 w22 : word, lm_early (ds_window d) (ds_strstart d) cur best se1 se = false ->
    best < lm_len (ds_window d) (ds_strstart d) cur ->
    evt psegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L R.1 (if R.2 <=? ds_lookahead d then R.2 else ds_lookahead d) lo me)
      (MS (lmR (wz se) (wz (lm_len (ds_window d) (ds_strstart d) cur)) (wz cur) (wz best) (wz (lm_len (ds_window d) (ds_strstart d) cur - 258)) w19 w20 w21 w22 (wz chain) (wz se1))
          F (wz 0x19f08) fc None m (seg_rom psegs))).
  { intros w19 w20 w21 w22 HEARLY HLT. unfold lmR. unfold dsA_cells in GA.
    rewrite HEARLY in ER, VIS.
    remember (lm_len (ds_window d) (ds_strstart d) cur) as len eqn:Elen.
    replace (best <? len) with true in ER, VIS by (symmetry; apply Z.ltb_lt; lia).
    zs. zs. if_cases KN; zify_cond KN; rewrite ?signed_wz in KN by lia.
    -
      do 2 zs.
      replace (nice <=? len) with true in ER by (symmetry; apply Z.leb_le; lia).
      rewrite ER. cbn [fst snd].
      eapply (lm_exit cur len); [exact GA| exact FR| exact STK| exact MU| exact WM| eassumption| lia].
    - replace (nice <=? len) with false in ER, VIS by (symmetry; apply Z.leb_gt; lia).
      pose proof (Hwb (ds_strstart d + len - 1) ltac:(lia)). pose proof (Hwb (ds_strstart d + len) ltac:(lia)).
      do 3 zs. rewrite swrap32_mod64 by lia.
      ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + len - 1) ltac:(assumption).
      ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + len) ltac:(assumption).
      zs.
      eapply (HNEXT cur len (arr_get (ds_window d) (ds_strstart d + len - 1)) (arr_get (ds_window d) (ds_strstart d + len)));
        [exact GA| exact FR| exact STK| exact MU| exact WM| eassumption| exact Gwin| exact Gprev| lia| lia| lia| exact ER| exact VIS]. }
  assert (HREJ : forall w9 w18 w19 w20 w21 w22 : word, lm_early (ds_window d) (ds_strstart d) cur best se1 se = true ->
    evt psegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L R.1 (if R.2 <=? ds_lookahead d then R.2 else ds_lookahead d) lo me)
      (MS (lmR (wz se) w9 (wz cur) (wz best) w18 w19 w20 w21 w22 (wz chain) (wz se1)) F (wz 0x19f28) fc None m (seg_rom psegs))).
  { intros w9 w18 w19 w20 w21 w22 HE. rewrite HE in ER, VIS.
    eapply (HNEXT msk best se1 se); [exact GA| exact FR| exact STK| exact MU| exact WM| exact MI| exact Gwin| exact Gprev| lia| lia| lia| exact ER| exact VIS]. }
  assert (HNOLEN : forall w9 w18 w19 w20 w21 w22 : word, lm_early (ds_window d) (ds_strstart d) cur best se1 se = false ->
    ~ best < lm_len (ds_window d) (ds_strstart d) cur ->
    evt psegs (lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L R.1 (if R.2 <=? ds_lookahead d then R.2 else ds_lookahead d) lo me)
      (MS (lmR (wz se) w9 (wz cur) (wz best) w18 w19 w20 w21 w22 (wz chain) (wz se1)) F (wz 0x19f28) fc None m (seg_rom psegs))).
  { intros w9 w18 w19 w20 w21 w22 HE HL. rewrite HE in ER, VIS.
    replace (best <? lm_len (ds_window d) (ds_strstart d) cur) with false in ER, VIS by (symmetry; apply Z.ltb_ge; lia).
    eapply (HNEXT msk best se1 se); [exact GA| exact FR| exact STK| exact MU| exact WM| exact MI| exact Gwin| exact Gprev| lia| lia| lia| exact ER| exact VIS]. }
  clear HNEXT ER VIS IH.
  pose proof (Hwb (cur + best) ltac:(lia)). pose proof (Hwb (cur + best - 1) ltac:(lia)).
  pose proof (Hwb (ds_strstart d) ltac:(lia)). pose proof (Hwb cur ltac:(lia)).
  pose proof (Hwb (ds_strstart d + 1) ltac:(lia)). pose proof (Hwb (cur + 1) ltac:(lia)).
  unfold lmR. do 2 zs.
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (cur + best) ltac:(assumption).
  zs. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  { eapply HREJ. unfold lm_early. replace (arr_get (ds_window d) (cur + best) =? se) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (cur + best - 1) ltac:(assumption).
  zs. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  { eapply HREJ. unfold lm_early. replace (arr_get (ds_window d) (cur + best - 1) =? se1) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite orb_true_r. reflexivity. }
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d) ltac:(assumption).
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) cur ltac:(assumption).
  zs. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
  { eapply HREJ. unfold lm_early. replace (arr_get (ds_window d) cur =? arr_get (ds_window d) (ds_strstart d)) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite orb_true_r. reflexivity. }
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + 1) ltac:(assumption).
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (cur + 1) ltac:(assumption).
  zs. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
  { eapply HREJ. unfold lm_early. replace (arr_get (ds_window d) (cur + 1) =? arr_get (ds_window d) (ds_strstart d + 1)) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite orb_true_r. reflexivity. }
  assert (HE : lm_early (ds_window d) (ds_strstart d) cur best se1 se = false).
  { unfold lm_early. rewrite !(proj2 (Z.eqb_eq _ _)) by lia. reflexivity. }
  do 2 zs.
  replace (wz 0) with (wz (8 * (32 - Z.of_nat 32))) by reflexivity.
  eapply (lm_inner _ cur best (wz se) (wz chain) (wz se1) m Gwin ltac:(lia) Hbest) with (n := 32%nat) (i := 8 * (32 - Z.of_nat 32)).
  - intros. eapply HNOLEN; assumption.
  - intros. eapply HUPD; assumption.
  - lia.
  - reflexivity.
  - change (8 * (32 - Z.of_nat 32)) with 0. rewrite !Z.add_0_r. unfold lm_len. lia.
Qed.

End LM.

Definition lm_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (d : deflate_state) (cur lo : Z) (m : mem) : machine_state -> Prop :=
  lm_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (fst (longest_match d cur)) (snd (longest_match d cur)) lo m.

Lemma longest_match_spec : forall (L : dlay) (d : deflate_state) (cur lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L d -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> dlay_below L lo (bv_unsigned sp) ->
  lm_ok d cur -> ds_w_size d = 32768 ->
  a0 = wz (dl_As L) -> a1 = wz cur ->
  evt psegs (lm_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L d cur lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_LONGEST_MATCH) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST MI STK LO BEL LMOK WS -> ->. unfold Z_LONGEST_MATCH.
  destruct LMOK as (Hwb & Hpb & Hs0 & Hs258 & Hwm & Hpl & Hnice & Hlook & Hgood & Hmc & Hch & Hcur & Hvis & Hres).
  rewrite WS in Hwb, Hpb, Hs258, Hwm.
  assert (HREST : forall m' ms, munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] m m' -> wmono psegs m m' ->
            dsA m' L (set_match_start d ms) -> DST m' L (set_match_start d ms)).
  { intros m' ms MUx WMx GAx. pose proof (st_lay _ _ _ _ ST) as LAYx. below_open BEL. lay_open LAYx. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY].
    clear GA. tr_groups MUx WMx.
    constructor; [exact GAx| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS| exact LAY]. }
  open_DST ST. open_A GA. open_win Gwin. open_u16 Gprev. lay_open LAY. below_open BEL.
  pose proof (munch_refl [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  assert (RWS : 0 <= ds_w_size d < 2^31) by lia.
  do 8 zs. do 9 zs. rewrite limit_mask by lia. do 2 zs.
  replace (Z.lxor (Z.b2z (ds_prev_length d <? ds_good_match d)) 1 ≪ 1) with (if ds_good_match d <=? ds_prev_length d then 2 else 0)
    by (destruct (Z.ltb_spec (ds_prev_length d) (ds_good_match d)); destruct (Z.leb_spec (ds_good_match d) (ds_prev_length d)); try lia; reflexivity).
  zs.
  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - replace (wz (ds_nice_match d)) with (wz (if ds_lookahead d <? ds_nice_match d then ds_lookahead d else ds_nice_match d))
        by (f_equal; destruct (Z.ltb_spec (ds_lookahead d) (ds_nice_match d)); lia).
      apply evt_done. reflexivity.
    - zs. apply evt_done. repeat f_equal. destruct (Z.ltb_spec (ds_lookahead d) (ds_nice_match d)); lia. }
  intros ms' ->.
  carve_frame 64%nat STK.
  do 8 zs. do 3 zs.
  pose proof (Hwb (ds_strstart d + ds_prev_length d - 1) ltac:(lia)). pose proof (Hwb (ds_strstart d + ds_prev_length d) ltac:(lia)).
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + ds_prev_length d - 1) ltac:(assumption).
  ld8 Gwin (ds_window d) 65536 (dl_Aw L) (ds_strstart d + ds_prev_length d) ltac:(assumption).
  do 3 zs.
  set (chain0 := if ds_good_match d <=? ds_prev_length d then ds_max_chain_length d ≫ 2 else ds_max_chain_length d) in *.
  replace (wz (bv_swrap 32 (bv_wrap 32 (ds_max_chain_length d) ≫ ((if ds_good_match d <=? ds_prev_length d then 2 else 0) mod 32)))) with (wz chain0).
  2:{ f_equal. subst chain0. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. change (2 ^ 32) with 4294967296. rewrite (Z.mod_small (ds_max_chain_length d)) by lia.
      assert (SH : 0 <= ds_max_chain_length d ≫ 2 <= ds_max_chain_length d).
      { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]. }
      destruct (ds_good_match d <=? ds_prev_length d).
      - change (2 mod 32) with 2. rewrite bv_swrap32_id by lia. reflexivity.
      - change (0 mod 32) with 0. rewrite Z.shiftr_0_r, bv_swrap32_id by lia. reflexivity. }
  assert (RCH : 1 <= chain0 < 2^31).
  { subst chain0. split; [exact Hch|]. destruct (ds_good_match d <=? ds_prev_length d); [|lia].
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. apply Z.div_lt_upper_bound; lia. }
  assert (VIS0 : Forall (fun c => 0 <= c < ds_strstart d)
            (lm_curs (Z.to_nat chain0) (set_match_start d (ds_match_start d)) cur chain0 (ds_prev_length d)
               (if ds_lookahead d <? ds_nice_match d then ds_lookahead d else ds_nice_match d)
               (if ds_w_size d - 262 <? ds_strstart d then ds_strstart d - (ds_w_size d - 262) else 0)
               (arr_get (ds_window d) (ds_strstart d + ds_prev_length d - 1)) (arr_get (ds_window d) (ds_strstart d + ds_prev_length d)))).
  { rewrite set_ms_self. exact Hvis. }
  assert (EQ : longest_match d cur =
               (let r := longest_match_loop (Z.to_nat chain0) (set_match_start d (ds_match_start d)) cur chain0 (ds_prev_length d)
                           (if ds_lookahead d <? ds_nice_match d then ds_lookahead d else ds_nice_match d)
                           (if ds_w_size d - 262 <? ds_strstart d then ds_strstart d - (ds_w_size d - 262) else 0)
                           (arr_get (ds_window d) (ds_strstart d + ds_prev_length d - 1)) (arr_get (ds_window d) (ds_strstart d + ds_prev_length d)) in
                (fst r, if snd r <=? ds_lookahead d then snd r else ds_lookahead d))).
  { rewrite set_ms_self. unfold longest_match, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH, NIL. cbv zeta. fold chain0.
    replace (ds_w_size d - (258 + 3 + 1)) with (ds_w_size d - 262) by lia.
    match goal with |- context [longest_match_loop ?f ?s ?c ?ch ?b ?n ?l ?e1 ?e] =>
      destruct (longest_match_loop_ms f s c ch b n l e1 e) as [msF EF]; destruct (longest_match_loop f s c ch b n l e1 e) as [sF bF] end.
    cbn [fst snd] in *. subst sF. change (ds_lookahead (set_match_start d msF)) with (ds_lookahead d).
    destruct (bF <=? ds_lookahead d); reflexivity. }
  clearbody chain0.
  unfold lm_post. rewrite EQ. cbv zeta. cbn [fst snd].
  assert (T1 : ds_w_mask d = 32767) by lia.
  assert (T2 : 0 < dl_Ap L /\ dl_Ap L + 65536 < 2^62) by lia.
  assert (T3 : 0 < dl_Aw L /\ dl_Aw L + 65536 < 2^62) by lia.
  assert (T4 : 0 <= (if ds_lookahead d <? ds_nice_match d then ds_lookahead d else ds_nice_match d) <= 258) by (destruct (Z.ltb_spec (ds_lookahead d) (ds_nice_match d)); lia).
  assert (T5 : 0 <= (if ds_w_size d - 262 <? ds_strstart d then ds_strstart d - (ds_w_size d - 262) else 0) < 65536) by (destruct (Z.ltb_spec (ds_w_size d - 262) (ds_strstart d)); lia).
  assert (T6 : 0 <= ds_strstart d /\ ds_strstart d + 258 < 65536) by lia.
  assert (T7 : lo <= bv_unsigned sp + -64) by lia.
  assert (T8 : dl_As L + 5968 <= lo) by lia.
  assert (T9 : 0 < dl_As L) by lia.
  eapply (lm_loop L d lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m Hwb Hpb T6 Hlook HREST T7 T8 T9
            (if ds_lookahead d <? ds_nice_match d then ds_lookahead d else ds_nice_match d)
            (if ds_w_size d - 262 <? ds_strstart d then ds_strstart d - (ds_w_size d - 262) else 0)
            T3 T4 T5 T1 LAY LW L16
            (Z.to_nat chain0) (ds_match_start d) cur chain0 (ds_prev_length d)
            (arr_get (ds_window d) (ds_strstart d + ds_prev_length d - 1)) (arr_get (ds_window d) (ds_strstart d + ds_prev_length d)));
    [exact GA| exact FR| exact STK| exact MU| exact WM| exact MI| exact Gwin| exact Gprev| reflexivity| lia| lia| lia| lia| exact VIS0].
Qed.
