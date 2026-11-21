(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_pure2 Z_updwin_pure Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface InflateState RefUpdWin1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition Z_UPDATEWINDOW : Z := 0x21690.
Definition PC_UW_BODY : Z := 0x21708.
Definition PC_UW_RET : Z := 0x21700.

Definition updwin_post (L : ilay) (s' : inflate_state) (rc : Z) (lo : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (W : list ivl) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz rc) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp) /\ isA m' L s' /\ iwin m' L s'.
Definition PC_UW_COPY : Z := 0x21714.

Lemma xor_guard_sub : forall a b, 0 < a -> 0 <= b -> a <> b -> Z.lxor (Z.b2z (0 <? a)) (Z.b2z (Z.lxor a b <? 1)) = 1.
Proof.
  intros a b Ha Hb Hne. rewrite (proj2 (Z.ltb_lt 0 a) Ha).
  assert (NZ : Z.lxor a b <> 0) by (intros E0; apply Hne; apply Z.lxor_eq; exact E0).
  pose proof (Z.lxor_nonneg a b) as NN.
  replace (Z.lxor a b <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma xor_guard_sub0 : forall a, 0 < a -> Z.lxor (Z.b2z (0 <? a)) (Z.b2z (a <? 1)) = 1.
Proof. intros a Ha. rewrite (proj2 (Z.ltb_lt 0 a) Ha). replace (a <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Ltac gXsub := first [ rewrite xor_guard_sub by lia | rewrite xor_guard_sub0 by lia ]; zs; br_false.

Lemma updwin_copy_spec : forall (fj : list byte) (L : ilay) (s : inflate_state) (src : arr) (put copy E lo : Z) (b : ZProg.blk)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a3 a4 a5 a6 a7 x18 x20 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (W0 : list ivl),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  isA m L s -> is_window_blk s = Some b -> iwin m L s -> arr_len (is_window s) = 32768 ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) ->
  is_wbits s = 15 -> 0 <= copy <= 1 ->
  is_wsize s = 32768 -> 0 <= is_wnext s < 32768 -> 0 <= is_whave s <= 32768 ->
  lo <= bv_unsigned sp - 64 -> 0x5e000 <= lo -> bv_unsigned sp < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo -> 0 < il_Aw L -> il_Aw L + 32768 <= lo -> apart (il_As L) 7176 (il_Aw L) 32768 ->
  0 < E - copy -> E <= lo -> (E <= il_Aw L \/ il_Aw L + 32768 <= E - copy) ->
  mem_inv usegs m ->
  munch W0 m0 m -> wmono usegs m0 m ->
  W0 = [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (il_Aw L, il_Aw L + 32768)] ->
  evt usegs (updwin_post L (updw_core s src put copy) 0 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W0 m0)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz (il_Aw L)) a1 (wz 32768) a3 a4 a5 a6 a7 x18 (wz (il_As L)) x20
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_COPY) fc None m (seg_rom usegs)).
Proof.
  intros until W0. intros FR STK GA HB GW LW SRC Hwb Hc Hws Hwn Hwh LO1 LO2 SP63 As0 As1 Aw0 Aw1 SEPW E0 E1 SEPE MI MU WM EW.
  rewrite (updw_small1 s src put copy Hwb Hc Hws Hwn Hwh).
  unfold iwin in GW. rewrite HB in GW.
  pose proof (av8_zlength (is_window s) 32768 ltac:(lia)) as LWIN.
  unfold apart in SEPW. subst W0.
  assert (EBL : firstn (Z.to_nat (is_wnext s)) (av8 (is_window s) 32768) ++ map (Z_to_bv 8) (arr_slice src (put - copy) copy)
                ++ skipn (Z.to_nat (is_wnext s) + Z.to_nat copy) (av8 (is_window s) 32768)
                = av8 (arr_blit (is_window s) (is_wnext s) src (put - copy) copy) 32768) by (apply av8_blit; lia).
  destruct (u8arr_split3 m _ _ (Z.to_nat (is_wnext s)) (Z.to_nat copy) GW ltac:(rewrite av8_length; lia)) as (W1 & WC & W3).
  replace (Z.of_nat (Z.to_nat (is_wnext s))) with (is_wnext s) in WC, W3 by lia. replace (Z.of_nat (Z.to_nat copy)) with copy in W3 by lia.
  assert (LW1 : Z.of_nat (length (firstn (Z.to_nat (is_wnext s)) (av8 (is_window s) 32768))) = is_wnext s) by (rewrite length_firstn, av8_length; lia).
  assert (LW3 : Z.of_nat (length (skipn (Z.to_nat (is_wnext s) + Z.to_nat copy) (av8 (is_window s) 32768))) = 32768 - is_wnext s - copy) by (rewrite length_skipn, av8_length; lia).
  clear GW. open_isA GA.
  set (bsrc := map (Z_to_bv 8) (arr_slice src (put - copy) copy)) in *.
  assert (LSRC : length bsrc = Z.to_nat copy) by (subst bsrc; rewrite length_map; unfold arr_slice; apply arr_slice_nat_length).
  set (bpre := firstn (Z.to_nat (is_wnext s)) (av8 (is_window s) 32768)) in *.
  set (bsuf := skipn (Z.to_nat (is_wnext s) + Z.to_nat copy) (av8 (is_window s) 32768)) in *.
  set (bjunk := firstn (Z.to_nat copy) (skipn (Z.to_nat (is_wnext s)) (av8 (is_window s) 32768))) in *.
  assert (C01 : copy = 0 \/ copy = 1) by lia. clear Hc.
  destruct C01 as [-> | ->].
  - destruct bsrc as [|b0 bsrc]; try discriminate LSRC. change (Z.to_nat 0) with 0%nat in *.
    unfold PC_UW_COPY. do 3 zs. zs. br_false. zs.
    zs. rewrite zb_lxor_ones by lia. zs. br_false.
    do 2 zs. rewrite ?land_u32_small by lia. zs. br_false.
    do 4 zs. gXsub.
    do 4 zs. rewrite ?land_u32_small by lia. zs.
    call (memcpy_Z (il_Aw L + is_wnext s) (E - 0) 0).
    1:{ exact SRC. } 1:{ reflexivity. } 1:{ exact WC. } 1:{ lia. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    assert (LEN1 : length bpre = Z.to_nat (is_wnext s)) by lia.
    pose proof (u8arr_join3k _ (il_Aw L) _ _ _ (Z.to_nat (is_wnext s)) 0%nat LEN1 W1 ltac:(replace (Z.of_nat (Z.to_nat (is_wnext s))) with (is_wnext s) by lia; exact PC)
                  ltac:(replace (Z.of_nat (Z.to_nat (is_wnext s))) with (is_wnext s) by lia; exact W3)) as GW.
    rewrite EBL in GW. clear W1 W3 PC POST SRC EBL LW1 LW3 LEN1.
    pose proof (av8_zlength (arr_blit (is_window s) (is_wnext s) src (put - 0) 0) 32768 ltac:(lia)) as LWIN2.
    zs. br_true. do 8 zs. rewrite mask_eq_clang by lia. rewrite Hws.
    do 3 zs. br_cases K.
    +
      replace (is_whave s <? 32768) with false by (symmetry; apply Z.ltb_ge; lia).
      do 9 zs. release_frame FR STK (bv_unsigned sp). zs.
      apply evt_done. unfold updwin_post. do 15 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [exact STK|]. split; [unfold isA, isA_cells, uw_set; ired; rewrite ?Z.add_0_r; close_cells GA|].
      unfold iwin, uw_set; ired; rewrite HB; exact GW.
    + replace (is_whave s <? 32768) with true by (symmetry; apply Z.ltb_lt; lia).
      do 3 zs. do 9 zs. release_frame FR STK (bv_unsigned sp). zs.
      apply evt_done. unfold updwin_post. do 15 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [exact STK|]. split; [unfold isA, isA_cells, uw_set; ired; rewrite ?Z.add_0_r; close_cells GA|].
      unfold iwin, uw_set; ired; rewrite HB; exact GW.

  - destruct bsrc as [|b0 [|b1 bsrc]]; try discriminate LSRC. change (Z.to_nat 1) with 1%nat in *.
    unfold PC_UW_COPY. do 3 zs. zs. br_false. zs.
    zs. rewrite zb_lxor_ones by lia. zs. br_false.
    do 2 zs. rewrite ?land_u32_small by lia. zs. br_false.
    do 4 zs. gXsub.
    do 4 zs. rewrite ?land_u32_small by lia. zs.
    call (memcpy_Z (il_Aw L + is_wnext s) (E - 1) 1).
    1:{ exact SRC. } 1:{ reflexivity. } 1:{ exact WC. } 1:{ lia. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    assert (LEN1 : length bpre = Z.to_nat (is_wnext s)) by lia.
    pose proof (u8arr_join3k _ (il_Aw L) _ _ _ (Z.to_nat (is_wnext s)) 1%nat LEN1 W1 ltac:(replace (Z.of_nat (Z.to_nat (is_wnext s))) with (is_wnext s) by lia; exact PC)
                  ltac:(replace (Z.of_nat (Z.to_nat (is_wnext s))) with (is_wnext s) by lia; exact W3)) as GW.
    rewrite EBL in GW. clear W1 W3 PC POST SRC EBL LW1 LW3 LEN1.
    pose proof (av8_zlength (arr_blit (is_window s) (is_wnext s) src (put - 1) 1) 32768 ltac:(lia)) as LWIN2.
    zs. br_true. do 8 zs. rewrite mask_eq_clang by lia. rewrite Hws.
    do 3 zs. br_cases K.
    +
      replace (is_whave s <? 32768) with false by (symmetry; apply Z.ltb_ge; lia).
      do 9 zs. release_frame FR STK (bv_unsigned sp). zs.
      apply evt_done. unfold updwin_post. do 15 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [exact STK|]. split; [unfold isA, isA_cells, uw_set; ired; rewrite ?Z.add_0_r; close_cells GA|].
      unfold iwin, uw_set; ired; rewrite HB; exact GW.
    + replace (is_whave s <? 32768) with true by (symmetry; apply Z.ltb_lt; lia).
      do 3 zs. do 9 zs. release_frame FR STK (bv_unsigned sp). zs.
      apply evt_done. unfold updwin_post. do 15 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [exact STK|]. split; [unfold isA, isA_cells, uw_set; ired; rewrite ?Z.add_0_r; close_cells GA|].
      unfold iwin, uw_set; ired; rewrite HB; exact GW.

Qed.

Lemma updwin_body_spec : forall (fj : list byte) (L : ilay) (s : inflate_state) (src : arr) (put copy E lo : Z) (b : ZProg.blk)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a2 a3 a4 a5 a6 a7 x18 x20 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (W0 : list ivl),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  isA m L s -> is_window_blk s = Some b -> iwin m L s -> arr_len (is_window s) = 32768 ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) ->
  is_wbits s = 15 -> 0 <= copy <= 1 ->
  (is_wsize s <> 0 -> is_wsize s = 32768) -> 0 <= uw_wnext0 s < 32768 -> 0 <= uw_whave0 s <= 32768 ->
  lo <= bv_unsigned sp - 64 -> 0x5e000 <= lo -> bv_unsigned sp < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo -> 0 < il_Aw L -> il_Aw L + 32768 <= lo -> apart (il_As L) 7176 (il_Aw L) 32768 ->
  0 < E - copy -> E <= lo -> (E <= il_Aw L \/ il_Aw L + 32768 <= E - copy) -> (E <= il_As L \/ il_As L + 7176 <= E - copy) ->
  mem_inv usegs m ->
  munch W0 m0 m -> wmono usegs m0 m ->
  W0 = [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (il_Aw L, il_Aw L + 32768)] ->
  evt usegs (updwin_post L (updw_core s src put copy) 0 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W0 m0)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz (il_Aw L)) a1 a2 a3 a4 a5 a6 a7 x18 (wz (il_As L)) x20
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_BODY) fc None m (seg_rom usegs)).
Proof.
  intros until W0. intros FR STK GA HB GW LW SRC Hwb Hc Hws Hwn Hwh LO1 LO2 SP63 As0 As1 Aw0 Aw1 SEPW E0 E1 SEPE SEPS MI MU WM EW.
  rewrite (updw_core_sA s src put copy Hwb).
  destruct (Z.eq_dec (is_wsize s) 0) as [W0z|W0n].
  -
    assert (ESA : sA s = iset_whave (iset_wnext (iset_wsize s 32768) 0) 0).
    { unfold sA. rewrite W0z, Hwb. reflexivity. }
    pose proof SEPW as SEPW0. unfold apart in SEPW. pose proof EW as EW0. subst W0.
    pose proof GA as GA0. open_isA GA. unfold iwin in GW. rewrite HB in GW.
    pose proof (av8_zlength (is_window s) 32768 ltac:(lia)) as LWIN.
    assert (C01 : copy = 0 \/ copy = 1) by lia.
    destruct C01 as [-> | ->].
    + change (map (Z_to_bv 8) (arr_slice src (put - 0) 0)) with (@nil byte) in SRC.
      unfold PC_UW_BODY. zs. rewrite W0z. zs. br_true. zs. rewrite Hwb. zs. zs. br_false. do 3 zs.
      (* 1.4 UBSan: whave (76) and wnext (80) are two word stores (sw, sw); 1.3.1 cleared both with one sd zero,64 through a recast *)
      zs. zs.
      zs. br_true.
      rewrite ESA.
      eapply (updwin_copy_spec _ L (iset_whave (iset_wnext (iset_wsize s 32768) 0) 0) src put 0 E lo b);
        [ exact FR | exact STK | unfold isA, isA_cells; ired; close_cells GA | exact HB | unfold iwin; ired; rewrite HB; exact GW | exact LW
        | exact SRC | exact Hwb | lia | reflexivity | cbn; lia | cbn; lia | lia | lia | lia | lia | lia | lia | lia | exact SEPW0 | lia | lia | exact SEPE
        | eassumption | exact MU | exact WM | reflexivity ].
    + change (map (Z_to_bv 8) (arr_slice src (put - 1) 1)) with [Z_to_bv 8 (arr_get src (put - 1))] in SRC.
      unfold PC_UW_BODY. zs. rewrite W0z. zs. br_true. zs. rewrite Hwb. zs. zs. br_false. do 3 zs.
      (* 1.4 UBSan: whave (76) and wnext (80) are two word stores (sw, sw); 1.3.1 cleared both with one sd zero,64 through a recast *)
      zs. zs.
      zs. br_true.
      rewrite ESA.
      eapply (updwin_copy_spec _ L (iset_whave (iset_wnext (iset_wsize s 32768) 0) 0) src put 1 E lo b);
        [ exact FR | exact STK | unfold isA, isA_cells; ired; close_cells GA | exact HB | unfold iwin; ired; rewrite HB; exact GW | exact LW
        | exact SRC | exact Hwb | lia | reflexivity | cbn; lia | cbn; lia | lia | lia | lia | lia | lia | lia | lia | exact SEPW0 | lia | lia | exact SEPE
        | eassumption | exact MU | exact WM | reflexivity ].
  -
    specialize (Hws W0n).
    assert (ESA : sA s = s) by (unfold sA; replace (is_wsize s =? 0) with false by (symmetry; apply Z.eqb_neq; exact W0n); reflexivity).
    rewrite ESA. unfold uw_wnext0, uw_whave0 in Hwn, Hwh. replace (is_wsize s =? 0) with false in Hwn, Hwh by (symmetry; apply Z.eqb_neq; exact W0n).
    pose proof GA as GA0. open_isA GA.
    unfold PC_UW_BODY. zs. rewrite Hws. zs. br_false. zs. br_false.
    eapply (updwin_copy_spec _ L s src put copy E lo b);
      [ exact FR | exact STK | exact GA0 | exact HB | exact GW | exact LW
      | exact SRC | exact Hwb | lia | exact Hws | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact SEPW | lia | lia | exact SEPE
      | eassumption | exact MU | exact WM | exact EW ].
Qed.

Lemma updwin_have_spec : forall (L : ilay) (s : inflate_state) (c : icall) (src : arr) (put copy E lo : Z) (b : ZProg.blk)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk usegs m lo (bv_unsigned sp) -> izs m L c ->
  isA m L s -> is_window_blk s = Some b -> iwin m L s -> arr_len (is_window s) = 32768 ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) ->
  is_wbits s = 15 -> 0 <= copy <= 1 ->
  (is_wsize s <> 0 -> is_wsize s = 32768) -> 0 <= uw_wnext0 s < 32768 -> 0 <= uw_whave0 s <= 32768 ->
  lo <= bv_unsigned sp - 64 -> 0x5e000 <= lo -> bv_unsigned sp <= il_S L -> il_S L + 112 < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo -> 0 < il_Aw L -> il_Aw L + 32768 <= lo -> apart (il_As L) 7176 (il_Aw L) 32768 ->
  0 < E - copy -> E <= lo -> (E <= il_Aw L \/ il_Aw L + 32768 <= E - copy) -> (E <= il_As L \/ il_As L + 7176 <= E - copy) ->
  mem_inv usegs m ->
  il_S L mod 8 = 0 -> il_As L mod 16 = 0 ->
  evt usegs (updwin_post L (updw_core s src put copy) 0 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                         [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (il_Aw L, il_Aw L + 32768)] m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (il_S L)) (wz E) (wz copy) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_UPDATEWINDOW) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros STK ZS GA HB GW LW SRC Hwb Hc Hws Hwn Hwh LO1 LO2 SPS S63 As0 As1 Aw0 Aw1 SEPW E0 E1 SEPE SEPS MI ALS ALA.
  pose proof (munch_refl [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (il_Aw L, il_Aw L + 32768)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof SEPW as SEPW0. unfold apart in SEPW.
  set (bsrc := map (Z_to_bv 8) (arr_slice src (put - copy) copy)) in *.
  assert (LSRC : Z.of_nat (length bsrc) = copy) by (subst bsrc; rewrite length_map; unfold arr_slice; rewrite arr_slice_nat_length; lia).
  pose proof GA as GA0. open_isA GA. pose proof GW as GW0. unfold iwin in GW. rewrite HB in GW.
  pose proof (av8_zlength (is_window s) 32768 ltac:(lia)) as LWIN.
  open_izs ZS.
  unfold Z_UPDATEWINDOW. carve_frame 64%nat STK.
  do 10 zs. zs. al8 (il_S L). gF. zs. gF. zs. al8 (il_As L). gF.
  do 2 zs. rewrite HB. cbn [win_addr]. zs. br_true.
  eapply (updwin_body_spec _ L s src put copy E lo b);
    [ exact FR | exact STK | unfold isA, isA_cells; exact GA | exact HB | unfold iwin; rewrite HB; exact GW | exact LW
    | exact SRC | exact Hwb | lia | exact Hws | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact SEPW0 | lia | lia | exact SEPE | exact SEPS
    | eassumption | exact MU | exact WM | reflexivity ].
Qed.

Definition PC_MALLOC : Z := 0x23708.

Definition uw_at_malloc (L : ilay) (copy E lo : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' fj,
    ms' = MS (mkR (wz PC_UW_RET) (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz 32768) a1 a2 a3 a4 a5 a6 a7
                  (wz 1) (wz (il_As L)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz PC_MALLOC) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Lemma updwin_to_malloc : forall (L : ilay) (s : inflate_state) (c : icall) (copy E lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk usegs m lo (bv_unsigned sp) -> izs m L c ->
  isA m L s -> is_window_blk s = None -> is_wbits s = 15 ->
  lo <= bv_unsigned sp - 64 -> 0x5e000 <= lo -> bv_unsigned sp <= il_S L -> il_S L + 112 < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo ->
  mem_inv usegs m ->
  il_S L mod 8 = 0 -> il_As L mod 16 = 0 ->
  evt usegs (uw_at_malloc L copy E lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (il_S L)) (wz E) (wz copy) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_UPDATEWINDOW) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros STK ZS GA HB Hwb LO1 LO2 SPS S63 As0 As1 MI ALS ALA.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  open_isA GA. open_izs ZS.
  unfold Z_UPDATEWINDOW. carve_frame 64%nat STK.
  do 10 zs. zs. al8 (il_S L). gF. zs. gF. zs. al8 (il_As L). gF.
  do 2 zs. rewrite HB. cbn [win_addr]. zs. br_false.
  zs. rewrite Hwb. zs. gF.
  do 6 zs. do 4 zs.
  apply evt_done. unfold uw_at_malloc. do 16 eexists. split; [reflexivity|].
  split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma updwin_ret_null : forall (fj : list byte) (L : ilay) (s : inflate_state) (copy E lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  isA m L s -> is_window_blk s = None ->
  lo <= bv_unsigned sp - 64 -> 0x5e000 <= lo -> bv_unsigned sp < 2^63 -> 0 < il_As L -> il_As L + 7176 <= lo ->
  mem_inv usegs m ->
  evt usegs (updwin_post L s 1 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(lo, bv_unsigned sp); (il_As L, il_As L + 168)] m)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz 0) a1 a2 a3 a4 a5 a6 a7 (wz 1) (wz (il_As L)) s4
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_RET) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros FR STK GA HB LO1 LO2 SP63 As0 As1 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (il_As L, il_As L + 168)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  open_isA GA. rewrite HB in GA. cbn [win_addr] in GA.
  unfold PC_UW_RET. zs. zs. br_true. do 9 zs. release_frame FR STK (bv_unsigned sp). zs.
  apply evt_done. unfold updwin_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [exact STK|]. split; [unfold isA, isA_cells; rewrite HB; cbn [win_addr]; exact GA|].
  unfold iwin; rewrite HB; exact I.
Qed.

Definition il_setw (L : ilay) (A : Z) : ilay := mkIL (il_S L) (il_As L) A (il_NI L) (il_NO L).
Definition s_fresh (s : inflate_state) (wb : ZProg.blk) (junk : list byte) : inflate_state :=
  iset_window (iset_window_blk s (Some wb)) (iarr_u8_of (gwb junk) 0 32768).

Lemma updwin_ret_block : forall (fj : list byte) (L : ilay) (s : inflate_state) (src : arr) (put copy E lo A : Z) (wb : ZProg.blk) (junk : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  isA m L s -> is_window_blk s = None -> rw_cells usegs m A [CB (Z.to_nat 32768) junk] ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) ->
  is_wbits s = 15 -> 0 <= copy <= 1 ->
  (is_wsize s <> 0 -> is_wsize s = 32768) -> 0 <= uw_wnext0 s < 32768 -> 0 <= uw_whave0 s <= 32768 ->
  lo <= bv_unsigned sp - 64 -> 0x5e000 <= lo -> bv_unsigned sp < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo -> 0 < A -> A + 32768 <= lo -> apart (il_As L) 7176 A 32768 ->
  0 < E - copy -> E <= lo -> (E <= A \/ A + 32768 <= E - copy) -> (E <= il_As L \/ il_As L + 7176 <= E - copy) ->
  mem_inv usegs m ->
  evt usegs (updwin_post (il_setw L A) (updw_core (s_fresh s wb junk) src put copy) 0 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                         [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (A, A + 32768)] m)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz A) a1 a2 a3 a4 a5 a6 a7 (wz 1) (wz (il_As L)) s4
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_RET) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros FR STK GA HB WJ SRC Hwb Hc Hws Hwn Hwh LO1 LO2 SP63 As0 As1 A0 A1 SEPW E0 E1 SEPE SEPS MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (A, A + 32768)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof SEPW as SEPW0. unfold apart in SEPW.
  set (bsrc := map (Z_to_bv 8) (arr_slice src (put - copy) copy)) in *.
  assert (LSRC : Z.of_nat (length bsrc) = copy) by (subst bsrc; rewrite length_map; unfold arr_slice; rewrite arr_slice_nat_length; lia).
  assert (LJ : Z.of_nat (length junk) = 32768) by (destruct WJ as [[[LL _] _] _]; cbn [cells_wf cell_wf] in LL; lia).
  apply (u8arr_of_rw_cells usegs m A (Z.to_nat 32768)) in WJ.
  open_isA GA. rewrite HB in GA. cbn [win_addr] in GA.
  unfold PC_UW_RET. zs. zs. br_false.
  rewrite <- (av8_junk junk 32768 LJ) in WJ.
  eapply (updwin_body_spec _ (il_setw L A) (s_fresh s wb junk) src put copy E lo wb);
    [ exact FR | exact STK | unfold isA, isA_cells, il_setw, s_fresh; ired; cbn [il_S il_As il_Aw win_addr cp_addr]; close_cells GA | reflexivity
    | unfold iwin, s_fresh, il_setw; ired; cbn [il_Aw]; exact WJ | unfold s_fresh; ired; unfold iarr_u8_of; apply arr_len_init
    | exact SRC | exact Hwb | lia | exact Hws | exact Hwn | exact Hwh | lia | lia | lia | exact As0 | exact As1 | exact A0 | exact A1 | exact SEPW0 | lia | lia | exact SEPE | exact SEPS
    | eassumption | exact MU | exact WM | reflexivity ].
Qed.
