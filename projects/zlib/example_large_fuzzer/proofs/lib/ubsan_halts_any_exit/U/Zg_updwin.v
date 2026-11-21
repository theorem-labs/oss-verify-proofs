(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_pure2 Z_updwin_pure Zh_kit Z_updwin Z_ukit Zg_updwin_pure Zg_updwin_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface InflateState RefUpdWin1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition PC_UW_FULL : Z := 0x21bf0.
Lemma arr_slice_nat_app : forall (src : arr) o na nb,
  arr_slice_nat src o (na + nb) = arr_slice_nat src o na ++ arr_slice_nat src (o + Z.of_nat na) nb.
Proof.
  intros src o na nb. revert o. induction na as [|na IH]; intros o.
  - cbn [arr_slice_nat Nat.add app]. f_equal. lia.
  - cbn [arr_slice_nat Nat.add app]. rewrite IH. f_equal. f_equal. f_equal. lia.
Qed.
Lemma arr_slice_app : forall (src : arr) o a b, 0 <= a -> 0 <= b ->
  arr_slice src o (a + b) = arr_slice src o a ++ arr_slice src (o + a) b.
Proof.
  intros src o a b Ha Hb. unfold arr_slice. rewrite Z2Nat.inj_add by lia. rewrite arr_slice_nat_app. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma src_suffix : forall m src put copy E n,
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) -> 0 <= n <= copy ->
  bytes_at usegs m (E - n) (map (Z_to_bv 8) (arr_slice src (put - n) n)).
Proof.
  intros m src put copy E n SRC Hn.
  replace copy with ((copy - n) + n) in SRC at 3 by lia. rewrite arr_slice_app, map_app in SRC by lia.
  apply bytes_at_app in SRC. destruct SRC as [_ SRC].
  rewrite length_map in SRC. unfold arr_slice in SRC at 1. rewrite arr_slice_nat_length in SRC.
  replace (E - copy + Z.of_nat (Z.to_nat (copy - n))) with (E - n) in SRC by lia.
  replace (put - copy + (copy - n)) with (put - n) in SRC by lia. exact SRC.
Qed.
Lemma src_prefix : forall m src put copy E n,
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) -> 0 <= n <= copy ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) n)).
Proof.
  intros m src put copy E n SRC Hn.
  replace copy with (n + (copy - n)) in SRC at 3 by lia. rewrite arr_slice_app, map_app in SRC by lia.
  apply bytes_at_app in SRC. exact (proj1 SRC).
Qed.
Lemma len_slice : forall (src : arr) o n, length (map (Z_to_bv 8) (arr_slice src o n)) = Z.to_nat n.
Proof. intros. rewrite length_map. unfold arr_slice. apply arr_slice_nat_length. Qed.
Lemma updwin_full_g : forall (fj : list byte) (L : ilay) (s : inflate_state) (src : arr) (put copy E lo : Z) (b : ZProg.blk)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a3 a4 a5 a6 a7 x18 x20 x21 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (W0 : list ivl),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  isA m L s -> is_window_blk s = Some b -> iwin m L s -> arr_len (is_window s) = 32768 ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) ->
  is_wbits s = 15 -> 0 <= copy < 2^32 -> is_wsize s = 32768 -> is_wsize s <= copy ->
  lo <= bv_unsigned sp - 64 -> 0x5f000 <= lo -> bv_unsigned sp < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo -> 0 < il_Aw L -> il_Aw L + 32768 <= lo -> apart (il_As L) 7176 (il_Aw L) 32768 ->
  0 < E - copy -> E <= lo -> (E <= il_Aw L \/ il_Aw L + 32768 <= E - copy) ->
  mem_inv usegs m ->
  munch W0 m0 m -> wmono usegs m0 m ->
  W0 = [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (il_Aw L, il_Aw L + 32768)] ->
  evt usegs (updwin_post L (updw_core s src put copy) 0 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W0 m0)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz (il_Aw L)) a1 (wz (is_wsize s)) a3 a4 a5 a6 a7 x18 (wz (il_As L)) x20
             x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_FULL) fc None m (seg_rom usegs)).
Proof.
  intros until W0. intros FR STK GA HB GW LW SRC Hwb Hc Hws Hge LO1 LO2 SP63 As0 As1 Aw0 Aw1 SEPW E0 E1 SEPE MI MU WM EW.
  rewrite (updw_full s src put copy Hws) by lia.
  unfold iwin in GW. rewrite HB in GW.
  pose proof (av8_zlength (is_window s) 32768 ltac:(lia)) as LWIN.
  unfold apart in SEPW. subst W0.
  pose proof (src_suffix m src put copy E (is_wsize s) SRC ltac:(lia)) as SRCW.
  pose proof (rw_cells_of_u8arr usegs _ _ _ GW) as WC.
  replace (length (av8 (is_window s) 32768)) with (Z.to_nat (is_wsize s)) in WC by (rewrite av8_length; lia).
  clear GW. open_isA GA.
  unfold PC_UW_FULL. do 2 zs. rewrite ?land_u32_small by lia. zs. br_false.
  zs. zs.
  replace (E - is_wsize s) with (E + - is_wsize s) in SRCW by lia.
  call (memcpy_Z (il_Aw L) (E + - is_wsize s) (is_wsize s)).
  1:{ exact SRCW. } 1:{ apply len_slice. } 1:{ exact WC. } 1:{ lia. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  try clear SRC; try clear SRCW; try clear WC. rename PC into GW.
  do 4 zs.
  do 9 zs. release_frame FR STK (bv_unsigned sp). zs.
  apply (u8arr_of_rw_cells usegs) in GW. rewrite Hws in GW. rewrite Hws in GA.
  assert (EBL : map (Z_to_bv 8) (arr_slice src (put - 32768) 32768) = av8 (arr_blit (is_window s) 0 src (put - 32768) 32768) 32768).
  { rewrite <- (av8_blit (is_window s) src 0 (put - 32768) 32768 32768) by lia. change (Z.to_nat 0) with 0%nat.
    rewrite firstn_O, app_nil_l, Nat.add_0_l. rewrite skipn_all2 by (rewrite av8_length; lia). rewrite app_nil_r. reflexivity. }
  rewrite EBL in GW. clear EBL.
  apply evt_done. unfold updwin_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [exact STK|]. split; [unfold isA, isA_cells, uw_set; ired; rewrite ?Z.add_0_r; close_cells GA|].
  unfold iwin, uw_set; ired; rewrite HB; exact GW.
Qed.
Lemma updwin_app_g : forall (fj : list byte) (L : ilay) (s : inflate_state) (src : arr) (put copy E lo : Z) (b : ZProg.blk)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a3 a4 a5 a6 a7 x18 x20 x21 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (W0 : list ivl),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  isA m L s -> is_window_blk s = Some b -> iwin m L s -> arr_len (is_window s) = 32768 ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) ->
  is_wbits s = 15 -> 0 <= copy < is_wsize s -> copy <= is_wsize s - is_wnext s ->
  is_wsize s = 32768 -> 0 <= is_wnext s < 32768 -> 0 <= is_whave s <= 32768 ->
  lo <= bv_unsigned sp - 64 -> 0x5f000 <= lo -> bv_unsigned sp < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo -> 0 < il_Aw L -> il_Aw L + 32768 <= lo -> apart (il_As L) 7176 (il_Aw L) 32768 ->
  0 < E - copy -> E <= lo -> (E <= il_Aw L \/ il_Aw L + 32768 <= E - copy) ->
  mem_inv usegs m ->
  munch W0 m0 m -> wmono usegs m0 m ->
  W0 = [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (il_Aw L, il_Aw L + 32768)] ->
  evt usegs (updwin_post L (updw_core s src put copy) 0 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W0 m0)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz (il_Aw L)) a1 (wz (is_wsize s)) a3 a4 a5 a6 a7 x18 (wz (il_As L)) x20
             x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_COPY) fc None m (seg_rom usegs)).
Proof.
  intros until W0. intros FR STK GA HB GW LW SRC Hwb Hc Hd Hws Hwn Hwh LO1 LO2 SP63 As0 As1 Aw0 Aw1 SEPW E0 E1 SEPE MI MU WM EW.
  rewrite (updw_app s src put copy Hws Hwn Hwh) by lia.
  unfold iwin in GW. rewrite HB in GW.
  pose proof (av8_zlength (is_window s) 32768 ltac:(lia)) as LWIN.
  unfold apart in SEPW. subst W0.
  assert (EBL : firstn (Z.to_nat (is_wnext s)) (av8 (is_window s) 32768) ++ map (Z_to_bv 8) (arr_slice src (put - copy) copy)
                ++ skipn (Z.to_nat (is_wnext s) + Z.to_nat copy) (av8 (is_window s) 32768)
                = av8 (arr_blit (is_window s) (is_wnext s) src (put - copy) copy) 32768) by (apply av8_blit; lia).
  destruct (u8arr_split3 m _ _ (Z.to_nat (is_wnext s)) (Z.to_nat copy) GW ltac:(rewrite av8_length; lia)) as (W1 & WC & W3).
  replace (Z.of_nat (Z.to_nat (is_wnext s))) with (is_wnext s) in WC by lia.
  replace (Z.of_nat (Z.to_nat (is_wnext s))) with (is_wnext s) in W3 by lia. replace (Z.of_nat (Z.to_nat copy)) with copy in W3 by lia.
  assert (LW1 : Z.of_nat (length (firstn (Z.to_nat (is_wnext s)) (av8 (is_window s) 32768))) = is_wnext s) by (rewrite length_firstn, av8_length; lia).
  assert (LW3 : Z.of_nat (length (skipn (Z.to_nat (is_wnext s) + Z.to_nat copy) (av8 (is_window s) 32768))) = 32768 - is_wnext s - copy) by (rewrite length_skipn, av8_length; lia).
  pose proof (len_slice src (put - copy) copy) as LSRC.
  clear GW. open_isA GA.
  set (bsrc := map (Z_to_bv 8) (arr_slice src (put - copy) copy)) in *.
  set (bpre := firstn (Z.to_nat (is_wnext s)) (av8 (is_window s) 32768)) in *.
  set (bsuf := skipn (Z.to_nat (is_wnext s) + Z.to_nat copy) (av8 (is_window s) 32768)) in *.
  unfold PC_UW_COPY. do 3 zs. zs. br_false. zs.
  zs. rewrite zb_lxor_ones by lia. zs. br_false.
  do 2 zs. rewrite ?land_u32_small by lia. zs. br_false.
  do 4 zs. gXsub.
  do 4 zs. rewrite ?land_u32_small by lia. zs.
  call (memcpy_Z (il_Aw L + is_wnext s) (E - copy) copy).
  1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact WC. } 1:{ lia. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  assert (LEN1 : length bpre = Z.to_nat (is_wnext s)) by lia.
  pose proof (u8arr_join3k _ (il_Aw L) _ _ _ (Z.to_nat (is_wnext s)) (Z.to_nat copy) LEN1 W1
                ltac:(replace (Z.of_nat (Z.to_nat (is_wnext s))) with (is_wnext s) by lia; exact PC)
                ltac:(replace (Z.of_nat (Z.to_nat (is_wnext s))) with (is_wnext s) by lia; replace (Z.of_nat (Z.to_nat copy)) with copy by lia; exact W3)) as GW.
  rewrite EBL in GW. clear W1 W3 PC EBL LW1 LW3 LEN1. try clear POST. try clear SRC.
  pose proof (av8_zlength (arr_blit (is_window s) (is_wnext s) src (put - copy) copy) 32768 ltac:(lia)) as LWIN2.
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
Lemma updwin_wrap_g : forall (fj : list byte) (L : ilay) (s : inflate_state) (src : arr) (put copy E lo : Z) (b : ZProg.blk)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a3 a4 a5 a6 a7 x18 x20 x21 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (W0 : list ivl),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  isA m L s -> is_window_blk s = Some b -> iwin m L s -> arr_len (is_window s) = 32768 ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) ->
  is_wbits s = 15 -> 0 <= copy < is_wsize s -> is_wsize s - is_wnext s < copy ->
  is_wsize s = 32768 -> 0 <= is_wnext s < 32768 -> 0 <= is_whave s <= 32768 ->
  lo <= bv_unsigned sp - 64 -> 0x5f000 <= lo -> bv_unsigned sp < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo -> 0 < il_Aw L -> il_Aw L + 32768 <= lo -> apart (il_As L) 7176 (il_Aw L) 32768 ->
  0 < E - copy -> E <= lo -> (E <= il_Aw L \/ il_Aw L + 32768 <= E - copy) ->
  mem_inv usegs m ->
  munch W0 m0 m -> wmono usegs m0 m ->
  W0 = [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (il_Aw L, il_Aw L + 32768)] ->
  evt usegs (updwin_post L (updw_core s src put copy) 0 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W0 m0)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz (il_Aw L)) a1 (wz (is_wsize s)) a3 a4 a5 a6 a7 x18 (wz (il_As L)) x20
             x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_COPY) fc None m (seg_rom usegs)).
Proof.
  intros until W0. intros FR STK GA HB GW LW SRC Hwb Hc Hd Hws Hwn Hwh LO1 LO2 SP63 As0 As1 Aw0 Aw1 SEPW E0 E1 SEPE MI MU WM EW.
  rewrite (updw_wrap s src put copy Hws Hwn) by lia.
  unfold iwin in GW. rewrite HB in GW.
  pose proof (av8_zlength (is_window s) 32768 ltac:(lia)) as LWIN.
  unfold apart in SEPW. subst W0.
  assert (Hn2 : 0 < copy - (is_wsize s - is_wnext s) < is_wnext s) by lia.
  pose proof (src_prefix m src put copy E (is_wsize s - is_wnext s) SRC ltac:(lia)) as SRC1.
  pose proof (src_suffix m src put copy E (copy - (is_wsize s - is_wnext s)) SRC ltac:(lia)) as SRC2.
  pose proof (len_slice src (put - copy) (is_wsize s - is_wnext s)) as LS1.
  pose proof (len_slice src (put - (copy - (is_wsize s - is_wnext s))) (copy - (is_wsize s - is_wnext s))) as LS2.
  assert (LS2z : Z.of_nat (length (map (Z_to_bv 8) (arr_slice src (put - (copy - (is_wsize s - is_wnext s))) (copy - (is_wsize s - is_wnext s))))) = copy - (is_wsize s - is_wnext s)) by (rewrite LS2; lia).
  clear SRC.
  destruct (u8arr_split3 m _ _ (Z.to_nat (is_wnext s)) (Z.to_nat (is_wsize s - is_wnext s)) GW ltac:(rewrite av8_length; lia)) as (W1 & WC & W3). clear W3.
  replace (Z.of_nat (Z.to_nat (is_wnext s))) with (is_wnext s) in WC by lia.
  assert (LW1 : Z.of_nat (length (firstn (Z.to_nat (is_wnext s)) (av8 (is_window s) 32768))) = is_wnext s) by (rewrite length_firstn, av8_length; lia).
  clear GW. open_isA GA.
  set (b1 := map (Z_to_bv 8) (arr_slice src (put - copy) (is_wsize s - is_wnext s))) in *.
  set (b2 := map (Z_to_bv 8) (arr_slice src (put - (copy - (is_wsize s - is_wnext s))) (copy - (is_wsize s - is_wnext s)))) in *.
  set (bpre := firstn (Z.to_nat (is_wnext s)) (av8 (is_window s) 32768)) in *.
  unfold PC_UW_COPY. do 3 zs. zs. br_true.
  zs. rewrite zb_lxor_ones by lia. zs. br_false.
  do 2 zs. rewrite ?land_u32_small by lia. zs. br_false.
  do 4 zs. gXsub.
  do 4 zs. rewrite ?land_u32_small by lia. zs.
  call (memcpy_Z (il_Aw L + is_wnext s) (E - copy) (is_wsize s - is_wnext s)).
  1:{ exact SRC1. } 1:{ exact LS1. } 1:{ exact WC. } 1:{ lia. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  rename PC into PC1. try clear POST. clear SRC1.
  zs. br_false. do 3 zs. rewrite ?land_u32_small by lia. zs. br_false.
  do 3 zs. first [gXsub | rewrite xor_guard1 by lia; zs; br_false].
  zs. rewrite HB. cbn [win_addr]. zs. zs.
  lazymatch type of W1 with u8arr _ ?mx _ _ =>
    destruct (u8arr_split3 mx _ _ 0%nat (Z.to_nat (copy - (is_wsize s - is_wnext s))) W1 ltac:(lia)) as (W1a & W2C & W1c) end.
  clear W1a. change (Z.of_nat 0) with 0 in W2C, W1c. rewrite Z.add_0_r in W2C, W1c. rewrite skipn_O in W2C. rewrite Nat.add_0_l in W1c.
  replace (Z.of_nat (Z.to_nat (copy - (is_wsize s - is_wnext s)))) with (copy - (is_wsize s - is_wnext s)) in W1c by lia.
  replace (E - (copy - (is_wsize s - is_wnext s))) with (E + - (copy - (is_wsize s - is_wnext s))) in SRC2 by lia.
  call (memcpy_Z (il_Aw L) (E + - (copy - (is_wsize s - is_wnext s))) (copy - (is_wsize s - is_wnext s))).
  1:{ exact SRC2. } 1:{ exact LS2. } 1:{ exact W2C. } 1:{ lia. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  rename PC into PC2. try clear POST. clear SRC2.
  assert (LEN1 : length bpre = Z.to_nat (is_wnext s)) by lia.
  apply (u8arr_of_rw_cells usegs) in PC1. apply (u8arr_of_rw_cells usegs) in PC2.
  lazymatch type of PC2 with u8arr _ ?mx _ _ =>
    assert (GW : u8arr usegs mx (il_Aw L) (b2 ++ skipn (Z.to_nat (copy - (is_wsize s - is_wnext s))) bpre ++ b1)) end.
  { apply (proj2 (u8arr_app _ _ _ _)). split; [exact PC2|]. rewrite LS2.
    replace (Z.of_nat (Z.to_nat (copy - (is_wsize s - is_wnext s)))) with (copy - (is_wsize s - is_wnext s)) by lia.
    apply (proj2 (u8arr_app _ _ _ _)). split; [exact W1c|]. rewrite length_skipn, LEN1.
    replace (il_Aw L + (copy - (is_wsize s - is_wnext s)) + Z.of_nat (Z.to_nat (is_wnext s) - Z.to_nat (copy - (is_wsize s - is_wnext s))))
      with (il_Aw L + is_wnext s) by lia. exact PC1. }
  clear PC1 PC2 W1c.
  assert (EBL : b2 ++ skipn (Z.to_nat (copy - (is_wsize s - is_wnext s))) bpre ++ b1
                = av8 (arr_blit (arr_blit (is_window s) (is_wnext s) src (put - copy) (is_wsize s - is_wnext s)) 0 src
                               (put - (copy - (is_wsize s - is_wnext s))) (copy - (is_wsize s - is_wnext s))) 32768).
  { subst b1 b2 bpre. apply av8_blit2; lia. }
  rewrite EBL in GW. clear EBL LS1 LS2 LS2z LW1 LEN1. subst b1 b2 bpre. rewrite Hws in GW.
  pose proof (av8_zlength (arr_blit (arr_blit (is_window s) (is_wnext s) src (put - copy) (32768 - is_wnext s)) 0 src
                               (put - (copy - (32768 - is_wnext s))) (copy - (32768 - is_wnext s))) 32768 ltac:(lia)) as LWIN2.
  do 4 zs. zs. do 9 zs. release_frame FR STK (bv_unsigned sp). zs. rewrite Hws in GA.
  apply evt_done. unfold updwin_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [exact STK|]. split; [unfold isA, isA_cells, uw_set; ired; rewrite ?Z.add_0_r; close_cells GA|].
  unfold iwin, uw_set; ired; rewrite HB; exact GW.
Qed.
Lemma updwin_copy_g : forall (fj : list byte) (L : ilay) (s : inflate_state) (src : arr) (put copy E lo : Z) (b : ZProg.blk)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a3 a4 a5 a6 a7 x18 x20 x21 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (W0 : list ivl),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  isA m L s -> is_window_blk s = Some b -> iwin m L s -> arr_len (is_window s) = 32768 ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) ->
  is_wbits s = 15 -> 0 <= copy < is_wsize s ->
  is_wsize s = 32768 -> 0 <= is_wnext s < 32768 -> 0 <= is_whave s <= 32768 ->
  lo <= bv_unsigned sp - 64 -> 0x5f000 <= lo -> bv_unsigned sp < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo -> 0 < il_Aw L -> il_Aw L + 32768 <= lo -> apart (il_As L) 7176 (il_Aw L) 32768 ->
  0 < E - copy -> E <= lo -> (E <= il_Aw L \/ il_Aw L + 32768 <= E - copy) ->
  mem_inv usegs m ->
  munch W0 m0 m -> wmono usegs m0 m ->
  W0 = [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (il_Aw L, il_Aw L + 32768)] ->
  evt usegs (updwin_post L (updw_core s src put copy) 0 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W0 m0)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz (il_Aw L)) a1 (wz (is_wsize s)) a3 a4 a5 a6 a7 x18 (wz (il_As L)) x20
             x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_COPY) fc None m (seg_rom usegs)).
Proof.
  intros until W0. intros FR STK GA HB GW LW SRC Hwb Hc Hws Hwn Hwh LO1 LO2 SP63 As0 As1 Aw0 Aw1 SEPW E0 E1 SEPE MI MU WM EW.
  destruct (Z.le_gt_cases copy (is_wsize s - is_wnext s)) as [Hd|Hd].
  - eapply (updwin_app_g fj L s src put copy E lo b); eassumption || lia.
  - eapply (updwin_wrap_g fj L s src put copy E lo b); eassumption || lia.
Qed.
Lemma updwin_body_g : forall (fj : list byte) (L : ilay) (s : inflate_state) (src : arr) (put copy E lo : Z) (b : ZProg.blk)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (W0 : list ivl),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  isA m L s -> is_window_blk s = Some b -> iwin m L s -> arr_len (is_window s) = 32768 ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) ->
  is_wbits s = 15 -> 0 <= copy < 2^32 ->
  (is_wsize s <> 0 -> is_wsize s = 32768) -> 0 <= uw_wnext0 s < 32768 -> 0 <= uw_whave0 s <= 32768 ->
  lo <= bv_unsigned sp - 64 -> 0x5f000 <= lo -> bv_unsigned sp < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo -> 0 < il_Aw L -> il_Aw L + 32768 <= lo -> apart (il_As L) 7176 (il_Aw L) 32768 ->
  0 < E - copy -> E <= lo -> (E <= il_Aw L \/ il_Aw L + 32768 <= E - copy) -> (E <= il_As L \/ il_As L + 7176 <= E - copy) ->
  mem_inv usegs m ->
  munch W0 m0 m -> wmono usegs m0 m ->
  W0 = [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (il_Aw L, il_Aw L + 32768)] ->
  evt usegs (updwin_post L (updw_core s src put copy) 0 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W0 m0)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz (il_Aw L)) a1 a2 a3 a4 a5 a6 a7 x18 (wz (il_As L)) x20
             x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_BODY) fc None m (seg_rom usegs)).
Proof.
  intros until W0. intros FR STK GA HB GW LW SRC Hwb Hc Hws Hwn Hwh LO1 LO2 SP63 As0 As1 Aw0 Aw1 SEPW E0 E1 SEPE SEPS MI MU WM EW.
  rewrite (updw_core_sA s src put copy Hwb).
  pose proof (len_slice src (put - copy) copy) as LSRC.
  assert (LSRCz : Z.of_nat (length (map (Z_to_bv 8) (arr_slice src (put - copy) copy))) = copy) by (rewrite LSRC; lia).
  destruct (Z.eq_dec (is_wsize s) 0) as [W0z|W0n].
  -
    assert (ESA : sA s = iset_whave (iset_wnext (iset_wsize s 32768) 0) 0).
    { unfold sA. rewrite W0z, Hwb. reflexivity. }
    pose proof SEPW as SEPW0. unfold apart in SEPW. pose proof EW as EW0. subst W0.
    pose proof GA as GA0. open_isA GA. unfold iwin in GW. rewrite HB in GW.
    pose proof (av8_zlength (is_window s) 32768 ltac:(lia)) as LWIN.
    unfold PC_UW_BODY. zs. rewrite W0z. zs. br_true. zs. rewrite Hwb. zs. zs. br_false. do 3 zs.
    zs. zs.
    rewrite ESA.
    zs. br_cases K.
    +
      eapply (updwin_copy_g fj L (iset_whave (iset_wnext (iset_wsize s 32768) 0) 0) src put copy E lo b);
        [ exact FR | exact STK | unfold isA, isA_cells; ired; close_cells GA | exact HB | unfold iwin; ired; rewrite HB; exact GW | exact LW
        | exact SRC | exact Hwb | cbn; lia | reflexivity | cbn; lia | cbn; lia | lia | lia | lia | lia | lia | lia | lia | exact SEPW0 | lia | lia | exact SEPE
        | eassumption | exact MU | exact WM | reflexivity ].
    +
      eapply (updwin_full_g fj L (iset_whave (iset_wnext (iset_wsize s 32768) 0) 0) src put copy E lo b);
        [ exact FR | exact STK | unfold isA, isA_cells; ired; close_cells GA | exact HB | unfold iwin; ired; rewrite HB; exact GW | exact LW
        | exact SRC | exact Hwb | lia | reflexivity | cbn; lia | lia | lia | lia | lia | lia | lia | lia | exact SEPW0 | lia | lia | exact SEPE
        | eassumption | exact MU | exact WM | reflexivity ].
  -
    specialize (Hws W0n).
    assert (ESA : sA s = s) by (unfold sA; replace (is_wsize s =? 0) with false by (symmetry; apply Z.eqb_neq; exact W0n); reflexivity).
    rewrite ESA. unfold uw_wnext0, uw_whave0 in Hwn, Hwh. replace (is_wsize s =? 0) with false in Hwn, Hwh by (symmetry; apply Z.eqb_neq; exact W0n).
    pose proof GA as GA0. open_isA GA.
    unfold PC_UW_BODY. zs. zs. br_false. zs. br_cases K.
    +
      eapply (updwin_full_g fj L s src put copy E lo b);
        [ exact FR | exact STK | exact GA0 | exact HB | exact GW | exact LW
        | exact SRC | exact Hwb | lia | exact Hws | lia | lia | lia | lia | lia | lia | lia | lia | exact SEPW | lia | lia | exact SEPE
        | eassumption | exact MU | exact WM | exact EW ].
    + eapply (updwin_copy_g fj L s src put copy E lo b);
        [ exact FR | exact STK | exact GA0 | exact HB | exact GW | exact LW
        | exact SRC | exact Hwb | lia | exact Hws | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact SEPW | lia | lia | exact SEPE
        | eassumption | exact MU | exact WM | exact EW ].
Qed.
Lemma updwin_have_g : updwin_have_stmt.
Proof.
  unfold updwin_have_stmt.
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
  eapply (updwin_body_g _ L s src put copy E lo b);
    [ exact FR | exact STK | unfold isA, isA_cells; exact GA | exact HB | unfold iwin; rewrite HB; exact GW | exact LW
    | exact SRC | exact Hwb | lia | exact Hws | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact SEPW0 | lia | lia | exact SEPE | exact SEPS
    | eassumption | exact MU | exact WM | reflexivity ].
Qed.
Lemma updwin_ret_block_g : updwin_ret_block_stmt.
Proof.
  unfold updwin_ret_block_stmt.
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
  eapply (updwin_body_g fj (il_setw L A) (s_fresh s wb junk) src put copy E lo wb);
    [ exact FR | exact STK | unfold isA, isA_cells, il_setw, s_fresh; ired; cbn [il_S il_As il_Aw win_addr cp_addr]; close_cells GA | reflexivity
    | unfold iwin, s_fresh, il_setw; ired; cbn [il_Aw]; exact WJ | unfold s_fresh; ired; unfold iarr_u8_of; apply arr_len_init
    | exact SRC | exact Hwb | lia | exact Hws | exact Hwn | exact Hwh | lia | lia | lia | exact As0 | exact As1 | exact A0 | exact A1 | exact SEPW0 | lia | lia | exact SEPE | exact SEPS
    | eassumption | exact MU | exact WM | reflexivity ].
Qed.
