(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_scan1 Z_tr_cb3 F_memset
     Z_tr_bt1 Z_tr_bt2 Z_tr_bt6 Z_tr_bt10 Z_tr_bt12 Z_tr_bt13 Z_tr_bt14 Z_tr_bt15 Z_tr_bt16 Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma blc_zero : forall BC, arr_len BC = 16 -> u16s (av16 (arr_fill BC 0 16 0) 16) = repeat (Z_to_bv 8 0) 32.
Proof.
  intros BC LBC. unfold av16. rewrite zseq_16. cbn [map]. rewrite !arr_get_fill. unfold arr_inb. rewrite !LBC. cbn. reflexivity.
Qed.
Lemma blc_zero_range : forall BC i, arr_len BC = 16 -> 0 <= i < 16 -> 0 <= arr_get (arr_fill BC 0 16 0) i < 65536.
Proof.
  intros BC i LBC Hi. rewrite arr_get_fill. unfold arr_inb. rewrite LBC.
  replace ((0 <=? i) && (i <? 0 + Z.max 0 16) && ((0 <=? i) && (i <? 16))) with true; [lia|].
  symmetry. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
Qed.

Definition gb_tail (t : tree_id) (mc : Z) (R1 : deflate_state * Z) : deflate_state :=
  let (X10, ovf) := R1 in
  if ovf =? 0 then X10
  else gen_bitlen_loop3 (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) t mc (sd_max_length t) HEAP_SIZE.
Lemma gb_tail_0 : forall t mc X, gb_tail t mc (X, 0) = X.
Proof. intros. reflexivity. Qed.
Lemma gb_tail_nz : forall t mc X ovf, ovf <> 0 ->
  gb_tail t mc (X, ovf) = gen_bitlen_loop3 (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X (sd_max_length t) ovf) t mc (sd_max_length t) 573.
Proof. intros t mc X ovf H. unfold gb_tail. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma gen_bitlen_flat : forall s t FC DL HP HL hm DP BC OL SL mc,
  gen_bitlen (bt_upd s t FC DL HP HL hm DP BC OL SL mc) t
  = gb_tail t mc (gen_bitlen_loop1 573 (bt_upd s t FC (arr_set DL (arr_get HP hm) (wrap16 0)) HP HL hm DP (arr_fill BC 0 16 0) OL SL mc) t mc
                    (sd_extra_base t) (sd_max_length t) (hm + 1) 0).
Proof.
  intros. unfold gen_bitlen, gb_tail. rewrite bt_max_code, bt_bl_count, bt_set_bl_count, bt_heap_max, bt_heap_get, bt_set_Len, bt_heap_max.
  change (MAX_BITS + 1) with 16.
  destruct (gen_bitlen_loop1 573 _ t mc _ _ (hm + 1) 0) as [X10 ovf]. reflexivity.
Qed.

Notation Wpre L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 2976, dl_As L + 5308)] (only parsing).

Definition gb_pre_post (L : dlay) (T N hm dsc SD mc stp xp : Z) (t : tree_id) (FC DL HP BC : arr) (hh : list byte)
    (ra sp gp tp s6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (gbR L T (hm + 1) 0 (sd_extra_base t) mc (sd_max_length t) stp xp (wz 0x1c160) sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6) F (wz 0x1c1d4) fc None m' (seg_rom psegs)
    /\ munch (Wpre L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC (arr_set DL (arr_get HP 1) (wrap16 0)) N))
    /\ u32arr psegs m' (dl_As L + 3008) (av32 (arr_set HP hm (arr_get HP 1)) 573)
    /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 (arr_fill BC 0 16 0) 16))
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)]
    /\ rw_cells psegs m' dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz SD)].

Lemma gb_pre : forall (L : dlay) (T N hm node dsc SD mc stp xp : Z) (t : tree_id) (FC DL HP BC : arr) (hh : list byte)
    (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz 1); C4 (wz (hm + 1))] ->
  rw_cells psegs m dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz SD)] ->
  rw_cells psegs m SD [C8 (wz stp); C8 (wz xp); C4 (wz (sd_extra_base t)); C4 (wz (sd_elems t)); C4 (wz (sd_max_length t))] ->
  mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  0 <= hm <= 570 -> 0 <= arr_get HP 1 < N -> -1 <= mc < N -> dsc = dl_As L + bt_desc t -> 0x10000 <= SD -> SD + 32 <= 0x5c000 -> 0 <= stp < 2^63 -> 0 <= xp < 2^63 ->
  evt psegs (gb_pre_post L T N hm dsc SD mc stp xp t FC DL HP BC hh ra sp gp tp (wz (dl_As L + 3008)) F fc m)
      (MS (l4R L T 1 node dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c118) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA BLC GC Gdsc Gsd MI LAY RT1 RT2 RN LFC LDL LHP LBC Rhm Rh1 Rmc Edsc RSD1 RSD2 Rstp Rxp.
  pose proof (munch_refl (Wpre L T N) m) as MU. pose proof (wmono_refl psegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (Bs : dl_As L + 5968 <= 0x10000 \/ 0x5c000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & Bs); exact Bs).
  assert (Rdsc : 2904 <= bt_desc t <= 2952) by (destruct t; cbn [bt_desc]; lia).
  assert (RE : sd_extra_base t <= 257 /\ 0 <= sd_extra_base t /\ 19 <= sd_elems t <= 286 /\ 7 <= sd_max_length t <= 15)
    by (destruct t; cbn [sd_extra_base sd_elems sd_max_length]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; lia).
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  pose proof (u32arr_read psegs m _ (av32 HP 573) 1 _ (wa (dl_As L + 2976 + 36)) HPA (av32_nth HP 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD1.
  unfold l4R. zs2. zs2. zs2. zs2. shl_norm. zstep. zs2. zs2.
  h32_store HPA HP 573 (dl_As L + 3008) hm (arr_get HP 1) ltac:(reflexivity).
  zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. clear Gsd.
  zstep.
  apply rw_cells_of_u8arr in BLC. change (length (u16s (av16 BC 16))) with (Z.to_nat 32) in BLC.
  call memset_callZ.
  1:{ exact BLC. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  match goal with H : rw_cells psegs ?mm (dl_As L + 2976) [CB _ _] |- _ =>
    change (Z.to_nat 32) with 32%nat in H; change (0 mod 256) with 0 in H; apply (u8arr_of_rw_cells psegs) in H; rewrite <- (blc_zero BC LBC) in H; rename H into BLC0 end.
  pose proof (av16_zlength (arr_fill BC 0 16 0) 16 ltac:(lia)) as L16z.
  zs2. zs2. shl_norm. zs2.
  match goal with HA : u32arr psegs ?mm (dl_As L + 3008) (av32 ?hp 573) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read psegs mm _ (av32 hp 573) hm _ (wa (dl_As L + 3008 + hm * 4)) HA (av32_nth hp 573 hm ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDh;
    rewrite arr_get_set_same in RDh by lia end.
  zs2. zs2. shl_norm. zs2.
  ct_store_dl ARR FC DL N T (arr_get HP 1) (wrap16 0) ltac:(reflexivity).
  zs2. zs2. zstep. br_false.
  zs2. zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zs2. zs2. zs2. zs2. zstep.
  reg_as (hm + 2) (hm + 1 + 1). reg_as (hm * 4 + (dl_As L + 2976) + 36) (dl_As L + 3008 + 4 * (hm + 1)).
  apply evt_done. unfold gb_pre_post, gbR. do 10 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [exact ARR|]. split; [eassumption|]. split; [exact BLC0|]. split; [eassumption| eassumption].
Qed.

Definition gb_main_post (L : dlay) (s : deflate_state) (t : tree_id) (T N hm mc stp xp : Z) (FC HP : arr) (HL : Z) (DP : arr) (R : deflate_state)
    (ra sp gp tp s6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s5x s9x t3 t4 t5 t6 DL' BC' OL' SL' g0 g1 g2 g3 g4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1x a0 a1 a2 a3 a4 a5 a6 a7 (wz T) (wz mc) (wz (dl_As L + 5300)) s5x s6 (wz T) (wz mc) s9x (wz stp) (wz xp) t3 t4 t5 t6)
             F (wz 0x1c378) fc None m' (seg_rom psegs)
    /\ munch (Wgb L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ R = bt_upd s t FC DL' HP HL hm DP BC' OL' SL' mc
    /\ arr_len DL' = N /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536) /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536)
    /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64.

Lemma gb_main : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N hm mc stp xp OL SL : Z) (FC DL HP : arr) (HL : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R1 : deflate_state * Z) (R : deflate_state)
    (ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> rw_cells psegs m (bv_unsigned sp) [C8 (wz (dl_As L + 2047))] ->
  mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp ->
  0 <= hm <= 570 -> -1 <= mc < sd_elems t -> (forall k, hm + 1 <= k < 573 -> 0 <= arr_get HP k < N) ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 144 < 2^63 ->
  R1 = gen_bitlen_loop1 573 (bt_upd s t FC DL HP HL hm DP BC OL SL mc) t mc (sd_extra_base t) (sd_max_length t) (hm + 1) 0 ->
  gb1_ok t mc 573 (bt_upd s t FC DL HP HL hm DP BC OL SL mc) (hm + 1) 0 ->
  (forall X10 ovf, R1 = (X10, ovf) -> ovf <> 0 ->
     gb2_ok (sd_max_length t) 573 X10 ovf /\ gb3_ok t mc (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) (sd_max_length t) 573) ->
  R = gb_tail t mc R1 ->
  evt psegs (gb_main_post L s t T N hm mc stp xp FC HP HL DP R ra sp gp tp s6 F fc m)
      (MS (gbR L T (hm + 1) 0 (sd_extra_base t) mc (sd_max_length t) stp xp ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6) F (wz 0x1c1d4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA BLC GD F0 MI LAY RT1 RT2 EN LFC LDL LHP LBC XV SV Rhm Rmc RHP RBC RDL RFC ROL RSL SEP RSP ER1 OK1 OK23 ER.
  pose proof (munch_refl (Wgb L T N) m) as MU. pose proof (wmono_refl psegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (RE : sd_extra_base t <= 257 /\ 0 <= sd_extra_base t /\ 19 <= sd_elems t <= 286 /\ 7 <= sd_max_length t <= 15 /\ N = 2 * sd_elems t + 1)
    by (subst N; destruct t; cbn [sd_extra_base sd_elems sd_max_length tsize]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; lia).
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  call (gb1_loop 573 L s t T N (hm + 1) 0 mc stp xp OL SL FC DL HP HL hm DP BC h0 h1 h2 h3 h4 R1 m).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact BLC. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact EN. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LBC. } 1:{ exact XV. } 1:{ exact SV. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact RHP. } 1:{ exact RBC. } 1:{ exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. } 1:{ exact RSL. }
  1:{ exact ER1. } 1:{ exact OK1. }
  match goal with H : R1 = (bt_upd _ _ _ ?dl' _ _ _ _ ?bc' ?ol' ?sl' _, ?ovf') |- _ => rename H into ER1'; clear ER1 end.
  unfold gbR. zstep. br_cases K.
  -
    lazymatch type of ER1' with R1 = (?X, ?o) => rewrite ER1' in ER; replace o with 0 in ER by lia; rewrite gb_tail_0 in ER end.
    apply evt_done. unfold gb_main_post. do 18 eexists.
    match goal with HT : u8arr psegs ?mm T (u16s (avct FC ?dl' N)), HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                     HG : rw_cells psegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' ?sl' ?g0 ?g1 ?g2 ?g3 ?g4) |- _ =>
      exists dl', bc', ol', sl', g0, g1, g2, g3, g4; eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HB|]; split; [exact HG|];
      split; [exact ER|] end.
    repeat (split; [assumption|]). assumption.
  -
    lazymatch type of ER1' with R1 = (?X, ?o) => destruct (OK23 X o ER1' ltac:(lia)) as [OK2 OK3]; rewrite ER1' in ER; rewrite (gb_tail_nz t mc X o) in ER by lia end.
    zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zs2.
    rewrite lor_hi32 by lia. reg_as (sd_max_length t * 4294967296 + 4294967295 + 1) ((sd_max_length t + 1) * 4294967296).
    reg_as (dl_As L + (sd_max_length t * 2 + 2976)) (dl_As L + 2976 + sd_max_length t * 2).
    lazymatch type of ER1' with R1 = (?X, ?o) => name_term R2 ER2 (gen_bitlen_loop2 573 X (sd_max_length t) o) end.
    match goal with HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)), HT : u8arr psegs ?mm T (u16s (avct FC ?dl' N)) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'; pose proof (avct_zlength FC dl' N ltac:(lia)) as LCT' end.
    lazymatch type of ER1' with R1 = (bt_upd _ _ _ ?dl' _ _ _ _ ?bc' ?ol' ?sl' _, ?o) =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (gl2_loop 573 L s t T o mc (sd_max_length t) FC dl' HP HL hm DP bc' ol' sl' R2 mm) end end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ assumption. } 1:{ assumption. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ER2. } 1:{ exact OK2. }
    match goal with H : R2 = bt_upd _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite H in ER, OK3; clear H ER2 end.

    unfold gl2R. zstep. br_false. zs2. zs2. reg_as (dl_As L + 2047 + 957) (dl_As L + 3004). zs2. zstep.
    match goal with HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'' end.
    lazymatch type of ER1' with R1 = (bt_upd _ _ _ ?dl' _ _ _ _ _ ?ol' ?sl' _, _) =>
    lazymatch goal with HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)), HG : rw_cells psegs ?mm' (dl_As L + 5881) (bD_cells L s _ _ ?g0 ?g1 ?g2 ?g3 ?g4)
      |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (g3_loop (Z.to_nat (sd_max_length t)) L s t T N (sd_max_length t) 573 mc ol' sl' FC dl' HP HL hm DP bc' g0 g1 g2 g3 g4 R mm) end end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ assumption. } 1:{ exact LHP. } 1:{ assumption. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. } 1:{ assumption. } 1:{ exact RFC. } 1:{ assumption. } 1:{ exact ER. } 1:{ exact OK3. }
    unfold g3oR. apply evt_done. unfold gb_main_post. do 18 eexists.
    match goal with HT : u8arr psegs ?mm T (u16s (avct FC ?dl'' N)), HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc'' 16)),
                     HG : rw_cells psegs ?mm (dl_As L + 5881) (bD_cells L s ?ol'' ?sl'' ?g0 ?g1 ?g2 ?g3 ?g4) |- _ =>
      exists dl'', bc'', ol'', sl'', g0, g1, g2, g3, g4; eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HB|]; split; [exact HG|];
      split; [assumption|] end.
    repeat (split; [assumption|]). all: lia.
Qed.

Notation WpB L T N sp := [(T%Z, (T + 4 * N)%Z); (dl_As L + 2976, dl_As L + 5308); (dl_As L + 5881, dl_As L + 5968); (bv_unsigned sp + 8, bv_unsigned sp + 40)] (only parsing).

Definition partB_post (L : dlay) (s : deflate_state) (t : tree_id) (T N hm dsc SD mc : Z) (HP7 DP : arr) (hh : list byte) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) FC' DL' BC' OL' SL' g0 g1 g2 g3 g4 junk' m',
    ms' = MS (mkR x1 sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz T) s3 (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1c4d8) fc None m' (seg_rom psegs)
    /\ munch (WpB L T N sp) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP7 573) /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)] /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ rw_cells psegs m' dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz SD)] /\ rw_cells psegs m' (bv_unsigned sp + 8) [CB 32 junk']
    /\ R = bt_upd s t FC' DL' HP7 1 hm DP BC' OL' SL' mc /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len BC' = 16.

Lemma partB : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N hm node dsc SD mc stp xp OL SL : Z) (FC DL HP DP BC : arr) (hh h0 h1 h2 h3 h4 junk : list byte)
    (R : deflate_state)
    (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  let HP7 := arr_set HP hm (arr_get HP 1) in
  let X7 := bt_upd s t FC DL HP7 1 hm DP BC OL SL mc in
  let X9 := bt_upd s t FC (arr_set DL (arr_get HP 1) (wrap16 0)) HP7 1 hm DP (arr_fill BC 0 16 0) OL SL mc in
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz 1); C4 (wz (hm + 1))] -> rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  rw_cells psegs m dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz SD)] ->
  rw_cells psegs m SD [C8 (wz stp); C8 (wz xp); C4 (wz (sd_extra_base t)); C4 (wz (sd_elems t)); C4 (wz (sd_max_length t))] ->
  rw_cells psegs m (bv_unsigned sp) [C8 (wz (dl_As L + 2047))] -> rw_cells psegs m (bv_unsigned sp + 8) [CB 32 junk] ->
  mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp -> 0 <= stp < 2^63 -> 0 <= xp < 2^63 -> 0x10000 <= SD -> SD + 32 <= 0x5c000 -> dsc = dl_As L + bt_desc t ->
  0 <= hm <= 570 -> 0 <= arr_get HP 1 < N -> -1 <= mc < sd_elems t ->
  (forall k, hm + 1 <= k < 573 -> 0 <= arr_get HP7 k < N) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 144 < 2^63 ->
  gb1_ok t mc 573 X9 (hm + 1) 0 ->
  (forall X10 ovf, gen_bitlen_loop1 573 X9 t mc (sd_extra_base t) (sd_max_length t) (hm + 1) 0 = (X10, ovf) -> ovf <> 0 ->
     gb2_ok (sd_max_length t) 573 X10 ovf /\ gb3_ok t mc (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) (sd_max_length t) 573) ->
  (forall i, 0 <= i <= mc -> 0 <= Len (gen_bitlen X7 t) t i <= 15) ->
  R = gen_codes (gen_bitlen X7 t) t mc ->
  evt psegs (partB_post L s t T N hm dsc SD mc HP7 DP hh R sp gp tp F fc m)
      (MS (l4R L T 1 node dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c118) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HP7 X7 X9 ARR HPA BLC GC GD Gdsc Gsd F0 F1 MI LAY RT1 RT2 EN LFC LDL LHP LBC XV SV Rstp Rxp RSD1 RSD2 Edsc Rhm Rh1 Rmc RHP RDL RFC ROL RSL SEP RSP
    OK1 OK23 LEN ER. subst HP7 X7 X9.
  pose proof (munch_refl (WpB L T N sp) m) as MU. pose proof (wmono_refl psegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (RE : 19 <= sd_elems t <= 286 /\ N = 2 * sd_elems t + 1)
    by (subst N; destruct t; cbn [sd_elems tsize]; unfold L_CODES, D_CODES, BL_CODES; lia).
  assert (Rdsc : 2904 <= bt_desc t <= 2952) by (destruct t; cbn [bt_desc]; lia).
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.

  rewrite (gen_bitlen_flat s t FC DL (arr_set HP hm (arr_get HP 1)) 1 hm DP BC OL SL mc) in ER, LEN.
  rewrite (arr_get_set_same HP hm (arr_get HP 1)) in ER, LEN by lia.
  name_term R1 ER1 (gen_bitlen_loop1 573 (bt_upd s t FC (arr_set DL (arr_get HP 1) (wrap16 0)) (arr_set HP hm (arr_get HP 1)) 1 hm DP (arr_fill BC 0 16 0) OL SL mc) t mc
                       (sd_extra_base t) (sd_max_length t) (hm + 1) 0).
  name_term RB ERB (gb_tail t mc R1).
  call (gb_pre L T N hm node dsc SD mc stp xp t FC DL HP BC hh).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact BLC. } 1:{ exact GC. } 1:{ exact Gdsc. } 1:{ exact Gsd. } 1:{ exact MI. } 1:{ exact LAY. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LBC. }
  1:{ exact Rhm. } 1:{ exact Rh1. } 1:{ lia. } 1:{ exact Edsc. } 1:{ exact RSD1. } 1:{ exact RSD2. } 1:{ exact Rstp. } 1:{ exact Rxp. }
  pose proof (avct_zlength FC (arr_set DL (arr_get HP 1) (wrap16 0)) N ltac:(lia)) as LCT'.
  pose proof (av32_zlength (arr_set HP hm (arr_get HP 1)) 573 ltac:(lia)) as L32'. pose proof (av16_zlength (arr_fill BC 0 16 0) 16 ltac:(lia)) as L16'.
  unfold gbR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (gb_main L s t T N hm mc stp xp OL SL FC (arr_set DL (arr_get HP 1) (wrap16 0)) (arr_set HP hm (arr_get HP 1)) 1 DP (arr_fill BC 0 16 0) h0 h1 h2 h3 h4 R1 RB) end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact GD. } 1:{ exact F0. } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact EN. } 1:{ exact LFC. } 1:{ rewrite arr_len_set. exact LDL. } 1:{ rewrite arr_len_set. exact LHP. } 1:{ rewrite arr_len_fill. exact LBC. }
  1:{ exact XV. } 1:{ exact SV. } 1:{ exact Rhm. } 1:{ exact Rmc. } 1:{ exact RHP. } 1:{ intros i Hi. apply blc_zero_range; [exact LBC| exact Hi]. }
  1:{ apply arr_set_range16. exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. } 1:{ exact RSL. } 1:{ exact SEP. } 1:{ exact RSP. }
  1:{ exact ER1. } 1:{ exact OK1. } 1:{ exact OK23. } 1:{ exact ERB. }
  match goal with H : RB = bt_upd _ _ _ ?dl' _ _ _ _ ?bc' _ _ _ |- _ => rewrite H in ER, LEN; clear H ERB;
    pose proof (avct_zlength FC dl' N ltac:(lia)) as LCT''; pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'' end.

  match goal with HG : rw_cells psegs _ (dl_As L + 5881) (bD_cells _ _ _ _ _ _ _ _ _) |- _ => unfold bD_cells in HG end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of ER with R = gen_codes (bt_upd s t FC ?dl' ?hp' 1 hm DP ?bc' ?ol' ?sl' mc) t mc =>
    call (gcs_phase s t L T N mc FC dl' hp' 1 hm DP bc' ol' sl' mc R junk) end end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ exact F1. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. }
  1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ exact SEP. } 1:{ lia. } 1:{ lia. }
  1:{ intros i Hi. pose proof (LEN i Hi) as Li. rewrite bt_Len in Li. exact Li. } 1:{ exact ER. }
  apply evt_done. unfold partB_post. do 24 eexists.
  match goal with HT : u8arr psegs ?mm T (u16s (avct ?fc' ?dl' N)), HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                   HG : rw_cells psegs ?mm (dl_As L + 5881) [CB 7 ?g0; _; _; _; _; CB 4 ?g1; C8 (wz ?ol'); C8 (wz ?sl'); _; _; _; CB 2 ?g2; _; CB 4 ?g3; _; _; CB 4 ?g4; _],
                   HF : rw_cells psegs ?mm (bv_unsigned sp + 8) [CB 32 ?j] |- _ =>
    exists fc', dl', bc', ol', sl', g0, g1, g2, g3, g4, j; eexists;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [eassumption|]; split; [exact HB|];
    split; [eassumption|]; split; [exact HG|]; split; [eassumption|]; split; [exact HF|] end.
  repeat (split; [assumption|]). assumption.
Qed.
