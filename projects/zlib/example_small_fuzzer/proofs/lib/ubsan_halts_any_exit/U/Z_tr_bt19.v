(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.

Module Z_tr_bt2.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_pq OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.


Lemma lxor_sign : forall a, 0 <= a < 2^63 -> Z.lxor a (2^63) = a + 2^63.
Proof.
  intros a H. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 63 n) as [<-|]; [|apply andb_false_r].
  rewrite andb_true_r. rewrite Z.testbit_false by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma l2node_mask : forall mc, -1 <= mc < 2^31 - 1 ->
  Z.land ((0 - Z.b2z (Z.lxor (mc mod 18446744073709551616) 9223372036854775808 <? 9223372036854775810)) mod 18446744073709551616) (mc + 1)
  = (if mc <? 2 then mc + 1 else 0).
Proof.
  intros mc H. destruct (Z.eq_dec mc (-1)) as [->|N1]; [reflexivity|]. destruct (Z.eq_dec mc 0) as [->|N0]; [reflexivity|]. destruct (Z.eq_dec mc 1) as [->|N2]; [reflexivity|].
  rewrite (Z.mod_small mc) by lia. change 9223372036854775808 with (2^63). rewrite lxor_sign by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_ge mc 2)) by lia. reflexivity.
Qed.
Lemma l2node_mask_ge : forall mc, 2 <= mc < 2^31 - 1 ->
  Z.land ((0 - Z.b2z (Z.lxor mc 9223372036854775808 <? 9223372036854775810)) mod 18446744073709551616) (mc + 1) = 0.
Proof.
  intros mc H. change 9223372036854775808 with (2^63). rewrite lxor_sign by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.
Lemma swrap32_succ_m1 : forall mc, -1 <= mc < 2^31 - 1 -> bv_swrap 32 (mc mod 18446744073709551616 + 1) = mc + 1.
Proof.
  intros mc H. destruct (Z.eq_dec mc (-1)) as [->|NE]; [reflexivity|].
  rewrite Z.mod_small by lia. apply Z_dkit.bv_swrap32_id. lia.
Qed.

Definition ubt2R (L : dlay) (T HL mc stp : Z) (x28 x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) :=
  mkR ra sp gp tp (wz 1) (wz HL) (wz mc) s0 s1 (wz stp) (wz (dl_As L + 3008)) (wz (ONES - (dl_As L + 3008))) (wz (ONES - stp))
      (wz 2) (wz 572) (wz (dl_As L + 5308)) (wz (ONES - (dl_As L + 5308))) s2 s3 s4 s5 (wz T) s7 s8 (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s11
      x28 (wz mc) x30 x31.

Notation Wbt2 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5968)] (only parsing).

Definition ubt_l2_post (L : dlay) (s : deflate_state) (T N stp : Z) (FC DL HP : arr) (HL HM : Z) (DP : arr) (OL SL mc : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x28 x30 x31 h0 h1 h2 h3 h4 pcx m',
    ms' = MS (ubt2R L T HL mc stp x28 x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wbt2 L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4)
    /\ ((pcx = BT_L2 /\ HL < 2) \/ (pcx = BT_L2X /\ 2 <= HL)).

Ltac ul2_close MU WM ARR HPA DPA GC GD :=
  let K3 := fresh "K3" in
  zs2; zs2; zs2;
  try (lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ (Z_to_bv 64 (?a + 0)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => reg_as (a + 0) a end);
  zstep; br_cases K3;
  (apply evt_done; unfold ubt_l2_post, ubt2R, bD_cells, BT_L2, BT_L2X; do 10 eexists;
   split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact ARR|]; split; [exact HPA|]; split; [exact DPA|];
   split; [exact GC|]; split; [close_cells GD|];
   first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]]).

Lemma ubt_l2_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL mc stp dsc HM OL SL node mc' : Z) (FC DL HP DP : arr) (h0 h1 h2 h3 h4 : list byte)
    (x28 x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) ->
  mem_inv usegs m -> dlay_ok L -> dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 3 <= N -> arr_len FC = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  stree_view t stp -> stp mod 4 = 0 -> 0 <= HL < 2 -> -1 <= mc < 286 -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  (node, mc') = l2node mc ->
  evt usegs (ubt_l2_post L s T N stp (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node) (HL + 1) HM (arr_set DP node (wrap8 0))
               (wrap64 (OL - 1)) (if stree_has t then wrap64 (SL - stree_Len t node) else SL) mc'
               ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 F fc m)
      (MS (ubt2R L T HL mc stp x28 x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11) F (wz BT_L2) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC GD F16 MI LAY Bsp Rsp AL4 RT1 RT2 RN LFC LHP LDP SV ALS RHL Rmc ROL RSL ENODE.
  pose proof (munch_refl (Wbt2 L T N) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. unfold ubt2R, BT_L2, bD_cells in *.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  assert (En : node = (if mc <? 2 then mc + 1 else 0) /\ mc' = (if mc <? 2 then mc + 1 else mc)).
  { unfold l2node in ENODE. destruct (mc <? 2); inversion ENODE; auto. }
  destruct En as [En Emc']. assert (Rnode : 0 <= node < 3) by (rewrite En; destruct (Z.ltb_spec mc 2); lia).
  assert (Rstp : 0 <= stp < 2^32) by (destruct SV as [[-> _]|(R & _)]; lia).
  zs2. rewrite swrap32_succ_m1 by lia. zs2. try reg_as (mc + 1 + 0) (mc + 1). zstep.
  br_cases K.
  -
    rewrite (proj2 (Z.ltb_lt _ _) K) in En, Emc'. subst node mc'.
    zs2. zstep. ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. try reg_as (mc + 1 + 0) (mc + 1). zs2. zs2. zs2.
    rewrite l2node_mask by lia. rewrite (proj2 (Z.ltb_lt _ _) K).
    zs2. zs2. shl_norm. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) (mc + 1) ltac:(reflexivity).
    do 4 ustep BT_TRAP. do 4 ustep BT_TRAP.
    ct_store_fc ARR FC DL N T (mc + 1) (wrap16 1) ltac:(reflexivity).
    ustep BT_TRAP. ustep BT_TRAP. zs2.
    pb_store DPA DP 573 (dl_As L + 5308) (mc + 1) (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2. zstep.
    zstep. destruct SV as [[Es Eh]|(Rs0 & Eh & RDS)]; rewrite Eh.
    + subst stp. br_true. ul2_close MU WM ARR HPA DPA GC GD.
    + br_false. lazymatch goal with H : mem_inv usegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (RDS mm (mc + 1) H ltac:(lia)) as [RDl Rsl] end.
      ustep BT_TRAP. zs2. ustep BT_TRAP. ustep BT_TRAP.
      zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zstep. zs2. ul2_close MU WM ARR HPA DPA GC GD.
  -
    rewrite (proj2 (Z.ltb_ge _ _)) in En, Emc' by lia. subst node mc'.
    zs2. try reg_as (mc + 0) mc.
    zs2. zstep. ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. try reg_as (mc + 0) mc. zs2. zs2. zs2.
    rewrite l2node_mask_ge by lia.
    zs2. zs2. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) 0 ltac:(reflexivity).
    do 4 ustep BT_TRAP. do 4 ustep BT_TRAP.
    ct_store_fc ARR FC DL N T 0 (wrap16 1) ltac:(reflexivity).
    ustep BT_TRAP. ustep BT_TRAP. zs2.
    pb_store DPA DP 573 (dl_As L + 5308) 0 (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2. zstep.
    zstep. destruct SV as [[Es Eh]|(Rs0 & Eh & RDS)]; rewrite Eh.
    + subst stp. br_true. ul2_close MU WM ARR HPA DPA GC GD.
    + br_false. lazymatch goal with H : mem_inv usegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (RDS mm 0 H ltac:(lia)) as [RDl Rsl] end.
      change (0 * 4) with 0 in RDl. replace (stp + 0 + 2) with (stp + 2) in RDl by lia.
      ustep BT_TRAP. zs2. ustep BT_TRAP. ustep BT_TRAP.
      zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zstep. zs2. ul2_close MU WM ARR HPA DPA GC GD.
Qed.

Definition ubt_loop2_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL mc : Z) (DL BC : arr) (HM MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t5 t6 h0 h1 h2 h3 h4 FC' HP' HL' DP' OL' SL' mc' m',
    ms' = MS (mkR ra sp gp tp t0 (wz HL') t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz T) s7 s8 (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s11 t3 (wz mc') t5 t6)
             F (wz BT_L2X) fc None m' (seg_rom usegs)
    /\ munch (Wbt2 L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL'); C4 (wz HM)] /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4)
    /\ R = (bt_upd s t FC' DL HP' HL' HM DP' BC OL' SL' MC, mc')
    /\ arr_len FC' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ HL' = Z.max HL 2 /\ -1 <= mc' <= Z.max mc 2 /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64.

Lemma ubt_loop2 : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL mc stp dsc HM OL SL MC : Z) (FC DL HP DP BC : arr) (h0 h1 h2 h3 h4 : list byte) (R : deflate_state * Z)
    (x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) ->
  mem_inv usegs m -> dlay_ok L -> dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 3 <= N -> arr_len FC = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  stree_view t stp -> stp mod 4 = 0 -> 0 <= HL < 2^31 -> -1 <= mc < 286 -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  R = build_tree_loop2 2 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t mc ->
  evt usegs (ubt_loop2_post L s t T N HL mc DL BC HM MC R ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 F fc m)
      (MS (ubt1R L T (sd_elems t) (sd_elems t) mc stp x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11) F (wz BT_L1X) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC GD F16 MI LAY Bsp Rsp AL4 RT1 RT2 RN LFC LHP LDP SV ALS RHL Rmc ROL RSL ER.
  pose proof (munch_refl (Wbt2 L T N) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. unfold ubt1R, BT_L1X.
  assert (Rstp : 0 <= stp < 2^32) by (destruct SV as [[-> _]|(R0 & _)]; lia).
  zs2. zs2. zstep. br_cases K.
  -
    rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.L2_step in ER by lia. destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.l2node mc) as [node mc1] eqn:E1. symmetry in E1.
    zs2. reg_as (dl_As L + 2047 + 961) (dl_As L + 3008). zs2. rewrite (zb_lxor_ones (dl_As L + 3008)) by lia.
    zstep. br_false.
    zs2. zs2. rewrite (zb_lxor_ones stp) by lia. zs2. zs2. zs2. zs2. zs2. zs2. rewrite (zb_lxor_ones (dl_As L + 5308)) by lia. zs2. zs2. try reg_as (mc + 0) mc. zs2.
    assert (Rn1 : -1 <= mc1 <= Z.max mc 2) by (unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.l2node in E1; destruct (Z.ltb_spec mc 2); inversion E1; lia).
    assert (ROL1 : 0 <= wrap64 (OL - 1) < 2^64) by apply wrap64_range.
    assert (RSL1 : 0 <= (if stree_has t then wrap64 (SL - stree_Len t node) else SL) < 2^64) by (destruct (stree_has t); [apply wrap64_range| exact RSL]).
    call (ubt_l2_iter L s t T N HL mc stp dsc HM OL SL node mc1 FC DL HP DP h0 h1 h2 h3 h4).
    1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact F16. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Bsp. } 1:{ exact Rsp. }
    1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact SV. } 1:{ exact ALS. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact ROL. } 1:{ exact RSL. } 1:{ exact E1. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> K1]|[-> K1]] end.
    +
      rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.L2_step in ER by lia. destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.l2node mc1) as [node2 mc2] eqn:E2. symmetry in E2.
      assert (Rn2 : -1 <= mc2 <= Z.max mc 2) by (unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.l2node in E2; destruct (Z.ltb_spec mc1 2); inversion E2; lia).
      unfold ubt2R.
      match goal with HT : u8arr usegs ?mm T _, HA : u32arr usegs ?mm _ _, HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                       HGD : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells _ _ _ _ ?g0 ?g1 ?g2 ?g3 ?g4), HF : rw_cells usegs ?mm (bv_unsigned sp + 16) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (ubt_l2_iter L s t T N (HL + 1) mc1 stp dsc HM (wrap64 (OL - 1)) (if stree_has t then wrap64 (SL - stree_Len t node) else SL) node2 mc2
                (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node) (arr_set DP node (wrap8 0)) g0 g1 g2 g3 g4);
        [exact HT| exact HA| exact HD| exact HG| exact HGD| exact HF| eassumption| exact LAY| exact Bsp| exact Rsp| exact AL4| exact RT1| exact RT2| exact RN| rewrite arr_len_set; exact LFC| rewrite arr_len_set; exact LHP
        | rewrite arr_len_set; exact LDP| exact SV| exact ALS| lia| lia| exact ROL1| exact RSL1| exact E2|] end.
      match goal with H : _ \/ _ |- _ => destruct H as [[-> K2]|[-> K2]] end; [exfalso; lia|].
      cbn [build_tree_loop2] in ER.
      apply evt_done. unfold ubt_loop2_post, ubt2R. do 26 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [exact ER|].
      split; [rewrite !arr_len_set; exact LFC|]. split; [rewrite !arr_len_set; exact LHP|]. split; [rewrite !arr_len_set; exact LDP|].
      split; [lia|]. split; [lia|]. split; [apply wrap64_range|]. destruct (stree_has t); [apply wrap64_range| exact RSL].
    + rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.L2_out in ER by lia.
      apply evt_done. unfold ubt_loop2_post, ubt2R. do 26 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [exact ER|].
      split; [rewrite !arr_len_set; exact LFC|]. split; [rewrite !arr_len_set; exact LHP|]. split; [rewrite !arr_len_set; exact LDP|].
      split; [lia|]. split; [lia|]. split; [exact ROL1| exact RSL1].
  - rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.L2_out in ER by lia.
    apply evt_done. unfold ubt_loop2_post. do 26 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|].
    split; [exact GC|]. split; [exact GD|]. split; [exact ER|].
    split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|]. split; [lia|]. split; [lia|]. split; [exact ROL| exact RSL].
Qed.
End Z_tr_bt2.

Module Z_tr_bt3.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_pq OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.


Lemma loop3_S : forall f X t n, 1 <= n -> build_tree_loop3 (S f) X t n = build_tree_loop3 f (pqdownheap X t n) t (n - 1).
Proof. intros. cbn [build_tree_loop3]. rewrite (proj2 (Z.leb_le 1 n)) by lia. reflexivity. Qed.
Lemma loop3_out : forall f X t n, n < 1 -> build_tree_loop3 f X t n = X.
Proof. intros [|f] X t n H; [reflexivity|]. cbn [build_tree_loop3]. rewrite (proj2 (Z.leb_gt 1 n)) by lia. reflexivity. Qed.

Definition ul3R (L : dlay) (T n : Z) (x1 t0 t1 t2 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x23 x27 t3 t4 t5 t6 sp gp tp : word) :=
  mkR x1 sp gp tp t0 t1 t2 (wz 1) x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 (wz (dl_As L)) x21 (wz T) x23 (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) x27
      t3 t4 t5 t6.

Notation Wl3 lo sp L := [(lo%Z, bv_unsigned sp); (dl_As L + 3008, dl_As L + 5300)] (only parsing).

Definition ul3_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n1 lo : Z) (FC DL DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (x9 x18 x21 x23 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP' pcx m',
    ms' = MS (ul3R L T (n1 + 1) x1 t0 t1 t2 x9 (wz n1) a1 a2 a3 a4 a5 a6 a7 x18 (wz (n1 + 1)) x21 x23 x27 t3 t4 t5 t6 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wl3 lo sp L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = build_tree_loop3 f (bt_upd s t FC DL HP' HL HM DP BC OL SL MC) t n1
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N)
    /\ ((pcx = BT_L3 /\ 1 <= n1) \/ (pcx = 0x1cb70 /\ n1 = 0)).

Lemma ubt_l3_trip : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (x1 t0 t1 t2 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x23 x27 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wl3 lo sp L) m0 T FC DL N -> mem_inv usegs m -> dlay_ok L -> munch (Wl3 lo sp L) m0 m -> wmono usegs m0 m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= n <= HL -> HL < 573 -> x10 = wz n ->
  R = build_tree_loop3 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t n ->
  evt usegs (ul3_post L s t T N HL HM (n - 1) lo FC DL DP BC OL SL MC f R x9 x18 x21 x23 x27 sp gp tp F fc m0)
      (MS (ul3R L T n x1 t0 t1 t2 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x23 x27 t3 t4 t5 t6 sp gp tp) F (wz BT_L3) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA DPA GC RDT MI LAY MU WM STK LO BEL AL4 RT1 RT2 RN LHP PQ RFC RDP Rn RHL -> ER.
  rewrite loop3_S in ER by lia.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. unfold Z_PQ_STACK in LO.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  unfold ul3R, BT_L3. zs2. try reg_as (n + 0) n. zs2. try reg_as (dl_As L + 0) (dl_As L). zs2. try reg_as (T + 0) T. zs2. try reg_as (n + 0) n.
  zstep.
  call (pqdownheap_spec L s t T N HL HM n lo FC DL HP DP BC OL SL MC).
  1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_PQ_STACK; lia. } 1:{ exact BEL. }
  1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ exact Rn. } 1:{ exact RHL. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  match goal with E : pqdownheap _ _ _ = bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _ |- _ => rewrite E in ER end.
  zs2. reg_as (n + -1) (n - 1). zstep. br_cases K;
    replace (wz n) with (wz (n - 1 + 1)) by (f_equal; lia);
    match goal with HA : u32arr usegs ?mm _ (av32 ?hp 573), HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                     HS : stk usegs ?mm _ _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply evt_done; unfold ul3_post, ul3R; do 18 eexists;
      split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact HS|];
      split; [exact HA|]; split; [exact HD|]; split; [exact HG|]; split; [exact ER|]; split; [exact HL'|]; split; [exact HQ|] end;
    [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].
Qed.

Definition ubt_loop3_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM lo : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (x9 x18 x21 x23 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP' m',
    ms' = MS (ul3R L T 1 x1 t0 t1 t2 x9 (wz 0) a1 a2 a3 a4 a5 a6 a7 x18 (wz 1) x21 x23 x27 t3 t4 t5 t6 sp gp tp) F (wz 0x1cb70) fc None m' (seg_rom usegs)
    /\ munch (Wl3 lo sp L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = bt_upd s t FC DL HP' HL HM DP BC OL SL MC
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N).

Lemma ubt_loop3 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (x1 t0 t1 t2 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x23 x27 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wl3 lo sp L) m0 T FC DL N -> mem_inv usegs m -> dlay_ok L -> munch (Wl3 lo sp L) m0 m -> wmono usegs m0 m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  Z.of_nat (S f) = n -> n <= HL -> HL < 573 -> x10 = wz n ->
  R = build_tree_loop3 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t n ->
  evt usegs (ubt_loop3_post L s t T N HL HM lo FC DL DP BC OL SL MC R x9 x18 x21 x23 x27 sp gp tp F fc m0)
      (MS (ul3R L T n x1 t0 t1 t2 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x23 x27 t3 t4 t5 t6 sp gp tp) F (wz BT_L3) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros HPA DPA GC RDT MI LAY MU WM STK LO BEL AL4 RT1 RT2 RN LHP PQ RFC RDP Ef Rn RHL Ex ER.
  - call (ubt_l3_trip L s t T N HL HM n lo FC DL HP DP BC OL SL MC 0%nat R m).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact STK. } 1:{ exact LO. } 1:{ exact BEL. }
    1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact Ex. } 1:{ exact ER. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    match goal with E : R = build_tree_loop3 0 _ _ _ |- _ => cbn [build_tree_loop3] in E; rename E into ER' end.
    replace (n - 1) with 0 by lia. unfold ul3R. replace (0 + 1) with 1 by lia.
    apply evt_done. unfold ubt_loop3_post, ul3R. do 17 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER'|]. split; assumption.
  - call (ubt_l3_trip L s t T N HL HM n lo FC DL HP DP BC OL SL MC (S f) R m).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact STK. } 1:{ exact LO. } 1:{ exact BEL. }
    1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact Ex. } 1:{ exact ER. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    unfold ul3R.
    match goal with E : R = build_tree_loop3 (S f) _ _ _, HA : u32arr usegs ?mm _ (av32 ?hp 573), HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                     HS : stk usegs ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N HL HM (n - 1) lo FC DL hp DP BC OL SL MC R m0);
        [exact HA| exact HD| exact HG| exact RDT| eassumption| exact LAY| exact MU| exact WM| exact HS| exact LO| exact BEL| exact AL4| exact RT1| exact RT2| exact RN
        | assumption| assumption| exact RFC| exact RDP| lia| lia| exact RHL| reflexivity| exact E] end.
Qed.
End Z_tr_bt3.

Module Z_tr_bt6.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_pq OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.


Lemma le2_add_sx16_2 : forall a b, le2 (wz (bv_unsigned (sx16 (wz b)) + bv_unsigned (sx16 (wz a)))) = le2 (wz (wrap16 (a + b))).
Proof.
  intros a b. apply le2_wz_mod. rewrite lo16_unsigned_wz, wrap16_mod, lo16_idem.
  rewrite Z.add_mod by lia. rewrite !lo16_sx16, !lo16_unsigned_wz. rewrite <- Z.add_mod by lia. f_equal. lia.
Qed.

Definition ul4R (L : dlay) (T node : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp : word) :=
  mkR x1 sp gp tp t0 t1 t2 (wz (T + node * 4)) (wz 572) a0 a1 a2 a3 a4 a5 a6 a7 (wz (dl_As L + 5308)) (wz (dl_As L + 3008)) (wz node) (wz (T + node * 4)) (wz T) x23
      (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz node) (wz (ONES - (dl_As L + 5308))) t3 t4 t5 t6.

Notation Wpq lo sp L := [(lo%Z, bv_unsigned sp); (dl_As L + 3008, dl_As L + 5300)] (only parsing).
Notation ubt_f64 L := ([C8 (wz (ONES - (dl_As L + 3008)))])%list (only parsing).
Notation W5m L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5881)] (only parsing).
Notation W4 lo sp L := [(lo%Z, bv_unsigned sp); (dl_As L + 3008, dl_As L + 5308)] (only parsing).
Notation W5 lo sp L T N := [(lo%Z, bv_unsigned sp); (T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5881)] (only parsing).

Definition ul4_remove_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP2 m',
    ms' = MS (ul4R L T node x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (arr_get HP 1)) t3 t4 t5 t6 sp gp tp) F (wz 0x1cbe4) fc None m' (seg_rom usegs)
    /\ munch (W4 lo sp L) m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HP2 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz (HL - 1)); C4 (wz HM)]
    /\ pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1 = bt_upd s t FC DL HP2 (HL - 1) HM DP BC OL SL MC
    /\ arr_len HP2 = 573 /\ (forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP2 i < N).

Lemma ul4_remove : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) -> rw_cells usegs m (bv_unsigned sp + 64) (ubt_f64 L) ->
  mem_inv usegs m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL < 573 -> a0 = wz HL ->
  evt usegs (ul4_remove_post L s t T N HL HM node lo FC DL HP DP BC OL SL MC sp gp tp F fc m)
      (MS (ul4R L T node x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz BT_L4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC F16 F64 MI LAY STK LO BEL Rsp AL4 RT1 RT2 RN LFC LHP PQ RFC RDP RHL ->.
  pose proof (munch_refl (W4 lo sp L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (PQ HL ltac:(lia)) as Rv. pose proof (PQ 1 ltac:(lia)) as Rn1. pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. unfold Z_PQ_STACK in LO.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  unfold ul4R, BT_L4. zs2. ustep BT_TRAP.
  pose proof (u32arr_read usegs m _ (av32 HP 573) 1 _ (wa (dl_As L + 2976 + 36)) HPA (av32_nth HP 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn.
  zs2. zstep. reg_as (HL + -1) (HL - 1). ustep BT_TRAP. zs2. shl_norm. zs2. ustep BT_TRAP. zs2.
  lazymatch goal with H : u32arr usegs ?mm _ (av32 HP 573) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read usegs mm _ (av32 HP 573) HL _ (wa (dl_As L + 3008 + HL * 4)) H (av32_nth HP 573 HL ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDv end.
  zs2.
  h32_store HPA HP 573 (dl_As L + 3008) 1 (arr_get HP HL) ltac:(reflexivity).
  zs2. zs2. zs2. try reg_as (T + 0) T. zstep.
  set (HP1 := arr_set HP 1 (arr_get HP HL)) in *.
  assert (PQ1 : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP1 i < N).
  { intros i Hi. subst HP1. destruct (Z.eq_dec 1 i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rv| rewrite arr_get_set_other by exact NE; apply PQ; lia]. }
  lazymatch goal with H : u8arr usegs ?mm T _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RDT : ct_readable (Wpq lo sp L) mm T FC DL N) by (eapply ct_readable_rw; [exact H| lia| lia| cbn [disjoint_from]; lia]) end.
  call (pqdownheap_spec L s t T N (HL - 1) HM 1 lo FC DL HP1 DP BC OL SL MC).
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact RDT. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ eassumption. } 1:{ unfold Z_PQ_STACK; lia. } 1:{ exact BEL. }
  1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ subst HP1; rewrite arr_len_set; exact LHP. } 1:{ exact PQ1. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  match goal with E : pqdownheap _ _ _ = bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, HA : u32arr usegs ?mm _ (av32 ?hp 573), HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                   HS : stk usegs ?mm _ _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply evt_done; unfold ul4_remove_post, ul4R; do 18 eexists;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HS|];
    split; [exact HA|]; split; [exact HD|]; split; [exact HG|]; split; [exact E|]; split; [exact HL'| exact HQ] end.
Qed.


Definition ul4_node_post (L : dlay) (T N HL HM node : Z) (FC' DL' HP3 DP' : arr)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 m',
    ms' = MS (mkR x1 sp gp tp t0 t1 t2 (wz (T + node * 4)) (wz 572) (wz (dl_As L)) (wz T) (wz 1) a3 a4 a5 a6 a7 (wz (dl_As L + 5308)) (wz (dl_As L + 3008)) (wz node) (wz (T + node * 4)) (wz T) x23
                  (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz (node + 1)) (wz (ONES - (dl_As L + 5308))) t3 t4 t5 t6) F (wz 0x1cd18) fc None m' (seg_rom usegs)
    /\ munch (W5m L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP3 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz (HM - 2))].

Ltac ul4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC :=
  ustep BT_TRAP; ustep BT_TRAP; zs2; zs2;
  match goal with |- context [wz (?d + 1)] => pb_store DPA DP 573 (dl_As L + 5308) node (wrap8 (d + 1)) ltac:(apply lo8_wz_wrap8; lia) end;
  ct_store_dl ARR (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_))) DL N T m_ (wrap16 node) ltac:(rewrite (wrap16_id node) by lia; reflexivity);
  ct_store_dl ARR (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_))) (arr_set DL m_ (wrap16 node)) N T n (wrap16 node) ltac:(rewrite (wrap16_id node) by lia; reflexivity);
  zs2;
  h32_store HPA (arr_set (arr_set HP2 (HM - 1) n) (HM - 2) m_) 573 (dl_As L + 3008) 1 node ltac:(reflexivity);
  zs2; zs2; zs2; try reg_as (T + 0) T;
  apply evt_done; unfold ul4_node_post; do 15 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact ARR|]; split; [exact HPA|]; split; [exact DPA| exact GC].

Lemma ul4_node : forall (L : dlay) (t : tree_id) (T N HL HM node dsc n m_ : Z) (FC DL HP2 DP : arr)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP2 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) -> rw_cells usegs m (bv_unsigned sp + 64) (ubt_f64 L) ->
  mem_inv usegs m -> dlay_ok L -> dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP2 = 573 -> arr_len DP = 573 ->
  (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  m_ = arr_get HP2 1 -> 0 <= n < N -> 0 <= m_ < N -> 0 <= node < N -> 1 <= HL < 573 -> 3 <= HM <= 573 -> 0 <= sd_elems t < 2 ^ 32 ->
  evt usegs (ul4_node_post L T N HL HM node (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_)))
               (arr_set (arr_set DL m_ (wrap16 node)) n (wrap16 node)) (arr_set (arr_set (arr_set HP2 (HM - 1) n) (HM - 2) m_) 1 node)
               (arr_set DP node (wrap8 (dmax DP n m_ + 1))) sp gp tp F fc m)
      (MS (ul4R L T node x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz n) t3 t4 t5 t6 sp gp tp) F (wz 0x1cbe4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC F16 F64 MI LAY Bsp Rsp AL4 RT1 RT2 RN LFC LDL LHP LDP RFC RDP Em Rn Rm Rnode RHL RHM RE.
  pose proof (munch_refl (W5m L T N) m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP2 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  unfold ul4R.
  zs2. zs2. reg_as (HM + -1) (HM - 1). ustep BT_TRAP.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read usegs mm _ (av32 HP2 573) 1 _ (wa (dl_As L + 2976 + 36)) HPA (av32_nth HP2 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDm; rewrite <- Em in RDm end.
  zs2. zstep. ustep BT_TRAP. zs2. shl_norm. zs2. ustep BT_TRAP. zs2. shl_norm. zs2.
  h32_store HPA HP2 573 (dl_As L + 3008) (HM - 1) n ltac:(reflexivity).
  zs2. zs2. reg_as (HM - 1 + -1) (HM - 2). ustep BT_TRAP. zstep. ustep BT_TRAP. zs2. shl_norm. zs2. ustep BT_TRAP.
  zs2. zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2.
  h32_store HPA (arr_set HP2 (HM - 1) n) 573 (dl_As L + 3008) (HM - 2) m_ ltac:(reflexivity).
  do 4 ustep BT_TRAP. do 4 ustep BT_TRAP. ustep BT_TRAP.
  zs2. shl_norm. zs2. do 4 ustep BT_TRAP. do 2 ustep BT_TRAP.
  ustep BT_TRAP. zs2. zs2. zs2. zs2. ustep BT_TRAP. ustep BT_TRAP.
  match goal with H : u8arr usegs ?mm T _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u16arr_read usegs mm T (avct FC DL N) (2 * n) _ (wa (T + n * 4)) H (avct_nth_fc FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDfn;
    pose proof (u16arr_read usegs mm T (avct FC DL N) (2 * m_) _ (wa (T + m_ * 4)) H (avct_nth_fc FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDfm end.
  zs2. zs2. zs2.
  ct_store_fc ARR FC DL N T node (wrap16 (arr_get FC n + arr_get FC m_)) ltac:(apply le2_add_sx16_2).
  pose proof (RDP n ltac:(lia)) as Rdn. pose proof (RDP m_ ltac:(lia)) as Rdm.
  do 4 ustep BT_TRAP. zs2. zs2.
  match goal with H : u8arr usegs ?mm (dl_As L + 5308) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_read usegs mm _ (av8 DP 573) n _ (wa (dl_As L + 5308 + n)) H (av8_nth DP 573 n ltac:(lia)) ltac:(lia) eq_refl) as RDdn;
    pose proof (u8arr_read usegs mm _ (av8 DP 573) m_ _ (wa (dl_As L + 5308 + m_)) H (av8_nth DP 573 m_ ltac:(lia)) ltac:(lia) eq_refl) as RDdm end.
  zsb. rewrite (bv8_small (arr_get DP n)) by lia. zsb. rewrite (bv8_small (arr_get DP m_)) by lia.
  zstep. br_cases K.
  -
    assert (ED : dmax DP n m_ = arr_get DP n) by (unfold dmax; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity). rewrite ED.
    ul4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC.
  - assert (ED : dmax DP n m_ = arr_get DP m_) by (unfold dmax; destruct (Z.leb_spec (arr_get DP m_) (arr_get DP n)); lia). rewrite ED.
    zs2. try reg_as (arr_get DP m_ + 0) (arr_get DP m_). ul4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC.
Qed.


Definition ul4_down_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 HPf pcx m',
    ms' = MS (ul4R L T (node + 1) x1 t0 t1 t2 (wz HL) a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (W4 lo sp L) m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HPf 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t 1 = bt_upd s t FC DL HPf HL HM DP BC OL SL MC
    /\ arr_len HPf = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HPf i < N)
    /\ ((pcx = BT_L4 /\ 2 <= HL) \/ (pcx = BT_PARTB /\ HL < 2)).

Lemma ul4_down : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (x1 t0 t1 t2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  mem_inv usegs m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= HL < 573 -> 0 <= node ->
  evt usegs (ul4_down_post L s t T N HL HM node lo FC DL HP DP BC OL SL MC sp gp tp F fc m)
      (MS (mkR x1 sp gp tp t0 t1 t2 (wz (T + node * 4)) (wz 572) (wz (dl_As L)) (wz T) (wz 1) a3 a4 a5 a6 a7 (wz (dl_As L + 5308)) (wz (dl_As L + 3008)) (wz node) (wz (T + node * 4)) (wz T) x23
               (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz (node + 1)) (wz (ONES - (dl_As L + 5308))) t3 t4 t5 t6) F (wz 0x1cd18) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC MI LAY STK LO BEL AL4 RT1 RT2 RN LFC LHP PQ RFC RDP RHL Rnode.
  pose proof (munch_refl (W4 lo sp L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. unfold Z_PQ_STACK in LO. pose proof (PQ 1 ltac:(lia)) as R1.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  zstep.
  assert (RDT : ct_readable (Wpq lo sp L) m T FC DL N) by (eapply ct_readable_rw; [exact ARR| lia| lia| cbn [disjoint_from]; lia]).
  call (pqdownheap_spec L s t T N HL HM 1 lo FC DL HP DP BC OL SL MC).
  1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact RDT. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_PQ_STACK; lia. } 1:{ exact BEL. }
  1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  zs2. zs2. zs2. zs2. zs2. reg_as (T + node * 4 + 4) (T + (node + 1) * 4).
  zstep. br_cases K;
    match goal with E : pqdownheap _ _ _ = bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, HA : u32arr usegs ?mm _ (av32 ?hp 573), HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                     HS : stk usegs ?mm _ _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply evt_done; unfold ul4_down_post, ul4R; do 19 eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HS|];
      split; [exact HA|]; split; [exact HD|]; split; [exact HG|]; split; [exact E|]; split; [exact HL'|]; split; [exact HQ|] end;
    [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].
Qed.

Definition ul4_iter_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node lo : Z) (BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 FC' DL' HP' DP' pcx m',
    ms' = MS (ul4R L T (node + 1) x1 t0 t1 t2 (wz (HL - 1)) a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (W5 lo sp L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u8arr usegs m' T (u16s (avct FC' DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz (HL - 1)); C4 (wz (HM - 2))]
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573
    /\ (forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP' i < N) /\ (forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256)
    /\ ((pcx = BT_L4 /\ 2 <= HL - 1 /\ R = build_tree_loop4 f (bt_upd s t FC' DL' HP' (HL - 1) (HM - 2) DP' BC OL SL MC) t (node + 1))
        \/ (pcx = BT_PARTB /\ HL - 1 < 2 /\ R = bt_upd s t FC' DL' HP' (HL - 1) (HM - 2) DP' BC OL SL MC)).

Lemma ul4_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) -> rw_cells usegs m (bv_unsigned sp + 64) (ubt_f64 L) ->
  mem_inv usegs m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL < 573 -> 0 <= node < N -> 3 <= HM <= 573 -> 0 <= sd_elems t < 2 ^ 32 -> a0 = wz HL ->
  R = build_tree_loop4 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t node ->
  evt usegs (ul4_iter_post L s t T N HL HM node lo BC OL SL MC f R sp gp tp F fc m)
      (MS (ul4R L T node x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz BT_L4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC F16 F64 MI LAY STK LO BEL Rsp AL4 RT1 RT2 RN LFC LDL LHP LDP PQ RFC RDP RHL Rnode RHM RE Ea0 ER.
  pose proof (munch_refl (W5 lo sp L T N) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (dlay_ranges _ LAY) as (Rs & _). pose proof BEL as BEL0. below_open BEL0. unfold Z_PQ_STACK in LO.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT.
  call (ul4_remove L s t T N HL HM node dsc lo FC DL HP DP BC OL SL MC).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact F16. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_PQ_STACK; lia. } 1:{ exact BEL. }
  1:{ exact Rsp. } 1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LFC. } 1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ exact RHL. } 1:{ exact Ea0. }
  pose proof (PQ 1 ltac:(lia)) as Rn.
  match goal with E : pqdownheap _ _ _ = bt_upd _ _ _ _ ?hp2 _ _ _ _ _ _ _, H : u32arr usegs ?mm _ (av32 ?hp2 573), HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                   HLn : arr_len ?hp2 = 573, HQ : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get ?hp2 i < N,
                   HF16 : rw_cells usegs ?mm (bv_unsigned sp + 16) _, HF64 : rw_cells usegs ?mm (bv_unsigned sp + 64) _, HT : u8arr usegs ?mm T _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    rename hp2 into HP2; rename E into E2; rename HLn into LHP2; rename HQ into PQ2; pose proof (PQ2 1 ltac:(lia)) as Rm;
    assert (EHP2 : HP2 = ds_heap (pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1)) by (rewrite E2, bt_heap; reflexivity);
    call (ul4_node L t T N (HL - 1) HM node dsc (arr_get HP 1) (arr_get HP2 1) FC DL HP2 DP);
    [exact HT| exact H| exact HD| exact HG| exact HF16| exact HF64| eassumption| exact LAY| lia| exact Rsp| exact AL4| exact RT1| exact RT2| exact RN| exact LFC| exact LDL| exact LHP2| exact LDP| exact RFC| exact RDP
    | reflexivity| exact Rn| exact Rm| exact Rnode| lia| exact RHM| exact RE|] end.
  match goal with H : u8arr usegs _ T (u16s (avct ?fc' ?dl' N)) |- _ => name_term FC' EFC fc'; name_term DL' EDL dl'; rename H into ARR' end.
  match goal with H : u32arr usegs _ _ (av32 ?hp3 573) |- _ => name_term HP3 EHP3 hp3; rename H into HPA3 end.
  match goal with H : u8arr usegs _ (dl_As L + 5308) (av8 ?dp' 573) |- _ => name_term DP' EDP dp'; rename H into DPA' end.
  assert (LFC' : arr_len FC' = N) by (rewrite EFC, arr_len_set; exact LFC).
  assert (LDL' : arr_len DL' = N) by (rewrite EDL, !arr_len_set; exact LDL).
  assert (LHP3 : arr_len HP3 = 573) by (rewrite EHP3, !arr_len_set; exact LHP2).
  assert (LDP' : arr_len DP' = 573) by (rewrite EDP, arr_len_set; exact LDP).
  assert (RFC' : forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536).
  { intros i Hi. rewrite EFC. destruct (Z.eq_dec node i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RFC; exact Hi]. }
  assert (RDP' : forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256).
  { intros i Hi. rewrite EDP. destruct (Z.eq_dec node i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply wrap8_range| rewrite arr_get_set_other by exact NE; apply RDP; exact Hi]. }
  assert (E31 : arr_get HP3 1 = node) by (rewrite EHP3; apply arr_get_set_same; rewrite !arr_len_set; lia).
  assert (PQ3 : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP3 i < N).
  { intros i Hi. rewrite EHP3. destruct (Z.eq_dec 1 i) as [<-|NE1]; [rewrite arr_get_set_same by (rewrite !arr_len_set; lia); exact Rnode|].
    rewrite arr_get_set_other by exact NE1. destruct (Z.eq_dec (HM - 2) i) as [<-|NE2]; [rewrite arr_get_set_same by (rewrite !arr_len_set; lia); exact Rm|].
    rewrite arr_get_set_other by exact NE2. destruct (Z.eq_dec (HM - 1) i) as [<-|NE3]; [rewrite arr_get_set_same by lia; exact Rn|].
    rewrite arr_get_set_other by exact NE3. apply PQ2. exact Hi. }
  pose proof (avct_zlength FC' DL' N ltac:(lia)) as LCT'. pose proof (av8_zlength DP' 573 ltac:(lia)) as L8'.
  match goal with HG : rw_cells usegs ?mm (dl_As L + 5300) _, HS : stk usegs ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (ul4_down L s t T N (HL - 1) (HM - 2) node lo FC' DL' HP3 DP' BC OL SL MC);
    [exact ARR'| exact HPA3| exact DPA'| exact HG| eassumption| exact LAY| exact HS| unfold Z_PQ_STACK; lia| exact BEL| exact AL4| exact RT1| exact RT2| exact RN| exact LFC'| exact LHP3
    | exact PQ3| exact RFC'| exact RDP'| lia| lia|] end.
  match goal with E : pqdownheap _ _ _ = bt_upd _ _ _ _ ?hpf _ _ _ _ _ _ _, H : u32arr usegs _ _ (av32 ?hpf 573) |- _ =>
    rename hpf into HPf; rename E into Ef; rename H into HPAf;
    assert (EHPf : HPf = ds_heap (pqdownheap (bt_upd s t FC' DL' HP3 (HL - 1) (HM - 2) DP' BC OL SL MC) t 1)) by (rewrite Ef, bt_heap; reflexivity) end.
  pose proof (l4_model s t BC OL SL MC FC DL HP HL HM DP node f R HP2 (arr_get HP2 1) FC' DL' HP3 DP' HPf ER EHP2 eq_refl EFC EDL EHP3 EDP EHPf) as EM.
  apply evt_done. unfold ul4_iter_post. do 16 eexists. exists FC', DL', HPf, DP'. do 2 eexists.
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ARR'|]. split; [exact HPAf|]. split; [eassumption|]. split; [eassumption|].
  split; [exact LFC'|]. split; [exact LDL'|]. split; [assumption|]. split; [exact LDP'|]. split; [assumption|]. split; [exact RFC'|]. split; [exact RDP'|].
  match goal with H : _ /\ _ \/ _ /\ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - left. split; [reflexivity|]. split; [exact K|]. rewrite (proj2 (Z.leb_le 2 (HL - 1)) K) in EM. exact EM.
  - right. split; [reflexivity|]. split; [exact K|]. rewrite (proj2 (Z.leb_gt 2 (HL - 1)) K) in EM. exact EM.
Qed.


Definition ubt_loop4_post (L : dlay) (s : deflate_state) (t : tree_id) (T N lo : Z) (BC : arr) (OL SL MC : Z) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 FC' DL' HP' DP' HM' node' m',
    ms' = MS (ul4R L T node' x1 t0 t1 t2 (wz 1) a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz BT_PARTB) fc None m' (seg_rom usegs)
    /\ munch (W5 lo sp L T N) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u8arr usegs m' T (u16s (avct FC' DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz HM')]
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573
    /\ 0 <= arr_get HP' 1 < N /\ (forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256)
    /\ 1 <= HM' <= 571 /\ 0 <= node'
    /\ R = bt_upd s t FC' DL' HP' 1 HM' DP' BC OL SL MC.

Lemma ubt_loop4 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) -> rw_cells usegs m (bv_unsigned sp + 64) (ubt_f64 L) ->
  mem_inv usegs m -> dlay_ok L -> munch (W5 lo sp L T N) m0 m -> wmono usegs m0 m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL -> HL <= Z.of_nat f -> 0 <= node -> node + HL <= N -> 2 * HL <= HM + 1 -> HM <= 573 -> 0 <= sd_elems t < 2 ^ 32 -> a0 = wz HL ->
  R = build_tree_loop4 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t node ->
  evt usegs (ubt_loop4_post L s t T N lo BC OL SL MC R sp gp tp F fc m0)
      (MS (ul4R L T node x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz BT_L4) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA DPA GC F16 F64 MI LAY MU WM STK LO BEL Rsp AL4 RT1 RT2 RN LFC LDL LHP LDP PQ RFC RDP RHL Hf Rnode RC RK RHM RE Ea0 ER.
  { exfalso. lia. }
  pose proof (dlay_ranges _ LAY) as (Rs & _). pose proof BEL as BEL0. below_open BEL0. unfold Z_PQ_STACK in LO.
  call (ul4_iter L s t T N HL HM node dsc lo FC DL HP DP BC OL SL MC f R).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact F16. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_PQ_STACK; lia. } 1:{ exact BEL. } 1:{ exact Rsp. }
  1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RE. } 1:{ exact Ea0. } 1:{ exact ER. }
  match goal with H : _ \/ _ |- _ => destruct H as [(-> & K & ER')|(-> & K & ER')] end.
  - match goal with HT : u8arr usegs ?mm T (u16s (avct ?fc' ?dl' N)), HA : u32arr usegs ?mm _ (av32 ?hp' 573), HD : u8arr usegs ?mm (dl_As L + 5308) (av8 ?dp' 573),
                     HG : rw_cells usegs ?mm (dl_As L + 5300) _, HS : stk usegs ?mm _ _, HF16 : rw_cells usegs ?mm (bv_unsigned sp + 16) _, HF64 : rw_cells usegs ?mm (bv_unsigned sp + 64) _
                     |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N (HL - 1) (HM - 2) (node + 1) dsc lo fc' dl' hp' dp' BC OL SL MC R m0);
        [exact HT| exact HA| exact HD| exact HG| exact HF16| exact HF64| eassumption| exact LAY| eassumption| eassumption| exact HS| unfold Z_PQ_STACK; exact LO| exact BEL| exact Rsp| exact AL4| exact RT1| exact RT2| exact RN
        | assumption| assumption| assumption| assumption| assumption| assumption| assumption| exact K| lia| lia| lia| lia| lia| exact RE| reflexivity| exact ER'] end.
  - replace (HL - 1) with 1 in * by lia.
    apply evt_done. unfold ubt_loop4_post. do 16 eexists.
    match goal with HT : u8arr usegs ?mm T (u16s (avct ?fc' ?dl' N)), HA : u32arr usegs ?mm _ (av32 ?hp' 573), HD : u8arr usegs ?mm (dl_As L + 5308) (av8 ?dp' 573),
                     HQ : forall i, 1 <= i <= 1 -> _, HS : stk usegs ?mm _ _ |- _ =>
      exists fc', dl', hp', dp', (HM - 2), (node + 1); eexists;
      split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact HS|]; split; [exact HT|]; split; [exact HA|]; split; [exact HD|]; split; [eassumption|];
      split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [apply HQ; lia|]; split; [assumption|]; split; [assumption|];
      split; [lia|]; split; [lia| exact ER'] end.
Qed.
End Z_tr_bt6.

Module Z_tr_bt11.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt19p.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_pq OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.


Lemma toff_mod4 : forall t, toff t mod 4 = 0. Proof. destruct t; reflexivity. Qed.
Lemma bt_desc_mod8 : forall t, bt_desc t mod 8 = 0. Proof. destruct t; reflexivity. Qed.

Lemma dlay_below_lower : forall L lo hi hi', dlay_below L lo hi -> hi' <= hi -> dlay_below L lo hi'.
Proof. unfold dlay_below. intros. lia. Qed.
Lemma STP_mod4 : forall t, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.STP t mod 4 = 0. Proof. destruct t; reflexivity. Qed.
Lemma srliw1 : forall c, 0 <= c < 65536 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 c) 1) = c / 2 ^ 1.
Proof.
  intros c Hc. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. apply Z_dkit.bv_swrap32_id. change (2 ^ 1) with 2. Z.div_mod_to_equations. lia.
Qed.

Lemma frame_split4 : forall m A j16 v1 v2 v3 v4 v5 v6 j40 rest,
  rw_cells usegs m A (CB 16 j16 :: C8 v1 :: C8 v2 :: C8 v3 :: C8 v4 :: C8 v5 :: C8 v6 :: CB 40 j40 :: rest) ->
  exists j8 j32, rw_cells usegs m A [CB 16 j16] /\ rw_cells usegs m (A + 16) [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6]
                 /\ rw_cells usegs m (A + 64) [CB 8 j8] /\ rw_cells usegs m (A + 72) (CB 32 j32 :: rest).
Proof.
  intros m A j16 v1 v2 v3 v4 v5 v6 j40 rest H.
  apply (rw_cells_split_CB usegs m A [CB 16 j16; C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6] 40 j40 rest [8; 32]%nat) in H; [|reflexivity].
  cbn [mk_CB_cells app] in H.
  exists (firstn 8 j40), (firstn 32 (skipn 8 j40)).
  destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.rw_cells_split2 m A [CB 16 j16] _ (A + 16) H ltac:(reflexivity)) as [H0 H1].
  destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.rw_cells_split2 m (A + 16) [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6] _ (A + 64) H1 ltac:(cbn; lia)) as [H1' H2].
  destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.rw_cells_split2 m (A + 64) [CB 8 (firstn 8 j40)] _ (A + 72) H2 ltac:(cbn; lia)) as [H2' H3].
  split; [exact H0|]. split; [exact H1'|]. split; [exact H2'| exact H3].
Qed.

Lemma frame_join4 : forall m A j0 mc v1 v2 v3 v4 v5 v6 h nc c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13,
  rw_cells usegs m A [CB 8 j0; C8 mc] -> rw_cells usegs m (A + 16) [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6] ->
  rw_cells usegs m (A + 64) [C8 h] ->
  rw_cells usegs m (A + 72) [CB 32 nc; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  rw_cells usegs m A [CB 8 j0; C8 mc; C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 h;
                      CB 32 nc; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13].
Proof.
  intros until c13. intros H0 H1 H2 H3.
  pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.rw_cells_join2 m (A + 64) [C8 h] _ (A + 72) H2 H3 ltac:(cbn; lia)) as H23.
  pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.rw_cells_join2 m (A + 16) [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6] _ (A + 64) H1 H23 ltac:(cbn; lia)) as H123.
  exact (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.rw_cells_join2 m A [CB 8 j0; C8 mc] _ (A + 16) H0 H123 ltac:(cbn; lia)).
Qed.

Tactic Notation "callx" uconstr(SPEC) "drop" ne_hyp_list(HS) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | clear HS; post_call segs m ]
  end.
Ltac name_groups A Hh D G :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : u8arr usegs mm _ (u16s (avct _ _ _)) |- _ => rename H into A end;
    match goal with H : u32arr usegs mm _ _ |- _ => rename H into Hh end;
    match goal with H : u8arr usegs mm _ (av8 _ _) |- _ => rename H into D end;
    match goal with H : rw_cells usegs mm (dl_As _ + 5300) _ |- _ => rename H into G end
  end.

Lemma bt_front : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc lo : Z) (hh g0 g1 g2 g3 g4 : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct (tree_fc s t) (tree_dl s t) N)) -> u32arr usegs m (dl_As L + 3008) (av32 (ds_heap s) 573) ->
  u8arr usegs m (dl_As L + 5308) (av8 (ds_depth s) 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 (ds_bl_count s) 16)) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz (ds_heap_len s)); C4 (wz (ds_heap_max s))] ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s (ds_opt_len s) (ds_static_len s) g0 g1 g2 g3 g4) ->
  rw_cells usegs m dsc [C8 (wz T); C4 (wz (max_code s t)); CB 4 hh; C8 (wz (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.SDA t))] ->
  mem_inv usegs m -> relro_clean m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_BT_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  bt_safe s t -> T = dl_As L + toff t -> N = tsize t -> dsc = dl_As L + bt_desc t ->
  arr_len (tree_fc s t) = N -> arr_len (tree_dl s t) = N -> arr_len (ds_heap s) = 573 -> arr_len (ds_depth s) = 573 -> arr_len (ds_bl_count s) = 16 ->
  a0 = wz (dl_As L) -> a1 = wz dsc ->
  evt usegs (bt_mid_post L s t T N dsc lo hh ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz Z_BUILD_TREE) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA BLC GC GD Gdsc MI RC LAY STK LO AL BEL SAFE ET EN Edsc LFC LDL LHP LDP LBC -> ->.
  unfold Z_BUILD_TREE. unfold Z_BT_STACK in LO.
  pose proof (munch_refl (WBT L T N dsc lo sp) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. clear Rw Rp Rh Rb Bw Bp Bh Bb.
  assert (BsK : dl_As L + 5968 <= 0x10000 \/ 0x5e000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & X); exact X).
  assert (ALs : dl_As L mod 16 = 0) by (destruct (lo_s _ LAY) as (_ & X & _); exact X).
  pose proof (toff_tsize t) as Rtt. pose proof (toff_mod4 t) as Rt4. pose proof (bt_desc_mod8 t) as Rd8.
  pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.elems_range t) as RE. pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.tsize_elems t) as EN2.
  assert (Rdsc : 2904 <= bt_desc t <= 2952) by (destruct t; cbn; lia).
  assert (RML : 7 <= sd_max_length t <= 15 /\ 0 <= sd_extra_base t <= 257) by (destruct t; cbn; unfold MAX_BITS, MAX_BL_BITS, LITERALS; lia).
  pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.SDA_range t) as RSDA. pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.SDA_al8 t) as ASDA. pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.STP_range t) as RSTP. pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.XP_range t) as RXP.
  destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt19p.safe_s0 s t SAFE) as (RFC0 & ROL0 & RSL0). rewrite <- EN in RFC0.
  pose proof (avct_zlength (tree_fc s t) (tree_dl s t) N ltac:(lia)) as LCT. pose proof (av32_zlength (ds_heap s) 573 ltac:(lia)) as L32.
  pose proof (av8_zlength (ds_depth s) 573 ltac:(lia)) as L8. pose proof (av16_zlength (ds_bl_count s) 16 ltac:(lia)) as L16.
  unfold bD_cells in GD.
  pose proof (conj ARR (conj HPA (conj DPA (conj BLC GD)))) as BIG. clear ARR HPA DPA BLC GD.
  pose proof (munch_refl [(bv_unsigned sp + -208, bv_unsigned sp); (dl_As L + 5300, dl_As L + 5308)] m) as MUp.
  carve_frame 208%nat STK.
  zstep.
  do 13 zstep.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -208)) = bv_unsigned sp + -208) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  uwalk 0x1ca1c BT_TRAP. at_pc 0x1ca1c.

  pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.sdesc_relro t _ (relro_clean_munch _ _ _ RC MU ltac:(cbn [disjoint_from]; unfold RELRO_LO, RELRO_HI; lia))) as Gsd. unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.sd_cells in Gsd.
  zs2. zs2. clear Gsd.
  uwalk 0x1ca5c BT_TRAP. at_pc 0x1ca5c.

  zstep. br_false.
  uwalk 0x1ca9c BT_TRAP. at_pc 0x1ca9c. zstep.

  destruct BIG as (ARR & HPA & DPA & BLC & GD).
  lazymatch type of MUp with munch ?W ?ma ?mb =>
    apply (u8arr_transport usegs W ma mb) in ARR; [| exact MUp| exact WM| cbn [disjoint_from]; lia];
    apply (u32arr_transport usegs W ma mb) in HPA; [| exact MUp| exact WM| cbn [disjoint_from]; lia];
    apply (u8arr_transport usegs W ma mb) in DPA; [| exact MUp| exact WM| cbn [disjoint_from]; lia];
    apply (u8arr_transport usegs W ma mb) in BLC; [| exact MUp| exact WM| cbn [disjoint_from]; lia];
    apply (rw_cells_transport usegs W ma mb) in GD; [| exact MUp| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
  clear MUp.
  rewrite (zb_lxor_ones (dl_As L + 3008)) by lia. rewrite (zb_lxor_ones (dl_As L + 5308)) by lia.
  rewrite (zb_lxor_ones T) in FR by lia.
  assert (ALT : T mod 4 = 0) by (rewrite ET; Z.div_mod_to_equations; lia).
  rewrite (land1_mod2 T) in FR by (Z.div_mod_to_equations; lia).
  reg_as (T + 2) (T + 4 * 0 + 2). reg_as 2 (4 * 0 + 2).
  lazymatch type of FR with rw_cells _ ?mm ?A _ => destruct (frame_split4 _ _ _ _ _ _ _ _ _ _ _ FR) as (j8 & j32 & F0 & F1 & F2 & F3); clear FR end.
  replace (bv_unsigned sp + -208 + 16) with (bv_unsigned sp + -192) in F1 by lia.
  replace (bv_unsigned sp + -208 + 64) with (bv_unsigned sp + -144) in F2 by lia.
  replace (bv_unsigned sp + -208 + 72) with (bv_unsigned sp + -136) in F3 by lia.

  name_term R1 ER1 (L1 t (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt19p.btX0 s t) 0 (-1)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    callx (ubt_loop1 (Z.to_nat (sd_elems t) - 1) L s t T N (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.STP t) dsc (tree_fc s t) (ds_bl_count s) 573 (ds_opt_len s) (ds_static_len s) (max_code s t) R1 mm
                    (tree_dl s t) (ds_heap s) 0 (ds_depth s) 0 (-1)) drop ARR HPA DPA GC LCT L32 L8 end.
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ rewrite ESP. replace (bv_unsigned sp + -208 + 16) with (bv_unsigned sp + -192) by lia. exact F1. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ exact ALT. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact RFC0. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt19p.btX0 in ER1. exact ER1. }

  match goal with H : R1 = (bt_upd _ _ _ ?dl1 ?hp1 ?hl1 _ ?dp1 _ _ _ _, ?mc1) |- _ =>
    rename H into ER1';
    assert (E1 : build_tree_loop1 (Z.to_nat (sd_elems t)) (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt19p.btX0 s t) t (sd_elems t) 0 (-1) = (bt_upd s t (tree_fc s t) dl1 hp1 hl1 573 dp1 (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t), mc1))
      by (rewrite <- ER1', ER1; unfold L1; rewrite Z.sub_0_r; reflexivity);
    clear ER1 ER1';
    pose proof (avct_zlength (tree_fc s t) dl1 N ltac:(lia)) as LCT1; pose proof (av32_zlength hp1 573 ltac:(lia)) as L32_1; pose proof (av8_zlength dp1 573 ltac:(lia)) as L8_1 end.
  name_groups ARR1 HPA1 DPA1 GC1.
  lazymatch type of E1 with _ = (?X1, ?mc1) => name_term R2 ER2 (build_tree_loop2 2 X1 t mc1) end.
  lazymatch type of E1 with _ = (bt_upd _ _ _ ?dl1 ?hp1 ?hl1 _ ?dp1 _ _ _ _, ?mc1) =>
    callx (ubt_loop2 L s t T N hl1 mc1 (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.STP t) dsc 573 (ds_opt_len s) (ds_static_len s) (max_code s t) (tree_fc s t) dl1 hp1 dp1 (ds_bl_count s) g0 g1 g2 g3 g4 R2)
      drop ARR1 HPA1 DPA1 GC1 GD LCT1 L32_1 L8_1 end.
  1:{ exact ARR1. } 1:{ exact HPA1. } 1:{ exact DPA1. } 1:{ exact GC1. } 1:{ exact GD. }
  1:{ match goal with HF : rw_cells usegs ?mm (bv_unsigned sp + -192) _ |- rw_cells usegs ?mm _ _ => rewrite ESP; replace (bv_unsigned sp + -208 + 16) with (bv_unsigned sp + -192) by lia; exact HF end. }
  1:{ eassumption. } 1:{ exact LAY. }
  1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ exact ALT. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact LFC. } 1:{ assumption. } 1:{ assumption. }
  1:{ apply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.stree_view_of. } 1:{ apply STP_mod4. } 1:{ lia. } 1:{ lia. } 1:{ exact ROL0. } 1:{ exact RSL0. }
  1:{ exact ER2. }

  match goal with H : R2 = (bt_upd _ _ ?fc2 ?dl1 ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) |- _ =>
    rename H into ER2'; pose proof ER2' as E2; rewrite ER2 in E2; clear ER2 ER2' R2;
    pose proof (avct_zlength fc2 dl1 N ltac:(lia)) as LCT2; pose proof (av32_zlength hp2 573 ltac:(lia)) as L32_2; pose proof (av8_zlength dp2 573 ltac:(lia)) as L8_2 end.
  match goal with HG : rw_cells usegs _ (dl_As L + 5881) (bD_cells _ _ _ _ _ _ _ _ _) |- _ => unfold bD_cells in HG; rename HG into GD2 end.
  destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt19p.safe_s3 s t SAFE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1 E2) as (PQ2 & RDP2 & RFC2 & S7). rewrite <- EN in PQ2, RFC2.
  unfold BT_L2X. zs2. reg_as (dl_As L + 2047 + 929) (dl_As L + 2976). zs2. zs2. zs2.

  zs2. lazymatch type of E2 with _ = (bt_upd _ _ _ _ _ ?hl2 _ _ _ _ _ _, _) => rewrite (srliw1 hl2) by lia; change (hl2 / 2 ^ 1) with (hl2 / 2) end.
  zs2. zs2.

  name_groups ARR2 HPA2 DPA2 GC2.
  lazymatch type of E2 with _ = (bt_upd _ _ ?fc2 ?dl1 ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) =>
    name_term R3 ER3 (build_tree_loop3 (Z.to_nat (hl2 / 2)) (bt_upd s t fc2 dl1 hp2 hl2 573 dp2 (ds_bl_count s) ol2 sl2 mc2) t (hl2 / 2));
    pose proof ER3 as ER3S; replace (Z.to_nat (hl2 / 2)) with (S (Z.to_nat (hl2 / 2) - 1)) in ER3S by lia end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of E2 with _ = (bt_upd _ _ ?fc2 ?dl1 ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) =>
    callx (ubt_loop3 (Z.to_nat (hl2 / 2) - 1) L s t T N hl2 573 (hl2 / 2) lo fc2 dl1 hp2 dp2 (ds_bl_count s) ol2 sl2 mc2 R3 mm) drop HPA2 DPA2 GC2 L32_2 end end.
  1:{ exact HPA2. } 1:{ exact DPA2. } 1:{ exact GC2. }
  1:{ eapply ct_readable_rw; [exact ARR2| lia| lia| cbn [disjoint_from]; lia]. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold Z_PQ_STACK. lia. } 1:{ apply (dlay_below_lower L lo (bv_unsigned sp)); [exact BEL| rewrite ESP; lia]. }
  1:{ exact ALT. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
  1:{ exact PQ2. } 1:{ exact RFC2. } 1:{ exact RDP2. } 1:{ lia. } 1:{ Z.div_mod_to_equations; lia. } 1:{ lia. } 1:{ reflexivity. } 1:{ exact ER3S. }
  rewrite ESP in *.

  match goal with H : R3 = bt_upd _ _ _ _ ?hp3 _ _ _ _ _ _ _ |- _ =>
    rename H into E3; clear ER3S; pose proof (av32_zlength hp3 573 ltac:(lia)) as L32_3 end.
  unfold ul3R. zs2. reg_as (dl_As L + 2047 + 961) (dl_As L + 3008). zs2. zs2. zs2. zs2. shl_norm. zs2.
  zs2. rewrite (zb_lxor_ones (dl_As L + 3008)) by lia. zs2.
  zs2. zs2. zs2. zs2. rewrite (zb_lxor_ones (dl_As L + 5308)) by lia.
  zs2. try reg_as (T + sd_elems t * 4 + 0) (T + sd_elems t * 4). zs2. try reg_as (sd_elems t + 0) (sd_elems t).

  name_groups ARR3 HPA3 DPA3 GC3.
  lazymatch type of E3 with R3 = ?X3 => name_term R4 ER4 (build_tree_loop4 573 X3 t (sd_elems t)) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of E3 with R3 = bt_upd _ _ ?fc2 ?dl1 ?hp3 ?hl2 _ ?dp2 _ ?ol2 ?sl2 ?mc2 =>
    callx (ubt_loop4 573 L s t T N hl2 573 (sd_elems t) dsc lo fc2 dl1 hp3 dp2 (ds_bl_count s) ol2 sl2 mc2 R4 mm) drop ARR3 HPA3 DPA3 GC3 LCT2 L8_2 L32_3 end end.
  1:{ exact ARR3. } 1:{ exact HPA3. } 1:{ exact DPA3. } 1:{ exact GC3. }
  1:{ match goal with HF : rw_cells usegs ?mm (bv_unsigned sp + -192) _ |- rw_cells usegs ?mm _ _ => rewrite ESP; replace (bv_unsigned sp + -208 + 16) with (bv_unsigned sp + -192) by lia; exact HF end. }
  1:{ match goal with HF : rw_cells usegs ?mm (bv_unsigned sp + -144) _ |- rw_cells usegs ?mm _ _ => rewrite ESP; replace (bv_unsigned sp + -208 + 64) with (bv_unsigned sp + -144) by lia; exact HF end. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ rewrite ESP. assumption. } 1:{ rewrite ESP. unfold Z_PQ_STACK. lia. } 1:{ apply (dlay_below_lower L lo (bv_unsigned sp)); [exact BEL| rewrite ESP; lia]. } 1:{ rewrite ESP. lia. }
  1:{ exact ALT. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. }
  1:{ assumption. } 1:{ exact RFC2. } 1:{ exact RDP2. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ reflexivity. } 1:{ exact ER4. }
  rewrite ESP in *.

  match goal with H : R4 = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ _ _ _ |- _ =>
    rename H into ER4'; pose proof ER4' as E4; rewrite ER4 in E4; clear ER4 ER4';
    pose proof (avct_zlength fc4 dl4 N ltac:(lia)) as LCT4; pose proof (av32_zlength hp4 573 ltac:(lia)) as L32_4; pose proof (av8_zlength dp4 573 ltac:(lia)) as L8_4 end.
  lazymatch type of E4 with _ = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ ?ol2 ?sl2 ?mc2 =>
    destruct (S7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E3 E4 ltac:(assumption) ltac:(lia)) as (RHP7 & RDL7 & OK1 & OK23 & LEN15) end.
  rewrite <- EN in RHP7, RDL7. clear S7.
  pose proof E3 as E3x. rewrite ER3 in E3x.
  pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt19p.build_tree_flat s t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1 E2 E3x E4) as EBT.
  pose proof (relro_clean_munch _ _ _ RC MU ltac:(cbn [disjoint_from]; unfold RELRO_LO, RELRO_HI; lia)) as RC'.

  match goal with HF0 : rw_cells usegs ?mm (bv_unsigned sp + -208) _, HF1 : rw_cells usegs ?mm (bv_unsigned sp + -192) _,
                   HF2 : rw_cells usegs ?mm (bv_unsigned sp + -144) _, HF3 : rw_cells usegs ?mm (bv_unsigned sp + -136) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    replace (bv_unsigned sp + -192) with (bv_unsigned sp + -208 + 16) in HF1 by lia;
    replace (bv_unsigned sp + -144) with (bv_unsigned sp + -208 + 64) in HF2 by lia;
    replace (bv_unsigned sp + -136) with (bv_unsigned sp + -208 + 72) in HF3 by lia;
    pose proof (frame_join4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HF0 HF1 HF2 HF3) as FRJ; clear HF0 HF1 HF2 HF3 end.

  unfold ul4R.
  apply evt_done. unfold bt_mid_post.
  lazymatch type of FRJ with rw_cells _ ?mm _ (CB 8 ?j0 :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 32 ?nc :: _) =>
  lazymatch type of GD2 with rw_cells _ _ _ [CB 7 ?k0; _; _; _; _; CB 4 ?k1; _; _; _; _; _; CB 2 ?k2; _; CB 4 ?k3; _; _; CB 4 ?k4; _] =>
  lazymatch type of E4 with _ = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ ?ol2 ?sl2 ?mc2 =>
    do 24 eexists; exists fc4, dl4, hp4, dp4, hm4, mc2, ol2, sl2, k0, k1, k2, k3, k4, j0, nc; exists mm end end end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact RC'|].
  split; [assumption|]. split; [exact FRJ|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact BLC|]. split; [eassumption|]. split; [exact GD2|]. split; [eassumption|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [lia|]. split; [assumption|]. split; [lia|].
  split; [exact RHP7|]. split; [exact RDL7|]. split; [assumption|]. split; [lia|]. split; [lia|].
  split; [exact OK1|]. split; [exact OK23|]. split; [exact LEN15| exact EBT].


Qed.
End Z_tr_bt11.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.

Module Z_tr_bt16.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt14 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt16.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition GC_HEAD : Z := 0x1d2b8.
Local Notation ONES := 18446744073709551615.

Lemma uncl_write : forall m A w0 nc i (w : word) v,
  u8arr usegs m A (u16s (ncl w0 nc)) -> 1 <= i < 16 -> arr_len nc = 16 -> le2 w = le2 (wz v) ->
  u8arr usegs (write_to_mem m (wa (A + 2 * i)) (le2 w)) A (u16s (ncl w0 (arr_set nc i v))).
Proof.
  intros m A w0 nc i w v ARR Hi Hn E.
  assert (EQ : u16s (ncl w0 (arr_set nc i v)) = u16s (upd (ncl w0 nc) (Z.to_nat i) w)).
  { unfold ncl. rewrite <- av16_upd by lia. rewrite (upd_comm (av16 nc 16) (Z.to_nat i) 0%nat) by lia. apply u16s_upd_le2. symmetry. exact E. }
  rewrite EQ. apply (u16arr_write usegs); [exact ARR|]. rewrite ncl_length. lia.
Qed.

Ltac unc_store ARR w0 nc A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok usegs _ A (ncl w0 nc) idx (wa (A + 2 * idx)) ARR ltac:(rewrite ncl_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (uncl_write m0 A w0 nc idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "LNC" in pose proof (ncl_zlength w0 (arr_set nc idx v)) as LN;
      let LA := fresh "LNB" in pose proof (arr_len_set nc idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Definition ugcR (T n mc : Z) (sp : word) (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz n) (wz (bv_unsigned sp + 72)) (wz 16) (wz (ONES - (bv_unsigned sp + 72))) (wz 2147483647) (wz 1) a6 a7
      s2 s3 s4 s5 (wz T) s7 s8 s9 s10 s11 t3 (wz mc) t5 t6.

Definition ugc_brl_post (T n mc v : Z) (sp a6 : word)
    (ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a7 m',
    ms' = MS (ugcR T n mc sp ra gp tp t0 t1 (wz v) s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1d30c) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Lemma ugc_brl : forall (d : nat) (T n mc c r l : Z) (sp a6 t2 : word)
    (ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv usegs m -> Z.of_nat d = l - 1 -> 1 <= l <= 15 -> 0 <= c < 65536 -> res_ok r l ->
  evt usegs (ugc_brl_post T n mc (brl c r l) sp a6 ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 F fc m)
      (MS (ugcR T n mc sp ra gp tp (wz c) (wz (l + 1)) t2 s0 s1 a6 (wz r) s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1d2f4) fc None m (seg_rom usegs)).
Proof.
  induction d as [|d IH]; intros until m; intros MI Ed Rl Rc RO.
  - assert (l = 1) by lia. subst l.
    pose proof (res_ok_lor c r 1 ltac:(lia) RO) as RB. pose proof (res_ok_bound r 1 ltac:(lia) RO) as Rr.
    unfold ugcR. zs2. zs2. zs2. zs2. shl_norm. zs2. rewrite srliw1 by lia. zstep. br_cases K; [exfalso; lia|].
    rewrite land1_mod, (Z.lor_comm r). rewrite <- (brl_last c r) by lia.
    apply evt_done. unfold ugc_brl_post, ugcR. do 4 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
  - pose proof (res_ok_lor c r l ltac:(lia) RO) as RB. pose proof (res_ok_bound r l ltac:(lia) RO) as Rr. pose proof (res_ok_step c r l ltac:(lia) RO) as RO'.
    pose proof (brl_step c r l ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as ES. change (2 ^ 1) with 2 in ES, RO'.
    unfold ugcR. zs2. zs2. zs2. zs2. shl_norm. zs2. rewrite srliw1 by lia. zstep. br_cases K; [|exfalso; lia].
    rewrite land1_mod. change (2 ^ 1) with 2. rewrite (Z.lor_comm r). reg_as l (l - 1 + 1). rewrite ES.
    eapply evt_mono; [eapply (IH T n mc (c / 2) (Z.lor (c mod 2) r * 2) (l - 1)); [exact MI| lia| lia| Z.div_mod_to_equations; lia| exact RO']|].
    intros ms' H. exact H.
Qed.

Notation uWgc T N sp := [(T%Z, (T + 4 * N)%Z); (bv_unsigned sp + 72, bv_unsigned sp + 104)] (only parsing).

Definition ugc_iter_post (T N n mc : Z) (w0 : word) (FC' DL nc' : arr) (sp : word)
    (ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a6 a7 t3 pcx m',
    ms' = MS (ugcR T (n + 1) mc sp ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (uWgc T N sp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL N)) /\ u8arr usegs m' (bv_unsigned sp + 72) (u16s (ncl w0 nc'))
    /\ ((pcx = 0x1d2b8 /\ n + 1 <= mc) \/ (pcx = 0x1d320 /\ n = mc)).

Ltac ugc_latch MU WM ARR NCA :=
  let K3 := fresh "K3" in
  ustep BT_TRAP; zs2; zs2; zstep; br_cases K3;
  apply evt_done; unfold ugc_iter_post, ugcR; do 8 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [eassumption|]);
  (split; [exact ARR|]); (split; [exact NCA|]); first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].

Lemma ugc_iter : forall (T N n mc : Z) (w0 : word) (FC DL nc : arr) (sp : word)
    (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u8arr usegs m (bv_unsigned sp + 72) (u16s (ncl w0 nc)) ->
  rw_cells usegs m (bv_unsigned sp + 48) [C8 (wz (ONES - T))] -> mem_inv usegs m ->
  0 < T -> T + 4 * N <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len nc = 16 ->
  0 <= n <= mc -> mc < N -> 0 <= arr_get DL n <= 15 -> (forall k, 1 <= k <= 15 -> 0 <= arr_get nc k < 65536) ->
  evt usegs (ugc_iter_post T N n mc w0
               (if arr_get DL n =? 0 then FC else arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) DL
               (if arr_get DL n =? 0 then nc else arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1)))
               sp ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (ugcR T n mc sp ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1d2b8) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR NCA CT MI RT0 SEP RSP RN LFC LDL LNC Rn Rmc Rl RNC.
  pose proof (munch_refl (uWgc T N sp) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (ncl_zlength w0 nc) as LNCZ.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + 72)) = bv_unsigned sp + 72) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  pose proof (u16arr_read usegs m T (avct FC DL N) (2 * n + 1) _ (wa (T + n * 4 + 2)) ARR (avct_nth_dl FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDl.
  unfold ugcR. zs2. shl_norm. zs2. ustep BT_TRAP. zs2. zs2. rewrite zx16_small by lia. zstep. br_cases K.
  -
    rewrite (proj2 (Z.eqb_eq _ 0) K).
    ugc_latch MU WM ARR NCA.
  - rewrite (proj2 (Z.eqb_neq _ 0) K).
    set (len := arr_get DL n) in *.
    pose proof (RNC len ltac:(lia)) as Rc.
    pose proof (u16arr_read usegs m _ (ncl w0 nc) len _ (wa (bv_unsigned sp + 72 + len * 2)) NCA (ncl_nth w0 nc len ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDc.
    ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. zs2. rewrite zx16_small by lia. zs2.
    unc_store NCA w0 nc (bv_unsigned sp + 72) len (wrap16 (arr_get nc len + 1)) ltac:(apply le2_wrap16; reflexivity).
    zs2.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (ugc_brl (Z.to_nat (len - 1)) T n mc (arr_get nc len) 0 len sp) end.
    1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ exact Rc. } 1:{ apply res_ok_0. lia. }
    rewrite <- bi_reverse_brl by lia.
    unfold ugcR.
    ct_store_fc ARR FC DL N T n (wrap16 (bi_reverse (arr_get nc len) len)) ltac:(apply le2_wrap16; reflexivity).

    ugc_latch MU WM ARR NCA.
Qed.

Definition ugc_loop_post (s : deflate_state) (t : tree_id) (T N mc : Z) (w0 : word) (DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state) (sp : word)
    (ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a6 a7 t3 FC' nc' m',
    ms' = MS (ugcR T (mc + 1) mc sp ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1d320) fc None m' (seg_rom usegs)
    /\ munch (uWgc T N sp) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL N)) /\ u8arr usegs m' (bv_unsigned sp + 72) (u16s (ncl w0 nc'))
    /\ R = bt_upd s t FC' DL HP HL HM DP BC OL SL MC /\ arr_len FC' = N.

Lemma ugc_loop : forall (f : nat) (s : deflate_state) (t : tree_id) (T N n mc : Z) (w0 : word) (FC DL nc HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (sp ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u8arr usegs m (bv_unsigned sp + 72) (u16s (ncl w0 nc)) ->
  rw_cells usegs m (bv_unsigned sp + 48) [C8 (wz (ONES - T))] -> mem_inv usegs m ->
  munch (uWgc T N sp) m0 m -> wmono usegs m0 m ->
  0 < T -> T + 4 * N <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len nc = 16 ->
  Z.of_nat f = mc + 1 - n -> 0 <= n <= mc -> mc < N -> (forall i, 0 <= i <= mc -> 0 <= arr_get DL i <= 15) -> (forall k, 1 <= k <= 15 -> 0 <= arr_get nc k < 65536) ->
  R = gen_codes_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t nc mc n ->
  evt usegs (ugc_loop_post s t T N mc w0 DL HP HL HM DP BC OL SL MC R sp ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m0)
      (MS (ugcR T n mc sp ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1d2b8) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR NCA CT MI MU WM RT0 SEP RSP RN LFC LDL LNC Ef Rn Rmc RDL RNC ER.
  { exfalso. lia. }
  pose proof (gc2_model' s t FC DL HP HL HM DP BC OL SL MC f nc mc n R ER ltac:(lia)) as ER'. clear ER.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (ncl_zlength w0 nc) as LNCZ.
  set (FC' := if arr_get DL n =? 0 then FC else arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) in *.
  set (nc' := if arr_get DL n =? 0 then nc else arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1))) in *.
  assert (LFC' : arr_len FC' = N) by (subst FC'; destruct (arr_get DL n =? 0); [exact LFC| rewrite arr_len_set; exact LFC]).
  assert (LNC' : arr_len nc' = 16) by (subst nc'; destruct (arr_get DL n =? 0); [exact LNC| rewrite arr_len_set; exact LNC]).
  assert (RNC' : forall k, 1 <= k <= 15 -> 0 <= arr_get nc' k < 65536).
  { intros k Hk. subst nc'. destruct (arr_get DL n =? 0); [apply RNC; exact Hk|].
    destruct (Z.eq_dec (arr_get DL n) k) as [<-|NE]; [rewrite arr_get_set_same by (pose proof (RDL n ltac:(lia)); lia); apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RNC; exact Hk]. }
  pose proof (avct_zlength FC' DL N ltac:(lia)) as LCT'. pose proof (ncl_zlength w0 nc') as LNCZ'.
  call (ugc_iter T N n mc w0 FC DL nc sp).
  1:{ exact ARR. } 1:{ exact NCA. } 1:{ exact CT. } 1:{ exact MI. } 1:{ exact RT0. } 1:{ exact SEP. } 1:{ exact RSP. } 1:{ exact RN. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LNC. }
  1:{ exact Rn. } 1:{ exact Rmc. } 1:{ apply RDL. lia. } 1:{ exact RNC. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - match goal with HC : rw_cells usegs ?mm (bv_unsigned sp + 48) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH s t T N (n + 1) mc w0 FC' DL nc' HP HL HM DP BC OL SL MC R m0);
        [eassumption| eassumption| exact HC| eassumption| exact MU| exact WM| exact RT0| exact SEP| exact RSP| exact RN| exact LFC'| exact LDL| exact LNC'| lia| lia| exact Rmc| exact RDL| exact RNC'| exact ER'] end.
  - rewrite gc2_out in ER' by lia. subst n.
    apply evt_done. unfold ugc_loop_post. do 6 eexists. exists FC', nc'. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER'| exact LFC'].
Qed.
End Z_tr_bt16.

Module Z_tr_bt17.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt14 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt16 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt16.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.


Lemma uncl_intro : forall m A j0 blc (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : word),
  rw_cells usegs m A [CB 2 j0; C2 r1; C2 r2; C2 r3; C2 r4; C2 r5; C2 r6; C2 r7; C2 r8; C2 r9; C2 r10; C2 r11; C2 r12; C2 r13; C2 r14; C2 r15] ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get blc i < 65536) ->
  eqm (bv_unsigned r1) (gcode (arr_get blc) 1) -> eqm (bv_unsigned r2) (gcode (arr_get blc) 2) -> eqm (bv_unsigned r3) (gcode (arr_get blc) 3) ->
  eqm (bv_unsigned r4) (gcode (arr_get blc) 4) -> eqm (bv_unsigned r5) (gcode (arr_get blc) 5) -> eqm (bv_unsigned r6) (gcode (arr_get blc) 6) ->
  eqm (bv_unsigned r7) (gcode (arr_get blc) 7) -> eqm (bv_unsigned r8) (gcode (arr_get blc) 8) -> eqm (bv_unsigned r9) (gcode (arr_get blc) 9) ->
  eqm (bv_unsigned r10) (gcode (arr_get blc) 10) -> eqm (bv_unsigned r11) (gcode (arr_get blc) 11) -> eqm (bv_unsigned r12) (gcode (arr_get blc) 12) ->
  eqm (bv_unsigned r13) (gcode (arr_get blc) 13) -> eqm (bv_unsigned r14) (gcode (arr_get blc) 14) -> eqm (bv_unsigned r15) (gcode (arr_get blc) 15) ->
  exists w0, u8arr usegs m A (u16s (ncl w0 (NC blc))).
Proof.
  intros until r15. intros FR RB E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15.
  destruct FR as [[WF BY] WR]. cbn [cells_wf cell_wf] in WF. destruct WF as [Lj _].
  destruct (le2_of_bytes j0 Lj) as [w0 Ew]. exists w0.
  cbn [cells_bytes cbytes app] in BY. cbn [cells_size csize Nat.add] in WR.
  unfold ncl, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview.av16. rewrite Z_tr_bt17.zseq_16. cbn [map upd u16s].
  rewrite Ew.
  rewrite <- (le2_eqm_NC blc r1 1 RB ltac:(lia) E1), <- (le2_eqm_NC blc r2 2 RB ltac:(lia) E2), <- (le2_eqm_NC blc r3 3 RB ltac:(lia) E3),
          <- (le2_eqm_NC blc r4 4 RB ltac:(lia) E4), <- (le2_eqm_NC blc r5 5 RB ltac:(lia) E5), <- (le2_eqm_NC blc r6 6 RB ltac:(lia) E6),
          <- (le2_eqm_NC blc r7 7 RB ltac:(lia) E7), <- (le2_eqm_NC blc r8 8 RB ltac:(lia) E8), <- (le2_eqm_NC blc r9 9 RB ltac:(lia) E9),
          <- (le2_eqm_NC blc r10 10 RB ltac:(lia) E10), <- (le2_eqm_NC blc r11 11 RB ltac:(lia) E11), <- (le2_eqm_NC blc r12 12 RB ltac:(lia) E12),
          <- (le2_eqm_NC blc r13 13 RB ltac:(lia) E13), <- (le2_eqm_NC blc r14 14 RB ltac:(lia) E14), <- (le2_eqm_NC blc r15 15 RB ltac:(lia) E15).
  split.
  - destruct j0 as [|x [|y [|z l]]]; try discriminate. cbn [app] in BY |- *. exact BY.
  - rewrite !length_app, !length_le2, Lj. cbn [Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact WR.
Qed.


Definition uncR (L : dlay) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 s10 s11 t3 t4 t5 t6.

Definition unc_phase_post (L : dlay) (BC : arr) (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7 w0 m',
    ms' = MS (uncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1d290) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp + 72, bv_unsigned sp + 104)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' (bv_unsigned sp + 72) (u16s (ncl w0 (NC BC))).

Ltac eqmk := cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm_go.
Lemma uzseq_16 : zseq 16 = [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]. Proof. reflexivity. Qed.

Lemma unc_phase : forall (L : dlay) (BC : arr) (junk : list byte)
    (a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> rw_cells usegs m (bv_unsigned sp + 72) [CB 32 junk] -> mem_inv usegs m -> dlay_ok L ->
  arr_len BC = 16 -> (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  evt usegs (unc_phase_post L BC ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (uncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1d1a4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros BLC FR MI LAY LBC RBC SEP RSP.
  pose proof (munch_refl [(bv_unsigned sp + 72, bv_unsigned sp + 104)] m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY.
  pose proof (RBC 0 ltac:(lia)) as R0. pose proof (RBC 1 ltac:(lia)) as R1. pose proof (RBC 2 ltac:(lia)) as R2. pose proof (RBC 3 ltac:(lia)) as R3.
  pose proof (RBC 4 ltac:(lia)) as R4. pose proof (RBC 5 ltac:(lia)) as R5. pose proof (RBC 6 ltac:(lia)) as R6. pose proof (RBC 7 ltac:(lia)) as R7.
  pose proof (RBC 8 ltac:(lia)) as R8. pose proof (RBC 9 ltac:(lia)) as R9. pose proof (RBC 10 ltac:(lia)) as R10. pose proof (RBC 11 ltac:(lia)) as R11.
  pose proof (RBC 12 ltac:(lia)) as R12. pose proof (RBC 13 ltac:(lia)) as R13. pose proof (RBC 14 ltac:(lia)) as R14.
  apply u16arr_to_cells in BLC. unfold av16 in BLC. rewrite uzseq_16 in BLC. cbn [map c2s] in BLC.
  unfold uncR.
  zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. rewrite !zx16_small by lia.
  zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep. zstep.
  zs2.
  zs2. zs2. zs2. zs2. rewrite !zx16_small by lia.
  zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep. zstep.
  zs2.
  zs2. zs2. zs2.
  zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep. zstep.
  zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep.
  match goal with FRf : rw_cells usegs ?mm (bv_unsigned sp + 72) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (uncl_intro _ _ _ BC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRf RBC ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk)
                ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk)) as [w0 NCA] end.
  apply evt_done. unfold unc_phase_post, uncR. do 8 eexists. exists w0. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact NCA].
Qed.


Definition ugcs_post (s : deflate_state) (t : tree_id) (L : dlay) (T N mc : Z) (DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 FC' junk' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz T) s7 (wz (dl_As L + 2976)) s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1d320) fc None m' (seg_rom usegs)
    /\ munch (uWgc T N sp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL N)) /\ rw_cells usegs m' (bv_unsigned sp + 72) [CB 32 junk']
    /\ R = bt_upd s t FC' DL HP HL HM DP BC OL SL MC /\ arr_len FC' = N.

Lemma uncl_cb32 : forall m A w0 nc, u8arr usegs m A (u16s (ncl w0 nc)) -> rw_cells usegs m A [CB 32 (u16s (ncl w0 nc))].
Proof. intros m A w0 nc H. apply rw_cells_of_u8arr in H. rewrite u16s_length, ncl_length in H. exact H. Qed.

Lemma ugcs_phase : forall (s : deflate_state) (t : tree_id) (L : dlay) (T N mc : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (junk : list byte)
    (a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> rw_cells usegs m (bv_unsigned sp + 72) [CB 32 junk] ->
  rw_cells usegs m (bv_unsigned sp + 8) [C8 (wz mc)] -> rw_cells usegs m (bv_unsigned sp + 24) [C8 (wz 0)] -> rw_cells usegs m (bv_unsigned sp + 48) [C8 (wz (ONES - T))] ->
  mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N ->
  arr_len BC = 16 -> (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  -1 <= mc < N -> (forall i, 0 <= i <= mc -> 0 <= arr_get DL i <= 15) ->
  R = gen_codes (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t mc ->
  evt usegs (ugcs_post s t L T N mc DL HP HL HM DP BC OL SL MC R ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s9 s10 s11 t5 t6 F fc m)
      (MS (uncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 (wz T) s7 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1d1a4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR BLC FR F8 F24 F48 MI LAY RT1 RT2 RN LFC LDL LBC RBC SEP RSP Rmc RDL ER.
  pose proof LAY as LAY0. lay_open LAY0.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  unfold gen_codes in ER. rewrite bt_bl_count in ER. change (gen_codes_loop1 16 BC (arr_make (MAX_BITS + 1) 0) 0 1) with (NC BC) in ER.
  pose proof (munch_refl (uWgc T N sp) m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + 72)) = bv_unsigned sp + 72) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  call (unc_phase L BC junk).
  1:{ exact BLC. } 1:{ exact FR. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact LBC. } 1:{ exact RBC. } 1:{ exact SEP. } 1:{ exact RSP. }
  unfold uncR. zs2. zstep. br_cases K.
  -
    replace (mc + 1) with 0 in ER by lia. cbn [Z.to_nat] in ER. rewrite loop2_0 in ER.
    apply evt_done. unfold ugcs_post. do 13 eexists. exists FC. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [apply uncl_cb32; eassumption|]. split; [exact ER| exact LFC].
  - zs2. ustep BT_TRAP. zs2. zs2. zs2. zs2. zs2. zs2.
    rewrite (zb_lxor_ones (bv_unsigned sp + 72)) by lia.
    destruct (NC_spec BC RBC) as [LNC _].
    lazymatch goal with HN : u8arr usegs ?mm (bv_unsigned sp + 72) (u16s (ncl ?w0 (NC BC))) |- evt _ _ (MS _ _ _ _ _ ?mm' _) =>
      call (ugc_loop (Z.to_nat (mc + 1)) s t T N 0 mc w0 FC DL (NC BC) HP HL HM DP BC OL SL MC R mm' sp) end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ lia. } 1:{ lia. } 1:{ exact RSP. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LNC. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RDL. } 1:{ intros k Hk. apply NC_range; [exact RBC| exact Hk]. }
    1:{ exact ER. }
    unfold ugcR. apply evt_done. unfold ugcs_post. do 13 eexists.
    match goal with HT : u8arr usegs ?mm T (u16s (avct ?fc' DL N)) |- _ => exists fc' end. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [apply uncl_cb32; eassumption|]. split; assumption.
Qed.
End Z_tr_bt17.


Module Z_tr_bt18.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.Z_tr_bt12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt14.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_pq OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.


Definition UGB_PRE2 : Z := 0x1cd9c.

Definition ugb_pre1_post (L : dlay) (t : tree_id) (T hm dsc mc : Z) (HP : arr)
    (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s4 s5 s6 s7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) (wz (sd_max_length t)) (wz (STP t)) (wz (XP t)) (wz (sd_extra_base t)) a6 a7
                  s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz (dl_As L + 5912)) s11 t3 t4 t5 t6)
             F (wz UGB_PRE2) fc None m' (seg_rom usegs)
    /\ munch [(dl_As L + 3008, dl_As L + 5308)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u32arr usegs m' (dl_As L + 3008) (av32 (arr_set HP hm (arr_get HP 1)) 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)].

Lemma ugb_pre1 : forall (L : dlay) (t : tree_id) (T hm dsc mc : Z) (HP : arr) (hh : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> rw_cells usegs m (dl_As L + 5300) [C4 (wz 1); C4 (wz (hm + 1))] ->
  rw_cells usegs m dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz (SDA t))] -> rw_cells usegs m (SDA t) (sd_cells t) ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) -> rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] ->
  mem_inv usegs m -> dlay_ok L ->
  arr_len HP = 573 -> 0 <= hm <= 570 -> 0 <= arr_get HP 1 < 2^31 -> -1 <= mc < 2^31 -> dsc = dl_As L + bt_desc t ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  evt usegs (ugb_pre1_post L t T hm dsc mc HP ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s4 s5 s6 s7 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) s10 s11 t3 t4 t5 t6)
          F (wz BT_PARTB) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA GC Gdsc Gsd F16 F64 MI LAY LHP Rhm Rh1 Rmc Edsc SEP RSP.
  pose proof (munch_refl [(dl_As L + 3008, dl_As L + 5308)] m) as MU. pose proof (wmono_refl usegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (Bs : dl_As L + 5968 <= 0x10000 \/ 0x5e000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & Bs); exact Bs).
  pose proof (bt_desc_range t) as Rdsc. pose proof (SDA_range t) as RSDA. pose proof (SDA_al8 t) as ASDA. pose proof (STP_range t) as RSTP. pose proof (XP_range t) as RXP.
  assert (RE : 0 <= sd_extra_base t <= 257 /\ 19 <= sd_elems t <= 286 /\ 7 <= sd_max_length t <= 15)
    by (destruct t; cbn [sd_extra_base sd_elems sd_max_length]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; lia).
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  pose proof (u32arr_read usegs m _ (av32 HP 573) 1 _ (wa (dl_As L + 2976 + 36)) HPA (av32_nth HP 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD1.
  unfold BT_PARTB, sd_cells in *.
  zs2. zs2. ustep BT_TRAP.
  zs2. zs2. zstep. ustep BT_TRAP.
  zs2. shl_norm. zs2. ustep BT_TRAP.
  zs2. zs2. zs2. shl_norm. zs2.
  h32_store HPA HP 573 (dl_As L + 3008) hm (arr_get HP 1) ltac:(reflexivity).
  uwalk UGB_PRE2 BT_TRAP.
  apply evt_done. unfold ugb_pre1_post. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA| exact GC].
Qed.


Lemma av16_fill0 : forall BC, arr_len BC = 16 -> av16 (arr_fill BC 0 16 0) 16 = repeat (wz 0) 16.
Proof.
  intros BC LBC. unfold av16. rewrite uzseq_16. cbn [map]. rewrite !arr_get_fill. unfold arr_inb. rewrite !LBC. cbn. reflexivity.
Qed.
Lemma blc_zero_range : forall BC i, arr_len BC = 16 -> 0 <= i < 16 -> 0 <= arr_get (arr_fill BC 0 16 0) i < 65536.
Proof.
  intros BC i LBC Hi. rewrite arr_get_fill. unfold arr_inb. rewrite LBC.
  replace ((0 <=? i) && (i <? 0 + Z.max 0 16) && ((0 <=? i) && (i <? 16))) with true; [lia|].
  symmetry. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
Qed.

Lemma shl32_shr30 : forall h, 0 <= h < 2^30 -> Z.shiftr (Z.shiftl h 32 mod 18446744073709551616) 30 = 4 * h.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (split; [lia|]; change 18446744073709551616 with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^32) with (4 * 2^30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Definition ugb_pre2_post (L : dlay) (t : tree_id) (T N hm mc : Z) (FC DL BC : arr) (n1 : Z)
    (ra sp gp tp s0 s1 s2 s4 s5 s6 s7 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t6 m',
    ms' = MS (ugbR L T (hm + 1) 0 mc (sd_max_length t) (STP t) (XP t) (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 (wz (dl_As L + 5300)) s11 t6)
             F (wz GB1_HEAD) fc None m' (seg_rom usegs)
    /\ munch [(T, T + 4 * N); (dl_As L + 2976, dl_As L + 3008)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC (arr_set DL n1 (wrap16 0)) N))
    /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 (arr_fill BC 0 16 0) 16)).

Lemma ugb_pre2 : forall (L : dlay) (t : tree_id) (T N hm mc : Z) (FC DL HP7 BC : arr) (n1 : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s4 s5 s6 s7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP7 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)] ->
  rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] ->
  mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> T mod 4 = 0 -> arr_len FC = N -> arr_len DL = N -> arr_len HP7 = 573 -> arr_len BC = 16 ->
  0 <= hm <= 570 -> n1 = arr_get HP7 hm -> 0 <= n1 < N -> -1 <= mc < 2^31 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  evt usegs (ugb_pre2_post L t T N hm mc FC DL BC n1 ra sp gp tp s0 s1 s2 s4 s5 s6 s7 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) (wz (sd_max_length t)) (wz (STP t)) (wz (XP t)) (wz (sd_extra_base t)) a6 a7
                  s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz (dl_As L + 5912)) s11 t3 t4 t5 t6)
          F (wz UGB_PRE2) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA BLC GC F64 MI LAY RT1 RT2 RN AT LFC LDL LHP LBC Rhm En1 Rn1 Rmc SEP RSP.
  pose proof (munch_refl [(T, T + 4 * N); (dl_As L + 2976, dl_As L + 3008)] m) as MU. pose proof (wmono_refl usegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  pose proof (STP_range t) as RSTP. pose proof (XP_range t) as RXP.
  assert (RE : 0 <= sd_extra_base t <= 257 /\ 19 <= sd_elems t <= 286 /\ 7 <= sd_max_length t <= 15)
    by (destruct t; cbn [sd_extra_base sd_elems sd_max_length]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; lia).
  pose proof (av32_zlength HP7 573 ltac:(lia)) as L32. pose proof (avct_zlength FC DL N ltac:(lia)) as LCT.
  change (u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16))) with (u16arr usegs m (dl_As L + 2976) (av16 BC 16)) in BLC.
  apply u16arr_to_cells in BLC. unfold av16 in BLC. rewrite uzseq_16 in BLC. cbn [map c2s] in BLC.
  unfold UGB_PRE2. do 15 (zstep; zstep; gN).
  zs2. zstep. zstep. ustep BT_TRAP.
  zs2. shl_norm. zs2. ustep BT_TRAP. zs2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read usegs mm _ (av32 HP7 573) hm _ (wa (dl_As L + 3008 + 4 * hm)) HPA (av32_nth HP7 573 hm ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDh;
    rewrite <- En1 in RDh end.
  zs2. zs2. shl_norm. zs2.
  do 11 ustep BT_TRAP.
  ct_store_dl ARR FC DL N T n1 (wrap16 0) ltac:(reflexivity).
  zs2. zs2. ustep BT_TRAP. zs2. zstep. br_false.
  zs2. zs2. zs2. zs2. zstep. br_false. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zstep.
  rewrite (zb_lxor_ones T) by lia. rewrite (zb_lxor_ones (dl_As L + 2976)) by lia.
  rewrite (Z.mod_small (hm + 1) 4294967296) by lia. rewrite shl32_shr30 by lia.
  apply evt_done. unfold ugb_pre2_post, ugbR, GB1_HEAD. do 2 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|].
  change (u8arr usegs ?mq ?A (u16s ?ws)) with (u16arr usegs mq A ws). rewrite av16_fill0 by exact LBC.
  apply u16arr_of_cells. cbn [repeat c2s]. exact BLC.
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

Lemma shl32_shr31 : forall x, 0 <= x < 2^30 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 31 = x * 2.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (split; [lia|]; change 18446744073709551616 with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^32) with (2 * 2^31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma shl32_shr32 : forall x, 0 <= x < 2^30 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (split; [lia|]; change 18446744073709551616 with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.
End Z_tr_bt18.


Module Z_tr_bt14.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.Z_tr_bt12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt14.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_scan1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.


Definition GL2_HEAD : Z := 0x1d094.
Definition GL2_FIND : Z := 0x1d098.
Definition GL2_FOUND : Z := 0x1d0c0.
Definition GL2_EXIT : Z := 0x1d100.

Definition ugl2R (L : dlay) (T ovf mc ML : Z) (sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) (wz ML) (wz ML) (wz (dl_As L + 2976 + ML * 2)) (wz 16) (wz (ONES - (dl_As L + 2976))) (wz ovf)
      s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 (wz (dl_As L + 5912)) s11 t3 t4 (wz 16) t6.

Lemma ugl2_find : forall (d : nat) (P : machine_state -> Prop) (L : dlay) (T ovf mc ML b B1 r : Z) (BC : arr)
    (sp ra gp tp t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv usegs m -> dlay_ok L ->
  Z.of_nat d = b - r -> 0 <= r -> b < 15 -> (forall j, r < j <= b -> arr_get BC j = 0) -> arr_get BC r <> 0 -> 0 <= arr_get BC r < 65536 -> B1 = b + 1 ->
  evt usegs P (MS (ugl2R L T ovf mc ML sp ra gp tp (wz (r + 1)) (wz r) (wz (dl_As L + 2976 + r * 2)) s0 s1 s2 s4 s5 s6 s7 s9 s11 (wz (arr_get BC r)) t4 t6) F (wz 0x1d0c0) fc None m (seg_rom usegs)) ->
  evt usegs P (MS (ugl2R L T ovf mc ML sp ra gp tp (wz B1) t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6) F (wz 0x1d098) fc None m (seg_rom usegs)).
Proof.
  induction d as [|d IH]; intros until m; intros BLC MI LAY Ed Rr Rb Z0 NZ RV EB1 K; subst B1.
  - assert (b = r) by lia. subst b.
    pose proof LAY as LAY0. lay_open LAY0. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
    pose proof (u16arr_read usegs m _ (av16 BC 16) r _ (wa (dl_As L + 2976 + r * 2)) BLC (av16_nth BC 16 r ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDb.
    unfold ugl2R. zs2. try rewrite (bv_swrap32_id (r + 1 + -1)) by lia. reg_as (r + 1 + -1) r. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. rewrite zx16_small by lia.
    zstep. br_cases K2; [|exfalso; lia].
    exact K.
  - pose proof LAY as LAY0. lay_open LAY0. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
    pose proof (u16arr_read usegs m _ (av16 BC 16) b _ (wa (dl_As L + 2976 + b * 2)) BLC (av16_nth BC 16 b ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDb.
    rewrite (Z0 b ltac:(lia)) in RDb.
    unfold ugl2R. zs2. try rewrite (bv_swrap32_id (b + 1 + -1)) by lia. reg_as (b + 1 + -1) b. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. rewrite zx16_small by lia.
    zstep. br_cases K2; [exfalso; lia|].
    zs2. try rewrite (bv_swrap32_id (b + 1 + -2)) by lia. zs2. zstep. br_true.
    eapply (IH P L T ovf mc ML (b - 1) b r BC); [exact BLC| exact MI| exact LAY| lia| exact Rr| lia| intros j Hj; apply Z0; lia| exact NZ| exact RV| lia| exact K].
Qed.

Notation uWg2 L := [(dl_As L + 2976, dl_As L + 3008)] (only parsing).

Definition ugl2_iter_post (L : dlay) (T ovf mc ML : Z) (BC' : arr)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 t3 pcx m',
    ms' = MS (ugl2R L T (ovf - 2) mc ML sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (uWg2 L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ ((pcx = 0x1d094 /\ 0 < ovf - 2) \/ (pcx = 0x1d100 /\ ovf - 2 <= 0)).

Lemma ugl2_iter : forall (L : dlay) (T ovf mc ML r : Z) (BC : arr)
    (sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv usegs m -> dlay_ok L -> arr_len BC = 16 ->
  7 <= ML <= 15 -> 1 <= ovf <= 573 -> 0 <= r <= ML - 1 -> (forall j, r < j <= ML - 1 -> arr_get BC j = 0) -> arr_get BC r <> 0 ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  evt usegs (ugl2_iter_post L T ovf mc ML (bl_adj ML BC r) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t4 t6 F fc m)
      (MS (ugl2R L T ovf mc ML sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6) F (wz 0x1d094) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros BLC MI LAY LBC RML Ro Rr Z0 NZ RBC.
  pose proof (munch_refl (uWg2 L) m) as MU. pose proof (wmono_refl usegs m) as WM. pose proof (RBC r ltac:(lia)) as RV.
  unfold ugl2R. zs2.
  eapply (ugl2_find (Z.to_nat (ML - 1 - r)) _ L T ovf mc ML (ML - 1) ML r BC); [exact BLC| exact MI| exact LAY| lia| lia| lia| exact Z0| exact NZ| exact RV| lia|].
  pose proof LAY as LAY0. lay_open LAY0. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  unfold ugl2R. zs2.
  ua16_store BLC BC 16 (dl_As L + 2976) r (wrap16 (arr_get BC r - 1)) ltac:(apply le2_wrap16; lia).
  set (BC1 := arr_set BC r (wrap16 (arr_get BC r - 1))) in *.
  assert (RBC1 : forall i, 0 <= i < 16 -> 0 <= arr_get BC1 i < 65536) by (subst BC1; apply arr_set_range16; exact RBC).
  match goal with H : u8arr usegs ?mm _ (u16s (av16 BC1 16)) |- _ =>
    pose proof (u16arr_read usegs mm _ (av16 BC1 16) (r + 1) _ (wa (dl_As L + 2976 + (r + 1) * 2)) H (av16_nth BC1 16 (r + 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD1 end.
  ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. zs2.
  ua16_store BLC BC1 16 (dl_As L + 2976) (r + 1) (wrap16 (arr_get BC1 (r + 1) + 2)) ltac:(apply le2_add_sx16).
  set (BC2 := arr_set BC1 (r + 1) (wrap16 (arr_get BC1 (r + 1) + 2))) in *.
  assert (RBC2 : forall i, 0 <= i < 16 -> 0 <= arr_get BC2 i < 65536) by (subst BC2; apply arr_set_range16; exact RBC1).
  match goal with H : u8arr usegs ?mm _ (u16s (av16 BC2 16)) |- _ =>
    pose proof (u16arr_read usegs mm _ (av16 BC2 16) ML _ (wa (dl_As L + 2976 + ML * 2)) H (av16_nth BC2 16 ML ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD2 end.
  zs2. zs2. zs2. try rewrite (bv_swrap32_id (ovf + -2)) by lia.
  ua16_store BLC BC2 16 (dl_As L + 2976) ML (wrap16 (arr_get BC2 ML - 1)) ltac:(replace (arr_get BC2 ML - 1) with (arr_get BC2 ML + -1) by lia; apply le2_add_sx16).
  ustep BT_TRAP. zs2. zstep.
  assert (EBA : bl_adj ML BC r = arr_set BC2 ML (wrap16 (arr_get BC2 ML - 1))) by reflexivity.
  br_cases K; reg_as (ovf + -2) (ovf - 2).
  - apply evt_done. unfold ugl2_iter_post, ugl2R. do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [rewrite EBA; exact BLC|]. first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].
  - apply evt_done. unfold ugl2_iter_post, ugl2R. do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [rewrite EBA; exact BLC|]. first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].
Qed.

Definition ugl2_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T mc ML : Z) (FC DL HP : arr) (HL HM : Z) (DP : arr) (OL SL : Z) (R : deflate_state)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 t3 BC' ovf' m',
    ms' = MS (ugl2R L T ovf' mc ML sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6) F (wz 0x1d100) fc None m' (seg_rom usegs)
    /\ munch (uWg2 L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ R = bt_upd s t FC DL HP HL HM DP BC' OL SL mc
    /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536).

Lemma ugl2_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T ovf mc ML : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL : Z) (R : deflate_state) (m0 : mem)
    (sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv usegs m -> dlay_ok L -> munch (uWg2 L) m0 m -> wmono usegs m0 m -> arr_len BC = 16 ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  7 <= ML <= 15 -> 1 <= ovf <= 573 -> ovf <= 2 * Z.of_nat f ->
  R = gen_bitlen_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) ML ovf ->
  gb2_ok ML f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) ovf ->
  evt usegs (ugl2_loop_post L s t T mc ML FC DL HP HL HM DP OL SL R sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t4 t6 F fc m0)
      (MS (ugl2R L T ovf mc ML sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6) F (wz 0x1d094) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros BLC MI LAY MU WM LBC RBC RML Ro Hf ER OK.
  { exfalso. lia. }
  pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  rewrite (GL2_step t ML) in ER. destruct (gb2_ok_step t ML f s FC DL HP HL HM DP BC OL SL mc ovf OK) as [Hr OK'].
  set (r := gen_bitlen_find (Z.to_nat ML) (bt_upd s t FC DL HP HL HM DP BC OL SL mc) (ML - 1)) in *.
  destruct (find_char t s FC DL HP HL HM DP BC OL SL mc ML r eq_refl Hr ltac:(lia)) as (Hr1 & Z0 & NZ).
  call (ugl2_iter L T ovf mc ML r BC sp).
  1:{ exact BLC. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact LBC. } 1:{ exact RML. } 1:{ exact Ro. } 1:{ lia. } 1:{ exact Z0. } 1:{ exact NZ. } 1:{ exact RBC. }
  pose proof (av16_zlength (bl_adj ML BC r) 16 ltac:(lia)) as L16'.
  match goal with H : _ \/ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - rewrite (proj2 (Z.ltb_lt 0 (ovf - 2)) K) in ER.
    eapply (IH L s t T (ovf - 2) mc ML FC DL HP HL HM DP (bl_adj ML BC r) OL SL R m0);
      [eassumption| eassumption| exact LAY| exact MU| exact WM| rewrite bl_adj_len; exact LBC| apply bl_adj_range; exact RBC| exact RML| lia| lia| exact ER| apply OK'; exact K].
  - rewrite (proj2 (Z.ltb_ge 0 (ovf - 2))) in ER by lia.
    apply evt_done. unfold ugl2_loop_post. do 4 eexists. exists (bl_adj ML BC r), (ovf - 2). eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER|].
    split; [rewrite bl_adj_len; exact LBC| apply bl_adj_range; exact RBC].
Qed.
End Z_tr_bt14.

Module Z_tr_bt15.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.Z_tr_bt12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt14 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt15.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_scan1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt14.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.


Definition G3_OHEAD : Z := 0x1d120.
Definition G3_OLATCH : Z := 0x1d118.
Definition G3_IHEAD : Z := 0x1d13c.
Definition G3_ILATCH : Z := 0x1d134.
Definition G3_EXIT : Z := 0x1d1a4.

Definition ug3R (L : dlay) (T bits n h mc : Z) (sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) (wz 572) (wz bits) (wz h) (wz n) a6 a7
      s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 (wz (dl_As L + 5912)) s11 t3 t4 t5 t6.

Notation uWg3 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 5881, dl_As L + 5968)] (only parsing).

Definition ug3_trip_post (L : dlay) (s : deflate_state) (T N bits n' h mc : Z) (FC DL' : arr) (OL' SL : Z)
    (sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a6 a7 h0 h1 h2 h3 h4 pcx m',
    ms' = MS (ug3R L T bits n' (h - 1) mc sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (uWg3 L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ ((pcx = 0x1d13c /\ n' <> 0) \/ (pcx = 0x1d118 /\ n' = 0)).

Ltac ug3_latch n MU WM ARR GD :=
  let K3 := fresh "K3" in
  zs2; try (rewrite (bv_swrap32_id (n + -1)) by lia); reg_as (n + -1) (n - 1); zstep; br_cases K3;
  apply evt_done; unfold ug3_trip_post, ug3R, bD_cells; do 11 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [eassumption|]);
  (split; [exact ARR|]); (split; [close_cells GD|]); first [right; split; [reflexivity| lia] | left; split; [reflexivity| lia]].

Lemma ug3_trip : forall (L : dlay) (s : deflate_state) (T N bits n h mc m_ OL SL : Z) (FC DL HP : arr) (h0 h1 h2 h3 h4 : list byte)
    (sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv usegs m -> dlay_ok L -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 ->
  1 <= n < 65536 -> 1 <= h <= 573 -> m_ = arr_get HP (h - 1) -> 0 <= m_ < 573 -> -1 <= mc < N -> 1 <= bits <= 15 ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  evt usegs (ug3_trip_post L s T N bits (g3_n mc m_ n) h mc FC (g3_DL DL mc m_ bits) (g3_OL FC DL OL mc m_ bits) SL
               sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 F fc m)
      (MS (ug3R L T bits n h mc sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d13c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA GD MI LAY RT1 RT2 RN LFC LDL LHP Rn Rh Em Rm Rmc Rb RDL RFC ROL.
  pose proof (munch_refl (uWg3 L T N) m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY. unfold bD_cells in GD.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  pose proof (u32arr_read usegs m _ (av32 HP 573) (h - 1) _ (wa (dl_As L + 3008 + (h - 1) * 4)) HPA (av32_nth HP 573 (h - 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDm. rewrite <- Em in RDm.
  unfold ug3R. zs2. zs2. try rewrite (bv_swrap32_id (h + -1)) by lia. reg_as (h + -1) (h - 1). ustep BT_TRAP. ustep BT_TRAP. zs2. shl_norm. zs2. zs2.
  zstep. br_cases K.
  -
    assert (EDL : g3_DL DL mc m_ bits = DL) by (unfold g3_DL; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    assert (EOL : g3_OL FC DL OL mc m_ bits = OL) by (unfold g3_OL; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    assert (En' : g3_n mc m_ n = n) by (unfold g3_n; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    rewrite EDL, EOL, En'.
    apply evt_done. unfold ug3_trip_post, ug3R, bD_cells. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ARR|]. split; [exact GD|]. left. split; [reflexivity| lia].
  - assert (En' : g3_n mc m_ n = n - 1) by (unfold g3_n; rewrite (proj2 (Z.ltb_ge mc m_)) by lia; reflexivity). rewrite En'.
    pose proof (u16arr_read usegs m T (avct FC DL N) (2 * m_ + 1) _ (wa (T + m_ * 4 + 2)) ARR (avct_nth_dl FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDl.
    pose proof (u16arr_read usegs m T (avct FC DL N) (2 * m_) _ (wa (T + m_ * 4)) ARR (avct_nth_fc FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDf.
    pose proof (RDL m_ ltac:(lia)) as Rl. pose proof (RFC m_ ltac:(lia)) as Rf.
    zs2. shl_norm. zs2. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP.
    zs2. rewrite zx16_small by lia. zstep. br_cases K2.
    +
      assert (EDL : g3_DL DL mc m_ bits = DL) by (unfold g3_DL; rewrite (proj2 (Z.eqb_eq (arr_get DL m_) bits)) by lia; rewrite orb_true_r; reflexivity).
      assert (EOL : g3_OL FC DL OL mc m_ bits = OL) by (unfold g3_OL; rewrite (proj2 (Z.eqb_eq (arr_get DL m_) bits)) by lia; rewrite orb_true_r; reflexivity).
      rewrite EDL, EOL.
      ug3_latch n MU WM ARR GD.
    + zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zs2.
      rewrite wz_mulmod. zstep.
      ct_store_dl ARR FC DL N T m_ (wrap16 bits) ltac:(apply le2_wrap16; reflexivity).
      zs2.
      assert (NEb : (arr_get DL m_ =? bits) = false) by (apply Z.eqb_neq; lia).
      assert (EDL : g3_DL DL mc m_ bits = arr_set DL m_ (wrap16 bits)) by (unfold g3_DL; rewrite (proj2 (Z.ltb_ge mc m_)), NEb by lia; reflexivity).
      assert (EOL : g3_OL FC DL OL mc m_ bits = wrap64 (OL + (bits - arr_get DL m_) * arr_get FC m_)) by (unfold g3_OL; rewrite (proj2 (Z.ltb_ge mc m_)), NEb by lia; reflexivity).
      rewrite EDL, EOL.
      ug3_latch n MU WM ARR GD.
Qed.

Definition ug3i_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N bits mc : Z) (FC HP : arr) (HL HM : Z) (DP BC : arr) (SL : Z) (R : deflate_state * Z)
    (sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a6 a7 h0 h1 h2 h3 h4 DL' OL' h' m',
    ms' = MS (ug3R L T bits 0 h' mc sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d118) fc None m' (seg_rom usegs)
    /\ munch (uWg3 L T N) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ R = (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc, h')
    /\ arr_len DL' = N /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64 /\ 0 <= h' <= 573.

Lemma ug3i_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N bits n h mc OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R : deflate_state * Z) (m0 : mem)
    (sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv usegs m -> dlay_ok L -> munch (uWg3 L T N) m0 m -> wmono usegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 ->
  1 <= n < 65536 -> 0 <= h -> h < Z.of_nat f -> -1 <= mc < N -> 1 <= bits <= 15 ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  R = gen_bitlen_loop3i f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits n h ->
  gb3i_ok t mc f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) bits n h ->
  evt usegs (ug3i_loop_post L s t T N bits mc FC HP HL HM DP BC SL R sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 F fc m0)
      (MS (ug3R L T bits n h mc sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d13c) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA GD MI LAY MU WM RT1 RT2 RN LFC LDL LHP Rn Rh0 Hf Rmc Rb RDL RFC ROL ER OK.
  { exfalso. lia. }
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  destruct (g3i_ok_step' s t FC DL HP HL HM DP BC OL SL mc f bits n h (arr_get HP (h - 1)) OK ltac:(lia) eq_refl) as (Rh & Rm & OK').
  pose proof (g3i_model' s t FC DL HP HL HM DP BC OL SL mc f bits n h R (arr_get HP (h - 1)) ER ltac:(lia) eq_refl) as ER'. clear ER OK.
  set (m_ := arr_get HP (h - 1)) in *.
  pose proof (avct_zlength FC (g3_DL DL mc m_ bits) N ltac:(lia)) as LCT'.
  call (ug3_trip L s T N bits n h mc m_ OL SL FC DL HP h0 h1 h2 h3 h4 sp).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. }
  1:{ exact Rn. } 1:{ exact Rh. } 1:{ reflexivity. } 1:{ exact Rm. } 1:{ exact Rmc. } 1:{ exact Rb. } 1:{ exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. }
  match goal with H : _ \/ _ |- _ => destruct H as [(-> & K)|(-> & K)] end.
  - assert (Rn' : 1 <= g3_n mc m_ n < 65536) by (revert K; unfold g3_n; destruct (mc <? m_); lia).
    match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)), HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' SL ?g0 ?g1 ?g2 ?g3 ?g4) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N bits (g3_n mc m_ n) (h - 1) mc ol' SL FC (g3_DL DL mc m_ bits) HP HL HM DP BC g0 g1 g2 g3 g4 R m0);
        [exact HT| exact HPA| exact HG| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact RN| exact LFC| rewrite g3_DL_len; exact LDL| exact LHP
        | exact Rn'| lia| lia| exact Rmc| exact Rb| apply g3_DL_range; exact RDL| exact RFC| apply g3_OL_range; exact ROL| exact ER'| exact OK'] end.
  - rewrite K in ER'. rewrite GL3i_done in ER'.
    rewrite K.
    apply evt_done. unfold ug3i_loop_post. do 9 eexists. exists (g3_DL DL mc m_ bits), (g3_OL FC DL OL mc m_ bits), (h - 1). eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER'|].
    split; [rewrite g3_DL_len; exact LDL|]. split; [apply g3_DL_range; exact RDL|]. split; [apply g3_OL_range; exact ROL|]. lia.
Qed.

Definition ug3oR (L : dlay) (T bits h mc : Z) (sp ra gp tp t0 t1 t2 s0 s1 s2 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) (wz 572) (wz bits) (wz h) a5 a6 a7
      s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 (wz (dl_As L + 5912)) s11 t3 t4 t5 t6.

Definition ug3_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N mc : Z) (FC HP : arr) (HL HM : Z) (DP BC : arr) (SL : Z) (R : deflate_state)
    (sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a5 a6 a7 h0 h1 h2 h3 h4 DL' OL' h' m',
    ms' = MS (ug3oR L T 0 h' mc sp ra gp tp t0 t1 t2 s0 s1 s2 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d1a4) fc None m' (seg_rom usegs)
    /\ munch (uWg3 L T N) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ R = bt_upd s t FC DL' HP HL HM DP BC OL' SL mc
    /\ arr_len DL' = N /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64.

Lemma ug3_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N bits h mc OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R : deflate_state) (m0 : mem)
    (sp ra gp tp t0 t1 t2 s0 s1 s2 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv usegs m -> dlay_ok L -> munch (uWg3 L T N) m0 m -> wmono usegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  Z.of_nat f = bits -> 1 <= bits <= 15 -> 0 <= h <= 573 -> -1 <= mc < N ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  R = gen_bitlen_loop3 f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits h ->
  gb3_ok t mc f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) bits h ->
  evt usegs (ug3_loop_post L s t T N mc FC HP HL HM DP BC SL R sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 F fc m0)
      (MS (ug3oR L T bits h mc sp ra gp tp t0 t1 t2 s0 s1 s2 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d120) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA BLC GD MI LAY MU WM RT1 RT2 RN LFC LDL LHP LBC Ef Rb Rh Rmc RBC RDL RFC ROL ER OK.
  { exfalso. lia. }
  pose proof (g3_model s t FC DL HP HL HM DP BC OL SL mc f bits h R ER ltac:(lia)) as ER'.
  destruct (g3_ok_step s t FC DL HP HL HM DP BC OL SL mc f bits h OK ltac:(lia)) as [OKi OKo]. clear ER OK.
  assert (TAIL : forall (DL' : arr) (OL' h' : Z) (g0 g1 g2 g3 g4 : list byte) (b0 b1 b5 b6 b7 : word) (m' : mem),
    u8arr usegs m' T (u16s (avct FC DL' N)) -> u32arr usegs m' (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC 16)) ->
    rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL g0 g1 g2 g3 g4) -> mem_inv usegs m' -> munch (uWg3 L T N) m0 m' -> wmono usegs m0 m' ->
    arr_len DL' = N -> (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) -> 0 <= OL' < 2^64 -> 0 <= h' <= 573 ->
    R = gen_bitlen_loop3 f (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc) t mc (bits - 1) h' ->
    gb3_ok t mc f (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc) (bits - 1) h' ->
    evt usegs (ug3_loop_post L s t T N mc FC HP HL HM DP BC SL R sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 F fc m0)
      (MS (ug3oR L T bits h' mc sp ra gp tp b0 b1 t2 s0 s1 s2 b5 b6 b7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d118) fc None m' (seg_rom usegs))).
  { intros DL' OL' h' g0 g1 g2 g3 g4 b0 b1 b5 b6 b7 m' ARR' HPA' BLC' GD' MI' MU' WM' LDL' RDL' ROL' Rh' ER2 OK2.
    unfold ug3oR. zs2. zstep. br_cases K; reg_as (bits + -1) (bits - 1).
    - replace (bits - 1) with 0 in * by lia. rewrite GL3_done in ER2.
      apply evt_done. unfold ug3_loop_post, ug3oR. do 10 eexists. exists DL', OL', h'. eexists.
      split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ARR'|]. split; [exact GD'|]. split; [exact ER2|].
      split; [exact LDL'|]. split; [exact RDL'| exact ROL'].
    - eapply (IH L s t T N (bits - 1) h' mc OL' SL FC DL' HP HL HM DP BC g0 g1 g2 g3 g4 R m0);
        [exact ARR'| exact HPA'| exact BLC'| exact GD'| exact MI'| exact LAY| exact MU'| exact WM'| exact RT1| exact RT2| exact RN| exact LFC| exact LDL'| exact LHP| exact LBC
        | lia| lia| exact Rh'| exact Rmc| exact RBC| exact RDL'| exact RFC| exact ROL'| exact ER2| exact OK2]. }
  pose proof LAY as LAY0. lay_open LAY0.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  pose proof (u16arr_read usegs m _ (av16 BC 16) bits _ (wa (dl_As L + 2976 + bits * 2)) BLC (av16_nth BC 16 bits ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn.
  pose proof (RBC bits ltac:(lia)) as Rn.
  unfold ug3oR. zs2. shl_norm. zs2. zs2. rewrite zx16_small by lia. zstep. br_cases K.
  - call (ug3i_loop 574 L s t T N bits (arr_get BC bits) h mc OL SL FC DL HP HL HM DP BC h0 h1 h2 h3 h4
            (gen_bitlen_loop3i 574 (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits (arr_get BC bits) h) m sp).
    1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ lia. } 1:{ lia. } 1:{ change (Z.of_nat 574) with 574. lia. } 1:{ exact Rmc. } 1:{ exact Rb. } 1:{ exact RDL. } 1:{ exact RFC. }
    1:{ exact ROL. } 1:{ reflexivity. } 1:{ exact OKi. }
    match goal with E : gen_bitlen_loop3i 574 _ _ _ _ _ _ = (_, _) |- _ => rewrite E in ER', OKo end.
    unfold ug3R.
    match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)), HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' SL ?g0 ?g1 ?g2 ?g3 ?g4)
      |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (wz ?hh) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _) =>
      eapply (TAIL dl' ol' hh g0 g1 g2 g3 g4); [exact HT| eassumption| eassumption| exact HG| eassumption| exact MU| exact WM| assumption| assumption| assumption| lia| exact ER'| exact OKo] end.
  -
    rewrite K in ER', OKo. rewrite GL3i_done in ER', OKo.
    zs2.
    eapply (TAIL DL OL h h0 h1 h2 h3 h4); [exact ARR| exact HPA| exact BLC| exact GD| exact MI| exact MU| exact WM| exact LDL| exact RDL| exact ROL| exact Rh| exact ER'| exact OKo].
Qed.
End Z_tr_bt15.

Module Z_tr_bt18b.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.Z_tr_bt12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt14.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_pq OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt14 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt15 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt16 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt17 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt18.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.

Notation uWgb L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 2976, dl_As L + 3008); (dl_As L + 5881, dl_As L + 5968)] (only parsing).

Definition ugb_main_post (L : dlay) (s : deflate_state) (t : tree_id) (T N hm mc : Z) (FC HP : arr) (HL : Z) (DP : arr) (R : deflate_state)
    (ra sp gp tp s6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s11 t3 t4 t5 t6 DL' BC' OL' SL' g0 g1 g2 g3 g4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) a2 a3 a4 a5 a6 a7 s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 (wz (dl_As L + 5912)) s11 t3 t4 t5 t6)
             F (wz 0x1d1a4) fc None m' (seg_rom usegs)
    /\ munch (uWgb L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ R = bt_upd s t FC DL' HP HL hm DP BC' OL' SL' mc
    /\ arr_len DL' = N /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536) /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536)
    /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64.

Lemma ugb_main : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N hm mc stp xp OL SL : Z) (FC DL HP : arr) (HL : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R1 : deflate_state * Z) (R : deflate_state)
    (ra sp gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] ->
  mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp -> 0 < xp < 2^32 -> xp mod 4 = 0 -> stp mod 4 = 0 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= hm <= 570 -> -1 <= mc < sd_elems t -> (forall k, hm + 1 <= k < 573 -> 0 <= arr_get HP k < N) ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  R1 = gen_bitlen_loop1 573 (bt_upd s t FC DL HP HL hm DP BC OL SL mc) t mc (sd_extra_base t) (sd_max_length t) (hm + 1) 0 ->
  gb1_ok t mc 573 (bt_upd s t FC DL HP HL hm DP BC OL SL mc) (hm + 1) 0 ->
  (forall X10 ovf, R1 = (X10, ovf) -> ovf <> 0 ->
     gb2_ok (sd_max_length t) 573 X10 ovf /\ gb3_ok t mc (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) (sd_max_length t) 573) ->
  R = gb_tail t mc R1 ->
  evt usegs (ugb_main_post L s t T N hm mc FC HP HL DP R ra sp gp tp s6 F fc m)
      (MS (ugbR L T (hm + 1) 0 mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz GB1_HEAD) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA BLC GD F64 MI LAY RT1 RT2 EN LFC LDL LHP LBC XV SV Rxp Axp Astp SEP RSP Rhm Rmc RHP RBC RDL RFC ROL RSL ER1 OK1 OK23 ER.
  pose proof (munch_refl (uWgb L T N) m) as MU. pose proof (wmono_refl usegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (RE : sd_extra_base t <= 257 /\ 0 <= sd_extra_base t /\ 19 <= sd_elems t <= 286 /\ 7 <= sd_max_length t <= 15 /\ N = 2 * sd_elems t + 1)
    by (subst N; destruct t; cbn [sd_extra_base sd_elems sd_max_length tsize]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; lia).
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  unfold GB1_HEAD.
  call (ugb1_loop 573 L s t T N (hm + 1) 0 mc stp xp OL SL FC DL HP HL hm DP BC h0 h1 h2 h3 h4 R1 m).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact BLC. } 1:{ exact GD. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact EN. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LBC. } 1:{ exact XV. } 1:{ exact SV. }
  1:{ exact Rxp. } 1:{ exact Axp. } 1:{ exact Astp. } 1:{ exact SEP. } 1:{ exact RSP. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact RHP. } 1:{ exact RBC. } 1:{ exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. } 1:{ exact RSL. }
  1:{ exact ER1. } 1:{ exact OK1. }
  match goal with H : R1 = (bt_upd _ _ _ ?dl' _ _ _ _ ?bc' ?ol' ?sl' _, ?ovf') |- _ => rename H into ER1'; clear ER1 end.
  unfold ugbR. zstep. br_cases K.
  -
    lazymatch type of ER1' with R1 = (?X, ?o) => rewrite ER1' in ER; replace o with 0 in ER by lia; rewrite gb_tail_0 in ER end.
    apply evt_done. unfold ugb_main_post. do 21 eexists.
    match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)), HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                     HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' ?sl' ?g0 ?g1 ?g2 ?g3 ?g4) |- _ =>
      exists dl', bc', ol', sl', g0, g1, g2, g3, g4; eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HB|]; split; [exact HG|];
      split; [exact ER|] end.
    repeat (split; [assumption|]). assumption.
  -
    lazymatch type of ER1' with R1 = (?X, ?o) => destruct (OK23 X o ER1' ltac:(lia)) as [OK2 OK3]; rewrite ER1' in ER; rewrite (gb_tail_nz t mc X o) in ER by lia end.
    zs2. ustep BT_TRAP. zs2. ustep BT_TRAP. zs2. zstep. br_false.
    zs2. zs2. rewrite shl32_shr31 by lia. zstep. br_false. zs2. try rewrite shl32_shr32 by lia. try rewrite (Z.mod_small (sd_max_length t) 4294967296) by lia. zs2. zs2.
    lazymatch type of ER1' with R1 = (?X, ?o) => name_term R2 ER2 (gen_bitlen_loop2 573 X (sd_max_length t) o) end.
    match goal with HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)), HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'; pose proof (avct_zlength FC dl' N ltac:(lia)) as LCT' end.
    lazymatch type of ER1' with R1 = (bt_upd _ _ _ ?dl' _ _ _ _ ?bc' ?ol' ?sl' _, ?o) =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (ugl2_loop 573 L s t T o mc (sd_max_length t) FC dl' HP HL hm DP bc' ol' sl' R2 mm) end end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ assumption. } 1:{ assumption. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ER2. } 1:{ exact OK2. }
    match goal with H : R2 = bt_upd _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite H in ER, OK3; clear H ER2 end.
    unfold ugl2R. zstep. br_false. zs2. ustep BT_TRAP. zs2. zs2. zstep.
    match goal with HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'' end.
    lazymatch type of ER1' with R1 = (bt_upd _ _ _ ?dl' _ _ _ _ _ ?ol' ?sl' _, _) =>
    lazymatch goal with HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)), HG : rw_cells usegs ?mm' (dl_As L + 5881) (bD_cells L s _ _ ?g0 ?g1 ?g2 ?g3 ?g4)
      |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (ug3_loop (Z.to_nat (sd_max_length t)) L s t T N (sd_max_length t) 573 mc ol' sl' FC dl' HP HL hm DP bc' g0 g1 g2 g3 g4 R mm) end end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ assumption. } 1:{ exact LHP. } 1:{ assumption. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. } 1:{ assumption. } 1:{ exact RFC. } 1:{ assumption. } 1:{ exact ER. } 1:{ exact OK3. }
    unfold ug3oR. apply evt_done. unfold ugb_main_post. do 21 eexists.
    match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl'' N)), HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc'' 16)),
                     HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol'' ?sl'' ?g0 ?g1 ?g2 ?g3 ?g4) |- _ =>
      exists dl'', bc'', ol'', sl'', g0, g1, g2, g3, g4; eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HB|]; split; [exact HG|];
      split; [assumption|] end.
    repeat (split; [assumption|]). all: lia.
Qed.


Lemma XP_pos : forall t, 0 < XP t < 2 ^ 32. Proof. destruct t; cbn; lia. Qed.
Lemma XP_al4 : forall t, XP t mod 4 = 0. Proof. destruct t; reflexivity. Qed.
Lemma STP_al4 : forall t, STP t mod 4 = 0. Proof. destruct t; reflexivity. Qed.

Notation uWpB L T N sp := [(T%Z, (T + 4 * N)%Z); (dl_As L + 2976, dl_As L + 5308); (dl_As L + 5881, dl_As L + 5968); (bv_unsigned sp + 72, bv_unsigned sp + 104)] (only parsing).

Definition upartB_post (L : dlay) (s : deflate_state) (t : tree_id) (T N hm dsc mc : Z) (HP7 DP : arr) (hh : list byte) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) FC' DL' BC' OL' SL' g0 g1 g2 g3 g4 junk' m',
    ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz BT_EPI) fc None m' (seg_rom usegs)
    /\ munch (uWpB L T N sp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP7 573) /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)] /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ rw_cells usegs m' dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz (SDA t))] /\ rw_cells usegs m' (bv_unsigned sp + 72) [CB 32 junk']
    /\ R = bt_upd s t FC' DL' HP7 1 hm DP BC' OL' SL' mc /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len BC' = 16.

Lemma upartB : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N hm dsc mc OL SL : Z) (FC DL HP DP BC : arr) (hh h0 h1 h2 h3 h4 nc : list byte)
    (R : deflate_state)
    (x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  let HP7 := arr_set HP hm (arr_get HP 1) in
  let X7 := bt_upd s t FC DL HP7 1 hm DP BC OL SL mc in
  let X9 := bt_upd s t FC (arr_set DL (arr_get HP 1) (wrap16 0)) HP7 1 hm DP (arr_fill BC 0 16 0) OL SL mc in
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz 1); C4 (wz (hm + 1))] -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  rw_cells usegs m dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz (SDA t))] -> rw_cells usegs m (SDA t) (sd_cells t) ->
  rw_cells usegs m (bv_unsigned sp + 8) [C8 (wz mc)] -> rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) ->
  rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] -> rw_cells usegs m (bv_unsigned sp + 72) [CB 32 nc] ->
  mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> T mod 4 = 0 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  dsc = dl_As L + bt_desc t -> 0 <= hm <= 570 -> 0 <= arr_get HP 1 < N -> -1 <= mc < sd_elems t ->
  (forall k, hm + 1 <= k < 573 -> 0 <= arr_get HP7 k < N) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  gb1_ok t mc 573 X9 (hm + 1) 0 ->
  (forall X10 ovf, gen_bitlen_loop1 573 X9 t mc (sd_extra_base t) (sd_max_length t) (hm + 1) 0 = (X10, ovf) -> ovf <> 0 ->
     gb2_ok (sd_max_length t) 573 X10 ovf /\ gb3_ok t mc (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) (sd_max_length t) 573) ->
  (forall i, 0 <= i <= mc -> 0 <= Len (gen_bitlen X7 t) t i <= 15) ->
  R = gen_codes (gen_bitlen X7 t) t mc ->
  evt usegs (upartB_post L s t T N hm dsc mc HP7 DP hh R sp gp tp F fc m)
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz (dl_As L + 3008)) s4 s5 (wz T) s7 (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) s10 s11 t3 t4 t5 t6)
          F (wz BT_PARTB) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HP7 X7 X9 ARR HPA BLC GC GD Gdsc Gsd F8 F16 F64 F72 MI LAY RT1 RT2 EN AT LFC LDL LHP LBC Edsc Rhm Rh1 Rmc RHP RDL RFC ROL RSL SEP RSP
    OK1 OK23 LEN ER. subst HP7 X7 X9.
  pose proof (munch_refl (uWpB L T N sp) m) as MU. pose proof (wmono_refl usegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (Bs : dl_As L + 5968 <= 0x10000 \/ 0x5e000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & Bs); exact Bs).
  assert (RE : 19 <= sd_elems t <= 286 /\ N = 2 * sd_elems t + 1)
    by (subst N; destruct t; cbn [sd_elems tsize]; unfold L_CODES, D_CODES, BL_CODES; lia).
  pose proof (bt_desc_range t) as Rdsc. pose proof (SDA_range t) as RSDA.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  rewrite (gen_bitlen_flat s t FC DL (arr_set HP hm (arr_get HP 1)) 1 hm DP BC OL SL mc) in ER, LEN.
  rewrite (arr_get_set_same HP hm (arr_get HP 1)) in ER, LEN by lia.
  name_term R1 ER1 (gen_bitlen_loop1 573 (bt_upd s t FC (arr_set DL (arr_get HP 1) (wrap16 0)) (arr_set HP hm (arr_get HP 1)) 1 hm DP (arr_fill BC 0 16 0) OL SL mc) t mc
                       (sd_extra_base t) (sd_max_length t) (hm + 1) 0).
  name_term RB ERB (gb_tail t mc R1).
  unfold sd_cells in Gsd.
  call (ugb_pre1 L t T hm dsc mc HP hh).
  1:{ exact HPA. } 1:{ exact GC. } 1:{ exact Gdsc. } 1:{ exact Gsd. } 1:{ exact F16. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. }
  1:{ exact LHP. } 1:{ exact Rhm. } 1:{ lia. } 1:{ lia. } 1:{ exact Edsc. } 1:{ exact SEP. } 1:{ exact RSP. }
  pose proof (av32_zlength (arr_set HP hm (arr_get HP 1)) 573 ltac:(lia)) as L32'.
  unfold UGB_PRE2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (ugb_pre2 L t T N hm mc FC DL (arr_set HP hm (arr_get HP 1)) BC (arr_get HP 1)) end.
  1:{ exact ARR. } 1:{ eassumption. } 1:{ exact BLC. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact AT. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ rewrite arr_len_set. exact LHP. } 1:{ exact LBC. }
  1:{ exact Rhm. } 1:{ rewrite arr_get_set_same by lia. reflexivity. } 1:{ lia. } 1:{ lia. } 1:{ exact SEP. } 1:{ exact RSP. }
  pose proof (avct_zlength FC (arr_set DL (arr_get HP 1) (wrap16 0)) N ltac:(lia)) as LCT'. pose proof (av16_zlength (arr_fill BC 0 16 0) 16 ltac:(lia)) as L16'.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (ugb_main L s t T N hm mc (STP t) (XP t) OL SL FC (arr_set DL (arr_get HP 1) (wrap16 0)) (arr_set HP hm (arr_get HP 1)) 1 DP (arr_fill BC 0 16 0) h0 h1 h2 h3 h4 R1 RB) end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact GD. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact EN. } 1:{ exact LFC. } 1:{ rewrite arr_len_set. exact LDL. } 1:{ rewrite arr_len_set. exact LHP. } 1:{ rewrite arr_len_fill. exact LBC. }
  1:{ apply xbits_view_of. } 1:{ apply stree_view_n_of. } 1:{ apply XP_pos. } 1:{ apply XP_al4. } 1:{ apply STP_al4. } 1:{ exact SEP. } 1:{ exact RSP. }
  1:{ exact Rhm. } 1:{ exact Rmc. } 1:{ exact RHP. } 1:{ intros i Hi. apply blc_zero_range; [exact LBC| exact Hi]. }
  1:{ apply arr_set_range16. exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. } 1:{ exact RSL. }
  1:{ exact ER1. } 1:{ exact OK1. } 1:{ exact OK23. } 1:{ exact ERB. }
  match goal with H : RB = bt_upd _ _ _ ?dl' _ _ _ _ ?bc' _ _ _ |- _ => rewrite H in ER, LEN; clear H ERB;
    pose proof (avct_zlength FC dl' N ltac:(lia)) as LCT''; pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'' end.
  match goal with HG : rw_cells usegs _ (dl_As L + 5881) (bD_cells _ _ _ _ _ _ _ _ _) |- _ => unfold bD_cells in HG end.
  lazymatch goal with HF : rw_cells usegs ?mm (bv_unsigned sp + 16) (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
    destruct (proj1 (rw_cells_app_iff mm _ [c0] (c1 :: c2 :: c3 :: c4 :: rest)) HF) as [_ HF1];
    destruct (proj1 (rw_cells_app_iff mm _ [c1] (c2 :: c3 :: c4 :: rest)) HF1) as [F24 HF2]; clear HF1;
    destruct (proj1 (rw_cells_app_iff mm _ [c2; c3] (c4 :: rest)) HF2) as [_ HF3]; clear HF2;
    destruct (proj1 (rw_cells_app_iff mm _ [c4] rest) HF3) as [F48 _]; clear HF3;
    cbn [cells_size csize Nat.add] in F24, F48 end.
  change (Z.of_nat 8) with 8 in F24. change (Z.of_nat 8) with 8 in F48. change (Z.of_nat 16) with 16 in F48.
  lazymatch type of F24 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + 24) in F24 by lia end.
  lazymatch type of F48 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + 48) in F48 by lia end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of ER with R = gen_codes (bt_upd s t FC ?dl' ?hp' 1 hm DP ?bc' ?ol' ?sl' mc) t mc =>
    call (ugcs_phase s t L T N mc FC dl' hp' 1 hm DP bc' ol' sl' mc R nc) end end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact F8. } 1:{ exact F24. } 1:{ exact F48. } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ exact SEP. } 1:{ exact RSP. } 1:{ lia. }
  1:{ intros i Hi. pose proof (LEN i Hi) as Li. rewrite bt_Len in Li. exact Li. } 1:{ exact ER. }
  apply evt_done. unfold upartB_post. do 28 eexists.
  match goal with HT : u8arr usegs ?mm T (u16s (avct ?fc' ?dl' N)), HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                   HG : rw_cells usegs ?mm (dl_As L + 5881) [CB 7 ?g0; _; _; _; _; CB 4 ?g1; C8 (wz ?ol'); C8 (wz ?sl'); _; _; _; CB 2 ?g2; _; CB 4 ?g3; _; _; CB 4 ?g4; _],
                   HF : rw_cells usegs ?mm (bv_unsigned sp + 72) [CB 32 ?j] |- _ =>
    exists fc', dl', bc', ol', sl', g0, g1, g2, g3, g4, j; eexists;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [eassumption|]; split; [exact HB|];
    split; [eassumption|]; split; [exact HG|]; split; [eassumption|]; split; [exact HF|] end.
  repeat (split; [assumption|]). assumption.
Qed.
End Z_tr_bt18b.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_pq OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt11 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt17 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt18 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt19.Z_tr_bt18b OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.


Definition body_post (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc lo : Z) (hh : list byte) (R : deflate_state)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (FC' DL' HP' DP' BC' : arr) (OL' SL' hm mc : Z) (g0 g1 g2 g3 g4 : list byte) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch (WBT L T N dsc lo sp) m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u8arr usegs m' T (u16s (avct FC' DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)] /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ rw_cells usegs m' dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz (SDA t))]
    /\ R = bt_upd s t FC' DL' HP' 1 hm DP' BC' OL' SL' mc
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ arr_len BC' = 16.

Lemma build_tree_body : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc lo : Z) (hh g0 g1 g2 g3 g4 : list byte) (R : deflate_state)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct (tree_fc s t) (tree_dl s t) N)) -> u32arr usegs m (dl_As L + 3008) (av32 (ds_heap s) 573) ->
  u8arr usegs m (dl_As L + 5308) (av8 (ds_depth s) 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 (ds_bl_count s) 16)) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz (ds_heap_len s)); C4 (wz (ds_heap_max s))] ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s (ds_opt_len s) (ds_static_len s) g0 g1 g2 g3 g4) ->
  rw_cells usegs m dsc [C8 (wz T); C4 (wz (max_code s t)); CB 4 hh; C8 (wz (SDA t))] ->
  mem_inv usegs m -> relro_clean m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_BT_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  bt_safe s t -> T = dl_As L + toff t -> N = tsize t -> dsc = dl_As L + bt_desc t ->
  arr_len (tree_fc s t) = N -> arr_len (tree_dl s t) = N -> arr_len (ds_heap s) = 573 -> arr_len (ds_depth s) = 573 -> arr_len (ds_bl_count s) = 16 ->
  a0 = wz (dl_As L) -> a1 = wz dsc ->
  R = build_tree s t ->
  evt usegs (body_post L s t T N dsc lo hh R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz Z_BUILD_TREE) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA BLC GC GD Gdsc MI RC LAY STK LO AL BEL SAFE ET EN Edsc LFC LDL LHP LDP LBC Ea0 Ea1 ER0.
  pose proof (munch_refl (WBT L T N dsc lo sp) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. pose proof LO as LO0. unfold Z_BT_STACK in LO0.
  assert (BsK : dl_As L + 5968 <= 0x10000 \/ 0x5e000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & X); exact X).
  assert (ALs : dl_As L mod 16 = 0) by (destruct (lo_s _ LAY) as (_ & X & _); exact X).
  pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.elems_range t) as RE. pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.tsize_elems t) as EN2.
  assert (Rdsc : 2904 <= bt_desc t <= 2952) by (destruct t; cbn; lia).
  assert (Rtf : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ toff t mod 4 = 0) by (destruct t; cbn; lia).
  pose proof (SDA_range t) as RSDA.
  assert (AT4 : T mod 4 = 0) by (rewrite ET; clear - ALs Rtf; Z.div_mod_to_equations; lia).
  pose proof (avct_zlength (tree_fc s t) (tree_dl s t) N ltac:(lia)) as LCT. pose proof (av32_zlength (ds_heap s) 573 ltac:(lia)) as L32.
  pose proof (av8_zlength (ds_depth s) 573 ltac:(lia)) as L8. pose proof (av16_zlength (ds_bl_count s) 16 ltac:(lia)) as L16.
  call (bt_front L s t T N dsc lo hh g0 g1 g2 g3 g4).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact BLC. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact Gdsc. } 1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. }
  1:{ exact STK. } 1:{ exact LO. } 1:{ exact AL. } 1:{ exact BEL. } 1:{ exact SAFE. } 1:{ exact ET. } 1:{ exact EN. } 1:{ exact Edsc. }
  1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact LBC. } 1:{ exact Ea0. } 1:{ exact Ea1. }
  lazymatch goal with H : build_tree s t = _ |- _ => rewrite <- ER0 in H; rename H into ER end.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -208)) = bv_unsigned sp + -208) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  reg_as (bv_unsigned sp - 208) (bv_unsigned sp + -208).
  match goal with HS : stk usegs ?mm lo (bv_unsigned sp - 208), HF : rw_cells usegs ?mm (bv_unsigned sp - 208) _ |- _ =>
    replace (bv_unsigned sp - 208) with (bv_unsigned sp + -208) in HS by lia; replace (bv_unsigned sp - 208) with (bv_unsigned sp + -208) in HF by lia;
    rename HS into STK; rename HF into FR end.
  lazymatch type of FR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
    destruct (proj1 (rw_cells_app_iff mm A [c0] (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: rest)) FR) as [F0 FR1]; clear FR;
    destruct (proj1 (rw_cells_app_iff mm _ [c1] (c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: rest)) FR1) as [F8 FR2]; clear FR1;
    destruct (proj1 (rw_cells_app_iff mm _ [c2; c3; c4; c5; c6; c7] (c8 :: c9 :: rest)) FR2) as [F16 FR3]; clear FR2;
    destruct (proj1 (rw_cells_app_iff mm _ [c8] (c9 :: rest)) FR3) as [F64 FR4]; clear FR3;
    destruct (proj1 (rw_cells_app_iff mm _ [c9] rest) FR4) as [F72 FS]; clear FR4;
    cbn [cells_size csize Nat.add] in F8, F16, F64, F72, FS end.
  lazymatch type of F8 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -200) in F8 by lia end.
  lazymatch type of F16 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -192) in F16 by lia end.
  lazymatch type of F64 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -144) in F64 by lia end.
  lazymatch type of F72 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -136) in F72 by lia end.
  lazymatch type of FS with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -104) in FS by lia end.
  match goal with HR : relro_clean ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (sdesc_relro t _ HR) as Gsd end.
  match goal with HG : rw_cells usegs _ (dl_As L + 5300) [C4 (wz 1); C4 (wz ?hm4)] |- _ =>
    replace (wz hm4) with (wz (hm4 - 1 + 1)) in HG by (f_equal; lia) end.
  lazymatch goal with HD : u8arr usegs ?mm (dl_As L + 5308) (av8 ?dp 573), HL : arr_len ?dp = 573 |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (av8_zlength dp 573 ltac:(lia)) as L8' end.
  lazymatch goal with HT : u8arr usegs ?mm T (u16s (avct ?fc ?dl N)), HH : u32arr usegs ?mm (dl_As L + 3008) (av32 ?hp 573), HD : u8arr usegs ?mm (dl_As L + 5308) (av8 ?dp 573),
                      HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol ?sl ?k0 ?k1 ?k2 ?k3 ?k4), HC : rw_cells usegs ?mm (dl_As L + 5300) [C4 (wz 1); C4 (wz (?hm - 1 + 1))],
                      Hd : rw_cells usegs ?mm dsc [C8 (wz T); C4 (wz ?mc); CB 4 hh; C8 (wz (SDA t))], HN : rw_cells usegs ?mm (bv_unsigned sp + -136) [CB 32 ?nc]
    |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (upartB L s t T N (hm - 1) dsc mc ol sl fc dl hp dp (ds_bl_count s) hh k0 k1 k2 k3 k4 nc R) end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact Gsd. }
  1:{ rewrite ESP. replace (bv_unsigned sp + -208 + 8) with (bv_unsigned sp + -200) by lia. exact F8. }
  1:{ rewrite ESP. replace (bv_unsigned sp + -208 + 16) with (bv_unsigned sp + -192) by lia. exact F16. }
  1:{ rewrite ESP. replace (bv_unsigned sp + -208 + 64) with (bv_unsigned sp + -144) by lia. exact F64. }
  1:{ rewrite ESP. replace (bv_unsigned sp + -208 + 72) with (bv_unsigned sp + -136) by lia. exact F72. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ lia. } 1:{ lia. } 1:{ exact EN. } 1:{ exact AT4. }
  1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ exact LBC. } 1:{ exact Edsc. } 1:{ lia. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. }
  1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. }
  1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ exact ER. }
  rewrite ESP in *. unfold BT_EPI.
  match goal with HN : rw_cells usegs _ (bv_unsigned sp + -208 + 72) [CB 32 _] |- _ => replace (bv_unsigned sp + -208 + 72) with (bv_unsigned sp + -136) in HN by lia; rename HN into F72' end.
  do 13 zs2. zstep. zstep.
  release_frame F0 STK (bv_unsigned sp + -200). release_frame F8 STK (bv_unsigned sp + -192). release_frame F16 STK (bv_unsigned sp + -144).
  release_frame F64 STK (bv_unsigned sp + -136). release_frame F72' STK (bv_unsigned sp + -104). release_frame FS STK (bv_unsigned sp).
  match goal with HG : rw_cells usegs _ (dl_As L + 5881) (bD_cells _ _ ?ol ?sl ?k0 ?k1 ?k2 ?k3 ?k4), HR : R = bt_upd s t ?fc ?dl ?hp 1 ?hm ?dp ?bc _ _ ?mc |- _ =>
    apply evt_done; unfold body_post; do 15 eexists; exists fc, dl, hp, dp, bc, ol, sl, hm, mc, k0, k1, k2, k3, k4; eexists;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact STK|];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact HG|];
    split; [eassumption|]; split; [exact HR|] end.
  repeat (split; [first [assumption | rewrite arr_len_set; assumption] |]). first [assumption | rewrite arr_len_set; assumption].
Qed.


Ltac bt_tree_lens LENS t :=
  lazymatch t with
  | TL => constr:(conj (ln_ltf _ LENS) (ln_ltd _ LENS))
  | TD => constr:(conj (ln_dtf _ LENS) (ln_dtd _ LENS))
  | TB => constr:(conj (ln_btf _ LENS) (ln_btd _ LENS))
  end.

Lemma dsB_cells_split : forall L s h1 h2 h3,
  dsB_cells L s h1 h2 h3
  = [C8 (wz (dl_As L + 212)); C4 (wz (ds_l_max_code s)); CB 4 h1; C8 (wz Z_SL_DESC)]
    ++ [C8 (wz (dl_As L + 2504)); C4 (wz (ds_d_max_code s)); CB 4 h2; C8 (wz Z_SD_DESC)]
    ++ [C8 (wz (dl_As L + 2748)); C4 (wz (ds_bl_max_code s)); CB 4 h3; C8 (wz Z_SBL_DESC)].
Proof. intros. reflexivity. Qed.

Lemma build_tree_spec : build_tree_stmt.
Proof.
  unfold build_tree_stmt. intros until m. intros ST MI RC STK LO AL BEL SAFE Ea0 Ea1.
  open_DST ST. pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0.
  destruct GB as (h1 & h2 & h3 & GB). destruct GD as (g0 & g1 & g2 & g3 & g4 & GD).
  rewrite dsB_cells_split in GB.
  destruct (proj1 (rw_cells_app_iff _ _ _ _) GB) as [GBl GB23]. destruct (proj1 (rw_cells_app_iff _ _ _ _) GB23) as [GBd GBb]. clear GB GB23.
  cbn [cells_size csize Nat.add] in GBd, GBb. change (Z.of_nat 24) with 24 in GBd, GBb.
  replace (dl_As L + 2904 + 24 + 24) with (dl_As L + 2952) in GBb by lia. replace (dl_As L + 2904 + 24) with (dl_As L + 2928) in GBd by lia.
  unfold dsC, dsC_cells in GC. change (dsD_cells L s g0 g1 g2 g3 g4) with (bD_cells L s (ds_opt_len s) (ds_static_len s) g0 g1 g2 g3 g4) in GD.
  unfold dblc, u16arr in Gblc. unfold dheap in Gheap. unfold ddep in Gdep.
  destruct t.
  -
    unfold dlt, u16arr in Glt.
    eapply evt_mono.
    { eapply (build_tree_body L s TL (dl_As L + 212) 573 (dl_As L + 2904) lo h1 g0 g1 g2 g3 g4 (build_tree s TL)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Glt. } 1:{ exact Gheap. } 1:{ exact Gdep. } 1:{ exact Gblc. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact GBl. }
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_ltf _ LENS). } 1:{ exact (ln_ltd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBl' & ER & LFC' & LDL' & LHP' & LDP' & LBC').
    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport usegs W m m') in GBd; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport usegs W m m') in GBb; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
    unfold build_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite ER. constructor.
    + exact GA.
    + exists h1, h2, h3. rewrite dsB_cells_split.
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2928)); [exact GBl'| | cbn; lia].
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2952)); [exact GBd| exact GBb| cbn; lia].
    + exact GC'.
    + exists k0, k1, k2, k3, k4. exact GD'.
    + exact ARR'.
    + exact Gdt.
    + exact Gbt.
    + exact BLC'.
    + exact HPA'.
    + exact DPA'.
    + exact Gwin.
    + exact Gprev.
    + exact Ghead.
    + exact Gpend.
    + destruct LENS; constructor; cbn -[arr_len Z.add]; assumption.
    + exact LAY.
  -
    unfold ddt, u16arr in Gdt.
    eapply evt_mono.
    { eapply (build_tree_body L s TD (dl_As L + 2504) 61 (dl_As L + 2928) lo h2 g0 g1 g2 g3 g4 (build_tree s TD)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Gdt. } 1:{ exact Gheap. } 1:{ exact Gdep. } 1:{ exact Gblc. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact GBd. }
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_dtf _ LENS). } 1:{ exact (ln_dtd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBd' & ER & LFC' & LDL' & LHP' & LDP' & LBC').
    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport usegs W m m') in GBl; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport usegs W m m') in GBb; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
    unfold build_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite ER. constructor.
    + exact GA.
    + exists h1, h2, h3. rewrite dsB_cells_split.
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2928)); [exact GBl| | cbn; lia].
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2952)); [exact GBd'| exact GBb| cbn; lia].
    + exact GC'.
    + exists k0, k1, k2, k3, k4. exact GD'.
    + exact Glt.
    + exact ARR'.
    + exact Gbt.
    + exact BLC'.
    + exact HPA'.
    + exact DPA'.
    + exact Gwin.
    + exact Gprev.
    + exact Ghead.
    + exact Gpend.
    + destruct LENS; constructor; cbn -[arr_len Z.add]; assumption.
    + exact LAY.
  -
    unfold dbt, u16arr in Gbt.
    eapply evt_mono.
    { eapply (build_tree_body L s TB (dl_As L + 2748) 39 (dl_As L + 2952) lo h3 g0 g1 g2 g3 g4 (build_tree s TB)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Gbt. } 1:{ exact Gheap. } 1:{ exact Gdep. } 1:{ exact Gblc. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact GBb. }
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_btf _ LENS). } 1:{ exact (ln_btd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBb' & ER & LFC' & LDL' & LHP' & LDP' & LBC').
    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport usegs W m m') in GBl; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport usegs W m m') in GBd; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
    unfold build_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite ER. constructor.
    + exact GA.
    + exists h1, h2, h3. rewrite dsB_cells_split.
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2928)); [exact GBl| | cbn; lia].
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2952)); [exact GBd| exact GBb'| cbn; lia].
    + exact GC'.
    + exists k0, k1, k2, k3, k4. exact GD'.
    + exact Glt.
    + exact Gdt.
    + exact ARR'.
    + exact BLC'.
    + exact HPA'.
    + exact DPA'.
    + exact Gwin.
    + exact Gprev.
    + exact Ghead.
    + exact Gpend.
    + destruct LENS; constructor; cbn -[arr_len Z.add]; assumption.
    + exact LAY.
Qed.
