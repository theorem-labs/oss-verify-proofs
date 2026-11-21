(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_bt1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel RefBuildTree1 RefBuildTree2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition bD_cells (L : dlay) (s : deflate_state) (OL SL : Z) (h0 h1 h2 h3 h4 : list byte) : list cell :=
  [CB 7 h0; C8 (wz (dl_Ab L + ds_lit_bufsize s)); C4 (wz (ds_lit_bufsize s)); C4 (wz (ds_sym_next s)); C4 (wz (ds_sym_end s)); CB 4 h1;
   C8 (wz OL); C8 (wz SL); C4 (wz (ds_matches s)); C4 (wz (ds_insert s)); C2 (wz (ds_bi_buf s)); CB 2 h2; C4 (wz (ds_bi_valid s)); CB 4 h3; C4 (wz 0); C8 (wz (ds_high_water s)); CB 4 h4; C4 (wz 0)].

Definition bt2R (L : dlay) (T HL mc dsc stp : Z) (ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz mc) t1 t2 s0 (wz (dl_As L)) a0 (wz dsc) (wz stp) (wz 2) (wz HL) (wz (dl_As L + 3008)) (wz (dl_As L + 5308)) (wz 1)
      (wz T) (wz mc) (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

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

Definition stree_view (t : tree_id) (stp : Z) : Prop :=
  (stp = 0 /\ stree_has t = false)
  \/ (0 < stp < 2^32 /\ stree_has t = true
      /\ forall mm node, mem_inv psegs mm -> 0 <= node < 3 ->
           ov_read_bytes psegs mm (wa (stp + node * 4 + 2)) 2 = Some (le2 (wz (stree_Len t node))) /\ 0 <= stree_Len t node < 16).

Notation Wbt2 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5968)] (only parsing).

Definition bt_l2_post (L : dlay) (s : deflate_state) (T N dsc stp : Z) (FC DL HP : arr) (HL HM : Z) (DP : arr) (OL SL mc : Z)
    (ra sp gp tp s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 h0 h1 h2 h3 h4 pcx m',
    ms' = MS (bt2R L T HL mc dsc stp ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wbt2 L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4)
    /\ ((pcx = 0x1c2f8 /\ HL < 2) \/ (pcx = 0x1baec /\ 2 <= HL)).

Ltac l2_close MU WM ARR HPA DPA GC GD :=
  let K3 := fresh "K3" in
  zs2; zs2; zstep; br_cases K3;
  (apply evt_done; unfold bt_l2_post, bt2R, bD_cells; do 9 eexists;
   split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact ARR|]; split; [exact HPA|]; split; [exact DPA|];
   split; [exact GC|]; split; [close_cells GD|];
   first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]]).

Lemma bt_l2_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL mc dsc stp HM OL SL node mc' : Z) (FC DL HP DP : arr) (h0 h1 h2 h3 h4 : list byte)
    (ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 3 <= N -> arr_len FC = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  stree_view t stp -> 0 <= HL < 2 -> -1 <= mc < 286 -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  (node, mc') = l2node mc ->
  evt psegs (bt_l2_post L s T N dsc stp (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node) (HL + 1) HM (arr_set DP node (wrap8 0))
               (wrap64 (OL - 1)) (if stree_has t then wrap64 (SL - stree_Len t node) else SL) mc'
               ra sp gp tp s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (bt2R L T HL mc dsc stp ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c2f8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA DPA GC GD MI LAY RT1 RT2 RN LFC LHP LDP SV RHL Rmc ROL RSL ENODE.
  pose proof (munch_refl (Wbt2 L T N) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. unfold bt2R, bD_cells in *.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  assert (En : node = (if mc <? 2 then mc + 1 else 0) /\ mc' = (if mc <? 2 then mc + 1 else mc)).
  { unfold l2node in ENODE. destruct (mc <? 2); inversion ENODE; auto. }
  destruct En as [En Emc']. assert (Rnode : 0 <= node < 3) by (rewrite En; destruct (Z.ltb_spec mc 2); lia).
  zs2. rewrite swrap32_succ_m1 by lia. zs2. zstep.
  br_cases K.
  -
    rewrite (proj2 (Z.ltb_lt _ _) K) in En, Emc'. subst node mc'.
    zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zs2. rewrite l2node_mask by lia. rewrite (proj2 (Z.ltb_lt _ _) K).
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) (mc + 1) ltac:(reflexivity).
    zs2. shl_norm. zs2. zs2.
    ct_store_fc ARR FC DL N T (mc + 1) (wrap16 1) ltac:(reflexivity).
    pb_store DPA DP 573 (dl_As L + 5308) (mc + 1) (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2.
    zstep. destruct SV as [[Es Eh]|(Rs0 & Eh & RDS)]; rewrite Eh.
    + subst stp. br_true. l2_close MU WM ARR HPA DPA GC GD.
    + br_false. destruct (RDS m0 (mc + 1) ltac:(eassumption) ltac:(lia)) as [RDl Rsl].
      zs2. zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zs2. l2_close MU WM ARR HPA DPA GC GD.
  -
    rewrite (proj2 (Z.ltb_ge _ _)) in En, Emc' by lia. subst node mc'.
    zs2.
    zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zs2. rewrite l2node_mask_ge by lia.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) 0 ltac:(reflexivity).
    zs2. zs2. zs2.
    ct_store_fc ARR FC DL N T 0 (wrap16 1) ltac:(reflexivity).
    pb_store DPA DP 573 (dl_As L + 5308) 0 (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2.
    zstep. destruct SV as [[Es Eh]|(Rs0 & Eh & RDS)]; rewrite Eh.
    + subst stp. br_true. l2_close MU WM ARR HPA DPA GC GD.
    + br_false. destruct (RDS m0 0 ltac:(eassumption) ltac:(lia)) as [RDl Rsl]. change (0 * 4) with 0 in RDl. replace (stp + 0 + 2) with (stp + 2) in RDl by lia.
      zs2. zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zs2. l2_close MU WM ARR HPA DPA GC GD.
Qed.
