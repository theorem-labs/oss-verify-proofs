(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.Z_tr_bt12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_scan1.

Module Z_tr_bt_mid.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.


Definition BT_TRAP : Z := 0x1d05c.
Definition BT_L1 : Z := 0x1cabc.
Definition BT_L1X : Z := 0x1cb2c.
Definition BT_L2 : Z := 0x1d3ac.
Definition BT_L2X : Z := 0x1cb38.
Definition BT_L3 : Z := 0x1cb54.
Definition BT_L4 : Z := 0x1cba8.
Definition BT_PARTB : Z := 0x1cd34.
Definition BT_EPI : Z := 0x1d320.

Notation ubt_frame j0 mc dsc E L T nc s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra :=
  ([CB 8 j0; C8 (wz mc); C8 (wz dsc); C8 (wz 0); C8 (wz E); C8 (wz (dl_As L + 5912)); C8 (wz (ONES - T)); C8 (wz (dl_As L)); C8 (wz (ONES - (dl_As L + 3008)));
    CB 32 nc; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])%list (only parsing).

Notation WBT L T N dsc lo sp := [(lo%Z, bv_unsigned sp); (T%Z, (T + 4 * N)%Z); ((dsc + 8)%Z, (dsc + 12)%Z); (dl_As L + 2976, dl_As L + 5968)] (only parsing).

Ltac name_term X EX t :=
  let H := fresh in
  assert (H : exists X0, X0 = t) by (eexists; reflexivity);
  destruct H as [X EX]; rewrite <- ?EX in *.

Definition bD_cells (L : dlay) (s : deflate_state) (OL SL : Z) (h0 h1 h2 h3 h4 : list byte) : list cell :=
  [CB 7 h0; C8 (wz (dl_Ab L + ds_lit_bufsize s)); C4 (wz (ds_lit_bufsize s)); C4 (wz (ds_sym_next s)); C4 (wz (ds_sym_end s)); CB 4 h1;
   C8 (wz OL); C8 (wz SL); C4 (wz (ds_matches s)); C4 (wz (ds_insert s)); C2 (wz (ds_bi_buf s)); CB 2 h2; C4 (wz (ds_bi_valid s)); CB 4 h3; C4 (wz 0); C8 (wz (ds_high_water s)); CB 4 h4; C4 (wz 0)].

Definition STP (t : tree_id) : Z := match t with TL => 0x11db0 | TD => 0x12230 | TB => 0 end.
Definition XP (t : tree_id) : Z := match t with TL => 0x122a8 | TD => 0x1231c | TB => 0x12394 end.
Definition SDA (t : tree_id) : Z := match t with TL => 0x2bf80 | TD => 0x2bfa0 | TB => 0x2bfc0 end.
Definition sd_cells (t : tree_id) : list cell :=
  [C8 (wz (STP t)); C8 (wz (XP t)); C4 (wz (sd_extra_base t)); C4 (wz (sd_elems t)); C4 (wz (sd_max_length t))].

Lemma SDA_range : forall t, 0x2bf80 <= SDA t <= 0x2bfc0. Proof. destruct t; cbn; lia. Qed.
Lemma SDA_al8 : forall t, SDA t mod 8 = 0. Proof. destruct t; reflexivity. Qed.
Lemma STP_range : forall t, 0 <= STP t < 2 ^ 32. Proof. destruct t; cbn; lia. Qed.
Lemma XP_range : forall t, 0 <= XP t < 2 ^ 32. Proof. destruct t; cbn; lia. Qed.
Lemma SDA_desc : forall t, SDA t = match t with TL => Z_SL_DESC | TD => Z_SD_DESC | TB => Z_SBL_DESC end.
Proof. destruct t; reflexivity. Qed.
Lemma bt_desc_range : forall t, 2904 <= bt_desc t <= 2952 /\ bt_desc t mod 8 = 0.
Proof. destruct t; cbn [bt_desc]; (split; [lia| reflexivity]). Qed.

Ltac relro_cells A cs n :=
  let RC := fresh "RC" in intros m RC; unfold relro_clean, RELRO_LO, RELRO_HI in RC;
  apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_recast usegs m A [CB n (cells_bytes cs)] cs);
  [ apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.InitMem.rw_cells_image0 usegs m A (cells_bytes cs));
    [ intros a Ha; apply RC; change (Z.of_nat (length (cells_bytes cs))) with (Z.of_nat n) in Ha; lia
    | vm_compute; reflexivity | lia | change (Z.of_nat (length (cells_bytes cs))) with (Z.of_nat n); lia ]
  | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ].

Lemma sdesc_relro_l : forall m, relro_clean m -> rw_cells usegs m 0x2bf80 [C8 (wz 0x11db0); C8 (wz 0x122a8); C4 (wz 257); C4 (wz 286); C4 (wz 15)].
Proof. relro_cells 0x2bf80 [C8 (wz 0x11db0); C8 (wz 0x122a8); C4 (wz 257); C4 (wz 286); C4 (wz 15)] 28%nat. Qed.
Lemma sdesc_relro_d : forall m, relro_clean m -> rw_cells usegs m 0x2bfa0 [C8 (wz 0x12230); C8 (wz 0x1231c); C4 (wz 0); C4 (wz 30); C4 (wz 15)].
Proof. relro_cells 0x2bfa0 [C8 (wz 0x12230); C8 (wz 0x1231c); C4 (wz 0); C4 (wz 30); C4 (wz 15)] 28%nat. Qed.
Lemma sdesc_relro_bl : forall m, relro_clean m -> rw_cells usegs m 0x2bfc0 [C8 (wz 0); C8 (wz 0x12394); C4 (wz 0); C4 (wz 19); C4 (wz 7)].
Proof. relro_cells 0x2bfc0 [C8 (wz 0); C8 (wz 0x12394); C4 (wz 0); C4 (wz 19); C4 (wz 7)] 28%nat. Qed.

Lemma sdesc_relro : forall t m, relro_clean m -> rw_cells usegs m (SDA t) (sd_cells t).
Proof.
  intros t m RC. destruct t; cbn [SDA sd_cells STP XP sd_extra_base sd_elems sd_max_length]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS;
    [apply sdesc_relro_l| apply sdesc_relro_d| apply sdesc_relro_bl]; exact RC.
Qed.

Lemma rod_extra_blbits : forall m, mem_inv usegs m -> bytes_at usegs m 0x12394 (u32s (av32 extra_blbits_a 19)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity]. Qed.

Lemma static_ltree_dl_range : forall n, 0 <= n < 288 -> 0 <= arr_get static_ltree_dl n < 16.
Proof. intros n H. ztab_tac 288 (fun i => (0 <=? arr_get static_ltree_dl i) && (arr_get static_ltree_dl i <? 16)) H. lia. Qed.
Lemma static_dtree_dl_range : forall n, 0 <= n < 30 -> 0 <= arr_get static_dtree_dl n < 16.
Proof. intros n H. ztab_tac 30 (fun i => (0 <=? arr_get static_dtree_dl i) && (arr_get static_dtree_dl i <? 16)) H. lia. Qed.
Lemma extra_blbits_range : forall c, 0 <= c < 19 -> 0 <= arr_get extra_blbits_a c < 16.
Proof. intros c H. ztab_tac 19 (fun i => (0 <=? arr_get extra_blbits_a i) && (arr_get extra_blbits_a i <? 16)) H. lia. Qed.

Definition stree_view (t : tree_id) (stp : Z) : Prop :=
  (stp = 0 /\ stree_has t = false)
  \/ (0 < stp < 2^32 /\ stree_has t = true
      /\ forall mm node, mem_inv usegs mm -> 0 <= node < 3 ->
           ov_read_bytes usegs mm (wa (stp + node * 4 + 2)) 2 = Some (le2 (wz (stree_Len t node))) /\ 0 <= stree_Len t node < 16).
Definition stree_view_n (t : tree_id) (stp : Z) : Prop :=
  (stp = 0 /\ stree_has t = false)
  \/ (0 < stp < 2^32 /\ stree_has t = true
      /\ forall mm n, mem_inv usegs mm -> 0 <= n < sd_elems t ->
           ov_read_bytes usegs mm (wa (stp + n * 4 + 2)) 2 = Some (le2 (wz (stree_Len t n))) /\ 0 <= stree_Len t n < 16).
Definition xbits_view (t : tree_id) (xp : Z) : Prop :=
  forall mm n, mem_inv usegs mm -> sd_extra_base t <= n < sd_elems t ->
    ov_read_bytes usegs mm (wa (xp + (n - sd_extra_base t) * 4)) 4 = Some (le4 (wz (arr_get (sd_extra_bits t) (n - sd_extra_base t))))
    /\ 0 <= arr_get (sd_extra_bits t) (n - sd_extra_base t) < 16.

Lemma stree_view_of : forall t, stree_view t (STP t).
Proof.
  intros [| |]; cbn [STP].
  - right. split; [lia|]. split; [reflexivity|]. intros mm node MI Hn. split.
    + apply (u16ro_read mm Z_STATIC_LTREE (avct static_ltree_fc static_ltree_dl 288) (2 * node + 1)); [apply rod_static_ltree; exact MI| apply avct_nth_dl; lia| lia| unfold Z_STATIC_LTREE; f_equal; lia].
    + cbn [stree_Len]. apply static_ltree_dl_range. lia.
  - right. split; [lia|]. split; [reflexivity|]. intros mm node MI Hn. split.
    + apply (u16ro_read mm Z_STATIC_DTREE (avct static_dtree_fc static_dtree_dl 30) (2 * node + 1)); [apply rod_static_dtree; exact MI| apply avct_nth_dl; lia| lia| unfold Z_STATIC_DTREE; f_equal; lia].
    + cbn [stree_Len]. apply static_dtree_dl_range. lia.
  - left. split; reflexivity.
Qed.

Lemma stree_view_n_of : forall t, stree_view_n t (STP t).
Proof.
  intros [| |]; cbn [STP]; unfold stree_view_n; cbn [sd_elems stree_has stree_Len]; unfold L_CODES, D_CODES.
  - right. split; [lia|]. split; [reflexivity|]. intros mm n MI Hn. split.
    + apply (u16ro_read mm Z_STATIC_LTREE (avct static_ltree_fc static_ltree_dl 288) (2 * n + 1)); [apply rod_static_ltree; exact MI| apply avct_nth_dl; lia| lia| unfold Z_STATIC_LTREE; f_equal; lia].
    + apply static_ltree_dl_range. lia.
  - right. split; [lia|]. split; [reflexivity|]. intros mm n MI Hn. split.
    + apply (u16ro_read mm Z_STATIC_DTREE (avct static_dtree_fc static_dtree_dl 30) (2 * n + 1)); [apply rod_static_dtree; exact MI| apply avct_nth_dl; lia| lia| unfold Z_STATIC_DTREE; f_equal; lia].
    + apply static_dtree_dl_range. lia.
  - left. split; reflexivity.
Qed.

Lemma xbits_view_of : forall t, xbits_view t (XP t).
Proof.
  intros [| |]; unfold xbits_view; cbn [XP sd_extra_base sd_elems sd_extra_bits]; unfold LITERALS, L_CODES, D_CODES, BL_CODES; intros mm n MI Hn; split.
  - apply (u32ro_read mm Z_EXTRA_LBITS (av32 extra_lbits_a 29) (n - (256 + 1))); [apply rod_extra_lbits; exact MI| apply av32_nth; lia| lia| unfold Z_EXTRA_LBITS; f_equal; lia].
  - pose proof (extra_lbits_facts (n - (256 + 1)) ltac:(lia)). lia.
  - apply (u32ro_read mm Z_EXTRA_DBITS (av32 extra_dbits_a 30) (n - 0)); [apply rod_extra_dbits; exact MI| apply av32_nth; lia| lia| unfold Z_EXTRA_DBITS; f_equal; lia].
  - pose proof (extra_dbits_facts (n - 0) ltac:(lia)). lia.
  - apply (u32ro_read mm 0x12394 (av32 extra_blbits_a 19) (n - 0)); [apply rod_extra_blbits; exact MI| apply av32_nth; lia| lia| f_equal; lia].
  - apply extra_blbits_range. lia.
Qed.

Lemma rw_cells_app_iff : forall m A l1 l2,
  rw_cells usegs m A (l1 ++ l2) <-> rw_cells usegs m A l1 /\ rw_cells usegs m (A + Z.of_nat (cells_size l1)) l2.
Proof.
  intros m A l1 l2. unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add. split.
  - intros (([W1 W2] & BY) & WR).
    rewrite bytes_at_app in BY. destruct BY as [B1 B2]. rewrite (cells_bytes_length l1 W1) in B2.
    apply wr_at_app in WR; [| lia| lia]. destruct WR as [R1 R2].
    split; (split; [split|]); assumption.
  - intros (([W1 B1] & R1) & ([W2 B2] & R2)). split; [split; [split; assumption|]|].
    + apply bytes_at_app. rewrite (cells_bytes_length l1 W1). split; assumption.
    + apply wr_at_app; [lia| lia|]. split; assumption.
Qed.
Lemma rw_cells_split2 : forall m A l1 l2 B, rw_cells usegs m A (l1 ++ l2) -> B = A + Z.of_nat (cells_size l1) ->
  rw_cells usegs m A l1 /\ rw_cells usegs m B l2.
Proof. intros m A l1 l2 B H ->. apply rw_cells_app_iff. exact H. Qed.
Lemma rw_cells_join2 : forall m A l1 l2 B, rw_cells usegs m A l1 -> rw_cells usegs m B l2 -> B = A + Z.of_nat (cells_size l1) ->
  rw_cells usegs m A (l1 ++ l2).
Proof. intros m A l1 l2 B H1 H2 ->. apply rw_cells_app_iff. split; assumption. Qed.

Definition bt_mid_post (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc lo : Z) (hh : list byte)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x23 x26 x27 t3 t4 t5 t6 : word)
                    (FC DL HP DP : arr) (HM mc OL SL : Z) (h0 h1 h2 h3 h4 j0 nc : list byte) (m' : mem),
    ms' = MS (mkR x1 (wz (bv_unsigned sp - 208)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (wz (dl_As L + 3008)) x20 x21 (wz T) x23
                  (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) x26 x27 t3 t4 t5 t6) F (wz BT_PARTB) fc None m' (seg_rom usegs)
    /\ munch (WBT L T N dsc lo sp) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ relro_clean m'
    /\ stk usegs m' lo (bv_unsigned sp - 208)
    /\ rw_cells usegs m' (bv_unsigned sp - 208) (ubt_frame j0 mc dsc (sd_elems t) L T nc s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ u8arr usegs m' T (u16s (avct FC DL N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 (ds_bl_count s) 16))
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz HM)] /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4)
    /\ rw_cells usegs m' dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz (SDA t))]
    /\ arr_len FC = N /\ arr_len DL = N /\ arr_len HP = 573 /\ arr_len DP = 573
    /\ 1 <= HM <= 571 /\ 0 <= arr_get HP 1 < N /\ -1 <= mc < sd_elems t
    /\ (forall k, HM - 1 + 1 <= k < 573 -> 0 <= arr_get (arr_set HP (HM - 1) (arr_get HP 1)) k < N)
    /\ (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) /\ (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536)
    /\ 0 <= OL < 2^64 /\ 0 <= SL < 2^64
    /\ gb1_ok t mc 573 (bt_upd s t FC (arr_set DL (arr_get HP 1) (wrap16 0)) (arr_set HP (HM - 1) (arr_get HP 1)) 1 (HM - 1) DP (arr_fill (ds_bl_count s) 0 16 0) OL SL mc) (HM - 1 + 1) 0
    /\ (forall X10 ovf,
          gen_bitlen_loop1 573 (bt_upd s t FC (arr_set DL (arr_get HP 1) (wrap16 0)) (arr_set HP (HM - 1) (arr_get HP 1)) 1 (HM - 1) DP (arr_fill (ds_bl_count s) 0 16 0) OL SL mc)
             t mc (sd_extra_base t) (sd_max_length t) (HM - 1 + 1) 0 = (X10, ovf) -> ovf <> 0 ->
          gb2_ok (sd_max_length t) 573 X10 ovf /\ gb3_ok t mc (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) (sd_max_length t) 573)
    /\ (forall i, 0 <= i <= mc -> 0 <= Len (gen_bitlen (bt_upd s t FC DL (arr_set HP (HM - 1) (arr_get HP 1)) 1 (HM - 1) DP (ds_bl_count s) OL SL mc) t) t i <= 15)
    /\ build_tree s t = gen_codes (gen_bitlen (bt_upd s t FC DL (arr_set HP (HM - 1) (arr_get HP 1)) 1 (HM - 1) DP (ds_bl_count s) OL SL mc) t) t mc.
End Z_tr_bt_mid.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel.

Module Z_tr_bits.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition Z_BI_FLUSH : Z := 0x1bc94.

Lemma bi_flush_spec : forall (L : dlay) (s : deflate_state)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv usegs m ->
  BINV DS_PEND s -> ds_pending (tr_flush_bits s) <= DS_PEND ->
  a0 = wz (dl_As L) ->
  evt usegs (tr_flush_bits_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_BI_FLUSH) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST MI BI ROOM ->. unfold Z_BI_FLUSH.
  destruct BI as (RBV & RBB & RPD). unfold tr_flush_bits in ROOM.
  pose proof (munch_refl [(dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MUf.
  open_DST ST. lay_open LAY. pose proof (ln_pend _ LENS) as LNP.
  pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  open_D GD.
  gF. zs2. al8 (dl_As L). gF.
  do 3 zstep. zs. do 2 zstep.
  if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  -
    do 2 zstep.
    if_cases K2; zify_cond K2; rewrite ?signed_wz in K2 by lia.
    +
      zstep. apply evt_done. unfold tr_flush_bits_post. do 15 eexists. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      unfold tr_flush_bits. rewrite bi_flush_eq0 by lia. rewrite upd4_self.
      constructor; [exact GA| exact GB| exact GC| exists hD0, hD1, hD2, hD3, hD4; exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY].
    +
      rewrite bi_flush_eq8, upd4_pending in ROOM by lia.
      open_A GA. open_pend Gpend.
      zstep. zstep. zstep. rewrite zx16_small by lia. zs2. zs2. zstep.
      gF. zs2. zs2. zs2. gX. gF.
      pb_store Gpend (ds_pending_buf s) 65536 (dl_Ab L) (ds_pending s) (wrap8 (ds_bi_buf s)) ltac:(apply b0h_w; lia).
      zs2. rd_c2 GD 55%nat 1. zstep. zs. rewrite (bv8_small (Z.shiftr (ds_bi_buf s) 8)) by (apply shr8_small; lia).
      zs2. gF. zstep. zstep.
      apply evt_done. unfold tr_flush_bits_post. do 15 eexists. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      unfold tr_flush_bits. rewrite bi_flush_eq8 by lia. tr_groups MUf WM.
      constructor; [eexists _, _, _, _, _; unfold dsA_cells, upd4; dsred; close_cells GA| exact GB| exact GC
                   | eexists _, _, _, _, _; unfold dsD_cells, upd4; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| unfold dpend, upd4; dsred; exact Gpend| close_lens_with LENS ltac:(unfold upd4)| exact LAY].
  -
    rewrite bi_flush_eq16, upd4_pending in ROOM by lia.
    open_A GA. open_pend Gpend.
    zstep. zstep. zstep. rewrite zx16_small by lia. zs2. zs2. zstep.
    gF. zs2. zs2. zs2. gX. gF.
    pb_store Gpend (ds_pending_buf s) 65536 (dl_Ab L) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255)) ltac:(apply b0h_land; lia).
    zstep. zstep. rd_c2 GD 55%nat 1. zstep. zs2.
    zs2. zstep.
    gF. zs2. zs2. zs2. gX. gF.
    zs2.
    pb_store Gpend (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255))) 65536 (dl_Ab L) (ds_pending s + 1)
             (wrap8 (Z.shiftr (wrap16 (ds_bi_buf s)) 8)) ltac:(apply b1_val; lia).
    zstep. zstep. zstep. zstep.
    apply evt_done. unfold tr_flush_bits_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    unfold tr_flush_bits. rewrite bi_flush_eq16 by lia. tr_groups MUf WM.
    constructor; [eexists _, _, _, _, _; unfold dsA_cells, upd4; dsred; close_cells GA| exact GB| exact GC
                 | eexists _, _, _, _, _; unfold dsD_cells, upd4; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| unfold dpend, upd4; dsred; exact Gpend| close_lens_with LENS ltac:(unfold upd4)| exact LAY].
Qed.

Lemma tr_flush_bits_spec : tr_flush_bits_stmt.
Proof.
  unfold tr_flush_bits_stmt. intros until m. intros ST MI BI ROOM Ea0. unfold Z_TR_FLUSH_BITS.
  zstep. apply (bi_flush_spec L s); assumption.
Qed.
End Z_tr_bits.

Module Z_tr_pq.
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
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
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

Definition Z_PQDOWNHEAP : Z := 0x1dd74.
Definition PQ_TRAP : Z := 0x1dfd8.
Definition PQ_HEAD : Z := 0x1de38.
Definition PQ_CMP : Z := 0x1df04.
Definition PQ_CONT : Z := 0x1df78.
Definition PQ_FIN : Z := 0x1dfac.
Definition Z_PQ_STACK : Z := 64.
Local Notation ONES := 18446744073709551615.

Ltac h32_store ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u32arr_store_ok usegs _ A (av32 a n) idx (wa (A + 4 * idx)) ARR ltac:(rewrite av32_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le4 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av32_write m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      replace (A + 4 * idx) with E in ARR' by lia;
      let LN := fresh "L32" in pose proof (av32_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNH" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Notation Wpq lo sp L := [(lo%Z, bv_unsigned sp); (dl_As L + 3008, dl_As L + 5300)] (only parsing).

Ltac decide_bools :=
  repeat match goal with
  | |- context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia]
  | |- context [?a <=? ?b] => first [rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia]
  | |- context [?a =? ?b] => first [rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia]
  end; cbn [andb orb negb].

Lemma hz17 : forall T, 0 < T -> Z.b2z (0 <? T) = 1.
Proof. intros T H. rewrite (proj2 (Z.ltb_lt 0 T) H). reflexivity. Qed.
Lemma hz28 : forall T q, 0 < T -> q mod 2 = 0 -> Z.land (Z.b2z (0 <? T)) (Z.b2z (Z.land q 1 <? 1)) = 1.
Proof. intros T q H Hq. rewrite (proj2 (Z.ltb_lt 0 T) H). rewrite (land1_mod2 q Hq). reflexivity. Qed.
Lemma hz29 : forall T q i, 0 < T -> 0 < q -> T <= q -> 0 <= i < 2^63 ->
  Z.land (Z.lxor (Z.b2z (0 <? T)) (Z.b2z (q <? 1))) (Z.lxor (Z.lxor (Z.b2z (q <? T)) (Z.b2z (Z.lxor i 9223372036854775808 <? 9223372036854775808))) 1) = 1.
Proof. intros T q i HT Hq HTq Hi. rewrite xor_guard by lia. rewrite xor_guard_idx by lia. reflexivity. Qed.

Definition upqR (L : dlay) (T v k j : Z) (x8 x9 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11 : word) :=
  mkR ra sp gp tp (wz (T + v * 4)) (wz (ONES - (dl_As L + 5308))) (wz (dl_As L + 5308 + v)) x8 x9
      (wz (dl_As L + 5308)) (wz T) (wz (dl_As L + 3008)) (wz (ONES - (dl_As L + 3008))) (wz v) (wz k) (wz (dl_As L + 5300)) (wz 1)
      x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 (wz 1) (wz 1) (wz 572) (wz j).

Lemma upq_sel : forall (L : dlay) (T N k j q HL v : Z) (FC DL HP DP : arr)
    (x8 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv usegs m -> dlay_ok L ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= j <= HL -> HL < 573 ->
  evt usegs (fun ms' => exists x9' x18' x19' x20' x21' x22',
               ms' = MS (upqR L T v k j (wz (sel3 FC HL DP HP j)) x9' x18' x19' x20' x21' x22' ra sp gp tp s7 s8 s9 s10 s11) F (wz PQ_CMP) fc None m (seg_rom usegs))
      (MS (upqR L T v k j x8 (wz HL) x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11) F (wz PQ_HEAD) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY AL4 RT1 RT2 RN PQ RFC RDP Ej Rj RHL. lay_open LAY. unfold upqR, PQ_HEAD, PQ_CMP.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  zs2. zstep. br_cases K.
  -
    zs2. apply evt_done. unfold sel3, smal. decide_bools. do 6 eexists. reflexivity.
  - pose proof (PQ j ltac:(lia)) as Rhj. pose proof (PQ (j + 1) ltac:(lia)) as Rhj1.
    pose proof (u32arr_read usegs m _ (av32 HP 573) j _ (wa (dl_As L + 3008 + j * 4)) HPA (av32_nth HP 573 j ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
    pose proof (u32arr_read usegs m _ (av32 HP 573) (j + 1) _ (wa (dl_As L + 3008 + (j + 1) * 4)) HPA (av32_nth HP 573 (j + 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj1.
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP j) ltac:(lia)) as [RDfj _].
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP (j + 1)) ltac:(lia)) as [RDfj1 _].
    replace (T + 4 * arr_get HP j) with (T + arr_get HP j * 4) in RDfj by lia. replace (T + 4 * arr_get HP (j + 1)) with (T + arr_get HP (j + 1) * 4) in RDfj1 by lia.
    pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rhj1) as Rfj1.
    zs2. ustep PQ_TRAP. zs2. shl_norm. ustep PQ_TRAP. zs2. zs2.
        zs2. shl_norm. zs2. zs2. ustep PQ_TRAP. zs2. zs2. zs2. zs2. ustep PQ_TRAP. ustep PQ_TRAP. zs2. ustep PQ_TRAP.
        zs2. shl_norm. zs2. zs2. zs2. shl_norm. zs2. ustep PQ_TRAP. zs2. zs2. zs2. zs2. ustep PQ_TRAP. zs2. ustep PQ_TRAP.
        zs2. rewrite (zx16_small (arr_get FC (arr_get HP (j + 1)))) by lia. zs2. rewrite (zx16_small (arr_get FC (arr_get HP j))) by lia.
    zstep. br_cases K1.
    +
      zstep. br_cases_s K2.
      *
        zs2. apply evt_done. unfold sel3, smal. decide_bools. do 6 eexists. reflexivity.
      *
        pose proof (u8arr_read usegs m _ (av8 DP 573) (arr_get HP j) _ (wa (dl_As L + 5308 + arr_get HP j)) DPA (av8_nth DP 573 (arr_get HP j) ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
        pose proof (u8arr_read usegs m _ (av8 DP 573) (arr_get HP (j + 1)) _ (wa (dl_As L + 5308 + arr_get HP (j + 1))) DPA (av8_nth DP 573 (arr_get HP (j + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RDdj1.
        pose proof (RDP (arr_get HP j) ltac:(lia)) as Rdj. pose proof (RDP (arr_get HP (j + 1)) ltac:(lia)) as Rdj1.
        do 4 ustep PQ_TRAP. zs2. zs2.
                zsb. rewrite (bv8_small (arr_get DP (arr_get HP (j + 1)))) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP j))) by lia.
        zs2. zstep. br_cases K3.
        -- zs2. zs2. apply evt_done. unfold sel3, smal. decide_bools. do 6 eexists. reflexivity.
        -- zs2. apply evt_done. unfold sel3, smal. decide_bools. do 6 eexists. reflexivity.
    +
      zs2. zs2. apply evt_done. unfold sel3, smal. decide_bools. do 6 eexists. reflexivity.
Qed.

Lemma upq_cmp : forall (L : dlay) (T N k jj j0 HL v : Z) (FC DL HP DP : arr)
    (x9 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv usegs m -> dlay_ok L ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= jj <= HL -> HL < 573 -> 0 <= v < N -> 1 <= k < 573 ->
  evt usegs (fun ms' => exists x9' x18' x19' x8v pcx,
               ms' = MS (upqR L T v k (arr_get HP jj) (wz x8v) x9' x18' x19' x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11) F (wz pcx) fc None m (seg_rom usegs)
               /\ ((pcx = PQ_FIN /\ x8v = k * 4 /\ smal FC DP v (arr_get HP jj) = true) \/ (pcx = PQ_CONT /\ x8v = jj /\ smal FC DP v (arr_get HP jj) = false)))
      (MS (upqR L T v k j0 (wz jj) x9 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11) F (wz PQ_CMP) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY AL4 RT1 RT2 RN PQ RFC RDP Rj RHL Rv Rk. lay_open LAY. unfold upqR, PQ_CMP.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (PQ jj Rj) as Rhj.
  pose proof (u32arr_read usegs m _ (av32 HP 573) jj _ (wa (dl_As L + 3008 + jj * 4)) HPA (av32_nth HP 573 jj ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP jj) ltac:(lia)) as [RDfj _].
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI v ltac:(lia)) as [RDfv _].
  replace (T + 4 * arr_get HP jj) with (T + arr_get HP jj * 4) in RDfj by lia. replace (T + 4 * v) with (T + v * 4) in RDfv by lia.
  pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rv) as Rfv.
  do 3 ustep PQ_TRAP. zs2. shl_norm. ustep PQ_TRAP. zs2. zs2.
  zs2. shl_norm. zs2. ustep PQ_TRAP. zs2. zs2. zs2. zs2. ustep PQ_TRAP. zs2. ustep PQ_TRAP.
  zs2. rewrite (zx16_small (arr_get FC v)) by lia. zs2. rewrite (zx16_small (arr_get FC (arr_get HP jj))) by lia.
  zstep. br_cases K1.
  -
    zs2. zs2. shl_norm. ustep PQ_TRAP.
    apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. split; [reflexivity|]. unfold smal. decide_bools. reflexivity.
  - zstep. br_cases_s K2.
    +
      apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. split; [reflexivity|]. unfold smal. decide_bools. reflexivity.
    + pose proof (u8arr_read usegs m _ (av8 DP 573) (arr_get HP jj) _ (wa (dl_As L + 5308 + arr_get HP jj)) DPA (av8_nth DP 573 (arr_get HP jj) ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
      pose proof (u8arr_read usegs m _ (av8 DP 573) v _ (wa (dl_As L + 5308 + v)) DPA (av8_nth DP 573 v ltac:(lia)) ltac:(lia) eq_refl) as RDdv.
      pose proof (RDP (arr_get HP jj) ltac:(lia)) as Rdj. pose proof (RDP v ltac:(lia)) as Rdv.
      do 4 ustep PQ_TRAP. zs2.
      zsb. rewrite (bv8_small (arr_get DP v)) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP jj))) by lia.
      zstep. br_cases K3.
      *
        zs2. shl_norm. zstep. br_true.
        apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. split; [reflexivity|]. unfold smal. decide_bools. reflexivity.
      * apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. split; [reflexivity|]. unfold smal. decide_bools. reflexivity.
Qed.

Definition fuel_ok (f : nat) (j HL : Z) : Prop := HL < j * 2 ^ Z.of_nat f.
Lemma fuel_ok_0 : forall j HL, fuel_ok 0 j HL -> HL < j.
Proof. unfold fuel_ok. intros j HL H. change (2 ^ Z.of_nat 0) with 1 in H. lia. Qed.
Lemma fuel_ok_S : forall f j j' HL, fuel_ok (S f) j HL -> 2 * j <= j' -> 0 < j -> fuel_ok f j' HL.
Proof.
  unfold fuel_ok. intros f j j' HL H Hj Hp. rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia.
  assert (0 < 2 ^ Z.of_nat f) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.
Lemma pq_out : forall f X t v k j, ds_heap_len X < j -> pqdownheap_loop f X t v k j = (X, k).
Proof. intros [|f] X t v k j H; [reflexivity|]. cbn [pqdownheap_loop]. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.
Lemma pqdownheap_flat : forall s t FC DL HP HL HM DP BC OL SL MC k,
  pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t k
  = heap_set (fst (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP k) k (k * 2)))
             (snd (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP k) k (k * 2))) (arr_get HP k).
Proof.
  intros. unfold pqdownheap. rewrite bt_heap_get. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  destruct (pqdownheap_loop 32 _ t (arr_get HP k) k (k * 2)); reflexivity.
Qed.

Notation Wh L := [(dl_As L + 3008, dl_As L + 5300)] (only parsing).

Definition upq_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x9 x18 x19 x20 x21 x22 jv HP' k' m',
    ms' = MS (upqR L T v k' jv (wz (k' * 4)) x9 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11) F (wz PQ_FIN) fc None m' (seg_rom usegs)
    /\ munch (Wh L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = (bt_upd s t FC DL HP' HL HM DP BC OL SL MC, k')
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N) /\ 1 <= k' <= HL.

Lemma upq_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z) (m0 : mem)
    (HP : arr) (k j q : Z)
    (x8 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wh L) m0 T FC DL N -> mem_inv usegs m -> dlay_ok L -> munch (Wh L) m0 m -> wmono usegs m0 m ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= k -> k < j -> j <= HL -> HL < 573 -> 0 <= v < N -> fuel_ok f j HL ->
  R = pqdownheap_loop f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t v k j ->
  evt usegs (upq_loop_post L s t T N HL HM v FC DL DP BC OL SL MC R ra sp gp tp s7 s8 s9 s10 s11 F fc m0)
      (MS (upqR L T v k j x8 (wz HL) x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11) F (wz PQ_HEAD) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros HPA DPA GC RDT MI LAY MU WM AL4 RT1 RT2 RN LHP PQ RFC RDP Ej Rk Rkj Rj RHL Rv FU ER.
  - apply fuel_ok_0 in FU. lia.
  - assert (RDTm : ct_readable [] m T FC DL N) by (eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; tauto]).
    pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.sel3_range FC HL DP HP j ltac:(lia)) as Rs3.
    rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.loop3_S_sel in ER by lia.
    eapply evt_cut; [eapply (upq_sel L T N k j q HL v FC DL HP DP); try eassumption; lia|]. intros ms' (x9' & x18' & x19' & x20' & x21' & x22' & ->).
    eapply evt_cut; [eapply (upq_cmp L T N k (sel3 FC HL DP HP j) j HL v FC DL HP DP); try eassumption; lia|].
    intros ms' (x9'' & x18'' & x19'' & x8v & pcx & -> & [(-> & -> & SM)|(-> & -> & SM)]); rewrite SM in ER.
    +
      apply evt_done. unfold upq_loop_post. do 10 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
      split; [exact ER|]. split; [exact LHP|]. split; [exact PQ| lia].
    +
      set (j' := sel3 FC HL DP HP j) in *.
      pose proof (PQ j' ltac:(lia)) as Rhj. lay_open LAY.
      pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
      unfold upqR, PQ_CONT. zs2. shl_norm. ustep PQ_TRAP. zs2.
      h32_store HPA HP 573 (dl_As L + 3008) k (arr_get HP j') ltac:(reflexivity).
      zs2. zs2. shl_norm. strip32. zs2. shl_norm. zs2. reg_as (j' + 0) j'.
      zstep. br_cases K.
      *
        eapply (IH L s t T N HL HM v FC DL DP BC OL SL MC R m0 (arr_set HP k (arr_get HP j')) j' (j' * 2) j');
          [exact HPA| exact DPA| exact GC| exact RDT| eassumption| assumption| exact MU| exact WM| exact AL4| exact RT1| exact RT2| exact RN| rewrite arr_len_set; exact LHP
          | | exact RFC| exact RDP| lia| lia| lia| lia| exact RHL| exact Rv| eapply fuel_ok_S; [exact FU| lia| lia]| exact ER].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
      *
        rewrite pq_out in ER by (rewrite bt_heap_len; lia).
        zs2. zs2. shl_norm. ustep PQ_TRAP.
        apply evt_done. unfold upq_loop_post, upqR. do 10 eexists.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
        split; [exact ER|]. split; [rewrite arr_len_set; exact LHP|]. split; [|lia].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
Qed.


Definition pqdownheap_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM k lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch (Wpq lo sp L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t k = bt_upd s t FC DL HP' HL HM DP BC OL SL MC
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N).

Lemma upq_fin : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM k k' v lo : Z) (FC DL HP HP' DP BC : arr) (OL SL MC : Z) (junk : list byte) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s0 s1 x9 a0 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP' 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> mem_inv usegs m -> dlay_ok L ->
  munch (Wpq lo sp L) m0 m -> wmono usegs m0 m ->
  stk usegs m lo (bv_unsigned sp + -64) -> rw_cells usegs m (bv_unsigned sp + -64) [CB 8 junk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] ->
  lo <= bv_unsigned sp - 64 -> dlay_below L lo (bv_unsigned sp) ->
  arr_len HP' = 573 -> (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N) -> 1 <= k' <= HL -> HL < 573 -> 0 <= v < N ->
  pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t k = bt_upd s t FC DL (arr_set HP' k' v) HL HM DP BC OL SL MC ->
  evt usegs (pqdownheap_post L s t T N HL HM k lo FC DL HP DP BC OL SL MC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0)
      (MS (mkR ra (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (k' * 4)) x9 a0 a1 (wz (dl_As L + 3008)) a3 (wz v) a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz PQ_FIN) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA DPA GC MI LAY MU WM STK FR LO BEL LHP PQ Rk RHL Rv EQ. unfold PQ_FIN.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0.
  pose proof (av32_zlength HP' 573 ltac:(lia)) as L32.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  zs2.
  h32_store HPA HP' 573 (dl_As L + 3008) k' v ltac:(reflexivity).
  do 7 zstep. zstep. zstep.
  release_frame FR STK (bv_unsigned sp).
  apply evt_done. unfold pqdownheap_post. do 17 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
  split; [exact HPA|]. split; [eassumption|]. split; [eassumption|]. split; [exact EQ|].
  split; [rewrite arr_len_set; exact LHP|].
  intros i Hi. destruct (Z.eq_dec k' i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rv| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
Qed.

Lemma pqdownheap_spec : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM k lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wpq lo sp L) m T FC DL N -> mem_inv usegs m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= k <= HL -> HL < 573 ->
  a0 = wz (dl_As L) -> a1 = wz T -> a2 = wz k ->
  evt usegs (pqdownheap_post L s t T N HL HM k lo FC DL HP DP BC OL SL MC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz Z_PQDOWNHEAP) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA DPA GC RDT MI LAY STK LO BEL AL4 RT1 RT2 RN LHP PQ RFC RDP Rk RHL -> -> ->. unfold Z_PQDOWNHEAP, Z_PQ_STACK in *.
  pose proof (munch_refl (Wpq lo sp L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (PQ k ltac:(lia)) as Rv.
  carve_frame 64%nat STK.
  do 8 zstep.
  do 2 ustep PQ_TRAP. zs2. zs2. rewrite (Z.mod_small k 4294967296) by lia.
  do 2 ustep PQ_TRAP. zs2. zs2. reg_as (dl_As L + 2047 + 961) (dl_As L + 3008). zs2. shl_norm. ustep PQ_TRAP. ustep PQ_TRAP.
  zs2. zs2. zs2. zs2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read usegs mm _ (av32 HP 573) k _ (wa (dl_As L + 3008 + k * 4)) HPA (av32_nth HP 573 k ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDk end.
  zs2. zs2. zs2. shl_norm. strip32.
  zstep. br_cases K.
  -
    zs2. zs2. zs2. zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2.
    rewrite (zb_lxor_ones (dl_As L + 5308)) by lia.
    rewrite hz29 by lia. rewrite hz28 by first [lia | Z.div_mod_to_equations; lia]. rewrite xor_guard by lia. rewrite hz17 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (upq_loop 32 L s t T N HL HM (arr_get HP k) FC DL DP BC OL SL MC
              (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP k) k (k * 2)) mm HP k (k * 2) k) end.
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. }
    1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact Rv. }
    1:{ unfold fuel_ok. change (2 ^ Z.of_nat 32) with 4294967296. lia. } 1:{ reflexivity. }
    match goal with E : pqdownheap_loop _ _ _ _ _ _ = (bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, ?kk), H : u32arr usegs ?mm _ (av32 ?hp 573), HD : u8arr usegs ?mm _ (av8 DP 573),
                     HG : rw_cells usegs ?mm (dl_As L + 5300) _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      unfold upqR;
      eapply (upq_fin L s t T N HL HM k kk (arr_get HP k) lo FC DL HP hp DP BC OL SL MC);
        [exact H| exact HD| exact HG| eassumption| exact LAY| exact MU| exact WM| exact STK| exact FR| lia| exact BEL| exact HL'| exact HQ| lia| exact RHL| exact Rv|
         rewrite pqdownheap_flat, E; cbn [fst snd]; rewrite bt_heap_set; reflexivity] end.
  -
    zs2. shl_norm. zstep. br_true.
    eapply (upq_fin L s t T N HL HM k k (arr_get HP k) lo FC DL HP HP DP BC OL SL MC);
      [exact HPA| exact DPA| exact GC| eassumption| exact LAY| exact MU| exact WM| exact STK| exact FR| lia| exact BEL| exact LHP| exact PQ| lia| exact RHL| exact Rv|].
    rewrite pqdownheap_flat, pq_out by (rewrite bt_heap_len; lia). cbn [fst snd]. rewrite bt_heap_set. reflexivity.
Qed.
End Z_tr_pq.

Module Z_tr_bt1.
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
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_pq OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_bt13.Z_tr_bt_mid.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.



Definition ubt1R (L : dlay) (T E n mc stp : Z) (x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) :=
  mkR ra sp gp tp (wz (ONES - (dl_As L + 3008))) (wz (dl_As L + 5308)) (wz (ONES - (dl_As L + 5308))) s0 s1 (wz stp) (wz E) (wz n) (wz n)
      (wz (dl_As L + 3008)) (wz (T + 4 * n + 2)) (wz (4 * n + 2)) (wz 573) s2 s3 s4 s5 (wz T) s7 s8 (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s11
      (wz 572) (wz mc) x30 x31.

Notation ubt_f16 dsc t L T := ([C8 (wz dsc); C8 (wz 0); C8 (wz (sd_elems t)); C8 (wz (dl_As L + 5912)); C8 (wz (ONES - T)); C8 (wz (dl_As L))])%list (only parsing).

Notation Wbt1 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5881)] (only parsing).

Definition ubt1_post (L : dlay) (s : deflate_state) (t : tree_id) (T N stp : Z) (FC BC : arr) (HM OL SL MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x30 x31 DL' HP' HL' DP' mc' m',
    ms' = MS (ubt1R L T (sd_elems t) (sd_elems t) mc' stp x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11) F (wz BT_L1X) fc None m' (seg_rom usegs)
    /\ munch (Wbt1 L T N) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL'); C4 (wz HM)]
    /\ R = (bt_upd s t FC DL' HP' HL' HM DP' BC OL SL MC, mc')
    /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ 0 <= HL' <= sd_elems t /\ -1 <= mc' < sd_elems t.

Lemma ubt_loop1 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N stp dsc : Z) (FC BC : arr) (HM OL SL MC : Z) (R : deflate_state * Z) (m0 : mem)
    (DL HP : arr) (HL : Z) (DP : arr) (n mc : Z)
    (x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) ->
  mem_inv usegs m -> dlay_ok L -> munch (Wbt1 L T N) m0 m -> wmono usegs m0 m ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> sd_elems t < N -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) ->
  0 <= HL <= n -> 0 <= n -> Z.of_nat (S f) = sd_elems t - n -> -1 <= mc < sd_elems t ->
  R = L1 t (bt_upd s t FC DL HP HL HM DP BC OL SL MC) n mc ->
  evt usegs (ubt1_post L s t T N stp FC BC HM OL SL MC R ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 F fc m0)
      (MS (ubt1R L T (sd_elems t) n mc stp x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11) F (wz BT_L1) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA DPA GC F16 MI LAY MU WM Bsp Rsp AL4 RT1 RT2 REN LFC LDL LHP LDP RFC RHL Rn Ef Rmc ER.
  all: pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.elems_range t) as RE.
  all: lay_open LAY.
  all: rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.L1_step in ER by lia.
  all: pose proof (RFC n ltac:(lia)) as Rf.
  all: pose proof (u16arr_read usegs m T (avct FC DL N) (2 * n) _ (wa (T + 4 * n + 2 + -2)) ARR (avct_nth_fc FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDf.
  all: pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  all: unfold ubt1R, BT_L1; zs2; reg_as (mc + 0) mc; zs2; reg_as (4 * n + 2 + -2) (n * 4); zs2; ustep BT_TRAP; zs2; ustep BT_TRAP.
  all: zs2; rewrite zx16_small by lia; zstep; br_cases_s K.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K) in ER. cbn [negb] in ER.
    ct_store_dl ARR FC DL N T n (wrap16 0) ltac:(reflexivity).
    zs2. reg_as (mc + 0) mc. zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (4 * n + 6) (4 * (n + 1) + 2).
    zstep. br_cases_s K2; [|exfalso; lia].
    replace (n + 1) with (sd_elems t) in * by lia. rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.L1_end in ER.
    apply evt_done. unfold ubt1_post, ubt1R, BT_L1X. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
    split; [exact ER|]. rewrite ?arr_len_set. repeat split; lia.
  -
    rewrite (proj2 (Z.eqb_neq _ _) K) in ER. cbn [negb] in ER.
    zs2. zs2. ustep BT_TRAP. zstep. ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. shl_norm. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) n ltac:(reflexivity).
    ustep BT_TRAP. ustep BT_TRAP. zs2.
    pb_store DPA DP 573 (dl_As L + 5308) n (wrap8 0) ltac:(reflexivity).
    zs2. reg_as (n + 0) n. zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (4 * n + 6) (4 * (n + 1) + 2).
    zstep. br_cases_s K2; [exfalso; lia|].
    replace (n + 1) with (sd_elems t) in * by lia. rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.L1_end in ER.
    apply evt_done. unfold ubt1_post, ubt1R, BT_L1X. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|]. split; [eassumption|].
    split; [exact ER|]. rewrite ?arr_len_set. repeat split; lia.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K) in ER. cbn [negb] in ER.
    ct_store_dl ARR FC DL N T n (wrap16 0) ltac:(reflexivity).
    zs2. reg_as (mc + 0) mc. zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (4 * n + 6) (4 * (n + 1) + 2).
    zstep. br_cases_s K2; [exfalso; lia|].
    eapply (IH L s t T N stp dsc FC BC HM OL SL MC R m0 (arr_set DL n (wrap16 0)) HP HL DP (n + 1) mc);
      [exact ARR| exact HPA| exact DPA| exact GC| eassumption| eassumption| exact LAY| exact MU| exact WM| exact Bsp| exact Rsp| exact AL4| exact RT1| exact RT2| exact REN| exact LFC
      | rewrite arr_len_set; exact LDL| exact LHP| exact LDP| exact RFC| lia| lia| lia| exact Rmc| exact ER].
  -
    rewrite (proj2 (Z.eqb_neq _ _) K) in ER. cbn [negb] in ER.
    zs2. zs2. ustep BT_TRAP. zstep. ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. shl_norm. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) n ltac:(reflexivity).
    ustep BT_TRAP. ustep BT_TRAP. zs2.
    pb_store DPA DP 573 (dl_As L + 5308) n (wrap8 0) ltac:(reflexivity).
    zs2. reg_as (n + 0) n. zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (4 * n + 6) (4 * (n + 1) + 2).
    zstep. br_cases_s K2; [|exfalso; lia].
    eapply (IH L s t T N stp dsc FC BC HM OL SL MC R m0 DL (arr_set HP (HL + 1) n) (HL + 1) (arr_set DP n (wrap8 0)) (n + 1) n);
      [exact ARR| exact HPA| exact DPA| eassumption| eassumption| eassumption| exact LAY| exact MU| exact WM| exact Bsp| exact Rsp| exact AL4| exact RT1| exact RT2| exact REN| exact LFC| exact LDL
      | rewrite arr_len_set; exact LHP| rewrite arr_len_set; exact LDP| exact RFC| lia| lia| lia| lia| exact ER].
Qed.
End Z_tr_bt1.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.


Definition GB1_HEAD : Z := 0x1cf18.
Definition GB1_LATCH : Z := 0x1cf0c.
Definition GB1_LEAF : Z := 0x1cf90.
Definition GB1_EXIT : Z := 0x1d060.

Definition ugbR (L : dlay) (T h ovf mc ML stp xp base : Z) (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) :=
  mkR ra sp gp tp (wz 573) (wz 573) (wz (ONES - T)) s0 s1 (wz T) (wz mc) (wz ML) (wz stp) (wz xp) (wz base) (wz (ONES - (dl_As L + 2976))) (wz ovf)
      s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 (wz (dl_As L + 5912)) s11 (wz (573 - h)) (wz (4 * h)) (wz 16) t6.

Definition ugb1_head_post (L : dlay) (T N h ovf base mc ML stp xp n bits ovf' : Z) (FC DL' : arr)
    (sp ra gp tp s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s5 m',
    ms' = MS (ugbR L T h ovf' mc ML stp xp base sp ra gp tp (wz 0) (wz (T + n * 4)) (wz bits) (wz n) s5 s6 s7 s9 s11 (wz (n * 4))) F
             (wz (if mc <? n then GB1_LATCH else GB1_LEAF)) fc None m' (seg_rom usegs)
    /\ munch [(T, T + 4 * N)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)).

Lemma ugb1_head : forall (L : dlay) (T N h ovf base mc ML stp xp n dlen bits : Z) (FC DL HP : arr)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) ->
  rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] -> mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= h < 573 -> n = arr_get HP h -> 0 <= n < N -> 0 <= arr_get DL n < N -> dlen = arr_get DL (arr_get DL n) -> 0 <= dlen < 65536 -> 1 <= ML <= 15 ->
  0 <= ovf < 2^30 -> -1 <= mc < 2^31 ->
  bits = (if ML <=? dlen then ML else dlen + 1) ->
  evt usegs (ugb1_head_post L T N h ovf base mc ML stp xp n bits (if ML <=? dlen then ovf + 1 else ovf) FC (arr_set DL n (wrap16 bits)) sp ra gp tp s6 s7 s9 s11 F fc m)
      (MS (ugbR L T h ovf mc ML stp xp base sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz 0x1cf18) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA F64 MI LAY RT1 RT2 RN LFC LDL LHP SEP RSP Rh En Rn Rd Ed Rdl RML Ro Rmc Eb.
  pose proof (munch_refl [(T, T + 4 * N)] m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  pose proof (u32arr_read usegs m _ (av32 HP 573) h _ (wa (dl_As L + 3008 + 4 * h)) HPA (av32_nth HP 573 h ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn. rewrite <- En in RDn.
  pose proof (u16arr_read usegs m T (avct FC DL N) (2 * n + 1) _ (wa (T + n * 4 + 2)) ARR (avct_nth_dl FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDd.
  pose proof (u16arr_read usegs m T (avct FC DL N) (2 * arr_get DL n + 1) _ (wa (T + arr_get DL n * 4 + 2)) ARR (avct_nth_dl FC DL N (arr_get DL n) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDl.
  rewrite <- Ed in RDl.
  unfold ugbR. zs2. ustep BT_TRAP. zs2. ustep BT_TRAP. zs2. zs2. zs2. shl_norm. zs2.
  ustep BT_TRAP. zs2. zs2. zs2. zs2. ustep BT_TRAP.
  zs2. rewrite zx16_small by lia. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. rewrite zx16_small by lia.
  zstep. br_cases K.
  -
    rewrite (proj2 (Z.leb_le ML dlen)) in Eb |- * by lia. subst bits.
    zs2. ustep BT_TRAP. zs2. zs2.
    ct_store_dl ARR FC DL N T n (wrap16 ML) ltac:(rewrite (wrap16_id ML) by lia; reflexivity).
    zstep. br_cases K2.
    + apply evt_done. unfold ugb1_head_post, ugbR, GB1_LATCH, GB1_LEAF. rewrite (proj2 (Z.ltb_lt mc n)) by lia.
      do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
    + apply evt_done. unfold ugb1_head_post, ugbR, GB1_LATCH, GB1_LEAF. rewrite (proj2 (Z.ltb_ge mc n)) by lia.
      do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
  - rewrite (proj2 (Z.leb_gt ML dlen)) in Eb |- * by lia. subst bits.
    zs2.
    ct_store_dl ARR FC DL N T n (wrap16 (dlen + 1)) ltac:(rewrite (wrap16_id (dlen + 1)) by lia; reflexivity).
    zstep. br_cases K2.
    + apply evt_done. unfold ugb1_head_post, ugbR, GB1_LATCH, GB1_LEAF. rewrite (proj2 (Z.ltb_lt mc n)) by lia.
      do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
    + zs2. apply evt_done. unfold ugb1_head_post, ugbR, GB1_LATCH, GB1_LEAF. rewrite (proj2 (Z.ltb_ge mc n)) by lia.
      do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
Qed.

Ltac ua16_store ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok usegs _ A (av16 a n) idx (wa (A + 2 * idx)) ARR ltac:(rewrite av16_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av16_write m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      unfold u16arr in ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "L16" in pose proof (av16_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNB" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Definition ugb1_cnt_post (L : dlay) (T h ovf base mc ML stp xp n bits xb : Z) (BC' : arr)
    (sp ra gp tp s6 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s5 s7 s9 m',
    ms' = MS (ugbR L T h ovf mc ML stp xp base sp ra gp tp (wz 0) (wz (T + n * 4)) (wz bits) (wz xb) s5 s6 s7 s9 s11 (wz (n * 4))) F (wz 0x1d000) fc None m' (seg_rom usegs)
    /\ munch [(dl_As L + 2976, dl_As L + 3008)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16)).

Lemma ugb1_cnt : forall (L : dlay) (t : tree_id) (T h ovf mc stp xp n bits : Z) (BC : arr)
    (sp ra gp tp s5 s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv usegs m -> dlay_ok L -> arr_len BC = 16 ->
  xbits_view t xp -> 0 < xp < 2^32 -> xp mod 4 = 0 -> 0 <= n -> n <= mc -> mc < sd_elems t -> 1 <= bits <= 15 -> 0 <= sd_extra_base t < 2^31 -> sd_elems t < 2^31 ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  evt usegs (ugb1_cnt_post L T h ovf (sd_extra_base t) mc (sd_max_length t) stp xp n bits (xbits t n) (arr_set BC bits (wrap16 (arr_get BC bits + 1)))
               sp ra gp tp s6 s11 F fc m)
      (MS (ugbR L T h ovf mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp (wz 0) (wz (T + n * 4)) (wz bits) (wz n) s5 s6 s7 s9 s11 (wz (n * 4)))
          F (wz 0x1cf90) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros BLC MI LAY LBC XV Rxp Axp Rn0 Rn Rmc Rb Rbase RE RBC.
  pose proof (munch_refl [(dl_As L + 2976, dl_As L + 3008)] m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY.
  pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  pose proof (av16_zlength BC 16 ltac:(lia)) as L16. pose proof (RBC bits ltac:(lia)) as Rcb.
  pose proof (u16arr_read usegs m _ (av16 BC 16) bits _ (wa (dl_As L + 2976 + bits * 2)) BLC (av16_nth BC 16 bits ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDb.
  unfold ugbR. ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. zs2.
  ua16_store BLC BC 16 (dl_As L + 2976) bits (wrap16 (arr_get BC bits + 1)) ltac:(apply le2_add_sx16).
  zstep. br_cases K.
  - assert (EX : xbits t n = arr_get (sd_extra_bits t) (n - sd_extra_base t)) by (unfold xbits; rewrite (proj2 (Z.leb_le _ _) K); reflexivity).
    match goal with MI' : mem_inv usegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (XV mm n MI' ltac:(lia)) as [RDx Rx] end.
    rewrite <- EX in RDx, Rx.
    zs2. zs2. try rewrite (bv_swrap32_id (n - sd_extra_base t)) by lia. try rewrite (bv_swrap32_id (n + - sd_extra_base t)) by lia.
    ustep BT_TRAP. zs2. zs2. try rewrite (bv_swrap32_id (n - sd_extra_base t)) by lia. try rewrite (bv_swrap32_id (n + - sd_extra_base t)) by lia.
    zs2. shl_norm. zs2. zs2.
    ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP.
    zs2.
    apply evt_done. unfold ugb1_cnt_post, ugbR. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact BLC].
  - assert (EX : xbits t n = 0) by (unfold xbits; rewrite (proj2 (Z.leb_gt _ _)) by lia; reflexivity). rewrite EX.
    zs2. zs2.
    apply evt_done. unfold ugb1_cnt_post, ugbR. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact BLC].
Qed.

Notation uWgl L := [(dl_As L + 5881, dl_As L + 5968)] (only parsing).

Definition ugb1_len_post (L : dlay) (s : deflate_state) (T h ovf base mc ML stp xp xb : Z) (OL' SL' : Z)
    (sp ra gp tp s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s5 t6 h0 h1 h2 h3 h4 m',
    ms' = MS (ugbR L T h ovf mc ML stp xp base sp ra gp tp s0 s1 s2 (wz xb) s5 s6 s7 s9 s11 t6) F (wz 0x1cf0c) fc None m' (seg_rom usegs)
    /\ munch (uWgl L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4).

Lemma ugb1_len : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf base mc ML stp xp n bits xb OL SL : Z) (FC DL : arr) (h0 h1 h2 h3 h4 : list byte)
    (sp ra gp tp s5 s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  stree_view_n t stp -> stp mod 4 = 0 -> 0 <= n < N -> n < sd_elems t -> 0 <= arr_get FC n < 65536 -> 1 <= bits <= 15 -> 0 <= xb < 16 -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  evt usegs (ugb1_len_post L s T h ovf base mc ML stp xp xb (wrap64 (OL + arr_get FC n * (bits + xb)))
               (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xb)) else SL) sp ra gp tp s6 s7 s9 s11 F fc m)
      (MS (ugbR L T h ovf mc ML stp xp base sp ra gp tp (wz 0) (wz (T + n * 4)) (wz bits) (wz xb) s5 s6 s7 s9 s11 (wz (n * 4)))
          F (wz 0x1d000) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR GD MI LAY RT1 RT2 RN SV Astp Rn RnE Rf Rb Rx ROL RSL.
  pose proof (munch_refl (uWgl L) m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY. unfold bD_cells in GD.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT.
  pose proof (u16arr_read usegs m T (avct FC DL N) (2 * n) _ (wa (T + n * 4)) ARR (avct_nth_fc FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDf.
  unfold ugbR. zs2. zs2. try rewrite (bv_swrap32_id (bits + xb)) by lia. ustep BT_TRAP.
  zs2. rewrite zx16_small by lia. zs2. zs2. zs2.
  try rewrite (Z.mod_small (bits + xb) 4294967296) by lia. try rewrite (Z.mod_small ((bits + xb) * 4294967296) 18446744073709551616) by lia.
  zs2. zs2. zstep.
  zstep. destruct SV as [[Es Eh]|(Rs0 & Eh & RDS)]; rewrite Eh.
  - subst stp. br_true.
    apply evt_done. unfold ugb1_len_post, ugbR, bD_cells. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    rewrite wz_wrap64. replace (OL + arr_get FC n * (bits + xb)) with (OL + (bits + xb) * arr_get FC n) by lia. eassumption.
  - br_false. match goal with MI' : mem_inv usegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (RDS mm n MI' ltac:(lia)) as [RDl Rsl] end.
    zs2. replace (wz (n * 4 + stp)) with (wz (stp + n * 4)) by (f_equal; lia).
    ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP.
    zs2. rewrite zx16_small by lia. zs2. zs2. try rewrite (bv_swrap32_id (stree_Len t n + xb)) by lia. ustep BT_TRAP.
    zs2. zs2. zs2. try rewrite (Z.mod_small (stree_Len t n + xb) 4294967296) by lia. try rewrite (Z.mod_small ((stree_Len t n + xb) * 4294967296) 18446744073709551616) by lia.
    zs2. zs2. zstep.
    apply evt_done. unfold ugb1_len_post, ugbR, bD_cells. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    rewrite !wz_wrap64.
    replace (OL + arr_get FC n * (bits + xb)) with (OL + (bits + xb) * arr_get FC n) by lia.
    replace (SL + arr_get FC n * (stree_Len t n + xb)) with (SL + (stree_Len t n + xb) * arr_get FC n) by lia. eassumption.
Qed.

Definition ugb1_latch_post (L : dlay) (T h ovf base mc ML stp xp : Z)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists pcx m',
    ms' = MS (ugbR L T (h + 1) ovf mc ML stp xp base sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ ((pcx = 0x1cf18 /\ h + 1 < 573) \/ (pcx = 0x1d060 /\ h + 1 = 573)).

Lemma ugb1_latch : forall (L : dlay) (T h ovf base mc ML stp xp : Z)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv usegs m -> 0 <= h < 573 ->
  evt usegs (ugb1_latch_post L T h ovf base mc ML stp xp sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 F fc m)
      (MS (ugbR L T h ovf mc ML stp xp base sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz 0x1cf0c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros MI Rh.
  unfold ugbR. zs2. zs2. zstep. br_cases K; reg_as (573 - h - 1) (573 - (h + 1)); reg_as (573 - h + -1) (573 - (h + 1)); reg_as (4 * h + 4) (4 * (h + 1)).
  - apply evt_done. unfold ugb1_latch_post, ugbR. do 2 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    first [right; split; [reflexivity| lia] | left; split; [reflexivity| lia]].
  - apply evt_done. unfold ugb1_latch_post, ugbR. do 2 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    first [right; split; [reflexivity| lia] | left; split; [reflexivity| lia]].
Qed.

Notation uWgb L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 2976, dl_As L + 3008); (dl_As L + 5881, dl_As L + 5968)] (only parsing).

Definition ugb1_iter_post (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf mc stp xp : Z) (FC HP : arr) (HL HM : Z) (DP : arr) (f : nat) (R : deflate_state * Z)
    (sp ra gp tp s6 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s4 s5 s7 s9 t6 h0 h1 h2 h3 h4 DL' BC' OL' SL' ovf' pcx m',
    ms' = MS (ugbR L T (h + 1) ovf' mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (uWgb L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4)
    /\ R = gen_bitlen_loop1 f (bt_upd s t FC DL' HP HL HM DP BC' OL' SL' mc) t mc (sd_extra_base t) (sd_max_length t) (h + 1) ovf'
    /\ gb1_ok t mc f (bt_upd s t FC DL' HP HL HM DP BC' OL' SL' mc) (h + 1) ovf'
    /\ arr_len DL' = N /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536) /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64 /\ ovf <= ovf' <= ovf + 1
    /\ ((pcx = 0x1cf18 /\ h + 1 < 573) \/ (pcx = 0x1d060 /\ h + 1 = 573)).

Lemma ugb1_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf mc stp xp OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (f : nat) (R : deflate_state * Z)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] ->
  mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp -> 0 < xp < 2^32 -> xp mod 4 = 0 -> stp mod 4 = 0 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= h < 573 -> 0 <= ovf <= h -> -1 <= mc < sd_elems t -> 0 <= arr_get HP h < N ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  R = gen_bitlen_loop1 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc (sd_extra_base t) (sd_max_length t) h ovf ->
  gb1_ok t mc (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL mc) h ovf ->
  evt usegs (ugb1_iter_post L s t T N h ovf mc stp xp FC HP HL HM DP f R sp ra gp tp s6 s11 F fc m)
      (MS (ugbR L T h ovf mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz 0x1cf18) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA BLC GD F64 MI LAY RT1 RT2 EN LFC LDL LHP LBC XV SV Rxp Axp Astp SEP RSP Rh Ro Rmc Rn RBC RDL RFC ROL RSL ER OK.
  pose proof (munch_refl (uWgb L T N) m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (RML : 7 <= sd_max_length t <= 15) by (destruct t; cbv; split; discriminate).
  assert (RBASE : 0 <= sd_extra_base t < 300) by (destruct t; cbv; split; congruence).
  assert (RE : 19 <= sd_elems t <= 286 /\ tsize t = 2 * sd_elems t + 1) by (destruct t; cbv; repeat split; congruence).
  set (n := arr_get HP h) in *. set (dlen := arr_get DL (arr_get DL n)).
  set (bits := if sd_max_length t <=? dlen then sd_max_length t else dlen + 1). set (ovf' := if sd_max_length t <=? dlen then ovf + 1 else ovf).
  destruct (gb1_ok_step s t FC DL HP HL HM DP BC OL SL mc f h ovf n dlen bits ovf' OK ltac:(lia) eq_refl eq_refl eq_refl eq_refl) as [RD OK'].
  pose proof (gb1_model s t FC DL HP HL HM DP BC OL SL mc f h ovf R n dlen bits ovf' ER ltac:(lia) eq_refl eq_refl eq_refl eq_refl) as ER'.
  clear ER OK. rewrite <- EN in RD.
  assert (Rdl : 0 <= dlen < 65536) by (apply RDL; exact RD).
  assert (Rb : 1 <= bits <= 15) by (subst bits; destruct (Z.leb_spec (sd_max_length t) dlen); lia).
  assert (Ro' : ovf <= ovf' <= ovf + 1) by (subst ovf'; destruct (sd_max_length t <=? dlen); lia).
  assert (Rx0 : n <= mc -> 0 <= xbits t n < 16).
  { intros Hn. unfold xbits. destruct (Z.leb_spec (sd_extra_base t) n); [|lia]. destruct (XV m n MI ltac:(lia)) as [_ X]. exact X. }
  call (ugb1_head L T N h ovf (sd_extra_base t) mc (sd_max_length t) stp xp n dlen bits FC DL HP sp).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. }
  1:{ exact SEP. } 1:{ exact RSP. } 1:{ exact Rh. } 1:{ reflexivity. } 1:{ exact Rn. } 1:{ exact RD. } 1:{ reflexivity. } 1:{ exact Rdl. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ reflexivity. }
  fold ovf'.
  pose proof (avct_zlength FC (arr_set DL n (wrap16 bits)) N ltac:(lia)) as LCT'. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  pose proof (av16_zlength (arr_set BC bits (wrap16 (arr_get BC bits + 1))) 16 ltac:(lia)) as L16'.
  unfold ugbR. destruct (Z.ltb_spec mc n) as [K|K].
  - try rewrite (proj2 (Z.ltb_lt mc n) K) in ER', OK'. unfold GB1_LATCH.
    call (ugb1_latch L T h ovf' (sd_extra_base t) mc (sd_max_length t) stp xp sp).
    1:{ eassumption. } 1:{ exact Rh. }
    apply evt_done. unfold ugb1_iter_post. do 13 eexists. exists (arr_set DL n (wrap16 bits)), BC, OL, SL, ovf'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [exact BLC|]. split; [exact GD|].
    split; [exact ER'|]. split; [exact OK'|]. split; [rewrite arr_len_set; exact LDL|]. split; [exact LBC|]. split; [exact RBC|].
    split; [intros i Hi; destruct (Z.eq_dec n i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RDL; exact Hi]|].
    split; [exact ROL|]. split; [exact RSL|]. split; [exact Ro'|]. assumption.
  - try rewrite (proj2 (Z.ltb_ge mc n)) in ER', OK' by lia. unfold GB1_LEAF.
    pose proof (Rx0 ltac:(lia)) as Rx.
    call (ugb1_cnt L t T h ovf' mc stp xp n bits BC sp).
    1:{ exact BLC. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact LBC. } 1:{ exact XV. } 1:{ exact Rxp. } 1:{ exact Axp. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rb. } 1:{ lia. } 1:{ lia. } 1:{ exact RBC. }
    match goal with HT : u8arr usegs ?mm T _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (ugb1_len L s t T N h ovf' (sd_extra_base t) mc (sd_max_length t) stp xp n bits (xbits t n) OL SL FC (arr_set DL n (wrap16 bits)) h0 h1 h2 h3 h4 sp);
      [exact HT| exact GD| eassumption| exact LAY| exact RT1| exact RT2| lia| exact SV| exact Astp| exact Rn| lia| apply RFC; exact Rn| exact Rb| exact Rx| exact ROL| exact RSL|] end.
    call (ugb1_latch L T h ovf' (sd_extra_base t) mc (sd_max_length t) stp xp sp).
    1:{ eassumption. } 1:{ exact Rh. }
    apply evt_done. unfold ugb1_iter_post. do 13 eexists. exists (arr_set DL n (wrap16 bits)), (arr_set BC bits (wrap16 (arr_get BC bits + 1))).
    exists (wrap64 (OL + arr_get FC n * (bits + xbits t n))), (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xbits t n)) else SL), ovf'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER'|]. split; [exact OK'|]. split; [rewrite arr_len_set; exact LDL|]. split; [rewrite arr_len_set; exact LBC|].
    split; [intros i Hi; destruct (Z.eq_dec bits i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RBC; exact Hi]|].
    split; [intros i Hi; destruct (Z.eq_dec n i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RDL; exact Hi]|].
    split; [apply wrap64_range|]. split; [destruct (stree_has t); [apply wrap64_range| exact RSL]|]. split; [exact Ro'|]. assumption.
Qed.

Definition ugb1_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N mc stp xp : Z) (FC HP : arr) (HL HM : Z) (DP : arr) (R : deflate_state * Z)
    (sp ra gp tp s6 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s4 s5 s7 s9 t6 h0 h1 h2 h3 h4 DL' BC' OL' SL' ovf' m',
    ms' = MS (ugbR L T 573 ovf' mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz 0x1d060) fc None m' (seg_rom usegs)
    /\ munch (uWgb L T N) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4)
    /\ R = (bt_upd s t FC DL' HP HL HM DP BC' OL' SL' mc, ovf')
    /\ arr_len DL' = N /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536) /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64 /\ 0 <= ovf' <= 573.

Lemma ugb1_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf mc stp xp OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R : deflate_state * Z) (m0 : mem)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] ->
  mem_inv usegs m -> dlay_ok L -> munch (uWgb L T N) m0 m -> wmono usegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp -> 0 < xp < 2^32 -> xp mod 4 = 0 -> stp mod 4 = 0 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= h < 573 -> 573 - h <= Z.of_nat f -> 0 <= ovf <= h -> -1 <= mc < sd_elems t -> (forall k, h <= k < 573 -> 0 <= arr_get HP k < N) ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  R = gen_bitlen_loop1 f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc (sd_extra_base t) (sd_max_length t) h ovf ->
  gb1_ok t mc f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) h ovf ->
  evt usegs (ugb1_loop_post L s t T N mc stp xp FC HP HL HM DP R sp ra gp tp s6 s11 F fc m0)
      (MS (ugbR L T h ovf mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz 0x1cf18) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA BLC GD F64 MI LAY MU WM RT1 RT2 EN LFC LDL LHP LBC XV SV Rxp Axp Astp SEP RSP Rh Hf Ro Rmc RHP RBC RDL RFC ROL RSL ER OK.
  { exfalso. lia. }
  pose proof (avct_zlength FC DL N ltac:(destruct t; subst N; cbv; discriminate)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  call (ugb1_iter L s t T N h ovf mc stp xp OL SL FC DL HP HL HM DP BC h0 h1 h2 h3 h4 f R sp).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact BLC. } 1:{ exact GD. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact EN. } 1:{ exact LFC. } 1:{ exact LDL. }
  1:{ exact LHP. } 1:{ exact LBC. } 1:{ exact XV. } 1:{ exact SV. } 1:{ exact Rxp. } 1:{ exact Axp. } 1:{ exact Astp. } 1:{ exact SEP. } 1:{ exact RSP. }
  1:{ exact Rh. } 1:{ exact Ro. } 1:{ exact Rmc. } 1:{ apply RHP; lia. } 1:{ exact RBC. } 1:{ exact RDL. } 1:{ exact RFC. }
  1:{ exact ROL. } 1:{ exact RSL. } 1:{ exact ER. } 1:{ exact OK. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)), HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                     HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' ?sl' ?g0 ?g1 ?g2 ?g3 ?g4), HC : rw_cells usegs ?mm (bv_unsigned sp + 64) _,
                     ER' : R = gen_bitlen_loop1 f _ _ _ _ _ _ ?o', OK' : gb1_ok t mc f _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N (h + 1) o' mc stp xp ol' sl' FC dl' HP HL HM DP bc' g0 g1 g2 g3 g4 R m0);
        [exact HT| exact HPA| exact HB| exact HG| exact HC| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact EN| exact LFC| assumption| exact LHP| assumption
        | exact XV| exact SV| exact Rxp| exact Axp| exact Astp| exact SEP| exact RSP| lia| lia| lia| exact Rmc| intros k Hk; apply RHP; lia| assumption| assumption| exact RFC| assumption| assumption| exact ER'| exact OK'] end.
  - match goal with ER' : R = gen_bitlen_loop1 f _ _ _ _ _ _ _ |- _ => rewrite gb1_done in ER' by lia end.
    replace (h + 1) with 573 by lia.
    apply evt_done. unfold ugb1_loop_post. do 13 eexists.
    match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)), HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                     HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' ?sl' ?g0 ?g1 ?g2 ?g3 ?g4), ER' : R = (_, ?o') |- _ =>
      exists dl', bc', ol', sl', o'; eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HB|]; split; [exact HG|];
      split; [exact ER'|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; lia end.
Qed.
