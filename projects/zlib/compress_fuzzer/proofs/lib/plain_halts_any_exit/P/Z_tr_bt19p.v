(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod InitMem Z_tr_bt2 Z_tr_bt13.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel RefBuildTree1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section Flat.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Local Notation ML := (sd_max_length t).

Definition btX0 : deflate_state :=
  bt_upd s t (tree_fc s t) (tree_dl s t) (ds_heap s) 0 573 (ds_depth s) (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t).

Lemma btX0_eq : set_heap_max (set_heap_len s 0) HEAP_SIZE = btX0.
Proof. unfold btX0. rewrite <- (bt_upd_self s t) at 1. rewrite bt_set_heap_len, bt_set_heap_max. reflexivity. Qed.

Lemma safe_s0 : bt_safe s t ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_fc s t) i < 65536) /\ 0 <= ds_opt_len s < 2 ^ 64 /\ 0 <= ds_static_len s < 2 ^ 64.
Proof. intros H. destruct H as (A & B & C & _). split; [exact A|]. split; [exact B| exact C]. Qed.

Lemma safe_s3 : bt_safe s t ->
  forall FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1 mc1 FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 MC2 mc2,
  build_tree_loop1 (Z.to_nat E) btX0 t E 0 (-1) = (bt_upd s t FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1, mc1) ->
  build_tree_loop2 2 (bt_upd s t FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1) t mc1 = (bt_upd s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 MC2, mc2) ->
  (forall i, 1 <= i <= HL2 -> 0 <= arr_get HP2 i < tsize t)
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP2 i < 256)
  /\ (forall i, 0 <= i < tsize t -> 0 <= arr_get FC2 i < 65536)
  /\ forall FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3 FC4 DL4 HP4 HL4 HM4 DP4 BC4 OL4 SL4 MC4,
     build_tree_loop3 (Z.to_nat (HL2 / 2)) (bt_upd s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 mc2) t (HL2 / 2) = bt_upd s t FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3 ->
     build_tree_loop4 573 (bt_upd s t FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3) t E = bt_upd s t FC4 DL4 HP4 HL4 HM4 DP4 BC4 OL4 SL4 MC4 ->
     arr_len HP4 = 573 -> 1 <= HM4 <= 573 ->
     (forall h, HM4 - 1 + 1 <= h < 573 -> 0 <= arr_get (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) h < tsize t)
     /\ (forall i, 0 <= i < tsize t -> 0 <= arr_get DL4 i < 65536)
     /\ gb1_ok t mc2 573 (bt_upd s t FC4 (arr_set DL4 (arr_get HP4 1) (wrap16 0)) (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 (arr_fill BC4 0 16 0) OL4 SL4 MC4) (HM4 - 1 + 1) 0
     /\ (forall X10 ovf,
           gen_bitlen_loop1 573 (bt_upd s t FC4 (arr_set DL4 (arr_get HP4 1) (wrap16 0)) (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 (arr_fill BC4 0 16 0) OL4 SL4 MC4)
              t mc2 (sd_extra_base t) ML (HM4 - 1 + 1) 0 = (X10, ovf) -> ovf <> 0 ->
           gb2_ok ML 573 X10 ovf /\ gb3_ok t mc2 (Z.to_nat ML) (gen_bitlen_loop2 573 X10 ML ovf) ML 573)
     /\ (forall i, 0 <= i <= mc2 -> 0 <= Len (gen_bitlen (bt_upd s t FC4 DL4 (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 BC4 OL4 SL4 MC4) t) t i <= 15).
Proof.
  intros SAFE. intros until mc2. intros E1 E2.
  unfold bt_safe in SAFE. rewrite btX0_eq in SAFE. cbv zeta in SAFE. rewrite E1 in SAFE. cbv beta iota in SAFE. rewrite E2 in SAFE. cbv beta iota in SAFE.
  rewrite !bt_set_max_code, !bt_heap_len in SAFE.
  destruct SAFE as (_ & _ & _ & PQ & RDP & RFC & REST).
  split; [intros i Hi; rewrite <- (bt_heap_get s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 mc2); apply PQ; exact Hi|].
  split; [intros i Hi; rewrite <- (bt_depth_get s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 mc2); apply RDP; exact Hi|].
  split; [intros i Hi; rewrite <- (bt_Freq s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 mc2); apply RFC; exact Hi|].
  intros until MC4. intros E3 E4 LHP4 RHM4.
  rewrite E3, E4 in REST. rewrite !bt_heap_max, !bt_set_heap_max, !bt_heap_get, !bt_heap_set, !bt_heap_max in REST.
  rewrite !bt_bl_count, !bt_set_bl_count, !bt_heap_max, !bt_heap_get, !bt_set_Len, !bt_heap_max in REST.
  change (MAX_BITS + 1) with 16 in REST. unfold HEAP_SIZE, SMALLEST in REST.
  rewrite (arr_get_set_same HP4 (HM4 - 1) (arr_get HP4 1)) in REST by lia.
  destruct REST as (RHP & RDL & OK1 & OK23 & LEN).
  split; [intros h Hh; rewrite <- (bt_heap_get s t FC4 DL4 (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 BC4 OL4 SL4 MC4); apply RHP; exact Hh|].
  split; [intros i Hi; rewrite <- (bt_tree_dl s t FC4 DL4 (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 BC4 OL4 SL4 MC4); apply RDL; exact Hi|].
  split; [exact OK1|]. split; [| exact LEN].
  intros X10 ovf EQ NZ. rewrite EQ in OK23. exact (OK23 NZ).
Qed.

Lemma build_tree_flat :
  forall FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1 mc1 FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 MC2 mc2
         FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3 FC4 DL4 HP4 HL4 HM4 DP4 BC4 OL4 SL4 MC4,
  build_tree_loop1 (Z.to_nat E) btX0 t E 0 (-1) = (bt_upd s t FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1, mc1) ->
  build_tree_loop2 2 (bt_upd s t FC1 DL1 HP1 HL1 HM1 DP1 BC1 OL1 SL1 MC1) t mc1 = (bt_upd s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 MC2, mc2) ->
  build_tree_loop3 (Z.to_nat (HL2 / 2)) (bt_upd s t FC2 DL2 HP2 HL2 HM2 DP2 BC2 OL2 SL2 mc2) t (HL2 / 2) = bt_upd s t FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3 ->
  build_tree_loop4 573 (bt_upd s t FC3 DL3 HP3 HL3 HM3 DP3 BC3 OL3 SL3 MC3) t E = bt_upd s t FC4 DL4 HP4 HL4 HM4 DP4 BC4 OL4 SL4 MC4 ->
  build_tree s t = gen_codes (gen_bitlen (bt_upd s t FC4 DL4 (arr_set HP4 (HM4 - 1) (arr_get HP4 1)) HL4 (HM4 - 1) DP4 BC4 OL4 SL4 MC4) t) t mc2.
Proof.
  intros until MC4. intros E1 E2 E3 E4.
  unfold build_tree. cbv zeta. rewrite btX0_eq, E1, E2. rewrite bt_set_max_code, bt_heap_len, E3, E4.
  rewrite bt_heap_max, bt_set_heap_max, bt_heap_max, bt_heap_get, bt_heap_set. unfold SMALLEST. reflexivity.
Qed.
End Flat.

Definition STP (t : tree_id) : Z := match t with TL => 0x11df0 | TD => 0x12270 | TB => 0 end.
Definition XP (t : tree_id) : Z := match t with TL => 0x122e8 | TD => 0x1235c | TB => 0x123d4 end.
Definition SDA (t : tree_id) : Z := match t with TL => 0x29478 | TD => 0x29498 | TB => 0x294b8 end.
Definition sd_cells (t : tree_id) : list cell :=
  [C8 (wz (STP t)); C8 (wz (XP t)); C4 (wz (sd_extra_base t)); C4 (wz (sd_elems t)); C4 (wz (sd_max_length t))].

Lemma SDA_range : forall t, 0x29478 <= SDA t <= 0x294b8. Proof. destruct t; cbn; lia. Qed.
Lemma STP_range : forall t, 0 <= STP t < 2 ^ 32. Proof. destruct t; cbn; lia. Qed.
Lemma XP_range : forall t, 0 <= XP t < 2 ^ 32. Proof. destruct t; cbn; lia. Qed.

Ltac relro_cells A cs n :=
  let RC := fresh "RC" in intros m RC; unfold relro_clean, RELRO_LO, RELRO_HI in RC;
  apply (InitMem.rw_cells_recast psegs m A [CB n (cells_bytes cs)] cs);
  [ apply (InitMem.rw_cells_image0 psegs m A (cells_bytes cs));
    [ intros a Ha; apply RC; change (Z.of_nat (length (cells_bytes cs))) with (Z.of_nat n) in Ha; lia
    | vm_compute; reflexivity | lia | change (Z.of_nat (length (cells_bytes cs))) with (Z.of_nat n); lia ]
  | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ].

Lemma sdesc_relro_l : forall m, relro_clean m -> rw_cells psegs m 0x29478 [C8 (wz 0x11df0); C8 (wz 0x122e8); C4 (wz 257); C4 (wz 286); C4 (wz 15)].
Proof. relro_cells 0x29478 [C8 (wz 0x11df0); C8 (wz 0x122e8); C4 (wz 257); C4 (wz 286); C4 (wz 15)] 28%nat. Qed.
Lemma sdesc_relro_d : forall m, relro_clean m -> rw_cells psegs m 0x29498 [C8 (wz 0x12270); C8 (wz 0x1235c); C4 (wz 0); C4 (wz 30); C4 (wz 15)].
Proof. relro_cells 0x29498 [C8 (wz 0x12270); C8 (wz 0x1235c); C4 (wz 0); C4 (wz 30); C4 (wz 15)] 28%nat. Qed.
Lemma sdesc_relro_bl : forall m, relro_clean m -> rw_cells psegs m 0x294b8 [C8 (wz 0); C8 (wz 0x123d4); C4 (wz 0); C4 (wz 19); C4 (wz 7)].
Proof. relro_cells 0x294b8 [C8 (wz 0); C8 (wz 0x123d4); C4 (wz 0); C4 (wz 19); C4 (wz 7)] 28%nat. Qed.

Lemma sdesc_relro : forall t m, relro_clean m -> rw_cells psegs m (SDA t) (sd_cells t).
Proof.
  intros t m RC. destruct t; cbn [SDA sd_cells STP XP sd_extra_base sd_elems sd_max_length]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS;
    [apply sdesc_relro_l| apply sdesc_relro_d| apply sdesc_relro_bl]; exact RC.
Qed.

Lemma rod_extra_blbits : forall m, mem_inv psegs m -> bytes_at psegs m 0x123d4 (u32s (av32 extra_blbits_a 19)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity]. Qed.

Lemma static_ltree_dl_range : forall n, 0 <= n < 288 -> 0 <= arr_get static_ltree_dl n < 16.
Proof. intros n H. ztab_tac 288 (fun i => (0 <=? arr_get static_ltree_dl i) && (arr_get static_ltree_dl i <? 16)) H. lia. Qed.
Lemma static_dtree_dl_range : forall n, 0 <= n < 30 -> 0 <= arr_get static_dtree_dl n < 16.
Proof. intros n H. ztab_tac 30 (fun i => (0 <=? arr_get static_dtree_dl i) && (arr_get static_dtree_dl i <? 16)) H. lia. Qed.
Lemma extra_blbits_range : forall c, 0 <= c < 19 -> 0 <= arr_get extra_blbits_a c < 16.
Proof. intros c H. ztab_tac 19 (fun i => (0 <=? arr_get extra_blbits_a i) && (arr_get extra_blbits_a i <? 16)) H. lia. Qed.

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
  - apply (u32ro_read mm 0x123d4 (av32 extra_blbits_a 19) (n - 0)); [apply rod_extra_blbits; exact MI| apply av32_nth; lia| lia| f_equal; lia].
  - apply extra_blbits_range. lia.
Qed.

Lemma rw_cells_app_iff : forall m A l1 l2,
  rw_cells psegs m A (l1 ++ l2) <-> rw_cells psegs m A l1 /\ rw_cells psegs m (A + Z.of_nat (cells_size l1)) l2.
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

Lemma rw_cells_join2 : forall m A l1 l2 B, rw_cells psegs m A l1 -> rw_cells psegs m B l2 -> B = A + Z.of_nat (cells_size l1) ->
  rw_cells psegs m A (l1 ++ l2).
Proof. intros m A l1 l2 B H1 H2 ->. apply rw_cells_app_iff. split; assumption. Qed.
