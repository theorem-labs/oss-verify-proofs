(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefBuildTree1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.
Definition BT_TRAP : Z := 0x1d480.
Definition BT_L1 : Z := 0x1cee0.
Definition BT_L1X : Z := 0x1cf50.
Definition BT_L2 : Z := 0x1d7d0.
Definition BT_L2X : Z := 0x1cf5c.
Definition BT_L3 : Z := 0x1cf78.
Definition BT_L4 : Z := 0x1cfcc.
Definition BT_PARTB : Z := 0x1d158.
Definition BT_EPI : Z := 0x1d744.
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
Definition STP (t : tree_id) : Z := match t with TL => 0x11e10 | TD => 0x12290 | TB => 0 end.
Definition XP (t : tree_id) : Z := match t with TL => 0x12308 | TD => 0x1237c | TB => 0x123f4 end.
Definition SDA (t : tree_id) : Z := match t with TL => 0x2c350 | TD => 0x2c370 | TB => 0x2c390 end.
Definition sd_cells (t : tree_id) : list cell :=
  [C8 (wz (STP t)); C8 (wz (XP t)); C4 (wz (sd_extra_base t)); C4 (wz (sd_elems t)); C4 (wz (sd_max_length t))].
Lemma SDA_range : forall t, 0x2c350 <= SDA t <= 0x2c390. Proof. destruct t; cbn; lia. Qed.
Lemma SDA_al8 : forall t, SDA t mod 8 = 0. Proof. destruct t; reflexivity. Qed.
Lemma STP_range : forall t, 0 <= STP t < 2 ^ 32. Proof. destruct t; cbn; lia. Qed.
Lemma XP_range : forall t, 0 <= XP t < 2 ^ 32. Proof. destruct t; cbn; lia. Qed.
Lemma bt_desc_range : forall t, 2904 <= bt_desc t <= 2952 /\ bt_desc t mod 8 = 0.
Proof. destruct t; cbn [bt_desc]; (split; [lia| reflexivity]). Qed.
Ltac relro_cells A cs n :=
  let RC := fresh "RC" in intros m RC; unfold relro_clean, RELRO_LO, RELRO_HI in RC;
  apply (InitMem.rw_cells_recast usegs m A [CB n (cells_bytes cs)] cs);
  [ apply (InitMem.rw_cells_image0 usegs m A (cells_bytes cs));
    [ intros a Ha; apply RC; change (Z.of_nat (length (cells_bytes cs))) with (Z.of_nat n) in Ha; lia
    | vm_compute; reflexivity | lia | change (Z.of_nat (length (cells_bytes cs))) with (Z.of_nat n); lia ]
  | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ].
Lemma sdesc_relro_l : forall m, relro_clean m -> rw_cells usegs m 0x2c350 [C8 (wz 0x11e10); C8 (wz 0x12308); C4 (wz 257); C4 (wz 286); C4 (wz 15)].
Proof. relro_cells 0x2c350 [C8 (wz 0x11e10); C8 (wz 0x12308); C4 (wz 257); C4 (wz 286); C4 (wz 15)] 28%nat. Qed.
Lemma sdesc_relro_d : forall m, relro_clean m -> rw_cells usegs m 0x2c370 [C8 (wz 0x12290); C8 (wz 0x1237c); C4 (wz 0); C4 (wz 30); C4 (wz 15)].
Proof. relro_cells 0x2c370 [C8 (wz 0x12290); C8 (wz 0x1237c); C4 (wz 0); C4 (wz 30); C4 (wz 15)] 28%nat. Qed.
Lemma sdesc_relro_bl : forall m, relro_clean m -> rw_cells usegs m 0x2c390 [C8 (wz 0); C8 (wz 0x123f4); C4 (wz 0); C4 (wz 19); C4 (wz 7)].
Proof. relro_cells 0x2c390 [C8 (wz 0); C8 (wz 0x123f4); C4 (wz 0); C4 (wz 19); C4 (wz 7)] 28%nat. Qed.
Lemma sdesc_relro : forall t m, relro_clean m -> rw_cells usegs m (SDA t) (sd_cells t).
Proof.
  intros t m RC. destruct t; cbn [SDA sd_cells STP XP sd_extra_base sd_elems sd_max_length]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS;
    [apply sdesc_relro_l| apply sdesc_relro_d| apply sdesc_relro_bl]; exact RC.
Qed.
Lemma rod_extra_blbits : forall m, mem_inv usegs m -> bytes_at usegs m 0x123f4 (u32s (av32 extra_blbits_a 19)).
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
  - apply (u32ro_read mm 0x123f4 (av32 extra_blbits_a 19) (n - 0)); [apply rod_extra_blbits; exact MI| apply av32_nth; lia| lia| f_equal; lia].
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
