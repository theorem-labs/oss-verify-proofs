(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState.

Module Z_tr_rod.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_DIST_CODE : Z := 0x11ab0.
Definition Z_LENGTH_CODE : Z := 0x11cb0.
Definition Z_STATIC_LTREE : Z := 0x11db0.
Definition Z_STATIC_DTREE : Z := 0x12230.
Definition Z_EXTRA_LBITS : Z := 0x122a8.
Definition Z_EXTRA_DBITS : Z := 0x1231c.
Definition Z_BL_ORDER : Z := 0x123e0.
Definition Z_BASE_LENGTH : Z := 0x123f4.
Definition Z_BASE_DIST : Z := 0x12468.

Lemma u16ro_read : forall m A ws (i : Z) w a,
  bytes_at psegs m A (u16s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 2 * i) ->
  ov_read_bytes psegs m a 2 = Some (le2 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i) with (Z.of_nat (2 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read psegs m A (u16s ws) (2 * Z.to_nat i) 2 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le2; lia).
  rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u32ro_read : forall m A ws (i : Z) w a,
  bytes_at psegs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 4 * i) ->
  ov_read_bytes psegs m a 4 = Some (le4 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * i) with (Z.of_nat (4 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read psegs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Ltac rod_tac := intros m MI; apply ro_bytes_at; [exact MI| unfold Z_DIST_CODE, Z_LENGTH_CODE, Z_STATIC_LTREE, Z_STATIC_DTREE, Z_EXTRA_LBITS, Z_EXTRA_DBITS, Z_BL_ORDER, Z_BASE_LENGTH, Z_BASE_DIST; lia
  | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].

Lemma rod_dist_code : forall m, mem_inv psegs m -> bytes_at psegs m Z_DIST_CODE (av8 dist_code_a 512).
Proof. rod_tac. Qed.
Lemma rod_length_code : forall m, mem_inv psegs m -> bytes_at psegs m Z_LENGTH_CODE (av8 length_code_a 256).
Proof. rod_tac. Qed.
Lemma rod_bl_order : forall m, mem_inv psegs m -> bytes_at psegs m Z_BL_ORDER (av8 bl_order_a 19).
Proof. rod_tac. Qed.
Lemma rod_static_ltree : forall m, mem_inv psegs m -> bytes_at psegs m Z_STATIC_LTREE (u16s (avct static_ltree_fc static_ltree_dl 288)).
Proof. rod_tac. Qed.
Lemma rod_static_dtree : forall m, mem_inv psegs m -> bytes_at psegs m Z_STATIC_DTREE (u16s (avct static_dtree_fc static_dtree_dl 30)).
Proof. rod_tac. Qed.
Lemma rod_extra_lbits : forall m, mem_inv psegs m -> bytes_at psegs m Z_EXTRA_LBITS (u32s (av32 extra_lbits_a 29)).
Proof. rod_tac. Qed.
Lemma rod_extra_dbits : forall m, mem_inv psegs m -> bytes_at psegs m Z_EXTRA_DBITS (u32s (av32 extra_dbits_a 30)).
Proof. rod_tac. Qed.
Lemma rod_base_length : forall m, mem_inv psegs m -> bytes_at psegs m Z_BASE_LENGTH (u32s (av32 base_length_a 29)).
Proof. rod_tac. Qed.
Lemma rod_base_dist : forall m, mem_inv psegs m -> bytes_at psegs m Z_BASE_DIST (u32s (av32 base_dist_a 30)).
Proof. rod_tac. Qed.


Lemma zforall_lt : forall (P : Z -> bool) n, forallb P (zseq n) = true -> forall i, 0 <= i < n -> P i = true.
Proof.
  intros P n H i Hi. rewrite forallb_forall in H. apply H. eapply nth_error_In. apply (zseq_nth n i Hi).
Qed.

Ltac ztab_tac n P H :=
  let X := fresh "X" in
  pose proof (zforall_lt P n ltac:(vm_compute; reflexivity) _ H) as X; cbv beta in X;
  repeat (apply andb_true_iff in X; let Y := fresh "Y" in destruct X as [X Y]);
  repeat match goal with
  | Y : (_ <=? _) = true |- _ => apply Z.leb_le in Y
  | Y : (_ <? _) = true |- _ => apply Z.ltb_lt in Y
  | Y : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in Y
  end.

Lemma length_code_range : forall lc, 0 <= lc < 256 -> 0 <= arr_get length_code_a lc < 29.
Proof. intros lc H. ztab_tac 256 (fun i => (0 <=? arr_get length_code_a i) && (arr_get length_code_a i <? 29)) H. lia. Qed.

Lemma dist_code_range : forall i, 0 <= i < 512 -> 0 <= arr_get dist_code_a i < 30.
Proof. intros i H. ztab_tac 512 (fun i => (0 <=? arr_get dist_code_a i) && (arr_get dist_code_a i <? 30)) H. lia. Qed.

Lemma extra_lbits_facts : forall c, 0 <= c < 29 ->
  0 <= arr_get extra_lbits_a c <= 5 /\ 0 <= arr_get base_length_a c <= 255
  /\ (negb (arr_get extra_lbits_a c =? 0) = ((8 <=? c) && (c <=? 27))).
Proof.
  intros c H.
  ztab_tac 29 (fun c => (0 <=? arr_get extra_lbits_a c) && (arr_get extra_lbits_a c <=? 5) && (0 <=? arr_get base_length_a c) && (arr_get base_length_a c <=? 255)
                        && Bool.eqb (negb (arr_get extra_lbits_a c =? 0)) ((8 <=? c) && (c <=? 27))) H.
  split; [lia|]. split; [lia|]. assumption.
Qed.

Lemma extra_dbits_facts : forall c, 0 <= c < 30 ->
  0 <= arr_get extra_dbits_a c <= 13 /\ 0 <= arr_get base_dist_a c <= 24576
  /\ (negb (arr_get extra_dbits_a c =? 0) = (4 <=? c)).
Proof.
  intros c H.
  ztab_tac 30 (fun c => (0 <=? arr_get extra_dbits_a c) && (arr_get extra_dbits_a c <=? 13) && (0 <=? arr_get base_dist_a c) && (arr_get base_dist_a c <=? 24576)
                        && Bool.eqb (negb (arr_get extra_dbits_a c =? 0)) (4 <=? c)) H.
  split; [lia|]. split; [lia|]. assumption.
Qed.

Lemma length_base_le : forall lc, 0 <= lc < 256 -> arr_get base_length_a (arr_get length_code_a lc) <= lc.
Proof. intros lc H. ztab_tac 256 (fun i => arr_get base_length_a (arr_get length_code_a i) <=? i) H. lia. Qed.

Lemma dist_base_le : forall d, 0 <= d < 32768 -> 0 <= d_code d < 30 /\ arr_get base_dist_a (d_code d) <= d.
Proof.
  intros d H. unfold d_code. destruct (Z.ltb_spec d 256) as [C|C].
  - assert (H1 : 0 <= d < 256) by lia.
    ztab_tac 256 (fun i => (0 <=? arr_get dist_code_a i) && (arr_get dist_code_a i <? 30) && (arr_get base_dist_a (arr_get dist_code_a i) <=? i)) H1. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128.
    assert (H1 : 0 <= d / 128 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof (Z.mul_div_le d 128 ltac:(lia)) as LE.
    ztab_tac 256 (fun i => (0 <=? arr_get dist_code_a (256 + i)) && (arr_get dist_code_a (256 + i) <? 30) && (arr_get base_dist_a (arr_get dist_code_a (256 + i)) <=? 128 * i)) H1. lia.
Qed.
End Z_tr_rod.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).


Definition Z_ZCALLOC : Z := 0x19f7c.
Definition Z_ZCFREE : Z := 0x19f8c.
Definition Z_SL_DESC : Z := 0x29008.
Definition Z_SD_DESC : Z := 0x29028.
Definition Z_SBL_DESC : Z := 0x29048.
Notation DS_SIZE := 5968 (only parsing).
Notation DS_WIN := 65536 (only parsing).
Notation DS_NPREV := 32768 (only parsing).
Notation DS_NHEAD := 32768 (only parsing).
Notation DS_PEND := 65536 (only parsing).

Definition Z_ERRMSG_PTRS : list Z := [0x1040a; 0x105fc; 0x1038c; 0x10486; 0x103f5; 0x1030d; 0x104c9; 0x104bc; 0x10583; 0x1038c].
Definition msg_ptr (k : Z) : Z := if k <? 0 then 0 else nth (Z.to_nat k) Z_ERRMSG_PTRS 0.


Definition cell_sim (c c' : cell) : Prop :=
  match c, c' with
  | C8 v, C8 v' => v = v'
  | C4 v, C4 v' => le4 v = le4 v'
  (* a word stored into a junk cell (bi_used, slid) closes it again *)
  | C4 v, CB n' bs' => n' = 4%nat /\ bs' = le4 v
  | C2 v, C2 v' => le2 v = le2 v'
  | C1 b, C1 b' => b = b'
  | CB n bs, CB n' bs' => n = n' /\ bs = bs'
  | _, _ => False
  end.
Fixpoint cells_sim (cs cs' : list cell) : Prop :=
  match cs, cs' with
  | [], [] => True
  | c :: r, c' :: r' => cell_sim c c' /\ cells_sim r r'
  | _, _ => False
  end.

Lemma cell_sim_props : forall c c', cell_sim c c' -> cbytes c' = cbytes c /\ csize c' = csize c /\ (cell_wf c -> cell_wf c').
Proof.
  intros [v|v|v|b|n bs] [v'|v'|v'|b'|n' bs'] H; unfold cell_sim in H; try (exfalso; exact H); cbn [cbytes csize cell_wf].
  - subst. auto.
  - rewrite H. auto.
  - destruct H as [-> ->]. split; [reflexivity|]. split; [reflexivity|]. intros _. apply length_le4.
  - rewrite H. auto.
  - subst. auto.
  - destruct H as [-> ->]. auto.
Qed.

Lemma cells_sim_props : forall cs cs', cells_sim cs cs' ->
  cells_bytes cs' = cells_bytes cs /\ cells_size cs' = cells_size cs /\ (cells_wf cs -> cells_wf cs').
Proof.
  induction cs as [|c cs IH]; intros [|c' cs'] H; cbn [cells_sim] in H; try (exfalso; exact H); [auto|].
  destruct H as [H1 H2]. destruct (cell_sim_props _ _ H1) as (A1 & A2 & A3). destruct (IH _ H2) as (B1 & B2 & B3).
  cbn [cells_bytes cells_size cells_wf]. rewrite A1, A2, B1, B2.
  split; [reflexivity|]. split; [reflexivity|]. intros [W1 W2]. split; [apply A3; exact W1| apply B3; exact W2].
Qed.

Lemma rw_cells_sim : forall m A cs cs', rw_cells psegs m A cs -> cells_sim cs cs' -> rw_cells psegs m A cs'.
Proof.
  intros m A cs cs' H S. destruct (cells_sim_props _ _ S) as (B & Z & W).
  destruct H as [[Hwf Hb] Hw]. split; [split; [apply W; exact Hwf| rewrite B; exact Hb]| rewrite Z; exact Hw].
Qed.


Record dlay : Type := mkDL {
  dl_S : Z;
  dl_As : Z;
  dl_Aw : Z;
  dl_Ap : Z;
  dl_Ah : Z;
  dl_Ab : Z;
  dl_NI : Z;
  dl_NO : Z
}.

Definition dfoot (L : dlay) : list ivl :=
  [(dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN); (dl_Ap L, dl_Ap L + 2 * DS_NPREV);
   (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_Ab L, dl_Ab L + DS_PEND)].

Definition blk_ok (A n : Z) : Prop := 0 < A /\ A mod 16 = 0 /\ A + n < 2^62 /\ (A + n <= 0x10000 \/ 0x5b000 <= A).
Definition apart (A n B k : Z) : Prop := A + n <= B \/ B + k <= A.

Record dlay_ok (L : dlay) : Prop := mkDLok {
  lo_s : blk_ok (dl_As L) DS_SIZE;
  lo_w : blk_ok (dl_Aw L) DS_WIN;
  lo_p : blk_ok (dl_Ap L) (2 * DS_NPREV);
  lo_h : blk_ok (dl_Ah L) (2 * DS_NHEAD);
  lo_b : blk_ok (dl_Ab L) DS_PEND;
  lo_S : 0 < dl_S L /\ dl_S L mod 8 = 0 /\ dl_S L + 112 < 2^63;
  lo_sw : apart (dl_As L) DS_SIZE (dl_Aw L) DS_WIN;
  lo_sp : apart (dl_As L) DS_SIZE (dl_Ap L) (2 * DS_NPREV);
  lo_sh : apart (dl_As L) DS_SIZE (dl_Ah L) (2 * DS_NHEAD);
  lo_sb : apart (dl_As L) DS_SIZE (dl_Ab L) DS_PEND;
  lo_wp : apart (dl_Aw L) DS_WIN (dl_Ap L) (2 * DS_NPREV);
  lo_wh : apart (dl_Aw L) DS_WIN (dl_Ah L) (2 * DS_NHEAD);
  lo_wb : apart (dl_Aw L) DS_WIN (dl_Ab L) DS_PEND;
  lo_ph : apart (dl_Ap L) (2 * DS_NPREV) (dl_Ah L) (2 * DS_NHEAD);
  lo_pb : apart (dl_Ap L) (2 * DS_NPREV) (dl_Ab L) DS_PEND;
  lo_hb : apart (dl_Ah L) (2 * DS_NHEAD) (dl_Ab L) DS_PEND;
  lo_Ss : apart (dl_S L) 112 (dl_As L) DS_SIZE;
  lo_Sw : apart (dl_S L) 112 (dl_Aw L) DS_WIN;
  lo_Sp : apart (dl_S L) 112 (dl_Ap L) (2 * DS_NPREV);
  lo_Sh : apart (dl_S L) 112 (dl_Ah L) (2 * DS_NHEAD);
  lo_Sb : apart (dl_S L) 112 (dl_Ab L) DS_PEND
}.

Definition dlay_below (L : dlay) (lo hi : Z) : Prop :=
  0x5b000 <= lo /\ dl_As L + DS_SIZE <= lo /\ dl_Aw L + DS_WIN <= lo /\ dl_Ap L + 2 * DS_NPREV <= lo /\ dl_Ah L + 2 * DS_NHEAD <= lo
  /\ dl_Ab L + DS_PEND <= lo /\ hi <= dl_S L.

Definition RELRO_LO : Z := 0x28f18.
Definition RELRO_HI : Z := 0x29100.
Definition relro_clean (m : mem) : Prop := forall a : word, RELRO_LO <= bv_unsigned a < RELRO_HI -> m a = None.

Lemma relro_clean_munch : forall W m m', relro_clean m -> munch W m m' -> disjoint_from W RELRO_LO (RELRO_HI - RELRO_LO) -> relro_clean m'.
Proof.
  intros W m m' H MU D a Ha. rewrite (MU a); [apply H; exact Ha|].
  eapply disjoint_outside; [exact D| lia].
Qed.


Section Groups.
Variable m : mem.
Variable L : dlay.
Variable s : deflate_state.

Definition dsA_cells (h1 h2 h3 h4 h5 : list byte) : list cell :=
  [C8 (wz (dl_S L));
   C4 (wz (ds_status s)); CB 4 h1;
   C8 (wz (dl_Ab L));
   C8 (wz (ds_pending_buf_size s));
   C8 (wz (dl_Ab L + ds_pending_out s));
   C8 (wz (ds_pending s));
   C4 (wz (ds_wrap s)); CB 4 h2;
   C8 (wz (ds_gzhead s));
   C8 (wz (ds_gzindex s));
   C1 (Z_to_bv 8 (ds_method s)); CB 3 h3;
   C4 (wz (ds_last_flush s));
   C4 (wz (ds_w_size s));
   C4 (wz (ds_w_bits s));
   C4 (wz (ds_w_mask s)); CB 4 h4;
   C8 (wz (dl_Aw L));
   C8 (wz (ds_window_size s));
   C8 (wz (dl_Ap L));
   C8 (wz (dl_Ah L));
   C4 (wz (ds_ins_h s));
   C4 (wz (ds_hash_size s));
   C4 (wz (ds_hash_bits s));
   C4 (wz (ds_hash_mask s));
   C4 (wz (ds_hash_shift s)); CB 4 h5;
   C8 (wz (ds_block_start s));
   C4 (wz (ds_match_length s));
   C4 (wz (ds_prev_match s));
   C4 (wz (ds_match_available s));
   C4 (wz (ds_strstart s));
   C4 (wz (ds_match_start s));
   C4 (wz (ds_lookahead s));
   C4 (wz (ds_prev_length s));
   C4 (wz (ds_max_chain_length s));
   C4 (wz (ds_max_lazy_match s));
   C4 (wz (ds_level s));
   C4 (wz (ds_strategy s));
   C4 (wz (ds_good_match s));
   C4 (wz (ds_nice_match s))].
Definition dsA : Prop := exists h1 h2 h3 h4 h5, rw_cells psegs m (dl_As L) (dsA_cells h1 h2 h3 h4 h5).

Definition dsB_cells (h1 h2 h3 : list byte) : list cell :=
  [C8 (wz (dl_As L + 212));  C4 (wz (ds_l_max_code s));  CB 4 h1; C8 (wz Z_SL_DESC);
   C8 (wz (dl_As L + 2504)); C4 (wz (ds_d_max_code s));  CB 4 h2; C8 (wz Z_SD_DESC);
   C8 (wz (dl_As L + 2748)); C4 (wz (ds_bl_max_code s)); CB 4 h3; C8 (wz Z_SBL_DESC)].
Definition dsB : Prop := exists h1 h2 h3, rw_cells psegs m (dl_As L + 2904) (dsB_cells h1 h2 h3).
Definition dsBi_cells (d1 d2 d3 d4 d5 d6 : word) (h1 h2 h3 : list byte) : list cell :=
  [C8 d1; C4 (wz (ds_l_max_code s));  CB 4 h1; C8 d2;
   C8 d3; C4 (wz (ds_d_max_code s));  CB 4 h2; C8 d4;
   C8 d5; C4 (wz (ds_bl_max_code s)); CB 4 h3; C8 d6].
Definition dsBi : Prop := exists d1 d2 d3 d4 d5 d6 h1 h2 h3, rw_cells psegs m (dl_As L + 2904) (dsBi_cells d1 d2 d3 d4 d5 d6 h1 h2 h3).

Definition dsC_cells : list cell := [C4 (wz (ds_heap_len s)); C4 (wz (ds_heap_max s))].
Definition dsC : Prop := rw_cells psegs m (dl_As L + 5300) dsC_cells.

(* bi_used (int, 5944) and slid (int, 5960) are new; high_water moves
   5944 -> 5952 and the struct grows 5952 -> 5968. bi_used and slid are junk here (h3, h4): no harness call reads
   them (deflateUsed, deflateCopy). The two 4-byte pads after them are zero: 1.4's deflateInit2_ zeroes the state. *)
Definition dsD_cells (h0 h1 h2 h3 h4 : list byte) : list cell :=
  [CB 7 h0;
   C8 (wz (dl_Ab L + ds_lit_bufsize s));
   C4 (wz (ds_lit_bufsize s));
   C4 (wz (ds_sym_next s));
   C4 (wz (ds_sym_end s)); CB 4 h1;
   C8 (wz (ds_opt_len s));
   C8 (wz (ds_static_len s));
   C4 (wz (ds_matches s));
   C4 (wz (ds_insert s));
   C2 (wz (ds_bi_buf s)); CB 2 h2;
   C4 (wz (ds_bi_valid s));
   CB 4 h3; C4 (wz 0);
   C8 (wz (ds_high_water s));
   CB 4 h4; C4 (wz 0)].
Definition dsD : Prop := exists h0 h1 h2 h3 h4, rw_cells psegs m (dl_As L + 5881) (dsD_cells h0 h1 h2 h3 h4).

Definition dlt : Prop := u16arr psegs m (dl_As L + 212) (avct (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573).
Definition ddt : Prop := u16arr psegs m (dl_As L + 2504) (avct (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) 61).
Definition dbt : Prop := u16arr psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc s) (ds_bl_tree_dl s) 39).
Definition dblc : Prop := u16arr psegs m (dl_As L + 2976) (av16 (ds_bl_count s) 16).
Definition dheap : Prop := u32arr psegs m (dl_As L + 3008) (av32 (ds_heap s) 573).
Definition ddep : Prop := u8arr psegs m (dl_As L + 5308) (av8 (ds_depth s) 573).

Definition dwin : Prop := u8arr psegs m (dl_Aw L) (av8 (ds_window s) DS_WIN).
Definition dprev : Prop := u16arr psegs m (dl_Ap L) (av16 (ds_prev s) DS_NPREV).
Definition dhead : Prop := u16arr psegs m (dl_Ah L) (av16 (ds_head s) DS_NHEAD).
Definition dpend : Prop := u8arr psegs m (dl_Ab L) (av8 (ds_pending_buf s) DS_PEND).
End Groups.

Record dlens (s : deflate_state) : Prop := mkDLens {
  ln_ltf : arr_len (ds_dyn_ltree_fc s) = 573; ln_ltd : arr_len (ds_dyn_ltree_dl s) = 573;
  ln_dtf : arr_len (ds_dyn_dtree_fc s) = 61;  ln_dtd : arr_len (ds_dyn_dtree_dl s) = 61;
  ln_btf : arr_len (ds_bl_tree_fc s) = 39;    ln_btd : arr_len (ds_bl_tree_dl s) = 39;
  ln_blc : arr_len (ds_bl_count s) = 16;      ln_heap : arr_len (ds_heap s) = 573;
  ln_dep : arr_len (ds_depth s) = 573;
  ln_win : arr_len (ds_window s) = DS_WIN;    ln_prev : arr_len (ds_prev s) = DS_NPREV;
  ln_head : arr_len (ds_head s) = DS_NHEAD;   ln_pend : arr_len (ds_pending_buf s) = DS_PEND
}.

Record DSTx (B : mem -> dlay -> deflate_state -> Prop) (m : mem) (L : dlay) (s : deflate_state) : Prop := mkDST {
  st_A : dsA m L s; st_B : B m L s; st_C : dsC m L s; st_D : dsD m L s;
  st_lt : dlt m L s; st_dt : ddt m L s; st_bt : dbt m L s; st_blc : dblc m L s; st_heap : dheap m L s; st_dep : ddep m L s;
  st_win : dwin m L s; st_prev : dprev m L s; st_head : dhead m L s; st_pend : dpend m L s;
  st_lens : dlens s;
  st_lay : dlay_ok L
}.
Definition DST := DSTx dsB.
Definition DSTi := DSTx dsBi.


Definition zs_priv_cells (L : dlay) (msg dt adler : Z) (p3 : list byte) (resv : word) : list cell :=
  [C8 (wz (msg_ptr msg)); C8 (wz (dl_As L)); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0);
   C4 (wz dt); CB 4 p3; C8 (wz adler); C8 resv].

Definition zs_call_cells (L : dlay) (c : cstrm) (p1 p2 p3 : list byte) (resv : word) : list cell :=
  [C8 (wz (dl_NI L + cs_next_in c)); C4 (wz (cs_avail_in c)); CB 4 p1; C8 (wz (cs_total_in c));
   C8 (wz (dl_NO L + Z.of_nat (length (cs_out_rev c)))); C4 (wz (cs_avail_out c)); CB 4 p2; C8 (wz (cs_total_out c))]
  ++ zs_priv_cells L (cs_msg c) (cs_data_type c) (cs_adler c) p3 resv.
Definition dzs (m : mem) (L : dlay) (c : cstrm) : Prop :=
  exists p1 p2 p3 resv, rw_cells psegs m (dl_S L) (zs_call_cells L c p1 p2 p3 resv).

Definition dzq (m : mem) (L : dlay) (z : zstrm) : Prop :=
  exists p3 resv, rw_cells psegs m (dl_S L + 48) (zs_priv_cells L (zs_msg z) (zs_data_type z) (zs_adler z) p3 resv).

Definition zb8 (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition din (m : mem) (L : dlay) (inp : list Z) : Prop := bytes_at psegs m (dl_NI L) (zb8 inp).
Definition outv (rest0 : list byte) (c : cstrm) : list byte := zb8 (rev (cs_out_rev c)) ++ skipn (length (cs_out_rev c)) rest0.
Definition dout (m : mem) (L : dlay) (rest0 : list byte) (c : cstrm) : Prop := u8arr psegs m (dl_NO L) (outv rest0 c).

Lemma outv_emit : forall rest0 c l, (length (cs_out_rev c) + length l <= length rest0)%nat ->
  outv rest0 (cs_emit c l)
  = firstn (length (cs_out_rev c)) (outv rest0 c) ++ zb8 l ++ skipn (length (cs_out_rev c) + length l) (outv rest0 c).
Proof.
  intros rest0 c l H. unfold outv, cs_emit. destruct c as [ci cn ca o cao cti cto cm cd cad]; cbn [cs_out_rev cset_out_rev] in *.
  set (k := length o) in *.
  assert (Lk : length (zb8 (rev o)) = k) by (unfold zb8; rewrite length_map, length_rev; reflexivity).
  rewrite rev_append_rev, rev_app_distr, rev_involutive, length_app, length_rev.
  unfold zb8 at 1. rewrite map_app. fold (zb8 (rev o)). fold (zb8 l).
  rewrite ?firstn_app, ?Lk, ?Nat.sub_diag, ?firstn_O, ?app_nil_r, ?firstn_all2 by lia.
  rewrite skipn_app, Lk, (skipn_all2 (zb8 (rev o))) by lia. cbn [app].
  replace (k + length l - k)%nat with (length l) by lia. rewrite skipn_skipn.
  subst k. rewrite <- app_assoc. reflexivity.
Qed.

Lemma zb8_length : forall l, length (zb8 l) = length l.
Proof. intros. unfold zb8. apply length_map. Qed.
Lemma outv_length : forall rest0 c, (length (cs_out_rev c) <= length rest0)%nat -> length (outv rest0 c) = length rest0.
Proof. intros rest0 c H. unfold outv. rewrite length_app, zb8_length, length_rev, length_skipn. lia. Qed.

Record dio_sep (L : dlay) (nin nout lo : Z) : Prop := mkDio {
  io_ni : 0 < dl_NI L /\ 0 <= nin /\ dl_NI L + nin <= lo;
  io_no : 0 < dl_NO L /\ 0 <= nout /\ dl_NO L + nout <= lo;
  io_img : dl_NO L + nout <= 0x10000 \/ 0x5b000 <= dl_NO L;
  io_io : apart (dl_NI L) nin (dl_NO L) nout;
  io_is : apart (dl_NI L) nin (dl_As L) DS_SIZE;  io_iw : apart (dl_NI L) nin (dl_Aw L) DS_WIN;
  io_ip : apart (dl_NI L) nin (dl_Ap L) (2 * DS_NPREV);  io_ih : apart (dl_NI L) nin (dl_Ah L) (2 * DS_NHEAD);
  io_ib : apart (dl_NI L) nin (dl_Ab L) DS_PEND;
  io_os : apart (dl_NO L) nout (dl_As L) DS_SIZE;  io_ow : apart (dl_NO L) nout (dl_Aw L) DS_WIN;
  io_op : apart (dl_NO L) nout (dl_Ap L) (2 * DS_NPREV);  io_oh : apart (dl_NO L) nout (dl_Ah L) (2 * DS_NHEAD);
  io_ob : apart (dl_NO L) nout (dl_Ab L) DS_PEND
}.

Definition DREP (m : mem) (L : dlay) (s : deflate_state) : Prop := dzs m L (ds_strm s) /\ DST m L s.
Definition DREPq (m : mem) (L : dlay) (s : deflate_state) (z : zstrm) : Prop := dzq m L z /\ DST m L s.


Lemma agree_on_of_munch : forall W m m' A n, munch W m m' -> wmono psegs m m' -> 0 <= A -> A + n <= 2^64 ->
  disjoint_from W A n -> agree_on A (A + n) m m'.
Proof.
  intros W m m' A n MU WM HA Hn D. eapply agree_on_munch; [exact MU| exact WM| exact HA| exact Hn|].
  replace (A + n - A) with n by lia. exact D.
Qed.

Lemma u16arr_bound : forall m A ws, u16arr psegs m A ws -> 0 <= A /\ A + 2 * Z.of_nat (length ws) <= 2^64.
Proof. intros m A ws H. pose proof (u8arr_bound psegs m A _ H) as B. rewrite u16s_length in B. lia. Qed.

Section Frame.
Variables (m m' : mem) (L : dlay) (s : deflate_state).

Lemma dsA_agree : dsA m L s -> agree_on (dl_As L) (dl_As L + 212) m m' -> dsA m' L s.
Proof. intros (h1 & h2 & h3 & h4 & h5 & H) AG. exists h1, h2, h3, h4, h5. apply (rw_cells_agree m); [exact H| exact AG]. Qed.
Lemma dsA_munch : forall W, dsA m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_As L) 212 -> dsA m' L s.
Proof.
  intros W H MU WM D. apply dsA_agree; [exact H|]. destruct H as (h1 & h2 & h3 & h4 & h5 & H). pose proof (rw_cells_bound psegs m _ _ H) as B.
  match type of B with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in B end.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dsB_agree : dsB m L s -> agree_on (dl_As L + 2904) (dl_As L + 2904 + 72) m m' -> dsB m' L s.
Proof. intros (h1 & h2 & h3 & H) AG. exists h1, h2, h3. apply (rw_cells_agree m); [exact H| exact AG]. Qed.
Lemma dsB_munch : forall W, dsB m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_As L + 2904) 72 -> dsB m' L s.
Proof.
  intros W H MU WM D. apply dsB_agree; [exact H|]. destruct H as (h1 & h2 & h3 & H). pose proof (rw_cells_bound psegs m _ _ H) as B.
  match type of B with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in B end.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dsBi_agree : dsBi m L s -> agree_on (dl_As L + 2904) (dl_As L + 2904 + 72) m m' -> dsBi m' L s.
Proof. intros (d1 & d2 & d3 & d4 & d5 & d6 & h1 & h2 & h3 & H) AG. exists d1, d2, d3, d4, d5, d6, h1, h2, h3. apply (rw_cells_agree m); [exact H| exact AG]. Qed.
Lemma dsBi_munch : forall W, dsBi m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_As L + 2904) 72 -> dsBi m' L s.
Proof.
  intros W H MU WM D. apply dsBi_agree; [exact H|]. destruct H as (d1 & d2 & d3 & d4 & d5 & d6 & h1 & h2 & h3 & H). pose proof (rw_cells_bound psegs m _ _ H) as B.
  match type of B with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in B end.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dsC_agree : dsC m L s -> agree_on (dl_As L + 5300) (dl_As L + 5300 + 8) m m' -> dsC m' L s.
Proof. intros H AG. apply (rw_cells_agree m); [exact H| exact AG]. Qed.
Lemma dsC_munch : forall W, dsC m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_As L + 5300) 8 -> dsC m' L s.
Proof.
  intros W H MU WM D. apply dsC_agree; [exact H|]. pose proof (rw_cells_bound psegs m _ _ H) as B.
  match type of B with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in B end.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dsD_agree : dsD m L s -> agree_on (dl_As L + 5881) (dl_As L + 5881 + 87) m m' -> dsD m' L s.
Proof. intros (h0 & h1 & h2 & h3 & h4 & H) AG. exists h0, h1, h2, h3, h4. apply (rw_cells_agree m); [exact H| exact AG]. Qed.
Lemma dsD_munch : forall W, dsD m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_As L + 5881) 87 -> dsD m' L s.
Proof.
  intros W H MU WM D. apply dsD_agree; [exact H|]. destruct H as (h0 & h1 & h2 & h3 & h4 & H). pose proof (rw_cells_bound psegs m _ _ H) as B.
  match type of B with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in B end.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dlt_agree : dlt m L s -> agree_on (dl_As L + 212) (dl_As L + 212 + 2292) m m' -> dlt m' L s.
Proof. intros H AG. apply (u16arr_agree m); [exact H|]. rewrite avct_length, Z2Nat.id by lia. exact AG. Qed.
Lemma dlt_munch : forall W, dlt m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_As L + 212) 2292 -> dlt m' L s.
Proof.
  intros W H MU WM D. apply dlt_agree; [exact H|]. pose proof (u16arr_bound m _ _ H) as B. rewrite avct_length, Z2Nat.id in B by lia.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma ddt_agree : ddt m L s -> agree_on (dl_As L + 2504) (dl_As L + 2504 + 244) m m' -> ddt m' L s.
Proof. intros H AG. apply (u16arr_agree m); [exact H|]. rewrite avct_length, Z2Nat.id by lia. exact AG. Qed.
Lemma ddt_munch : forall W, ddt m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_As L + 2504) 244 -> ddt m' L s.
Proof.
  intros W H MU WM D. apply ddt_agree; [exact H|]. pose proof (u16arr_bound m _ _ H) as B. rewrite avct_length, Z2Nat.id in B by lia.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dbt_agree : dbt m L s -> agree_on (dl_As L + 2748) (dl_As L + 2748 + 156) m m' -> dbt m' L s.
Proof. intros H AG. apply (u16arr_agree m); [exact H|]. rewrite avct_length, Z2Nat.id by lia. exact AG. Qed.
Lemma dbt_munch : forall W, dbt m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_As L + 2748) 156 -> dbt m' L s.
Proof.
  intros W H MU WM D. apply dbt_agree; [exact H|]. pose proof (u16arr_bound m _ _ H) as B. rewrite avct_length, Z2Nat.id in B by lia.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dblc_agree : dblc m L s -> agree_on (dl_As L + 2976) (dl_As L + 2976 + 32) m m' -> dblc m' L s.
Proof. intros H AG. apply (u16arr_agree m); [exact H|]. rewrite av16_length, Z2Nat.id by lia. exact AG. Qed.
Lemma dblc_munch : forall W, dblc m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_As L + 2976) 32 -> dblc m' L s.
Proof.
  intros W H MU WM D. apply dblc_agree; [exact H|]. pose proof (u16arr_bound m _ _ H) as B. rewrite av16_length, Z2Nat.id in B by lia.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dheap_agree : dheap m L s -> agree_on (dl_As L + 3008) (dl_As L + 3008 + 2292) m m' -> dheap m' L s.
Proof. intros H AG. apply (u32arr_agree m); [exact H|]. rewrite av32_length, Z2Nat.id by lia. exact AG. Qed.
Lemma dheap_munch : forall W, dheap m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_As L + 3008) 2292 -> dheap m' L s.
Proof.
  intros W H MU WM D. apply dheap_agree; [exact H|]. pose proof (u32arr_bound psegs m _ _ H) as B. rewrite av32_length, Z2Nat.id in B by lia.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma ddep_agree : ddep m L s -> agree_on (dl_As L + 5308) (dl_As L + 5308 + 573) m m' -> ddep m' L s.
Proof. intros H AG. apply (u8arr_agree m); [exact H|]. rewrite av8_length, Z2Nat.id by lia. exact AG. Qed.
Lemma ddep_munch : forall W, ddep m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_As L + 5308) 573 -> ddep m' L s.
Proof.
  intros W H MU WM D. apply ddep_agree; [exact H|]. pose proof (u8arr_bound psegs m _ _ H) as B. rewrite av8_length, Z2Nat.id in B by lia.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dwin_agree : dwin m L s -> agree_on (dl_Aw L) (dl_Aw L + 65536) m m' -> dwin m' L s.
Proof. intros H AG. apply (u8arr_agree m); [exact H|]. rewrite av8_length, Z2Nat.id by lia. exact AG. Qed.
Lemma dwin_munch : forall W, dwin m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_Aw L) 65536 -> dwin m' L s.
Proof.
  intros W H MU WM D. apply dwin_agree; [exact H|]. pose proof (u8arr_bound psegs m _ _ H) as B. rewrite av8_length, Z2Nat.id in B by lia.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dprev_agree : dprev m L s -> agree_on (dl_Ap L) (dl_Ap L + 65536) m m' -> dprev m' L s.
Proof. intros H AG. apply (u16arr_agree m); [exact H|]. rewrite av16_length, Z2Nat.id by lia. exact AG. Qed.
Lemma dprev_munch : forall W, dprev m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_Ap L) 65536 -> dprev m' L s.
Proof.
  intros W H MU WM D. apply dprev_agree; [exact H|]. pose proof (u16arr_bound m _ _ H) as B. rewrite av16_length, Z2Nat.id in B by lia.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dhead_agree : dhead m L s -> agree_on (dl_Ah L) (dl_Ah L + 65536) m m' -> dhead m' L s.
Proof. intros H AG. apply (u16arr_agree m); [exact H|]. rewrite av16_length, Z2Nat.id by lia. exact AG. Qed.
Lemma dhead_munch : forall W, dhead m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_Ah L) 65536 -> dhead m' L s.
Proof.
  intros W H MU WM D. apply dhead_agree; [exact H|]. pose proof (u16arr_bound m _ _ H) as B. rewrite av16_length, Z2Nat.id in B by lia.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dpend_agree : dpend m L s -> agree_on (dl_Ab L) (dl_Ab L + 65536) m m' -> dpend m' L s.
Proof. intros H AG. apply (u8arr_agree m); [exact H|]. rewrite av8_length, Z2Nat.id by lia. exact AG. Qed.
Lemma dpend_munch : forall W, dpend m L s -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_Ab L) 65536 -> dpend m' L s.
Proof.
  intros W H MU WM D. apply dpend_agree; [exact H|]. pose proof (u8arr_bound psegs m _ _ H) as B. rewrite av8_length, Z2Nat.id in B by lia.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.

Lemma dzs_agree : forall c, dzs m L c -> agree_on (dl_S L) (dl_S L + 112) m m' -> dzs m' L c.
Proof. intros c (p1 & p2 & p3 & resv & H) AG. exists p1, p2, p3, resv. apply (rw_cells_agree m); [exact H| exact AG]. Qed.
Lemma dzs_munch : forall W c, dzs m L c -> munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_S L) 112 -> dzs m' L c.
Proof.
  intros W c H MU WM D. apply dzs_agree; [exact H|]. destruct H as (p1 & p2 & p3 & resv & H). pose proof (rw_cells_bound psegs m _ _ H) as B.
  match type of B with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in B end.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.
Lemma dzq_agree : forall z, dzq m L z -> agree_on (dl_S L + 48) (dl_S L + 48 + 64) m m' -> dzq m' L z.
Proof. intros z (p3 & resv & H) AG. exists p3, resv. apply (rw_cells_agree m); [exact H| exact AG]. Qed.

Definition ag_blocks : Prop :=
  agree_on (dl_As L) (dl_As L + DS_SIZE) m m' /\ agree_on (dl_Aw L) (dl_Aw L + DS_WIN) m m' /\ agree_on (dl_Ap L) (dl_Ap L + 2 * DS_NPREV) m m'
  /\ agree_on (dl_Ah L) (dl_Ah L + 2 * DS_NHEAD) m m' /\ agree_on (dl_Ab L) (dl_Ab L + DS_PEND) m m'.

Lemma DSTx_agree : forall B, (forall lo hi, B m L s -> dl_As L <= lo -> hi <= dl_As L + DS_SIZE -> (agree_on (dl_As L) (dl_As L + DS_SIZE) m m' -> B m' L s)) ->
  DSTx B m L s -> ag_blocks -> DSTx B m' L s.
Proof.
  intros B HB [] (A0 & A1 & A2 & A3 & A4).   assert (G : forall lo hi, dl_As L <= lo -> hi <= dl_As L + 5968 -> agree_on lo hi m m') by (intros lo hi H1 H2; eapply agree_on_sub; [exact A0| lia| lia]).
  constructor.
  - apply dsA_agree; [assumption| apply G; lia].
  - apply (HB (dl_As L) (dl_As L + 5968)); [assumption| lia| lia| exact A0].
  - apply dsC_agree; [assumption| apply G; lia].
  - apply dsD_agree; [assumption| apply G; lia].
  - apply dlt_agree; [assumption| apply G; lia].
  - apply ddt_agree; [assumption| apply G; lia].
  - apply dbt_agree; [assumption| apply G; lia].
  - apply dblc_agree; [assumption| apply G; lia].
  - apply dheap_agree; [assumption| apply G; lia].
  - apply ddep_agree; [assumption| apply G; lia].
  - apply dwin_agree; assumption.
  - apply dprev_agree; assumption.
  - apply dhead_agree; assumption.
  - apply dpend_agree; assumption.
  - assumption.
  - assumption.
Qed.
Lemma DST_agree : DST m L s -> ag_blocks -> DST m' L s.
Proof.
  apply DSTx_agree. intros lo hi H _ _ AG. apply dsB_agree; [exact H|]. eapply agree_on_sub; [exact AG| lia| lia].
Qed.
Lemma DSTi_agree : DSTi m L s -> ag_blocks -> DSTi m' L s.
Proof.
  apply DSTx_agree. intros lo hi H _ _ AG. apply dsBi_agree; [exact H|]. eapply agree_on_sub; [exact AG| lia| lia].
Qed.

Lemma DREP_agree : DREP m L s -> ag_blocks -> agree_on (dl_S L) (dl_S L + 112) m m' -> DREP m' L s.
Proof. intros [Z D] AB AS. split; [eapply dzs_agree; eauto| apply DST_agree; assumption]. Qed.

Lemma DREPq_agree : forall z, DREPq m L s z -> ag_blocks -> agree_on (dl_S L + 48) (dl_S L + 112) m m' -> DREPq m' L s z.
Proof.
  intros z [Z D] AB AS. split; [eapply dzq_agree; [exact Z|]| apply DST_agree; assumption].
  eapply agree_on_sub; [exact AS| lia| lia].
Qed.
End Frame.

Lemma ag_blocks_munch : forall W m m' L, dlay_ok L -> munch W m m' -> wmono psegs m m' ->
  disjoint_from W (dl_As L) DS_SIZE -> disjoint_from W (dl_Aw L) DS_WIN -> disjoint_from W (dl_Ap L) (2 * DS_NPREV) ->
  disjoint_from W (dl_Ah L) (2 * DS_NHEAD) -> disjoint_from W (dl_Ab L) DS_PEND -> ag_blocks m m' L.
Proof.
  intros W m m' L HL MU WM D0 D1 D2 D3 D4.
  destruct (lo_s L HL) as (s1 & _ & s2 & _). destruct (lo_w L HL) as (w1 & _ & w2 & _). destruct (lo_p L HL) as (p1 & _ & p2 & _).
  destruct (lo_h L HL) as (h1 & _ & h2 & _). destruct (lo_b L HL) as (b1 & _ & b2 & _). clear HL.
  unfold ag_blocks in *.
  split; [apply (agree_on_of_munch W); [exact MU|exact WM|lia|lia|exact D0]|].
  split; [apply (agree_on_of_munch W); [exact MU|exact WM|lia|lia|exact D1]|].
  split; [apply (agree_on_of_munch W); [exact MU|exact WM|lia|lia|exact D2]|].
  split; [apply (agree_on_of_munch W); [exact MU|exact WM|lia|lia|exact D3]| apply (agree_on_of_munch W); [exact MU|exact WM|lia|lia|exact D4]].
Qed.

Lemma DST_set_strm : forall B m L s c, (B m L s -> B m L (set_strm s c)) -> DSTx B m L s -> DSTx B m L (set_strm s c).
Proof.
  intros B m L s c HB [HA HB0 HC HD Hlt Hdt Hbt Hblc Hheap Hdep Hwin Hprev Hhead Hpend Hlens Hlay].
  constructor; [exact HA| exact (HB HB0)| exact HC| exact HD| exact Hlt| exact Hdt| exact Hbt| exact Hblc| exact Hheap| exact Hdep
               | exact Hwin| exact Hprev| exact Hhead| exact Hpend| | exact Hlay].
  destruct Hlens as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13].
  constructor; [exact L1| exact L2| exact L3| exact L4| exact L5| exact L6| exact L7| exact L8| exact L9| exact L10| exact L11| exact L12| exact L13].
Qed.
