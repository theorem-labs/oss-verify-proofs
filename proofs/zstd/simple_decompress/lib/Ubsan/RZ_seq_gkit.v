(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition bit_ok (SEQ n bc ptr : Z) : Prop := bc <= 64 -> ptr = SEQ \/ (8 <= n /\ SEQ <= ptr <= SEQ + n - 8).

Lemma bit_ok_mono : forall S n bc bc' ptr, bit_ok S n bc ptr -> bc <= bc' -> bit_ok S n bc' ptr.
Proof. intros S n bc bc' ptr H L H64. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma tbl_len_LL : forall t, seq_table_ok K_LL t -> Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes t))) <= 4104.
Proof. intros t OK. pose proof (seq_tbl_len_le K_LL t OK) as H. cbn [kind_maxLog] in H. change (8 * (1 + 2^9)) with 4104 in H. exact H. Qed.
Lemma tbl_len_OF : forall t, seq_table_ok K_OF t -> Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes t))) <= 2056.
Proof. intros t OK. pose proof (seq_tbl_len_le K_OF t OK) as H. cbn [kind_maxLog] in H. change (8 * (1 + 2^8)) with 2056 in H. exact H. Qed.
Lemma tbl_len_ML : forall t, seq_table_ok K_ML t -> Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes t))) <= 4104.
Proof. intros t OK. pose proof (seq_tbl_len_le K_ML t OK) as H. cbn [kind_maxLog] in H. change (8 * (1 + 2^9)) with 4104 in H. exact H. Qed.

Lemma seq_pow_le : forall k t, seq_table_ok k t -> 1 <= 2^(st_log t) <= 512.
Proof.
  intros k t OK. pose proof (seq_tl_range k t OK) as R. split; [pose proof (Z.pow_pos_nonneg 2 (st_log t)); lia|].
  change 512 with (2^9). apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Ltac kx_lia ::= kx_bv_ranges; first [ assumption | lia ].

(* [comment removed for export] *)
Lemma rbf_bound : forall x a, 0 <= x < 2^64 -> 1 <= a <= 63 -> 0 <= x / 2 ^ (((-1 * a) mod 2 ^ 64) mod 64) < 2^a.
Proof.
  intros x a Hx Ha.
  assert (E : ((-1 * a) mod 2 ^ 64) mod 64 = 64 - a).
  { replace ((-1 * a) mod 2^64) with (2^64 - a) by (apply Z.mod_unique with (-1); lia).
    symmetry. apply Z.mod_unique with (2^58 - 1); lia. }
  rewrite E. split; [apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  replace (2^64) with (2^(64 - a) * 2^a) in Hx by (rewrite <- Z.pow_add_r by lia; f_equal; lia). lia.
Qed.

Lemma rbf_bound_w : forall (w : word) a, 1 <= a <= 63 -> 0 <= bv_unsigned w / 2 ^ (((-1 * a) mod 2 ^ 64) mod 64) < 2^a.
Proof. intros w a Ha. apply rbf_bound; [|exact Ha]. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. exact R. Qed.

(* [comment removed for export] *)
Ltac sd_rbf :=
  repeat match goal with
  | |- context [bv_unsigned ?w / 2 ^ (((-1 * ?a) mod 2 ^ 64) mod 64)] =>
      lazymatch goal with
      | _ : 0 <= bv_unsigned w / 2 ^ (((-1 * a) mod 2 ^ 64) mod 64) < 2 ^ a |- _ => fail
      | _ => pose proof (rbf_bound_w w a ltac:(lia))
      end
  end.

(* [comment removed for export] *)
Lemma land_mask_lt2 : forall x nb, 0 <= nb -> 0 <= Z.land x (2^nb - 1) < 2^nb.
Proof.
  intros x nb Hn. replace (2^nb - 1) with (Z.ones nb) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
Lemma land_mask_lt3 : forall x nb, 0 <= nb <= 62 -> 0 <= Z.land x ((2^nb + -1) mod 2^64) < 2^nb.
Proof.
  intros x nb Hn. assert (P : 0 < 2^nb) by (apply Z.pow_pos_nonneg; lia).
  assert (Q : 2^nb <= 2^62) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.mod_small by lia. replace (2^nb + -1) with (2^nb - 1) by lia. apply land_mask_lt2. lia.
Qed.
(* [comment removed for export] *)
Ltac sd_land :=
  repeat match goal with
  | |- context [Z.land ?x ((2 ^ ?b + -1) mod 2 ^ 64)] =>
      let H := fresh "LND" in pose proof (land_mask_lt3 x b ltac:(lia)) as H;
      let v := fresh "lv" in set (v := Z.land x ((2 ^ b + -1) mod 2 ^ 64)) in *; clearbody v
  end.
(* [comment removed for export] *)
Ltac sd_rbf2 :=
  repeat match goal with
  | |- context [bv_unsigned ?w / 2 ^ (((-1 * ?a) mod 2 ^ 64) mod 64)] =>
      let H := fresh "RBF" in pose proof (rbf_bound_w w a ltac:(lia)) as H;
      let v := fresh "rv" in set (v := bv_unsigned w / 2 ^ (((-1 * a) mod 2 ^ 64) mod 64)) in *; clearbody v
  end.

(* [comment removed for export] *)
Lemma signed_small : forall x, - 2^63 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x H. rewrite zb_signed. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  destruct (Z_lt_ge_dec x 0) as [N|N].
  - replace (x mod 2^64) with (x + 2^64) by (apply Z.mod_unique with (-1); lia).
    destruct (Z.ltb_spec0 (x + 2^64) (2^63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec0 x (2^63)); lia.
Qed.
Lemma mod64_neg : forall x, - 2^64 < x < 0 -> x mod 2^64 = x + 2^64.
Proof. intros x H. symmetry; apply Z.mod_unique with (-1); lia. Qed.
(* [comment removed for export] *)
Ltac sd_diffs :=
  repeat match goal with
  | H : context [bv_signed (Z_to_bv 64 ?x)] |- _ => rewrite (signed_small x) in H by lia
  | H : context [?x mod 2 ^ 64] |- _ => first [ rewrite (Z.mod_small x) in H by lia | rewrite (mod64_neg x) in H by lia ]
  end.

(* [comment removed for export] *)
Ltac sd_copy_intro INV :=
  let ms' := fresh "ms'" in
  intros ms' (?t0 & ?t1 & ?t2 & ?a1 & ?a2 & ?a3 & ?a4 & ?a5 & ?a6 & ?a7 & ?t3 & ?t4 & ?t5 & ?t6 & ?m' & -> & INV);
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition h5_j1 (ws : list word) : list byte :=
  le8 (wnth ws 0) ++ le4 (wnth ws 1) ++ le4 (wnth ws 2) ++ le4 (wnth ws 3) ++ le4 (wnth ws 4).
Definition h5_j2 (ws : list word) : list byte := le8 (wnth ws 6) ++ le8 (wnth ws 7) ++ le8 (wnth ws 8).
Definition h5_j3 (ws : list word) : list byte :=
  le8 (wnth ws 10) ++ le8 (wnth ws 11) ++ le4 (wnth ws 12) ++ le4 (wnth ws 13) ++ le8 (wnth ws 14) ++ le8 (wnth ws 15) ++
  le4 (wnth ws 16) ++ le4 (wnth ws 17) ++ le4 (wnth ws 18) ++ le4 (wnth ws 19) ++ le8 (wnth ws 20) ++
  le4 (wnth ws 21) ++ le4 (wnth ws 22) ++ le4 (wnth ws 23) ++ le4 (wnth ws 24) ++ le8 (wnth ws 25) ++ le8 (wnth ws 26) ++
  le8 (wnth ws 27) ++ le8 (wnth ws 28) ++ le8 (wnth ws 29) ++ le8 (wnth ws 30) ++ le8 (wnth ws 31) ++ le8 (wnth ws 32) ++
  le8 (wnth ws 33) ++ le4 (wnth ws 34) ++ le4 (wnth ws 35) ++ le4 (wnth ws 36) ++ le4 (wnth ws 37) ++ le8 (wnth ws 38) ++
  le8 (wnth ws 39) ++ le8 (wnth ws 40).
Definition h5_vcells (ws : list word) (loc : word) : list cell :=
  [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws);
   C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 loc].
Definition h5_viewed (m : word -> option byte) (DCTX : Z) (ws : list word) (loc : word) : Prop :=
  rw_cells usegs m (DCTX + 30096) (h5_vcells ws loc) /\ length ws = 44%nat.

Lemma h5_view2 : forall (m : word -> option byte) DCTX ws,
  dctx_h5 usegs m DCTX ws -> h5_viewed m DCTX ws (wnth ws H5_litBufferLocation).
Proof.
  intros m DCTX ws (RW & WL). split; [|exact WL].
  destruct (h5_explode ws WL) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & w32 & w33 & w34 & w35 & w36 & w37 & w38 & w39 & w40 & w41 & w42 & w43 & ->).
  cbv beta iota delta [h5_vcells h5_j1 h5_j2 h5_j3 h5_cells h5_sizes mk_wcells wnth nth H5_litPtr H5_litSize H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in *.
  eapply rw_cells_recell; [exact RW| |].
  - cbn [cells_wf cell_wf]. rewrite !length_app, ?length_le8, ?length_le4. repeat split; reflexivity.
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma h5_close : forall (m : word -> option byte) DCTX ws loc,
  h5_viewed m DCTX ws loc -> dctx_h5 usegs m DCTX (wupd ws H5_litBufferLocation loc).
Proof.
  intros m DCTX ws loc (RW & WL).
  destruct (h5_explode ws WL) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & w32 & w33 & w34 & w35 & w36 & w37 & w38 & w39 & w40 & w41 & w42 & w43 & ->).
  split; [|reflexivity].
  cbv beta iota delta [h5_vcells h5_j1 h5_j2 h5_j3 h5_cells h5_sizes mk_wcells wnth wupd nth H5_litPtr H5_litSize H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in *.
  eapply rw_cells_recell; [exact RW| |].
  - cbn [cells_wf cell_wf]. repeat split; reflexivity.
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wnth_wupd_other : forall ws i j v, i <> j -> wnth (wupd ws j v) i = wnth ws i.
Proof.
  unfold wnth. induction ws as [|w ws IH]; intros i j v NE; [destruct j; reflexivity|].
  destruct j as [|j]; destruct i as [|i]; cbn [wupd nth]; try reflexivity; [congruence|]. apply IH. congruence.
Qed.

(* [comment removed for export] *)
Lemma h5_lbe_know : forall (m : word -> option byte) DCTX ws loc LBE,
  h5_viewed m DCTX ws loc -> wnth ws H5_litBufferEnd = Z_to_bv 64 LBE ->
  rdn usegs m (wa (DCTX + 30360)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 LBE)).
Proof.
  intros m DCTX ws loc LBE (RW & _) E.
  pose proof (rw_cells_read usegs m (DCTX + 30096) _ 264%nat (C8 (wnth ws H5_litBufferEnd)) RW eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (DCTX + 30096 + Z.of_nat 264) with (DCTX + 30360) in R by lia.
  rewrite E in R. exact R.
Qed.
