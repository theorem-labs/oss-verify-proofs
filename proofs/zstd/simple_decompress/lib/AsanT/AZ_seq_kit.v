(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition held (P : Prop) : Prop := P.
Lemma held_intro : forall P : Prop, P -> held P. Proof. intros P H; exact H. Qed.
(* [comment removed for export] *)
Ltac hold H := lazymatch type of H with ?T => change (held T) in H end.

Lemma stk_mid_frame : forall (m m' : word -> option byte) D n lo hi,
  stk bsegs m lo hi -> munch [(D, D + n)] m m' -> wmono bsegs m m' -> stk bsegs m' D (D + n) -> stk bsegs m' lo hi.
Proof.
  intros m m' D n lo hi (H1 & H2 & H) MU WM (_ & _ & HD). split; [lia|]. split; [lia|].
  intros a Ha. destruct (Z_lt_ge_dec a D) as [L|L]; [|destruct (Z_lt_ge_dec a (D + n)) as [L2|L2]].
  - destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|]. exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
  - apply HD. lia.
  - destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|]. exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
Qed.

Lemma rdbl_mid_frame : forall (m m' : word -> option byte) D n lo hi,
  rdbl bsegs m lo hi -> munch [(D, D + n)] m m' -> stk bsegs m' D (D + n) -> rdbl bsegs m' lo hi.
Proof.
  intros m m' D n lo hi (H1 & H2 & H) MU (_ & _ & HD). split; [lia|]. split; [lia|].
  intros a Ha. destruct (Z_lt_ge_dec a D) as [L|L]; [|destruct (Z_lt_ge_dec a (D + n)) as [L2|L2]].
  - destruct (H a Ha) as (b & Hb). exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
  - apply HD. lia.
  - destruct (H a Ha) as (b & Hb). exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
Qed.

Lemma stk_sub : forall (m : word -> option byte) lo hi lo' hi',
  stk bsegs m lo hi -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> stk bsegs m lo' hi'.
Proof.
  intros m lo hi lo' hi' ST H1 H2 H3.
  destruct (stk_split bsegs m lo lo' hi ST ltac:(lia)) as [_ T]. destruct (stk_split bsegs m lo' hi' hi T ltac:(lia)) as [T2 _]. exact T2.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_forget : forall (m : word -> option byte) A cs (k n : nat),
  rw_cells bsegs m A cs -> cells_size (firstn k cs) = n ->
  rw_cells bsegs m A (CB n (cells_bytes (firstn k cs)) :: skipn k cs).
Proof.
  intros m A cs k n RW SZ. pose proof RW as [[WF _] _].
  rewrite <- (firstn_skipn k cs) in WF. apply cells_wf_app in WF. destruct WF as [W1 W2].
  eapply rw_cells_recell; [exact RW| |].
  - cbn [cells_wf cell_wf]. split; [|exact W2]. rewrite cells_bytes_length by exact W1. exact SZ.
  - cbn [cells_bytes cbytes]. rewrite <- cells_bytes_app, firstn_skipn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma h5_explode : forall ws : list word, length ws = 44%nat ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 : word,
    ws = [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15; w16; w17; w18; w19; w20; w21; w22; w23; w24; w25; w26; w27; w28; w29; w30; w31; w32; w33; w34; w35; w36; w37; w38; w39; w40; w41; w42; w43].
Proof.
  intros ws L. do 44 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [|discriminate L].
  do 44 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma h5_view : forall (m : word -> option byte) DCTX ws,
  dctx_h5 bsegs m DCTX ws ->
  exists j1 j2 j3, length j1 = 24%nat /\ length j2 = 24%nat /\ length j3 = 192%nat /\
    rw_cells bsegs m (DCTX + 30096)
      [CB 24 j1; C8 (wnth ws H5_litPtr); CB 24 j2; C8 (wnth ws H5_litSize); CB 192 j3;
       C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (wnth ws H5_litBufferLocation)].
Proof.
  intros m DCTX ws (RW & WL).
  destruct (h5_explode ws WL) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & w32 & w33 & w34 & w35 & w36 & w37 & w38 & w39 & w40 & w41 & w42 & w43 & ->).
  cbv beta iota delta [h5_cells h5_sizes mk_wcells wnth nth H5_litPtr H5_litSize H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in *.
  exists (le8 w0 ++ le4 w1 ++ le4 w2 ++ le4 w3 ++ le4 w4),
         (le8 w6 ++ le8 w7 ++ le8 w8),
         (le8 w10 ++ le8 w11 ++ le4 w12 ++ le4 w13 ++ le8 w14 ++ le8 w15 ++ le4 w16 ++ le4 w17 ++ le4 w18 ++ le4 w19 ++ le8 w20 ++
          le4 w21 ++ le4 w22 ++ le4 w23 ++ le4 w24 ++ le8 w25 ++ le8 w26 ++ le8 w27 ++ le8 w28 ++ le8 w29 ++ le8 w30 ++ le8 w31 ++
          le8 w32 ++ le8 w33 ++ le4 w34 ++ le4 w35 ++ le4 w36 ++ le4 w37 ++ le8 w38 ++ le8 w39 ++ le8 w40).
  split; [rewrite !length_app, ?length_le8, ?length_le4; reflexivity|].
  split; [rewrite !length_app, ?length_le8, ?length_le4; reflexivity|].
  split; [rewrite !length_app, ?length_le8, ?length_le4; reflexivity|].
  eapply rw_cells_recell; [exact RW| |].
  - cbn [cells_wf cell_wf]. rewrite !length_app, ?length_le8, ?length_le4. repeat split; reflexivity.
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Definition BITMASK : Z := 0x22180.
Definition bitmask_bytes : list byte := Eval vm_compute in match image_bytes bsegs BITMASK 128 with Some bs => bs | None => [] end.

Lemma bitmask_at : forall m, mem_inv bsegs m -> bytes_at bsegs m BITMASK bitmask_bytes.
Proof.
  intros m MI. pose proof (ro_cells_image bsegs m BITMASK bitmask_bytes MI ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma bitmask_val : forall nb, 0 <= nb <= 31 ->
  bytes_le_to_Z (firstn 4 (skipn (Z.to_nat (4 * nb)) bitmask_bytes)) = 2^nb - 1.
Proof.
  intros nb H. assert (C : exists k : nat, (k <= 31)%nat /\ nb = Z.of_nat k) by (exists (Z.to_nat nb); lia).
  destruct C as (k & Hk & ->). do 32 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma bytes_eq_unsigned : forall a b : list byte, map (@bv_unsigned 8) a = map (@bv_unsigned 8) b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn [map] in H. injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma bitmask_know : forall m nb, mem_inv bsegs m -> 0 <= nb <= 31 ->
  rdn bsegs m (wa (BITMASK + 4 * nb)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (2^nb - 1))).
Proof.
  intros m nb MI H. replace (BITMASK + 4 * nb) with (BITMASK + Z.of_nat (Z.to_nat (4 * nb))) by lia.
  rewrite (bytes_at_rdn bsegs m BITMASK bitmask_bytes (Z.to_nat (4 * nb)) 4 (bitmask_at m MI)) by (change (length bitmask_bytes) with 128%nat; lia).
  f_equal. assert (C : exists k : nat, (k <= 31)%nat /\ nb = Z.of_nat k) by (exists (Z.to_nat nb); lia).
  destruct C as (k & Hk & ->). do 32 (destruct k as [|k]; [apply bytes_eq_unsigned; vm_compute; reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Lemma land_mask_lt : forall x nb, 0 <= x -> 0 <= nb -> 0 <= Z.land x (2^nb - 1) < 2^nb.
Proof.
  intros x nb Hx Hn. replace (2^nb - 1) with (Z.ones nb) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
