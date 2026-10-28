(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv BzContracts.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lbw_range : forall bs : list byte, (length bs <= 8)%nat ->
  0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs L. rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map bs)) as X.
  rewrite length_map in X. replace (2 ^ (8 * Z.of_nat (length bs))) with (256 ^ Z.of_nat (length bs)); [lia|].
  change 256 with (2 ^ 8). rewrite <- Z.pow_mul_r by lia. reflexivity.
Qed.

Lemma lbw_unsigned : forall bs : list byte, (length bs <= 8)%nat -> bv_unsigned (le_bytes_to_word bs) = bytes_le_to_Z bs.
Proof.
  intros bs L. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (lbw_range bs L). unfold bv_modulus.
  assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le4. rewrite lbw_unsigned by lia. rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

Lemma lbw4_range : forall bs : list byte, length bs = 4%nat -> 0 <= bv_unsigned (le_bytes_to_word bs) < 2 ^ 32.
Proof. intros bs L. rewrite lbw_unsigned by lia. pose proof (lbw_range bs ltac:(lia)). rewrite L in H. exact H. Qed.

(* [comment removed for export] *)
Definition zof4 (bs : list byte) : Z := bv_unsigned (le_bytes_to_word bs).
Lemma C4_of_bytes : forall bs, length bs = 4%nat -> cbytes (C4 (Z_to_bv 64 (zof4 bs))) = bs.
Proof. intros bs L. unfold zof4. cbn [cbytes]. rewrite Z_to_bv_bv_unsigned. apply le4_of_bytes. exact L. Qed.
Lemma zof4_range : forall bs, length bs = 4%nat -> 0 <= zof4 bs < 2 ^ 32.
Proof. intros. apply lbw4_range. assumption. Qed.

(* [comment removed for export] *)
Lemma u32s_of_bytes : forall (k : nat) (bs : list byte), length bs = (4 * k)%nat ->
  exists ws, u32s ws = bs /\ length ws = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - exists []. destruct bs; [split; reflexivity| cbn in L; lia].
  - cps_destruct (IH (skipn 4 bs)) as (ws & E & Lw); [rewrite skipn_length; lia|].
    exists (le_bytes_to_word (firstn 4 bs) :: ws). split.
    + cbn [u32s]. rewrite le4_of_bytes by (rewrite firstn_length_le; lia). rewrite E. apply firstn_skipn.
    + cbn. lia.
Qed.

Section WithSegs.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Lemma bytes_wr_split : forall m A bs n k,
    bytes_at segs m A bs -> wr_at segs m A n -> Z.of_nat (length bs) = n -> 0 <= k <= n ->
    (bytes_at segs m A (firstn (Z.to_nat k) bs) /\ wr_at segs m A k /\ Z.of_nat (length (firstn (Z.to_nat k) bs)) = k) /\
    (bytes_at segs m (A + k) (skipn (Z.to_nat k) bs) /\ wr_at segs m (A + k) (n - k) /\ Z.of_nat (length (skipn (Z.to_nat k) bs)) = n - k).
  Proof.
    intros m A bs n k B W L K.
    rewrite <- (firstn_skipn (Z.to_nat k) bs) in B. apply bytes_at_app in B. destruct B as [B1 B2].
    assert (L1 : Z.of_nat (length (firstn (Z.to_nat k) bs)) = k) by (rewrite firstn_length_le; lia).
    rewrite L1 in B2. cps_destruct W as (W0 & W1 & W2).
    split; (split; [assumption|]); split.
    - split; [lia|]. split; [lia|]. intros i Hi. apply W2. lia.
    - exact L1.
    - split; [lia|]. split; [lia|]. intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply W2. lia.
    - rewrite skipn_length. lia.
  Qed.

  Lemma u8arr_of_bw : forall m A bs n, bytes_at segs m A bs -> wr_at segs m A n -> Z.of_nat (length bs) = n -> u8arr segs m A bs.
  Proof. intros m A bs n B W L. split; [exact B|]. rewrite L. exact W. Qed.

  Lemma u32arr_of_bw : forall m A bs n (k : nat), bytes_at segs m A bs -> wr_at segs m A n -> Z.of_nat (length bs) = n -> n = 4 * Z.of_nat k ->
    exists ws, u32arr segs m A ws /\ length ws = k.
  Proof.
    intros m A bs n k B W L K. cps_destruct (u32s_of_bytes k bs ltac:(lia)) as (ws & E & Lw).
    exists ws. split; [|exact Lw]. split; [rewrite E; exact B|]. rewrite Lw, <- K. exact W.
  Qed.

  Lemma CB_of_bw : forall m A bs n (k : nat), bytes_at segs m A bs -> wr_at segs m A n -> Z.of_nat (length bs) = n -> n = Z.of_nat k ->
    rw_cells segs m A [CB k bs].
  Proof.
    intros m A bs n k B W L K. split; [split|].
    - cbn. split; [lia| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
    - cbn [cells_size csize]. rewrite Nat.add_0_r, <- K. exact W.
  Qed.

  Lemma C4_of_bw : forall m A bs n, bytes_at segs m A bs -> wr_at segs m A n -> Z.of_nat (length bs) = n -> n = 4 ->
    rw_cells segs m A [C4 (Z_to_bv 64 (zof4 bs))] /\ 0 <= zof4 bs < 2 ^ 32.
  Proof.
    intros m A bs n B W L K. assert (L4 : length bs = 4%nat) by lia. split; [| apply zof4_range; exact L4].
    split; [split|].
    - cbn. auto.
    - cbn [cells_bytes]. rewrite C4_of_bytes, app_nil_r by exact L4. exact B.
    - cbn [cells_size csize]. replace (Z.of_nat (4 + 0)) with n by lia. exact W.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dhead_init (strm small : Z) (p20 p4 p3 p12 : list byte) : list cell :=
    [C8 (Z_to_bv 64 strm); C4 (Z_to_bv 64 10); CB 20 p20; C8 (Z_to_bv 64 0);
     CB 4 p4; C1 (Z_to_bv 8 small); CB 3 p3; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 12 p12].
  Definition dmid_init (q12 q4 : list byte) : list cell :=
    [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 12 q12; C4 (Z_to_bv 64 0); CB 4 q4].

  (* [comment removed for export] *)
  Definition h_init (strm small : Z) (p20 p4 p3 p12 : list byte) : dsh :=
    DSH strm 10 (nth 0 p20 (Z_to_bv 8 0)) (firstn 3 (skipn 1 p20)) (zof4 (firstn 4 (skipn 4 p20)))
        (nth 8 p20 (Z_to_bv 8 0)) (firstn 3 (skipn 9 p20)) (zof4 (firstn 4 (skipn 12 p20))) (zof4 (firstn 4 (skipn 16 p20)))
        0 0 (zof4 p4) (Z_to_bv 8 small) p3 0 0 (zof4 (firstn 4 p12))
        (le_bytes_to_word (firstn 4 (skipn 4 p12))) (le_bytes_to_word (firstn 4 (skipn 8 p12))).

  Lemma list20 : forall (l : list byte), length l = 20%nat -> exists x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19,
    l = [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16;x17;x18;x19].
  Proof.
    intros l L.
    do 20 (destruct l as [|? l]; [cbn in L; lia|]). destruct l; [|cbn in L; lia]. repeat eexists. 
  Qed.
  Lemma list12 : forall (l : list byte), length l = 12%nat -> exists x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11,
    l = [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11].
  Proof. intros l L. do 12 (destruct l as [|? l]; [cbn in L; lia|]). destruct l; [|cbn in L; lia]. repeat eexists. Qed.
  Lemma list4 : forall (l : list byte), length l = 4%nat -> exists x0 x1 x2 x3, l = [x0;x1;x2;x3].
  Proof. intros l L. do 4 (destruct l as [|? l]; [cbn in L; lia|]). destruct l; [|cbn in L; lia]. repeat eexists. Qed.

  Lemma carve_head : forall m S strm small p20 p4 p3 p12,
    rw_cells segs m S (dhead_init strm small p20 p4 p3 p12) -> 0 <= small < 256 ->
    let h := h_init strm small p20 p4 p3 p12 in
    rw_cells segs m S (HEAD_CELLS h)
    /\ length (sh_p1 h) = 3%nat /\ length (sh_p2 h) = 3%nat /\ length (sh_p3 h) = 3%nat
    /\ 0 <= sh_solen h < 2 ^ 32 /\ 0 <= sh_rNToGo h < 2 ^ 32 /\ 0 <= sh_rTPos h < 2 ^ 32 /\ 0 <= sh_n h < 2 ^ 32 /\ 0 <= sh_origPtr h < 2 ^ 32
    /\ bv_unsigned (sh_small h) = small.
  Proof.
    intros m S strm small p20 p4 p3 p12 H SM h.
    pose proof (proj1 (proj1 H)) as WF. cbn in WF. cps_destruct WF as (_ & _ & L20 & _ & L4 & _ & L3 & _ & _ & L12 & _).
    cps_destruct (list20 p20 L20) as (x0&x1&x2&x3&x4&x5&x6&x7&x8&x9&x10&x11&x12&x13&x14&x15&x16&x17&x18&x19&E20).
    cps_destruct (list12 p12 L12) as (y0&y1&y2&y3&y4&y5&y6&y7&y8&y9&y10&y11&E12).
    cps_destruct (list4 p4 L4) as (z0&z1&z2&z3&E4).
    subst p20 p12 p4. subst h. unfold h_init. cbn [nth firstn skipn sh_p1 sh_p2 sh_p3 sh_solen sh_rNToGo sh_rTPos sh_n sh_origPtr sh_small].
    split.
    - eapply rw_cells_same_bytes; [ | | | exact H].
      + unfold dhead_init.
        cbn [cells_bytes cbytes app sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
             sh_cbn sh_verb sh_origPtr sh_tPos sh_k0].
        unfold zof4. rewrite !Z_to_bv_bv_unsigned. rewrite !le4_of_bytes by reflexivity. reflexivity.
      + reflexivity.
      + cbn. repeat split; auto; exact L3.
    - repeat match goal with |- _ /\ _ => split end; try reflexivity; try exact L3; try (apply zof4_range; reflexivity).
      apply byte_lit_unsigned. exact SM.
  Qed.

  Definition d_init (q12 q4 : list byte) : dsm :=
    DSM 0 0 0 (le_bytes_to_word (firstn 4 q12)) (le_bytes_to_word (firstn 4 (skipn 4 q12))) (le_bytes_to_word (firstn 4 (skipn 8 q12)))
        (Z_to_bv 64 0) (zof4 q4).

  Lemma carve_mid : forall m A q12 q4,
    rw_cells segs m A (dmid_init q12 q4) ->
    let d := d_init q12 q4 in
    rw_cells segs m A (MID_CELLS d) /\ sm_tt d = 0 /\ sm_ll16 d = 0 /\ sm_ll4 d = 0 /\ 0 <= sm_nInUse d < 2 ^ 32.
  Proof.
    intros m A q12 q4 H d.
    pose proof (proj1 (proj1 H)) as WF. cbn in WF. cps_destruct WF as (_ & _ & _ & L12 & _ & L4 & _).
    cps_destruct (list12 q12 L12) as (y0&y1&y2&y3&y4&y5&y6&y7&y8&y9&y10&y11&E12).
    cps_destruct (list4 q4 L4) as (z0&z1&z2&z3&E4). subst q12 q4 d. unfold d_init.
    cbn [firstn skipn sm_tt sm_ll16 sm_ll4 sm_nInUse].
    split; [| repeat split; try reflexivity; apply zof4_range; reflexivity].
    eapply rw_cells_same_bytes; [ | | | exact H].
    - unfold dmid_init. cbn [cells_bytes cbytes app sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse].
      unfold zof4. rewrite !Z_to_bv_bv_unsigned. rewrite !le4_of_bytes by reflexivity. reflexivity.
    - reflexivity.
    - cbn. repeat split; auto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac peel B W L k B1 W1 L1 :=
    let X := fresh in
    pose proof (bytes_wr_split _ _ _ _ k B W L ltac:(lia)) as X;
    clear B W L;
    destruct X as [[B1 [W1 L1]] [B [W L]]];
    cbn [Z.to_nat Pos.to_nat] in B1, L1;
    match type of B with bytes_at _ _ ?a _ => let a' := eval cbn in a in idtac end.

  Lemma carve_rest : forall m S bsA bsB,
    bytes_at segs m (S + 68) bsA -> wr_at segs m (S + 68) 3084 -> Z.of_nat (length bsA) = 3084 ->
    bytes_at segs m (S + 3196) bsB -> wr_at segs m (S + 3196) 60948 -> Z.of_nat (length bsB) = 60948 ->
    exists (nbu : Z) (cf : list word) (r : drest) (js : list byte),
      rw_cells segs m (S + 1092) [C4 (Z_to_bv 64 nbu)] /\ 0 <= nbu < 2 ^ 32 /\
      u32arr segs m (S + 1096) cf /\ length cf = 257%nat /\
      drest_at segs m S r /\
      rw_cells segs m (S + 64036) [CB 108 js] /\ length js = 108%nat.
  Proof.
    intros m S bsA bsB BA WA LA BB WB LB.
    (* [comment removed for export] *)
    peel BA WA LA 1024 Bu Wu Lu.
    cps_destruct (u32arr_of_bw _ _ _ _ 256 Bu Wu Lu ltac:(lia)) as (unz & Aunz & Lunz).
    replace (S + 68 + 1024) with (S + 1092) in BA, WA by lia.
    peel BA WA LA 4 Bn Wn Ln.
    destruct (C4_of_bw _ _ _ _ Bn Wn Ln ltac:(lia)) as [Cn Rn].
    replace (S + 1092 + 4) with (S + 1096) in BA, WA by lia.
    peel BA WA LA 1028 Bc Wc Lc.
    cps_destruct (u32arr_of_bw _ _ _ _ 257 Bc Wc Lc ltac:(lia)) as (cf & Acf & Lcf).
    replace (S + 1096 + 1028) with (S + 2124) in BA, WA by lia.
    replace (3084 - 1024 - 4 - 1028) with 1028 in WA, LA by lia.
    cps_destruct (u32arr_of_bw _ _ _ _ 257 BA WA LA ltac:(lia)) as (cfc & Acfc & Lcfc).
    (* [comment removed for export] *)
    peel BB WB LB 256 B1 W1 L1. pose proof (u8arr_of_bw _ _ _ _ B1 W1 L1) as A1.
    replace (S + 3196 + 256) with (S + 3452) in BB, WB by lia.
    peel BB WB LB 16 B2 W2 L2. pose proof (u8arr_of_bw _ _ _ _ B2 W2 L2) as A2.
    replace (S + 3452 + 16) with (S + 3468) in BB, WB by lia.
    peel BB WB LB 256 B3 W3 L3. pose proof (u8arr_of_bw _ _ _ _ B3 W3 L3) as A3.
    replace (S + 3468 + 256) with (S + 3724) in BB, WB by lia.
    peel BB WB LB 4096 B4 W4 L4. pose proof (u8arr_of_bw _ _ _ _ B4 W4 L4) as A4.
    replace (S + 3724 + 4096) with (S + 7820) in BB, WB by lia.
    peel BB WB LB 64 B5 W5 L5. cps_destruct (u32arr_of_bw _ _ _ _ 16 B5 W5 L5 ltac:(lia)) as (mtfb & A5 & L5').
    replace (S + 7820 + 64) with (S + 7884) in BB, WB by lia.
    peel BB WB LB 18002 B6 W6 L6. pose proof (u8arr_of_bw _ _ _ _ B6 W6 L6) as A6.
    replace (S + 7884 + 18002) with (S + 25886) in BB, WB by lia.
    peel BB WB LB 18002 B7 W7 L7. pose proof (u8arr_of_bw _ _ _ _ B7 W7 L7) as A7.
    replace (S + 25886 + 18002) with (S + 43888) in BB, WB by lia.
    peel BB WB LB 1548 B8 W8 L8. pose proof (u8arr_of_bw _ _ _ _ B8 W8 L8) as A8.
    replace (S + 43888 + 1548) with (S + 45436) in BB, WB by lia.
    peel BB WB LB 6192 B9 W9 L9. cps_destruct (u32arr_of_bw _ _ _ _ 1548 B9 W9 L9 ltac:(lia)) as (lim & A9 & L9').
    replace (S + 45436 + 6192) with (S + 51628) in BB, WB by lia.
    peel BB WB LB 6192 B10 W10 L10. cps_destruct (u32arr_of_bw _ _ _ _ 1548 B10 W10 L10 ltac:(lia)) as (base & A10 & L10').
    replace (S + 51628 + 6192) with (S + 57820) in BB, WB by lia.
    peel BB WB LB 6192 B11 W11 L11. cps_destruct (u32arr_of_bw _ _ _ _ 1548 B11 W11 L11 ltac:(lia)) as (perm & A11 & L11').
    replace (S + 57820 + 6192) with (S + 64012) in BB, WB by lia.
    peel BB WB LB 24 B12 W12 L12. cps_destruct (u32arr_of_bw _ _ _ _ 6 B12 W12 L12 ltac:(lia)) as (minl & A12 & L12').
    replace (S + 64012 + 24) with (S + 64036) in BB, WB by lia.
    replace (60948 - 256 - 16 - 256 - 4096 - 64 - 18002 - 18002 - 1548 - 6192 - 6192 - 6192 - 24) with 108 in WB, LB by lia.
    pose proof (CB_of_bw _ _ _ _ 108 BB WB LB ltac:(lia)) as A13.
    eexists. exists cf. eexists (DREST unz cfc _ _ _ _ mtfb _ _ _ lim base perm minl). eexists.
    split; [exact Cn|]. split; [exact Rn|]. split; [exact Acf|]. split; [exact Lcf|].
    split; [| split; [exact A13| lia]].
    unfold drest_at. cbn [r_unz r_cfc r_inUse r_in16 r_s2u r_mtfa r_mtfb r_sel r_selm r_len r_lim r_base r_perm r_minl].
    split; [split; [exact Aunz| lia]|]. split; [split; [exact Acfc| lia]|].
    split; [split; [exact A1| lia]|]. split; [split; [exact A2| lia]|]. split; [split; [exact A3| lia]|]. split; [split; [exact A4| lia]|].
    split; [split; [exact A5| lia]|]. split; [split; [exact A6| lia]|]. split; [split; [exact A7| lia]|]. split; [split; [exact A8| lia]|].
    split; [split; [exact A9| lia]|]. split; [split; [exact A10| lia]|]. split; [split; [exact A11| lia]| split; [exact A12| lia]].
  Qed.

  (* [comment removed for export] *)
  Lemma split_block : forall m S junk,
    rw_cells segs m S [CB (Z.to_nat 64144) junk] ->
    rw_cells segs m S [CB 68 (firstn 68 junk)]
    /\ (bytes_at segs m (S + 68) (firstn (Z.to_nat 3084) (skipn 68 junk)) /\ wr_at segs m (S + 68) 3084
        /\ Z.of_nat (length (firstn (Z.to_nat 3084) (skipn 68 junk))) = 3084)
    /\ rw_cells segs m (S + 3152) [CB 44 (firstn 44 (skipn (Z.to_nat 3084) (skipn 68 junk)))]
    /\ (exists bsB, bytes_at segs m (S + 3196) bsB /\ wr_at segs m (S + 3196) 60948 /\ Z.of_nat (length bsB) = 60948).
  Proof.
    intros m S junk H.
    pose proof (u8arr_of_rw_cells segs _ _ _ _ H) as [B W].
    pose proof (proj1 (proj1 H)) as WF. cbn in WF. destruct WF as [LJ _].
    assert (L : Z.of_nat (length junk) = 64144) by (rewrite LJ; rewrite Z2Nat.id; lia).
    rewrite LJ, Z2Nat.id in W by lia.
    peel B W L 68 B1 W1 L1.
    split; [apply (CB_of_bw _ _ _ _ 68 B1 W1 L1); lia|].
    peel B W L 3084 B2 W2 L2.
    replace (S + 68 + 3084) with (S + 3152) in B, W by lia.
    split; [split; [exact B2| split; [exact W2| exact L2]]|].
    peel B W L 44 B3 W3 L3.
    replace (S + 3152 + 44) with (S + 3196) in B, W by lia.
    replace (64144 - 68 - 3084 - 44) with 60948 in W, L by lia.
    split; [apply (CB_of_bw _ _ _ _ 44 B3 W3 L3); lia|].
    eexists. split; [exact B| split; [exact W| exact L]].
  Qed.
End WithSegs.

End ACeilS1.
