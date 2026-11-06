(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 520 of its 641 lines of code are new or changed and 714 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/reply.v; 290 of its 332 lines of code are new or changed and 599 lines of the source are left out. *)
(* reac-pw/fuzz_link, PLAIN build: the proofs of the two statements of lib/Prog/mf_bridge_c.v.

   - `mf_cells_of_k`: link's memory FILE as memfile_k / mf_dyn / mf_pend_bytes state it (each field a
     `YI04.val_mem` fact) gives the 232 FILE bytes as the cells `mf_file_l` and the buffer as the k
     pending bytes then the rest. The CB pieces are the bytes that are there: the block is writable
     (memfile_k's `wr_at`), and in link's image every writable segment is also readable, so each of its
     bytes reads as some byte (`wr_bytes`).
   - `mf_post_of_cells`: after a call that changed only [lo, sp), the 232 FILE bytes and the buffer, with
     the FILE's cells and the buffer's cells as the statement gives them, memfile_k, mf_dyn and
     mf_pend_bytes hold again. A field whose cell did not change has the same bytes in both memories
     (`val_mem_move`); the cookie (+232..+272) is outside the three changed ranges (`val_mem_munch`);
     the new window words and orientation are read off the new cells.

   Pure memory reasoning over lib/Lib's vocabulary (link_mem exports it); no walk. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem memfile_c printf_facts_c vfprintf_c mf_bridge_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YH02 YI04 YI14 YP09 YO0f.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Field facts and bytes, over any segment list
   ========================================================================== *)

Section G.
Variable segs : list Segment.

Lemma mbyte_is_mrd : forall m x, YP09.mbyte segs m x = mrd segs m (wa x).
Proof. reflexivity. Qed.

Lemma nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma le_byte_bv : forall v n k, (k < n)%nat ->
  Z_to_bv 8 (YO0f.le_byte v n k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v n k Hk. unfold YO0f.le_byte. apply Z_to_bv8_mod.
  change 256 with (2 ^ 8). rewrite Z.mod_mod by lia. apply shiftr_mod_mod8; lia.
Qed.

(* a field fact is the field's little-endian bytes, and back *)
Lemma val_mem_le : forall m a n v, YI04.val_mem segs m a n v -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  bytes_at segs m a (Z_to_le_bytes n v).
Proof.
  intros m a n v H Ha Hb. split; [exact Ha|]. rewrite length_Z_to_le_bytes. split; [exact Hb|].
  intros i Hi. rewrite nth_le_bytes by exact Hi.
  pose proof (H i Hi) as Hv. rewrite le_byte_bv in Hv by exact Hi. exact Hv.
Qed.

Lemma le_val_mem : forall m a n v, bytes_at segs m a (Z_to_le_bytes n v) -> YI04.val_mem segs m a n v.
Proof.
  intros m a n v (_ & _ & H) k Hk. rewrite length_Z_to_le_bytes in H. specialize (H k Hk).
  rewrite nth_le_bytes in H by exact Hk. rewrite le_byte_bv by exact Hk. exact H.
Qed.

Lemma list_ext_nth : forall {A : Type} (l1 l2 : list A), length l1 = length l2 ->
  (forall k, (k < length l1)%nat -> nth_error l1 k = nth_error l2 k) -> l1 = l2.
Proof.
  intros A. induction l1 as [|x l1 IH]; intros [|y l2] Hl H; cbn in Hl; try discriminate; [reflexivity|].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn in H0. injection H0 as ->. f_equal.
  apply IH; [lia|]. intros k Hk. exact (H (S k) ltac:(cbn; lia)).
Qed.

(* two field facts at one place, both values in the field's range, name one value *)
Lemma val_mem_det : forall m a n v1 v2, YI04.val_mem segs m a n v1 -> YI04.val_mem segs m a n v2 ->
  0 <= v1 < 2 ^ (8 * Z.of_nat n) -> 0 <= v2 < 2 ^ (8 * Z.of_nat n) -> v1 = v2.
Proof.
  intros m a n v1 v2 H1 H2 R1 R2.
  assert (E : Z_to_le_bytes n v1 = Z_to_le_bytes n v2).
  { apply list_ext_nth; [rewrite !length_Z_to_le_bytes; reflexivity|].
    intros k Hk. rewrite length_Z_to_le_bytes in Hk. rewrite !nth_le_bytes by exact Hk.
    rewrite <- (le_byte_bv v1 n k Hk), <- (le_byte_bv v2 n k Hk).
    rewrite <- (H1 k Hk), <- (H2 k Hk). reflexivity. }
  apply (f_equal bytes_le_to_Z) in E. rewrite !bytes_le_to_Z_to_le_bytes in E by lia.
  rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma val_mem_det4 : forall m a v1 v2, YI04.val_mem segs m a 4 v1 -> YI04.val_mem segs m a 4 v2 ->
  0 <= v1 < 2 ^ 32 -> 0 <= v2 < 2 ^ 32 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 R1 R2. apply (val_mem_det m a 4 v1 v2 H1 H2); change (8 * Z.of_nat 4) with 32; lia.
Qed.

Lemma val_mem_det8 : forall m a v1 v2, YI04.val_mem segs m a 8 v1 -> YI04.val_mem segs m a 8 v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 R1 R2. apply (val_mem_det m a 8 v1 v2 H1 H2); change (8 * Z.of_nat 8) with 64; lia.
Qed.

(* FRAME: a field fact over bytes that are the same in m and m' moves from m to m' *)
Lemma val_mem_move : forall m m' a n v A bs,
  YI04.val_mem segs m a n v -> bytes_at segs m A bs -> bytes_at segs m' A bs ->
  A <= a -> a + Z.of_nat n <= A + Z.of_nat (length bs) -> YI04.val_mem segs m' a n v.
Proof.
  intros m m' a n v A bs Hv (_ & _ & H) (_ & _ & H') H1 H2 k Hk.
  assert (E : YP09.mbyte segs m' (a + Z.of_nat k) = YP09.mbyte segs m (a + Z.of_nat k)).
  { replace (a + Z.of_nat k) with (A + Z.of_nat (Z.to_nat (a + Z.of_nat k - A))) by lia.
    rewrite !mbyte_is_mrd.
    rewrite (H (Z.to_nat (a + Z.of_nat k - A))) by lia. rewrite (H' (Z.to_nat (a + Z.of_nat k - A))) by lia.
    reflexivity. }
  rewrite E. exact (Hv k Hk).
Qed.

(* ... and a field fact over bytes a call did not write moves too *)
Lemma val_mem_munch : forall W m m' a n v, YI04.val_mem segs m a n v -> munch W m m' ->
  (forall x, a <= x < a + Z.of_nat n -> 0 <= x < 2 ^ 64 /\ outside W x) -> YI04.val_mem segs m' a n v.
Proof.
  intros W m m' a n v Hv Hm Ho k Hk.
  destruct (Ho (a + Z.of_nat k) ltac:(lia)) as [Hr Hx].
  assert (E : YP09.mbyte segs m' (a + Z.of_nat k) = YP09.mbyte segs m (a + Z.of_nat k)).
  { unfold YP09.mbyte. rewrite (Hm (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|].
    change (Z_to_bv 64 (a + Z.of_nat k)) with (wa (a + Z.of_nat k)). rewrite wa_unsigned by exact Hr. exact Hx. }
  rewrite E. exact (Hv k Hk).
Qed.

Lemma bytes_at_addr : forall m a b bs, bytes_at segs m a bs -> a = b -> bytes_at segs m b bs.
Proof. intros m a b bs H <-. exact H. Qed.

Lemma wr_at_sub : forall m a n b k, wr_at segs m a n -> a <= b -> b + k <= a + n -> 0 <= k -> wr_at segs m b k.
Proof.
  intros m a n b k (H0 & H1 & H) Hb Hk Hk0. split; [lia|]. split; [lia|].
  intros i Hi. replace (b + i) with (a + (b - a + i)) by lia. apply H. lia.
Qed.

(* cells as one byte fact per cell, at its own address *)
Fixpoint cells_each (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
  match cs with
  | [] => 0 <= A <= 2 ^ 64
  | c :: cs' => cell_wf c /\ bytes_at segs m A (cbytes c) /\ cells_each m (A + Z.of_nat (csize c)) cs'
  end.

Lemma cells_each_of : forall cs m A, cells_at segs m A cs -> cells_each m A cs.
Proof.
  induction cs as [|c cs IH]; intros m A [Hwf Hb]; cbn [cells_each].
  - destruct Hb as (H0 & H1 & _). cbn [cells_bytes length Z.of_nat] in H1. lia.
  - cbn [cells_wf cells_bytes] in Hwf, Hb. destruct Hwf as [Hc Hcs].
    apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2].
    rewrite cbytes_length in Hb2 by exact Hc.
    split; [exact Hc|]. split; [exact Hb1|]. apply IH. split; [exact Hcs | exact Hb2].
Qed.

Lemma cells_of_each : forall cs m A, cells_each m A cs -> cells_at segs m A cs.
Proof.
  induction cs as [|c cs IH]; intros m A H; cbn [cells_each] in H.
  - split; [exact I|]. apply bytes_at_nil. lia.
  - destruct H as (Hc & Hb & Hr). destruct (IH _ _ Hr) as [Hwf Hb2].
    split; [cbn [cells_wf]; split; assumption|]. cbn [cells_bytes]. apply bytes_at_app. split; [exact Hb|].
    rewrite cbytes_length by exact Hc. exact Hb2.
Qed.

End G.

Lemma le4_wz : forall v, le4 (wz v) = Z_to_le_bytes 4 v.
Proof.
  intros v. unfold le4, wz. rewrite Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64).
  apply Z_to_le_bytes_mod. lia.
Qed.

Lemma le8_wz : forall v, le8 (wz v) = Z_to_le_bytes 8 v.
Proof.
  intros v. unfold le8, word_to_le_bytes, wz. rewrite Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64).
  apply Z_to_le_bytes_mod. lia.
Qed.

(* ==========================================================================
   2. In link's image a writable byte reads as some byte
   ========================================================================== *)

Lemma find_segment_in : forall l a n sg, find_segment l a n = Some sg -> In sg l.
Proof.
  induction l as [|s l IH]; intros a n sg H; cbn in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c end.
  - injection H as <-. left. reflexivity.
  - right. exact (IH a n sg H).
Qed.

(* the image's segments: every writable one is readable (computed on rsegs) *)
Lemma rsegs_wr_rd : forall sg, In sg rsegs -> seg_writable sg = true -> seg_readable sg = true.
Proof.
  intros sg Hin W.
  assert (C : forallb (fun s => implb (seg_writable s) (seg_readable s)) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C sg Hin). rewrite W in C. exact C.
Qed.

Lemma wv_rd : forall m x, wview rsegs m x <> None -> exists b, mrd rsegs m x = Some b.
Proof.
  intros m x. unfold wview.
  change (mrd rsegs m x) with (match m x with Some b => Some b | None =>
    match memory_read rsegs x 1%N with Some (b :: _) => Some b | _ => None end end).
  destruct (m x) as [b|]; [intros _; exists b; reflexivity|].
  destruct (find_segment rsegs (bv_unsigned x) 1) as [sg|] eqn:F; [|intros H; exfalso; apply H; reflexivity].
  cbv beta iota.
  destruct (seg_writable sg) eqn:W; [|intros H; exfalso; apply H; reflexivity].
  cbv beta iota.
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned x - Z.of_N (seg_base sg)))) as [b|] eqn:S;
    [|intros H; exfalso; apply H; reflexivity].
  intros _. exists b. unfold memory_read. change (Z.of_N 1) with 1. rewrite F.
  cbv beta iota zeta. rewrite (rsegs_wr_rd sg (find_segment_in _ _ _ _ F) W).
  cbv beta iota. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite S. reflexivity.
Qed.

Lemma wr_bytes : forall m a n, wr_at rsegs m a n -> 0 <= n ->
  exists bs, length bs = Z.to_nat n /\ bytes_at rsegs m a bs.
Proof.
  intros m a n (H0 & H1 & H) Hn.
  assert (G : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\
            forall i, (i < k)%nat -> mrd rsegs m (wa (a + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (wv_rd m (wa (a + Z.of_nat k)) (H (Z.of_nat k) ltac:(lia))) as (b & Hb).
      exists (bs ++ [b]). split. { rewrite length_app; cbn [length]; lia. }
      intros i Hi. destruct (Nat.eqb_spec i k).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G (Z.to_nat n) ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [rewrite Hlen; lia|]. intros i Hi. apply Hbs. lia.
Qed.

(* ==========================================================================
   3. The two statements
   ========================================================================== *)

Ltac conj_split := repeat match goal with |- _ /\ _ => split end.

Ltac close_bytes := match goal with
  | H : bytes_at ?s ?m ?a ?bs |- bytes_at ?s ?m ?b ?bs => apply (bytes_at_addr s m a b bs H); lia
  end.

Ltac vm_bytes H := eapply bytes_at_addr; [apply val_mem_le; [exact H | lia | lia] | lia].

Theorem mf_cells_of_k : mf_cells_of_k_stmt.
Proof.
  unfold mf_cells_of_k_stmt.
  intros m f k fl om wend wpos wbase pos len pb Hk Hd Hpb Hlen.
  pose proof (memfile_k_range m f k Hk) as Hkr.
  destruct Hk as (Hat & Hwin & Hwr & _ & _).
  destruct Hat as (Hf0 & Hf1 & Hf16 & Hst & Hfl & Hom & Hw & _).
  unfold MemFile.memfile_static, MemFile.memfile_flags, MemFile.memfile_omode, MemFile.memfile_window
    in Hst, Hfl, Hom, Hw.
  change (ms_segs YH02.src0_msyms) with rsegs in Hst, Hfl, Hom, Hw.
  destruct Hst as (_ & _ & _ & _ & _ & Hbuf & Hbsz & _ & _ & _ & _ & _ & H140 & H144 & _).
  destruct Hw as (H8 & H16 & _).
  destruct Hd as (Rfl & Rom & Rwe & Rwp & Rwb & _ & _ & Dfl & Dom & Dwe & Dwp & Dwb & _ & _).
  unfold mf_fld in Dfl, Dom, Dwe, Dwp, Dwb, Hwin.
  unfold mf_pend_bytes in Hpb.
  assert (Hf2 : f + MemFile.MF_BLOCK <= 2 ^ 64 - 8).
  { pose proof (Z.div_mod f 16 ltac:(lia)) as Hq. rewrite Hf16 in Hq. unfold MemFile.MF_BLOCK in *. lia. }
  unfold MemFile.MF_BLOCK, MemFile.MF_BUF, MemFile.MF_BUFSIZ in *.
  (* the bytes of each value cell, from its field fact *)
  assert (B0 : bytes_at rsegs m f (le4 (wz fl))) by (rewrite le4_wz; vm_bytes Dfl).
  assert (B8 : bytes_at rsegs m (f + 8) (le8 (wz 0))) by (rewrite le8_wz; vm_bytes H8).
  assert (B16 : bytes_at rsegs m (f + 16) (le8 (wz 0))) by (rewrite le8_wz; vm_bytes H16).
  assert (B32 : bytes_at rsegs m (f + 32) (le8 (wz wend))) by (rewrite le8_wz; vm_bytes Dwe).
  assert (B40 : bytes_at rsegs m (f + 40) (le8 (wz wpos))) by (rewrite le8_wz; vm_bytes Dwp).
  assert (B56 : bytes_at rsegs m (f + 56) (le8 (wz wbase))) by (rewrite le8_wz; vm_bytes Dwb).
  assert (B88 : bytes_at rsegs m (f + 88) (le8 (wz (f + 280)))) by (rewrite le8_wz; vm_bytes Hbuf).
  assert (B96 : bytes_at rsegs m (f + 96) (le8 (wz 1024))) by (rewrite le8_wz; vm_bytes Hbsz).
  assert (B136 : bytes_at rsegs m (f + 136) (le4 (wz om))) by (rewrite le4_wz; vm_bytes Dom).
  assert (B140 : bytes_at rsegs m (f + 140) (le4 (wz (-1)))).
  { rewrite le4_wz. rewrite <- (Z_to_le_bytes_mod 4 (-1) 32) by lia.
    change ((-1) mod 2 ^ 32) with YI14.U32M1. vm_bytes H140. }
  assert (B144 : bytes_at rsegs m (f + 144) (le4 (wz YI14.U32M1))) by (rewrite le4_wz; vm_bytes H144).
  (* the bytes of each CB piece: whatever is there *)
  destruct (wr_bytes m (f + 4) 4 ltac:(eapply wr_at_sub; [exact Hwr | lia | lia | lia]) ltac:(lia))
    as (jp & Ljp & Bjp).
  destruct (wr_bytes m (f + 24) 8 ltac:(eapply wr_at_sub; [exact Hwr | lia | lia | lia]) ltac:(lia))
    as (jc & Ljc & Bjc).
  destruct (wr_bytes m (f + 48) 8 ltac:(eapply wr_at_sub; [exact Hwr | lia | lia | lia]) ltac:(lia))
    as (j48 & Lj48 & Bj48).
  destruct (wr_bytes m (f + 64) 24 ltac:(eapply wr_at_sub; [exact Hwr | lia | lia | lia]) ltac:(lia))
    as (j64 & Lj64 & Bj64).
  destruct (wr_bytes m (f + 104) 32 ltac:(eapply wr_at_sub; [exact Hwr | lia | lia | lia]) ltac:(lia))
    as (j104 & Lj104 & Bj104).
  destruct (wr_bytes m (f + 148) 84 ltac:(eapply wr_at_sub; [exact Hwr | lia | lia | lia]) ltac:(lia))
    as (jx & Ljx & Bjx).
  destruct (wr_bytes m (f + 280 + k) (1024 - k) ltac:(eapply wr_at_sub; [exact Hwr | lia | lia | lia]) ltac:(lia))
    as (bjunk & Lbj & Bbj).
  exists jp, jc, j48, j64, j104, jx, bjunk.
  split.
  { split.
    - apply cells_of_each. cbn [mf_file_l cells_each cell_wf cbytes csize].
      conj_split; first [exact I | close_bytes | lia].
    - cbn [mf_file_l cells_size csize]. eapply wr_at_sub; [exact Hwr | lia | lia | lia]. }
  split.
  { split.
    - apply cells_of_each. cbn [cells_each cell_wf cbytes csize].
      conj_split; first [reflexivity | close_bytes | lia].
    - cbn [cells_size csize]. eapply wr_at_sub; [exact Hwr | lia | lia | lia]. }
  split; [lia|].
  split.
  { destruct Hwin as [(Hk0 & W1 & W2 & W3) | (Hk1 & W1 & W2 & W3)].
    - left. split; [|exact Hk0]. apply (val_mem_det8 rsegs m (f + 32)); [exact Dwe | exact W1 | lia | lia].
    - right. split; [|split].
      + apply (val_mem_det8 rsegs m (f + 32)); [exact Dwe | exact W1 | lia | lia].
      + apply (val_mem_det8 rsegs m (f + 40)); [exact Dwp | exact W2 | lia | lia].
      + apply (val_mem_det8 rsegs m (f + 56)); [exact Dwb | exact W3 | lia | lia]. }
  split.
  { unfold MemFile.F_NORD, MemFile.F_ERR in Hfl. destruct Hfl as [H|H].
    - assert (E : fl = 4) by (apply (val_mem_det4 rsegs m (f + 0)); [exact Dfl | exact H | lia | lia]).
      subst fl. reflexivity.
    - assert (E : fl = 4 + 32) by (apply (val_mem_det4 rsegs m (f + 0)); [exact Dfl | exact H | lia | lia]).
      subst fl. reflexivity. }
  destruct Hom as [H|H]; [left|right];
    (apply (val_mem_det4 rsegs m (f + 136)); [exact Dom | exact H | lia | try unfold YI14.U32M1; lia]).
Qed.

Ltac move_fld HO Hmu :=
  match goal with
  | H : YI04.val_mem rsegs ?m ?a ?n ?v |- YI04.val_mem rsegs ?m' ?a ?n ?v =>
    first [
      match goal with
      | C : bytes_at rsegs m ?A ?bs, C' : bytes_at rsegs m' ?A ?bs |- _ =>
          apply (val_mem_move rsegs m m' a n v A bs H C C'); rewrite ?length_le8, ?length_le4; lia
      end
    | apply (val_mem_munch rsegs _ m m' a n v H Hmu); intros x Hx; apply HO;
      unfold MemFile.MF_COOKIE, MemFile.MF_ZEROED in *; lia ]
  end.

Ltac from_cell := apply le_val_mem; first [rewrite <- le8_wz | rewrite <- le4_wz]; close_bytes.

Theorem mf_post_of_cells : mf_post_of_cells_stmt.
Proof.
  unfold mf_post_of_cells_stmt.
  intros m m' f k fl om wend wpos wbase pos len lo sp pb T jp jc j48 j64 j104 jx bj
    Hk Hd Hlen Hc Hmu Hlo Hf63 Hmono Hc' Hb' Hfit.
  unfold pf_file_post.
  destruct Hk as (Hat & _ & Hwr & Hws & Hpl).
  destruct Hat as (Hf0 & Hf1 & Hf16 & Hst & Hfl & Hom & Hw & Hck).
  unfold MemFile.memfile_static, MemFile.memfile_flags, MemFile.memfile_omode, MemFile.memfile_window,
    MemFile.memfile_cookie in Hst, Hfl, Hom, Hw, Hck.
  change (ms_segs YH02.src0_msyms) with rsegs in Hst, Hfl, Hom, Hw, Hck.
  destruct Hd as (Rfl & Rom & Rwe & Rwp & Rwb & Rpos & Rlen & Dfl & Dom & Dwe & Dwp & Dwb & Dpos & Dlen).
  unfold mf_fld in Dfl, Dom, Dwe, Dwp, Dwb, Dpos, Dlen.
  (* the cells before and after, one byte fact each *)
  destruct Hc as [Hc _]. apply cells_each_of in Hc. cbn [mf_file_l cells_each cell_wf cbytes csize] in Hc.
  destruct Hc as (_ & C0 & Ljp & Cjp & _ & C8 & _ & C16 & Ljc & Cjc & _ & C32 & _ & C40 & Lj48 & Cj48 & _ & C56 &
    Lj64 & Cj64 & _ & C88 & _ & C96 & Lj104 & Cj104 & _ & C136 & _ & C140 & _ & C144 & Ljx & Cjx & _).
  destruct Hc' as [Hc' _]. apply cells_each_of in Hc'. cbn [mf_file_l cells_each cell_wf cbytes csize] in Hc'.
  destruct Hc' as (_ & C0' & _ & Cjp' & _ & C8' & _ & C16' & _ & Cjc' & _ & C32' & _ & C40' & _ & Cj48' & _ & C56' &
    _ & Cj64' & _ & C88' & _ & C96' & _ & Cj104' & _ & C136' & _ & C140' & _ & C144' & _ & Cjx' & _).
  clear C32 C40 C56 C136.
  destruct Hb' as [Hb' _]. apply cells_each_of in Hb'. cbn [cells_each cell_wf cbytes csize] in Hb'.
  destruct Hb' as (_ & Hpb' & _).
  set (om' := if wend =? 0 then YI14.U32M1 else om) in *.
  (* the cookie and the bytes after it are outside the three ranges the call wrote *)
  assert (HO : forall x, f + MemFile.MF_COOKIE <= x < f + MemFile.MF_ZEROED ->
      0 <= x < 2 ^ 64 /\ outside [(lo, sp); (f, f + 232); (f + MemFile.MF_BUF, f + MemFile.MF_BLOCK)] x).
  { intros x Hx. unfold MemFile.MF_COOKIE, MemFile.MF_ZEROED, MemFile.MF_BUF, MemFile.MF_BLOCK in *.
    split; [lia|]. cbn [outside]. repeat split; lia. }
  (* the new orientation *)
  assert (Hom' : om' = 0 \/ om' = YI14.U32M1).
  { unfold om'. destruct (wend =? 0); [right; reflexivity|].
    destruct Hom as [H|H]; [left|right];
      (apply (val_mem_det4 rsegs m (f + 136)); [exact Dom | exact H | lia | try unfold YI14.U32M1; lia]). }
  assert (V136 : YI04.val_mem rsegs m' (f + 136) 4 om') by from_cell.
  assert (Hk0 : 0 <= k) by lia.
  (* the window, active with k + |T| pending *)
  assert (Hwin' : mf_win m' f (k + Z.of_nat (length T))).
  { unfold mf_win, mf_fld. right. split; [unfold MemFile.MF_BUFSIZ in *; lia|].
    replace (f + MemFile.MF_BUF + (k + Z.of_nat (length T))) with (f + MemFile.MF_BUF + k + Z.of_nat (length T))
      by lia.
    split; [from_cell|]. split; [from_cell | from_cell]. }
  (* the FILE as memfile_at states it *)
  assert (Hat' : MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m' f).
  { unfold MemFile.memfile_at, MemFile.memfile_static, MemFile.memfile_flags, MemFile.memfile_omode,
      MemFile.memfile_window, MemFile.memfile_cookie.
    change (ms_segs YH02.src0_msyms) with rsegs.
    destruct Hst as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 &
      S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27).
    destruct Hw as (W8 & W16 & _).
    refine (conj Hf0 (conj Hf1 (conj Hf16 (conj _ (conj _ (conj _ (conj _ _))))))).
    - conj_split; move_fld HO Hmu.
    - destruct Hfl as [H|H]; [left|right]; move_fld HO Hmu.
    - destruct Hom' as [E|E]; [left|right]; rewrite E in V136; exact V136.
    - split; [move_fld HO Hmu|]. split; [move_fld HO Hmu|]. right. exists (k + Z.of_nat (length T)).
      split; [unfold MemFile.MF_BUFSIZ in *; lia|].
      replace (f + MemFile.MF_BUF + (k + Z.of_nat (length T))) with (f + MemFile.MF_BUF + k + Z.of_nat (length T))
        by lia.
      split; [from_cell|]. split; [from_cell | from_cell].
    - destruct Hck as (p0 & l0 & Hp0 & Hl0 & K1 & K2). exists p0, l0.
      split; [exact Hp0|]. split; [exact Hl0|]. split; move_fld HO Hmu. }
  split; [|split].
  - unfold memfile_k. split; [exact Hat'|]. split; [exact Hwin'|].
    split; [exact (wr_at_transport rsegs m m' f MemFile.MF_BLOCK Hwr Hmono)|].
    split; [exact (wr_at_transport rsegs m m' A_G_SAID SAID_SIZE Hws Hmono) | exact Hpl].
  - unfold mf_dyn, mf_fld.
    refine (conj Rfl (conj _ (conj _ (conj _ (conj _ (conj Rpos (conj Rlen _))))))).
    + destruct Hom' as [E|E]; rewrite E; [lia | unfold YI14.U32M1; lia].
    + unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *. lia.
    + unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *. lia.
    + unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *. lia.
    + conj_split; first [exact V136 | from_cell | move_fld HO Hmu].
  - unfold mf_pend_bytes. exact Hpb'.
Qed.
