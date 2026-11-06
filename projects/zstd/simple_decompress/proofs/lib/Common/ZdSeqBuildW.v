(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Mem.
Variable segs : list Segment.

Lemma u8arr_readn : forall m A bs (i : Z) (k : nat) a,
  u8arr segs m A bs -> 0 <= i -> (Z.to_nat i + k <= length bs)%nat -> a = wa (A + i) ->
  ov_read_bytes segs m a k = Some (firstn k (skipn (Z.to_nat i) bs)).
Proof. intros m A bs i k a [Hb _] Hi Hk ->. apply bytes_at_read; assumption. Qed.

Lemma u8arr_storen_ok : forall m A bs (i : Z) (k : nat) a,
  u8arr segs m A bs -> 0 <= i -> i + Z.of_nat k <= Z.of_nat (length bs) -> a = wa (A + i) ->
  store_ok segs m a k = true.
Proof. intros m A bs i k a [_ Hw] Hi Hk ->. eapply wr_at_store_ok; eauto. Qed.

Lemma u8arr_writen : forall m A bs (i : Z) xs,
  u8arr segs m A bs -> 0 <= i -> (Z.to_nat i + length xs <= length bs)%nat ->
  u8arr segs (write_to_mem m (wa (A + i)) xs) A (upd_bytes bs (Z.to_nat i) xs).
Proof.
  intros m A bs i xs [Hb Hw] Hi Hk. split.
  - apply bytes_at_write_inside; assumption.
  - rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma u8arr_app : forall m A b1 b2,
  u8arr segs m A (b1 ++ b2) <-> u8arr segs m A b1 /\ u8arr segs m (A + Z.of_nat (length b1)) b2.
Proof.
  intros m A b1 b2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add. split.
  - intros ((H1 & H2) & (W0 & W1 & W)). split; (split; [assumption|]).
    + split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (length b1) + i) with (A + (Z.of_nat (length b1) + i)) by lia. apply W. lia.
  - intros ((H1 & (W0 & W1 & W)) & (H2 & (V0 & V1 & V))). split; [split; assumption|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (length b1))) as [L|L]; [apply W; lia|].
    replace (A + i) with (A + Z.of_nat (length b1) + (i - Z.of_nat (length b1))) by lia. apply V. lia.
Qed.
End Mem.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma upd_bytes_app_r : forall (P R xs : list byte) k,
  upd_bytes (P ++ R) (length P + k) xs = P ++ upd_bytes R k xs.
Proof.
  intros P R xs k. unfold upd_bytes.
  rewrite firstn_app, firstn_all2 by lia. replace (length P + k - length P)%nat with k by lia.
  rewrite <- app_assoc. f_equal. f_equal. f_equal.
  rewrite skipn_app, skipn_all2 by lia. cbn [app]. f_equal. lia.
Qed.
Lemma upd_bytes_app_l : forall (M Q xs : list byte) k, (k + length xs <= length M)%nat ->
  upd_bytes (M ++ Q) k xs = upd_bytes M k xs ++ Q.
Proof.
  intros M Q xs k H. unfold upd_bytes.
  rewrite firstn_app. replace (k - length M)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
  rewrite skipn_app. replace (k + length xs - length M)%nat with 0%nat by lia. rewrite skipn_O.
  rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le1_Z : forall x v, x mod 2^8 = v mod 2^8 -> le1 (Z_to_bv 64 x) = [Z_to_bv 8 v].
Proof. intros x v E. rewrite le1_lit. f_equal. apply Z_to_bv8_mod. exact E. Qed.
Lemma le2_Z : forall x v, x mod 2^16 = v mod 2^16 -> le2 (Z_to_bv 64 x) = map (Z_to_bv 8) (zle2 v).
Proof.
  intros x v E. unfold le2, zle2. cbn [Z_to_le_bytes map]. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256 in *. change (2^16) with 65536 in *.
  f_equal; [|f_equal]; apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; lia.
Qed.
Lemma le4_Z : forall x v, x mod 2^32 = v mod 2^32 -> le4 (Z_to_bv 64 x) = map (Z_to_bv 8) (zle4 v).
Proof.
  intros x v E. unfold le4, zle4. cbn [Z_to_le_bytes map]. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia. cbn [Z.add Pos.add Pos.succ].
  change (2^8) with 256 in *. change (2^16) with 65536 in *. change (2^24) with 16777216 in *. change (2^32) with 4294967296 in *.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]]; apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cellsB (cells : list seqsym) : list byte := map (Z_to_bv 8) (flat_map seqsym_bytes cells).
Definition cellB (c : seqsym) : list byte := map (Z_to_bv 8) (seqsym_bytes c).

Lemma cellB_length c : length (cellB c) = 8%nat.
Proof. reflexivity. Qed.
Lemma cellsB_app a b : cellsB (a ++ b) = cellsB a ++ cellsB b.
Proof. unfold cellsB. rewrite flat_map_app, map_app. reflexivity. Qed.
Lemma cellsB_cons c l : cellsB (c :: l) = cellB c ++ cellsB l.
Proof. unfold cellsB, cellB. cbn [flat_map]. rewrite map_app. reflexivity. Qed.
Lemma cellsB_length cells : length (cellsB cells) = (8 * length cells)%nat.
Proof. induction cells as [|c l IH]; [reflexivity|]. rewrite cellsB_cons, length_app, IH, cellB_length. cbn [length]. lia. Qed.

Lemma cells_split : forall (cells : list seqsym) u, 0 <= u < FseNCount.Zlength cells ->
  exists pre post, cells = pre ++ cell_nth cells u :: post /\ length pre = Z.to_nat u.
Proof.
  intros cells u Hu. unfold FseNCount.Zlength in Hu. unfold cell_nth.
  destruct (nth_split cells ss0 (n := Z.to_nat u) ltac:(lia)) as (pre & post & E & L).
  exists pre, post. split; [exact E| exact L].
Qed.
Lemma set_cell_split : forall pre c post c' u, length pre = Z.to_nat u -> 0 <= u ->
  set_cell u c' (pre ++ c :: post) = pre ++ c' :: post.
Proof.
  intros pre c post c' u L Hu. unfold set_cell. destruct (Z.ltb_spec u 0); [lia|]. rewrite <- L. clear L Hu H.
  induction pre as [|p pre IH]; cbn [length app set_cell_nat]; [reflexivity| rewrite IH; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma cellsB_upd : forall cells u c' (off : nat) xs, 0 <= u < FseNCount.Zlength cells -> (off + length xs <= 8)%nat ->
  upd_bytes (cellB (cell_nth cells u)) off xs = cellB c' ->
  upd_bytes (cellsB cells) (Z.to_nat (8 * u) + off) xs = cellsB (set_cell u c' cells).
Proof.
  intros cells u c' off xs Hu Hoff E.
  destruct (cells_split cells u Hu) as (pre & post & EC & L).
  rewrite EC at 1. rewrite EC at 2. rewrite (set_cell_split pre _ post c' u L ltac:(lia)).
  rewrite !cellsB_app, !cellsB_cons.
  replace (Z.to_nat (8 * u)) with (length (cellsB pre)) by (rewrite cellsB_length; lia).
  rewrite upd_bytes_app_r, upd_bytes_app_l by (rewrite cellB_length; exact Hoff). rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Definition with_next (c : seqsym) (v : Z) : seqsym := mkSS v (ss_nbAdd c) (ss_nbBits c) (ss_base c).
Definition with_nbAdd (c : seqsym) (v : Z) : seqsym := mkSS (ss_next c) v (ss_nbBits c) (ss_base c).
Definition with_nbBits (c : seqsym) (v : Z) : seqsym := mkSS (ss_next c) (ss_nbAdd c) v (ss_base c).
Definition with_base (c : seqsym) (v : Z) : seqsym := mkSS (ss_next c) (ss_nbAdd c) (ss_nbBits c) v.

Lemma cellsB_store_base : forall cells u x v, 0 <= u < FseNCount.Zlength cells -> x mod 2^32 = v mod 2^32 ->
  upd_bytes (cellsB cells) (Z.to_nat (8 * u + 4)) (le4 (Z_to_bv 64 x)) = cellsB (set_cell u (with_base (cell_nth cells u) v) cells).
Proof.
  intros cells u x v Hu E. replace (Z.to_nat (8 * u + 4)) with (Z.to_nat (8 * u) + 4)%nat by lia.
  apply cellsB_upd; [exact Hu| rewrite length_le4; lia|]. rewrite (le4_Z x v E). reflexivity.
Qed.
Lemma cellsB_store_next : forall cells u x v, 0 <= u < FseNCount.Zlength cells -> x mod 2^16 = v mod 2^16 ->
  upd_bytes (cellsB cells) (Z.to_nat (8 * u + 0)) (le2 (Z_to_bv 64 x)) = cellsB (set_cell u (with_next (cell_nth cells u) v) cells).
Proof.
  intros cells u x v Hu E. replace (Z.to_nat (8 * u + 0)) with (Z.to_nat (8 * u) + 0)%nat at 1 by lia.
  apply cellsB_upd; [exact Hu| rewrite length_le2; lia|]. rewrite (le2_Z x v E). reflexivity.
Qed.
Lemma cellsB_store_nbAdd : forall cells u x v, 0 <= u < FseNCount.Zlength cells -> x mod 2^8 = v mod 2^8 ->
  upd_bytes (cellsB cells) (Z.to_nat (8 * u + 2)) (le1 (Z_to_bv 64 x)) = cellsB (set_cell u (with_nbAdd (cell_nth cells u) v) cells).
Proof.
  intros cells u x v Hu E. replace (Z.to_nat (8 * u + 2)) with (Z.to_nat (8 * u) + 2)%nat by lia.
  apply cellsB_upd; [exact Hu| rewrite length_le1; lia|]. rewrite (le1_Z x v E). reflexivity.
Qed.
Lemma cellsB_store_nbBits : forall cells u x v, 0 <= u < FseNCount.Zlength cells -> x mod 2^8 = v mod 2^8 ->
  upd_bytes (cellsB cells) (Z.to_nat (8 * u + 3)) (le1 (Z_to_bv 64 x)) = cellsB (set_cell u (with_nbBits (cell_nth cells u) v) cells).
Proof.
  intros cells u x v Hu E. replace (Z.to_nat (8 * u + 3)) with (Z.to_nat (8 * u) + 3)%nat by lia.
  apply cellsB_upd; [exact Hu| rewrite length_le1; lia|]. rewrite (le1_Z x v E). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma set_base_as_set_cell : forall cells i v, 0 <= i < FseNCount.Zlength cells ->
  set_base i v cells = set_cell i (with_base (cell_nth cells i) v) cells.
Proof.
  intros cells i v Hi. destruct (cells_split cells i Hi) as (pre & post & EC & L).
  rewrite EC at 1. rewrite EC at 3. rewrite (set_cell_split pre _ post _ i L ltac:(lia)).
  unfold set_base. destruct (Z.ltb_spec i 0); [lia|]. rewrite <- L. clear.
  induction pre as [|p pre IH]; cbn [length app set_base_nat]; [reflexivity| rewrite IH; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma cellsB_read_base : forall cells u, 0 <= u < FseNCount.Zlength cells ->
  firstn 4 (skipn (Z.to_nat (8 * u + 4)) (cellsB cells)) = le4 (Z_to_bv 64 (ss_base (cell_nth cells u))).
Proof.
  intros cells u Hu. destruct (cells_split cells u Hu) as (pre & post & EC & L).
  rewrite EC at 1. rewrite cellsB_app, cellsB_cons.
  replace (Z.to_nat (8 * u + 4)) with (length (cellsB pre) + 4)%nat by (rewrite cellsB_length; lia).
  rewrite skipn_app, skipn_all2 by lia. cbn [app]. replace (length (cellsB pre) + 4 - length (cellsB pre))%nat with 4%nat by lia.
  rewrite (le4_Z _ (ss_base (cell_nth cells u)) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hdr_u8arr : forall segs m A a b, rw_cells segs m A [C4 a; C4 b] -> u8arr segs m A (le4 a ++ le4 b).
Proof.
  intros segs m A a b [[WF B] W]. split.
  - cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  - rewrite length_app, !length_le4. exact W.
Qed.

Lemma table_u8arr : forall segs m DT fast tl cells,
  rw_cells segs m DT [C4 (Z_to_bv 64 fast); C4 (Z_to_bv 64 tl)] -> u8arr segs m (DT + 8) (cellsB cells) ->
  u8arr segs m DT (map (Z_to_bv 8) (seq_table_bytes (mkST fast tl cells))).
Proof.
  intros segs m DT fast tl cells H C. unfold seq_table_bytes. cbn [st_fast st_log st_cells].
  rewrite !map_app, <- (le4_Z fast fast eq_refl), <- (le4_Z tl tl eq_refl), app_assoc.
  apply u8arr_app. split; [apply hdr_u8arr; exact H|].
  rewrite length_app, !length_le4. exact C.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le2_cong : forall x v, x mod 2^16 = v mod 2^16 -> le2 (Z_to_bv 64 x) = le2 (Z_to_bv 64 v).
Proof. intros x v E. rewrite (le2_Z x v E), (le2_Z v v eq_refl). reflexivity. Qed.

Lemma u16s_upd_Z : forall (l : list Z) (i : nat) x v, x mod 2^16 = v mod 2^16 ->
  u16s (upd (map (Z_to_bv 64) l) i (Z_to_bv 64 x)) = u16s (map (Z_to_bv 64) (upd_nat i v l)).
Proof.
  induction l as [|a l IH]; intros [|i] x v E; cbn -[le2]; try reflexivity.
  - rewrite (le2_cong x v E). reflexivity.
  - rewrite (IH i x v E). reflexivity.
Qed.

Lemma zx16_u : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zx16. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (2^16) with 65536. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition smear16 (x : Z) : Z :=
  let a := Z.lor x (x ≫ 1) in let b := Z.lor a (a ≫ 2) in let c := Z.lor b (b ≫ 4) in
  Z.lor c ((c ≪ 48 mod 18446744073709551616) ≫ 56).

Lemma smear16_ok : forall x, 1 <= x < 2048 -> smear16 x = 2^(Z.log2 x + 1) - 1.
Proof.
  assert (B : forallb (fun x => smear16 x =? 2^(Z.log2 x + 1) - 1) (zseq 2047 1) = true) by (vm_compute; reflexivity).
  intros x Hx. rewrite forallb_forall in B. apply Z.eqb_eq. apply B. apply zseq_In_iff. lia.
Qed.

(* [comment removed for export] *)
Lemma shl_hb_range : forall ns tl, 1 <= ns -> 0 <= tl -> Z.log2 ns <= tl ->
  2^tl <= ns * 2^(tl - Z.log2 ns) < 2 * 2^tl.
Proof.
  intros ns tl Hns Htl HL. set (L := Z.log2 ns) in *.
  assert (HL0 : 0 <= L) by apply Z.log2_nonneg.
  assert (B := Z.log2_spec ns ltac:(lia)). fold L in B. replace (Z.succ L) with (L + 1) in B by lia.
  rewrite Z.pow_add_r in B by lia. change (2^1) with 2 in B.
  assert (E : 2^tl = 2^L * 2^(tl - L)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  set (P := 2^(tl - L)) in *. assert (HP : 0 < P) by (apply Z.pow_pos_nonneg; lia).
  rewrite E. split.
  - apply Z.mul_le_mono_nonneg_r; lia.
  - replace (2 * (2^L * P)) with ((2^L * 2) * P) by ring. apply Z.mul_lt_mono_pos_r; lia.
Qed.

(* [comment removed for export] *)
Lemma set_cell_nat_twice : forall n (c c' : seqsym) l, set_cell_nat n c (set_cell_nat n c' l) = set_cell_nat n c l.
Proof. induction n as [|n IH]; intros c c' [|x l]; cbn [set_cell_nat]; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma set_cell_twice : forall u (c c' : seqsym) l, set_cell u c (set_cell u c' l) = set_cell u c l.
Proof. intros u c c' l. unfold set_cell. destruct (u <? 0); [reflexivity| apply set_cell_nat_twice]. Qed.

Lemma set_cell_fields : forall cells0 u0 n a b v, 0 <= u0 < FseNCount.Zlength cells0 ->
  let c1 := set_cell u0 (with_next (cell_nth cells0 u0) n) cells0 in
  let c2 := set_cell u0 (with_nbBits (cell_nth c1 u0) b) c1 in
  let c3 := set_cell u0 (with_nbAdd (cell_nth c2 u0) a) c2 in
  set_cell u0 (with_base (cell_nth c3 u0) v) c3 = set_cell u0 (mkSS n a b v) cells0.
Proof.
  intros cells0 u0 n a b v Hu c1 c2 c3.
  assert (L1 : FseNCount.Zlength c1 = FseNCount.Zlength cells0) by (unfold FseNCount.Zlength, c1; rewrite set_cell_length; reflexivity).
  assert (L2 : FseNCount.Zlength c2 = FseNCount.Zlength cells0) by (unfold FseNCount.Zlength, c2; rewrite set_cell_length; exact L1).
  assert (L3 : FseNCount.Zlength c3 = FseNCount.Zlength cells0) by (unfold FseNCount.Zlength, c3; rewrite set_cell_length; exact L2).
  assert (E1 : cell_nth c1 u0 = with_next (cell_nth cells0 u0) n) by (unfold c1; apply cell_nth_set_cell_same; lia).
  assert (E2 : cell_nth c2 u0 = with_nbBits (cell_nth c1 u0) b) by (unfold c2; apply cell_nth_set_cell_same; lia).
  assert (E3 : cell_nth c3 u0 = with_nbAdd (cell_nth c2 u0) a) by (unfold c3; apply cell_nth_set_cell_same; lia).
  rewrite E3, E2, E1. unfold c3, c2, c1. rewrite !set_cell_twice. reflexivity.
Qed.
