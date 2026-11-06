(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 392 of its 415 lines of code are new or changed and 299 lines of the source are left out. *)
(* proves diginet_frame_parse_holds, the walk of diginet_frame_parse in fuzz_transport.ubsan against its UBSan contract, with the memcpy, rd32 and diginet_sum16 contracts as hypotheses. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_frame_parse.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images *)
(* Walk of diginet_frame_parse (src/diginet_frame.c:60-91 at 835f336c) in fuzz_transport.ubsan,
   0x18034..0x1821c. The 64 bytes at f are one byte cell until the two memcpy calls; then they
   are the cells at f, f + 6 and f + 12 (uwp_split64), one for each store, and at the end the
   cells of parse_cells (uwp_final). The bytes 0..29 of the frame are a read-only cell list
   (uwp_ro), so each byte load reads one cell. No UBSan branch to 0x18218 is taken: the alignment
   check from f mod 8 = 0 (uwp_and7), the pointer-overflow checks from buf + len < 2^64 and
   len >= 30. The stack from lo to sp - 48 is the same after the walk because the walk writes
   only the 48 bytes of its frame and the 64 bytes at f (uwp_stk). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_frame_parse_c memcpy_c rd32_c
  diginet_sum16_c.
Import ListNotations.
Open Scope Z_scope.

(** * Lists and bytes *)

Lemma uwp_skipn_nth : forall (l : list byte) k, (k < length l)%nat -> skipn k l = nth k l (b8 0) :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros [|k] H; cbn [length skipn nth] in *; try lia; [reflexivity|].
  apply IH. lia.
Qed.

Lemma uwp_sub : forall m a (l : list byte) k n, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma uwp_bytes4 : forall m a (l : list byte) k, bytes_at rsegs m a l -> (k + 4 <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k)
    [nth k l (b8 0); nth (S k) l (b8 0); nth (S (S k)) l (b8 0); nth (S (S (S k))) l (b8 0)].
Proof.
  intros m a l k H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite (uwp_skipn_nth l k), (uwp_skipn_nth l (S k)), (uwp_skipn_nth l (S (S k))),
    (uwp_skipn_nth l (S (S (S k)))) in H by lia.
  change (bytes_at rsegs m (a + Z.of_nat k)
    ([nth k l (b8 0); nth (S k) l (b8 0); nth (S (S k)) l (b8 0); nth (S (S (S k))) l (b8 0)]
       ++ skipn (S (S (S (S k)))) l)) in H.
  apply bytes_at_app in H. exact (proj1 H).
Qed.

(* The bytes 0..29 of the frame as the cells the loads read. *)
Lemma uwp_ro : forall m buf b, bytes_at rsegs m buf b -> (30 <= length b)%nat ->
  ro_cells rsegs m buf
    [CB 6 (fr_dst b); CB 6 (fr_src b); C1 (nth 12 b (b8 0)); C1 (nth 13 b (b8 0)); C1 (nth 14 b (b8 0));
     C1 (nth 15 b (b8 0)); C1 (nth 16 b (b8 0)); C1 (nth 17 b (b8 0)); C1 (nth 18 b (b8 0));
     C1 (nth 19 b (b8 0)); C1 (nth 20 b (b8 0)); C1 (nth 21 b (b8 0)); C1 (nth 22 b (b8 0));
     C1 (nth 23 b (b8 0)); C1 (nth 24 b (b8 0)); C1 (nth 25 b (b8 0)); C1 (nth 26 b (b8 0));
     C1 (nth 27 b (b8 0)); C1 (nth 28 b (b8 0)); C1 (nth 29 b (b8 0))].
Proof.
  intros m buf b BB L.
  rewrite <- (firstn_skipn 30 b) in BB. apply bytes_at_app in BB. destruct BB as [BB _].
  do 30 (destruct b as [|? b]; [cbn [length] in L; lia|]).
  split.
  - cbn [cells_wf cell_wf fr_dst fr_src firstn skipn length]. repeat split.
  - cbn [cells_bytes cbytes firstn skipn app nth fr_dst fr_src] in BB |- *. exact BB.
Qed.

(** * Cells *)

Lemma uwp_wr_split : forall m A n1 n2, wr_at rsegs m A (n1 + n2) -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 (H1 & H2 & H) P1 P2. split.
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
Qed.

Lemma uwp_wr_join : forall m A n1 n2, wr_at rsegs m A n1 -> wr_at rsegs m (A + n1) n2 -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2).
Proof.
  intros m A n1 n2 (H1 & H2 & H) (G1 & G2 & G) P1 P2. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z.ltb_spec0 i n1); [apply H; lia|].
  replace (A + i) with (A + n1 + (i - n1)) by lia. apply G. lia.
Qed.

Lemma uwp_split2 : forall m A cs1 cs2 B, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A cs1 cs2 B [[Hwf Hb] Hw] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app, Nat2Z.inj_add in Hw.
  apply uwp_wr_split in Hw; [| lia | lia]. destruct Hw as [V1 V2].
  rewrite cells_bytes_length in B2 by exact W1.
  split; (split; [split|]); assumption.
Qed.

Lemma uwp_app2 : forall m A cs1 cs2 B, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 B [[W1 B1] V1] [[W2 B2] V2] ->.
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. apply uwp_wr_join; [exact V1 | exact V2 | lia | lia].
Qed.

Lemma uwp_conv : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] V] W' EB ES. split; [split|].
  - exact W'.
  - rewrite EB. exact B.
  - rewrite ES. exact V.
Qed.

(* The 64 bytes at f: the two MACs, then one byte cell for each field the walk stores. *)
Lemma uwp_split64 : forall m f fj, rw_cells rsegs m f [CB 64 fj] ->
  rw_cells rsegs m f [CB 6 (firstn 6 fj)] /\ rw_cells rsegs m (f + 6) [CB 6 (firstn 6 (skipn 6 fj))] /\
  rw_cells rsegs m (f + 12)
    [CB 2 (firstn 2 (skipn 12 fj)); CB 2 (firstn 2 (skipn 14 fj)); CB 2 (firstn 2 (skipn 16 fj));
     CB 2 (firstn 2 (skipn 18 fj)); CB 4 (firstn 4 (skipn 20 fj)); CB 4 (firstn 4 (skipn 24 fj));
     CB 2 (firstn 2 (skipn 28 fj)); CB 1 (firstn 1 (skipn 30 fj)); CB 1 (firstn 1 (skipn 31 fj));
     CB 8 (firstn 8 (skipn 32 fj)); CB 8 (firstn 8 (skipn 40 fj)); CB 8 (firstn 8 (skipn 48 fj));
     CB 2 (firstn 2 (skipn 56 fj)); CB 1 (firstn 1 (skipn 58 fj)); CB 5 (skipn 59 fj)].
Proof.
  intros m f fj H.
  assert (L : length fj = 64%nat) by (destruct H as [[[Hl _] _] _]; exact Hl).
  assert (R : rw_cells rsegs m f ([CB 6 (firstn 6 fj)] ++ [CB 6 (firstn 6 (skipn 6 fj))] ++
    [CB 2 (firstn 2 (skipn 12 fj)); CB 2 (firstn 2 (skipn 14 fj)); CB 2 (firstn 2 (skipn 16 fj));
     CB 2 (firstn 2 (skipn 18 fj)); CB 4 (firstn 4 (skipn 20 fj)); CB 4 (firstn 4 (skipn 24 fj));
     CB 2 (firstn 2 (skipn 28 fj)); CB 1 (firstn 1 (skipn 30 fj)); CB 1 (firstn 1 (skipn 31 fj));
     CB 8 (firstn 8 (skipn 32 fj)); CB 8 (firstn 8 (skipn 40 fj)); CB 8 (firstn 8 (skipn 48 fj));
     CB 2 (firstn 2 (skipn 56 fj)); CB 1 (firstn 1 (skipn 58 fj)); CB 5 (skipn 59 fj)])).
  { apply (uwp_conv _ _ _ _ H).
    - cbn [cells_wf cell_wf app]. rewrite ?length_firstn, ?length_skipn, ?L. repeat split.
    - clear H. do 64 (destruct fj as [|? fj]; [cbn [length] in L; lia|]).
      destruct fj; [reflexivity | cbn [length] in L; lia].
    - reflexivity. }
  destruct (uwp_split2 _ _ _ _ (f + 6) R ltac:(cbn; lia)) as [A0 R1].
  destruct (uwp_split2 _ _ _ _ (f + 12) R1 ltac:(cbn; lia)) as [A6 A12].
  tauto.
Qed.

Lemma uwp_le4_sx32 : forall z, 0 <= z < 2^32 -> le4 (sx32 (Z_to_bv 64 z)) = le4 (Z_to_bv 64 z).
Proof.
  intros z Hz. unfold le4, sx32. rewrite (unsigned_lit z) by lia. rewrite unsigned_lit_wrap.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 z mod 2^64) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 z 32) by lia.
  f_equal. change (bv_swrap 32 z) with ((z + 2^31) mod 2^32 - 2^31). Z.div_mod_to_equations. lia.
Qed.

(* The 64 bytes at f after a parse that answers 0. *)
Lemma uwp_final : forall m f buf b fj (w20 w24 : word),
  (30 <= length b)%nat -> length fj = 64%nat -> fr_ethertype b = 0x885f ->
  le4 w20 = le4 (Z_to_bv 64 (fr_send b)) -> le4 w24 = le4 (Z_to_bv 64 (fr_ack b)) ->
  rw_cells rsegs m f [CB 6 (fr_dst b)] -> rw_cells rsegs m (f + 6) [CB 6 (fr_src b)] ->
  rw_cells rsegs m (f + 12)
    [C2 (Z_to_bv 64 0x885f); CB 2 (firstn 2 (skipn 14 fj)); C2 (Z_to_bv 64 (fr_numbytes b));
     C2 (Z_to_bv 64 (fr_sum b)); C4 w20; C4 w24; C2 (Z_to_bv 64 (fr_retry b));
     C1 (nth 28 b (b8 0)); C1 (nth 29 b (b8 0)); C8 (Z_to_bv 64 (buf + 30)); C8 (Z_to_bv 64 (fr_body_len b));
     C8 (Z_to_bv 64 (fr_pad_len b)); C2 (Z_to_bv 64 (fr_body_sum b));
     C1 (b8 (if fr_sum b =? fr_body_sum b then 1 else 0)); CB 5 (skipn 59 fj)] ->
  rw_cells rsegs m f (parse_cells buf b fj).
Proof.
  intros m f buf b fj w20 w24 L30 Lfj ET E20 E24 A0 A6 A12.
  pose proof (uwp_app2 _ _ _ _ _ A6 A12 ltac:(cbn; lia)) as R1.
  pose proof (uwp_app2 _ _ _ _ _ A0 R1 ltac:(cbn; lia)) as R.
  apply (uwp_conv _ _ _ _ R).
  - unfold parse_cells. cbn [cells_wf cell_wf]. repeat split.
    all: unfold fr_dst, fr_src; rewrite ?length_firstn, ?length_skipn; lia.
  - unfold parse_cells. cbn [app cells_bytes cbytes]. rewrite ET, E20, E24.
    unfold fr_cmd, fr_ncmds, at8. rewrite !b8_bz. reflexivity.
  - reflexivity.
Qed.

(** * Stack *)

Definition uwp_hide (P : Prop) : Prop := P.

(* The stack below the frame after the walk: the walk wrote only its frame and the 64 bytes
   at f, and the bytes at f are there. *)
Lemma uwp_stk : forall m m' lo hi a0 a1 f bs, stk rsegs m lo hi -> hi <= a0 ->
  munch [(a0, a1); (f, f + 64)] m m' -> wmono rsegs m m' -> bytes_at rsegs m' f bs -> length bs = 64%nat ->
  stk rsegs m' lo hi.
Proof.
  intros m m' lo hi a0 a1 f bs (H1 & H2 & H) Ha MU WM B Hn. split; [lia|]. split; [lia|].
  intros x Hx. destruct (H x Hx) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct B as (Ba & Bl & Bn).
  destruct (Z.leb_spec f x) as [L1|L1]; [destruct (Z.ltb_spec x (f + 64)) as [L2|L2] |].
  - pose proof (Bn (Z.to_nat (x - f)) ltac:(lia)) as E. replace (f + Z.of_nat (Z.to_nat (x - f))) with x in E by lia.
    rewrite E. destruct (nth_error bs (Z.to_nat (x - f))) eqn:N; [eexists; reflexivity|].
    apply nth_error_None in N. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia | split; [lia | exact I]].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia | split; [lia | exact I]].
Qed.

Lemma uwp_rw_bytes64 : forall m A cs, rw_cells rsegs m A cs -> cells_size cs = 64%nat ->
  exists bs, bytes_at rsegs m A bs /\ length bs = 64%nat.
Proof.
  intros m A cs [[W B] _] S. exists (cells_bytes cs). split; [exact B|].
  rewrite cells_bytes_length by exact W. exact S.
Qed.

(** * Words *)

Lemma uwp_be16 : forall (l : list byte) i,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth i l (b8 0)))) 8)))
                    (bv_unsigned (zxb (nth (S i) l (b8 0)))))
  = Z_to_bv 64 (be16 l i).
Proof.
  intros l i. unfold be16, at8, zxb, bz.
  set (x := nth i l (b8 0)). set (y := nth (S i) l (b8 0)).
  pose proof (bz_range x) as Hx. pose proof (bz_range y) as Hy. unfold bz in Hx, Hy.
  rewrite (unsigned_lit (bv_unsigned x)) by lia. rewrite (unsigned_lit (bv_unsigned y)) by lia.
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned x) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia. f_equal. lia.
Qed.

Lemma uwp_and7 : forall f, 0 <= f -> f mod 8 = 0 -> Z.land f 7 = 0.
Proof. intros f H0 H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma uwp_lxor16 : forall x y, 0 <= x < 2^16 -> 0 <= y < 2^16 -> (Z.lxor x y <? 1) = (x =? y).
Proof.
  intros x y Hx Hy. destruct (Z.eqb_spec x y) as [E|E].
  - subst y. rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.ltb_ge. assert (Z.lxor x y <> 0) by (intros H; exact (E (proj1 (Z.lxor_eq_0_iff x y) H))).
    pose proof (proj2 (Z.lxor_nonneg x y) ltac:(split; lia)). lia.
Qed.

Lemma uwp_log2_16 : forall x, 0 <= x < 2^16 -> Z.log2 x < 16.
Proof.
  intros x Hx. destruct (Z.eq_dec x 0) as [->|N]; [cbn; lia|].
  apply (proj1 (Z.log2_lt_pow2 x 16 ltac:(lia))). lia.
Qed.

Lemma uwp_lxor_lt : forall x y, 0 <= x < 2^16 -> 0 <= y < 2^16 -> 0 <= Z.lxor x y < 2^16.
Proof.
  intros x y Hx Hy. pose proof (proj2 (Z.lxor_nonneg x y) ltac:(split; lia)) as P.
  split; [exact P|].
  destruct (Z.eq_dec (Z.lxor x y) 0) as [E|E]; [rewrite E; lia|].
  apply (proj2 (Z.log2_lt_pow2 (Z.lxor x y) 16 ltac:(lia))).
  pose proof (Z.log2_lxor x y ltac:(lia) ltac:(lia)) as L.
  pose proof (uwp_log2_16 x Hx). pose proof (uwp_log2_16 y Hy). lia.
Qed.

(* 0x181dc..0x181e4: f->sum (read back, lhu) against the answer of diginet_sum16. *)
Lemma uwp_summ : forall x y, 0 <= x < 2^16 -> 0 <= y < 2^16 ->
  v_sltiu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) (bv_unsigned (zx16 (Z_to_bv 64 y))))) 1 =
  zxb (b8 (if y =? x then 1 else 0)).
Proof.
  intros x y Hx Hy. unfold zx16.
  rewrite (unsigned_lit x), (unsigned_lit y) by lia.
  rewrite (Z.mod_small y) by lia. rewrite (unsigned_lit y) by lia.
  pose proof (uwp_lxor_lt x y Hx Hy) as L.
  unfold v_sltiu. rewrite (unsigned_lit (Z.lxor x y)) by lia. change (bv_wrap 64 1) with 1.
  rewrite (uwp_lxor16 x y Hx Hy). rewrite Z.eqb_sym. destruct (y =? x); reflexivity.
Qed.

(** * The code *)

Lemma uwp_code2 : forall b, (length b < 30)%nat -> fr_code b = -2.
Proof.
  intros b H. unfold fr_code. replace (length b <? 30)%nat with true by (symmetry; apply Nat.ltb_lt; exact H).
  reflexivity.
Qed.

Lemma uwp_code3 : forall b, (30 <= length b)%nat -> fr_ethertype b <> 0x885f -> fr_code b = -3.
Proof.
  intros b H E. unfold fr_code. replace (length b <? 30)%nat with false by (symmetry; apply Nat.ltb_ge; exact H).
  rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity.
Qed.

Lemma uwp_code4 : forall b, (30 <= length b)%nat -> fr_ethertype b = 0x885f ->
  fr_numbytes b < 16 \/ Z.of_nat (length b) - 14 < fr_numbytes b -> fr_code b = -4.
Proof.
  intros b H E N. unfold fr_code. replace (length b <? 30)%nat with false by (symmetry; apply Nat.ltb_ge; exact H).
  rewrite (proj2 (Z.eqb_eq _ _) E).
  replace ((fr_numbytes b <? 16) || (Z.of_nat (length b) - 14 <? fr_numbytes b)) with true; [reflexivity|].
  symmetry. apply orb_true_iff. destruct N; [left | right]; apply Z.ltb_lt; lia.
Qed.

Lemma uwp_code0 : forall b, (30 <= length b)%nat -> fr_ethertype b = 0x885f ->
  16 <= fr_numbytes b -> fr_numbytes b <= Z.of_nat (length b) - 14 -> fr_code b = 0.
Proof.
  intros b H E N1 N2. unfold fr_code.
  replace (length b <? 30)%nat with false by (symmetry; apply Nat.ltb_ge; exact H).
  rewrite (proj2 (Z.eqb_eq _ _) E).
  replace ((fr_numbytes b <? 16) || (Z.of_nat (length b) - 14 <? fr_numbytes b)) with false; [reflexivity|].
  symmetry. apply orb_false_iff. split; apply Z.ltb_ge; lia.
Qed.

(** * The walk *)

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.
Ltac curmem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(* post_call, with the callee's addresses Z_to_bv 64 a read back as a. *)
Ltac uwp_post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  rewrite ?unsigned_lit in PO by lia;
  change (Z.to_nat 6) with 6%nat in PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  destruct PO as [MIc PO];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac uwp_ret n := replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

(* An answer that is not 0: the epilogue has run; the 64 bytes at f are as before. *)
Ltac uwp_fail_end QQ FR ST sp code :=
  release_frame FR ST (bv_unsigned sp);
  apply evt_done; unfold QQ; cbv beta; rewrite code; cbn [Z.eqb];
  do 15 eexists; split; [reflexivity|];
  refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.

Theorem diginet_frame_parse_holds :
  memcpy_contract -> rd32_contract -> diginet_sum16_contract -> diginet_frame_parse_contract.
Proof.
  intros MEMCPY RD32 SUM16. unfold diginet_frame_parse_contract, DIGINET_FRAME_PARSE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf f lo b fj
    B0 BL FNZ FAL BB FJ DF ST LO DB DS MI.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (u64_range sp) as Rsp.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  pose proof (rw_cells_bound _ _ _ _ FJ) as FJb. cbn [cells_size csize Nat.add] in FJb.
  assert (Lfj : length fj = 64%nat) by (destruct FJ as [[[Hl _] _] _]; exact Hl).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (f, f + 64)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  assert (ST0 : uwp_hide (stk rsegs m lo (bv_unsigned sp + -48))) by exact ST.
  (* prologue; buf <> 0, f <> 0 *)
  do 10 step. br false.
  do 2 step. br false.
  (* len >= 30 *)
  do 3 step.
  destruct (Nat.ltb_spec (length b) 30) as [L30|L30].
  { br false. do 10 step. uwp_fail_end QQ FR ST sp (uwp_code2 b L30). }
  br true.
  pose proof (uwp_ro _ _ _ BB L30) as RO.
  (* 0x1807c, 0x18084: buf + 12, buf + 13 *)
  do 2 step. br false.
  do 2 step. br false.
  (* the EtherType *)
  do 7 step.
  rewrite (uwp_be16 b 12). change (be16 b 12) with (fr_ethertype b).
  pose proof (be16_range b 12) as ETR. change (be16 b 12) with (fr_ethertype b) in ETR.
  destruct (Z.eqb_spec (fr_ethertype b) 0x885f) as [ET|ET].
  2: { br true. do 9 step. uwp_fail_end QQ FR ST sp (uwp_code3 b L30 ET). }
  br false.
  (* 0x180a8, 0x180b4: buf + 14, h + 1 *)
  do 2 step. br false.
  do 3 step. br false.
  (* numbytes *)
  do 4 step.
  rewrite (uwp_be16 b 14). change (be16 b 14) with (fr_numbytes b).
  pose proof (be16_range b 14) as NBR. change (be16 b 14) with (fr_numbytes b) in NBR.
  do 3 step.
  destruct (Z.ltb_spec (fr_numbytes b) 16) as [N16|N16].
  { br true. do 8 step. uwp_fail_end QQ FR ST sp (uwp_code4 b L30 ET (or_introl N16)). }
  br false.
  do 2 step.
  destruct (Z.ltb_spec (Z.of_nat (length b) - 14) (fr_numbytes b)) as [NL|NL].
  { br true. do 8 step. uwp_fail_end QQ FR ST sp (uwp_code4 b L30 ET (or_intror NL)). }
  br false.
  (* 0x180e0: f & 7 *)
  do 2 step.
  rewrite ?(unsigned_lit f) by lia. rewrite (uwp_and7 f) by lia.
  br false.
  (* memcpy (f, buf, 6) *)
  do 4 step.
  destruct (uwp_split64 _ _ _ FJ) as (F0 & F6 & F12). clear FJ.
  curmem ltac:(fun mm => assert (DST : bytes_at rsegs mm buf (fr_dst b))
    by (pose proof (uwp_sub _ _ _ 0 6 BB ltac:(lia)) as H; rewrite Z.add_0_r in H; exact H)).
  curmem ltac:(fun mm => eapply evt_cut;
    [ eapply MEMCPY with (src := fr_dst b) (junk := firstn 6 fj) | uwp_post_call rsegs mm ]).
  1: { uns. exact DST. }
  1: { uns. unfold fr_dst. rewrite length_firstn. lia. }
  1: { uns. exact F0. }
  1: { uns. lia. }
  1: { eassumption. }
  (* 0x180f8: buf + 6 *)
  do 2 step. br false.
  (* memcpy (f + 6, buf + 6, 6) *)
  do 4 step.
  curmem ltac:(fun mm => assert (SRC : bytes_at rsegs mm (buf + 6) (fr_src b))
    by exact (uwp_sub _ _ _ 6 6 BB ltac:(lia))).
  curmem ltac:(fun mm => eapply evt_cut;
    [ eapply MEMCPY with (src := fr_src b) (junk := firstn 6 (skipn 6 fj)) | uwp_post_call rsegs mm ]).
  1: { uns. exact SRC. }
  1: { uns. unfold fr_src. rewrite length_firstn, length_skipn. lia. }
  1: { uns. exact F6. }
  1: { uns. lia. }
  1: { eassumption. }
  (* the EtherType and numbytes stores; 0x18120, 0x18128 *)
  do 6 step. br false.
  do 2 step. br false.
  (* sum *)
  do 4 step.
  rewrite (uwp_be16 b 16). change (be16 b 16) with (fr_sum b).
  do 3 step. br false.
  (* rd32 (buf + 18): send_counter *)
  do 2 step.
  curmem ltac:(fun mm => assert (B18 : bytes_at rsegs mm (buf + 18)
    [nth 18 b (b8 0); nth 19 b (b8 0); nth 20 b (b8 0); nth 21 b (b8 0)])
    by exact (uwp_bytes4 _ _ _ 18 BB ltac:(lia))).
  eapply evt_cut;
    [ eapply RD32 with (p := buf + 18) (l := [nth 18 b (b8 0); nth 19 b (b8 0); nth 20 b (b8 0); nth 21 b (b8 0)])
    | intros ms' (r1 & r2 & r3 & ->) ].
  1: reflexivity.
  1: exact B18.
  uwp_ret 0x18150. clear B18.
  do 3 step. br false.
  (* rd32 (buf + 22): ack_counter *)
  do 2 step.
  curmem ltac:(fun mm => assert (B22 : bytes_at rsegs mm (buf + 22)
    [nth 22 b (b8 0); nth 23 b (b8 0); nth 24 b (b8 0); nth 25 b (b8 0)])
    by exact (uwp_bytes4 _ _ _ 22 BB ltac:(lia))).
  eapply evt_cut;
    [ eapply RD32 with (p := buf + 22) (l := [nth 22 b (b8 0); nth 23 b (b8 0); nth 24 b (b8 0); nth 25 b (b8 0)])
    | intros ms' (r1' & r2' & r3' & ->) ].
  1: reflexivity.
  1: exact B22.
  uwp_ret 0x18164. clear B22.
  do 3 step. br false.
  do 2 step. br false.
  (* retry *)
  do 4 step.
  rewrite (uwp_be16 b 26). change (be16 b 26) with (fr_retry b).
  do 3 step. br false.
  (* cmd, ncmds; 0x181a0, 0x181b0 *)
  do 3 step. rewrite le1_zxb. mem_after_store. step. br false.
  do 3 step. rewrite le1_zxb. mem_after_store. step. br false.
  (* body, body_len, pad_len *)
  do 4 step.
  rewrite (unsigned_lit (Z.of_nat (length b))), (unsigned_lit (fr_numbytes b)) by lia.
  replace (Z.of_nat (length b) - fr_numbytes b + -14) with (fr_pad_len b) by (unfold fr_pad_len, fr_body_len; lia).
  change (fr_numbytes b + -16) with (fr_body_len b).
  do 3 step.
  (* diginet_sum16 (buf + 30, body_len) *)
  step.
  assert (BLEN : Z.of_nat (length (fr_body b)) = fr_body_len b).
  { unfold fr_body, fr_body_len. rewrite length_firstn, length_skipn. lia. }
  rewrite <- BLEN.
  curmem ltac:(fun mm => assert (BODY : bytes_at rsegs mm (buf + 30) (fr_body b))
    by exact (uwp_sub _ _ _ 30 (Z.to_nat (fr_body_len b)) BB ltac:(lia))).
  eapply evt_cut;
    [ eapply SUM16 with (p := buf + 30) (bb := fr_body b) | intros ms' (q1 & q2 & q3 & q4 & q5 & q6 & ->) ].
  1: lia.
  1: exact BODY.
  uwp_ret 0x181d4. clear BODY.
  rewrite lib_sum16_eq. change (sum16 (fr_body b)) with (fr_body_sum b).
  (* sum_matches *)
  pose proof (be16_range b 16) as SR. change (be16 b 16) with (fr_sum b) in SR.
  pose proof (sum16_range (fr_body b)) as BSR. change (sum16 (fr_body b)) with (fr_body_sum b) in BSR.
  do 5 step.
  rewrite (uwp_summ (fr_body_sum b) (fr_sum b) BSR SR).
  do 2 step. rewrite le1_zxb. mem_after_store.
  (* epilogue *)
  do 9 step.
  assert (C0 : fr_code b = 0) by (apply uwp_code0; lia).
  curmem ltac:(fun mm => assert (FIN : rw_cells rsegs mm f (parse_cells buf b fj))).
  { eapply uwp_final; try eassumption.
    - rewrite uwp_le4_sx32 by (apply be32_range). reflexivity.
    - rewrite uwp_le4_sx32 by (apply be32_range). reflexivity. }
  unfold uwp_hide in ST0.
  destruct (uwp_rw_bytes64 _ _ _ FIN eq_refl) as (fb & FB & FBL).
  curmem ltac:(fun mm => assert (ST : stk rsegs mm lo (bv_unsigned sp + -48))
    by (eapply uwp_stk; [exact ST0 | | exact MU | exact WM | exact FB | exact FBL]; lia)).
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold QQ. cbv beta. rewrite C0. cbn [Z.eqb].
  do 15 eexists. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
Qed.
