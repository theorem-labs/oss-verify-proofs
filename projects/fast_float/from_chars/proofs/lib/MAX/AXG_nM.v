(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS
                        AXF_eez AXG_ntfm AXG_ntfg AXG_nQ AXG_nD.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Steps.
Variables (L : layout) (EXC : list loc).
Hypothesis Hctx : ly_ctx L = 0x95ed8.

#[using="Hctx"] Lemma step_usage : forall s m k v a w, repr_x L s (bview SEGS m) EXC -> (k < 48)%nat -> length (st_usage s) = 48%nat ->
  a = 614568 + 8 * Z.of_nat k -> wa w = wa v ->
  repr_x L (set_usage (zupd (st_usage s) k v) s) (bview SEGS (wbytes m (wa a) (word_to_le_bytes 8 (wa w)))) EXC.
Proof. LiaFast.lf_pins (fun (Hctx : LiaFast.U) => LiaFast.u0).
  intros s m k v a w HR Hk Hl -> Ew. rewrite Ew.
  change (word_to_le_bytes 8 (wa v)) with (word_to_le_bytes (mc_w (usg_cell k v)) (wa (sval_num L (mc_val (usg_cell k v))))).
  apply (repr_x_wcell L s (set_usage (zupd (st_usage s) k v) s) m EXC (usg_cell k v) (614568 + 8 * Z.of_nat k) HR eq_refl eq_refl (RS_ctx_only L s (set_usage (zupd (st_usage s) k v) s) eq_refl eq_refl)).
  - intros c Hc. destruct (cov_ctx_only s (set_usage (zupd (st_usage s) k v) s) c eq_refl eq_refl Hc) as [H|H]; [left; exact H|].
    destruct (cov_usage s k v c ltac:(lia) H) as [H'|H']; [left; apply ctx_in_image; exact H' | right; exact H'].
  - pose proof (usg_cell_in (set_usage (zupd (st_usage s) k v) s) k Hk) as E. cbn [st_usage set_usage] in E.
    rewrite nth_zupd_same in E by lia. exact E.
  - intros z E. discriminate.
  - cbn. lia.
  - cbn [usg_cell mc_loc loc_addr]. rewrite Hctx. unfold CTX_usage. ring.
  - lia.
  - cbn. lia.
Qed.

#[using="Hctx"] Lemma step_seq : forall s m v a w, repr_x L s (bview SEGS m) EXC -> a = 615016 -> wa w = wa v ->
  repr_x L (set_seq v s) (bview SEGS (wbytes m (wa a) (word_to_le_bytes 1 (wa w)))) EXC.
Proof. LiaFast.lf_pins (fun (Hctx : LiaFast.U) => LiaFast.u0).
  intros s m v a w HR -> Ew. rewrite Ew.
  change (word_to_le_bytes 1 (wa v)) with (word_to_le_bytes (mc_w (seq_cell v)) (wa (sval_num L (mc_val (seq_cell v))))).
  apply (repr_x_wcell L s (set_seq v s) m EXC (seq_cell v) 615016 HR eq_refl eq_refl (RS_ctx_only L s (set_seq v s) eq_refl eq_refl)).
  - intros c Hc. destruct (cov_ctx_only s (set_seq v s) c eq_refl eq_refl Hc) as [H|H]; [left; exact H|].
    destruct (cov_seq s v c H) as [H'|H']; [left; apply ctx_in_image; exact H' | right; exact H'].
  - exact (seq_cell_in (set_seq v s)).
  - intros z E. discriminate.
  - cbn. lia.
  - cbn [seq_cell mc_loc loc_addr]. rewrite Hctx. reflexivity.
  - lia.
  - cbn. lia.
Qed.

#[using="Hctx"] Lemma step_unm1 : forall s m k v a w, repr_x L s (bview SEGS m) EXC -> (k < 32)%nat -> length (st_unmap_seq s) = 32%nat ->
  a = 614952 + Z.of_nat k -> wa w = wa v ->
  repr_x L (set_unmap_seq (zupd (st_unmap_seq s) k v) s) (bview SEGS (wbytes m (wa a) (word_to_le_bytes 1 (wa w)))) EXC.
Proof. LiaFast.lf_pins (fun (Hctx : LiaFast.U) => LiaFast.u0).
  intros s m k v a w HR Hk Hl -> Ew. rewrite Ew.
  change (word_to_le_bytes 1 (wa v)) with (word_to_le_bytes (mc_w (unm_cell k v)) (wa (sval_num L (mc_val (unm_cell k v))))).
  apply (repr_x_wcell L s (set_unmap_seq (zupd (st_unmap_seq s) k v) s) m EXC (unm_cell k v) (614952 + Z.of_nat k) HR eq_refl eq_refl (RS_ctx_only L s (set_unmap_seq (zupd (st_unmap_seq s) k v) s) eq_refl eq_refl)).
  - intros c Hc. destruct (cov_ctx_only s (set_unmap_seq (zupd (st_unmap_seq s) k v) s) c eq_refl eq_refl Hc) as [H|H]; [left; exact H|].
    destruct (cov_unmap s (zupd (st_unmap_seq s) k v) c ltac:(rewrite length_zupd; exact Hl) H) as [H'|(j & Hj & E)]; [left; apply ctx_in_image; exact H'|].
    destruct (Nat.eq_dec j k) as [->|Hne].
    + right. rewrite E. rewrite nth_zupd_same by lia. reflexivity.
    + left. rewrite E. rewrite nth_zupd_other by exact Hne. exact (unm_cell_in s j Hj).
  - pose proof (unm_cell_in (set_unmap_seq (zupd (st_unmap_seq s) k v) s) k Hk) as E. cbn [st_unmap_seq set_unmap_seq] in E.
    rewrite nth_zupd_same in E by lia. exact E.
  - intros z E. discriminate.
  - cbn. lia.
  - cbn [unm_cell mc_loc loc_addr]. rewrite Hctx. unfold CTX_unmap_seq. ring.
  - lia.
  - cbn. lia.
Qed.
Definition unm0m (m : word -> option byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m (wa (0 + 614952)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614960)) (word_to_le_bytes 8 (wa 0)))
    (wa (0 + 614968)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614976)) (word_to_le_bytes 8 (wa 0)).

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.
Ltac peel := rewrite MngWb.wbytes_out by side.

#[using="Type"] Lemma unm0_out : forall m x, 0 <= x < 2^64 -> ~ (614952 <= x < 614984) -> unm0m m (wa x) = m (wa x).
Proof. LiaFast.lf_pins LiaFast.u0. intros m x Hx H. unfold unm0m. do 4 peel. reflexivity. Qed.

#[using="Type"] Lemma unm0_byte : forall m j, 0 <= j < 32 -> unm0m m (wa (614952 + j)) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m j Hj. unfold unm0m.
  assert (Z0 : forall k, (k < 8)%nat -> nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0) = Z_to_bv 8 0).
  { intros k Hk. do 8 (destruct k as [|k]; [reflexivity|]). lia. }
  destruct (Z_lt_le_dec j 8) as [A|A].
  { do 3 peel. replace (614952 + j) with (0 + 614952 + Z.of_nat (Z.to_nat j)) by lia. rewrite wbytes_at_wa by (cbn; lia). apply f_equal. apply Z0. lia. }
  destruct (Z_lt_le_dec j 16) as [B|B].
  { do 2 peel. replace (614952 + j) with (0 + 614960 + Z.of_nat (Z.to_nat (j - 8))) by lia. rewrite wbytes_at_wa by (cbn; lia). apply f_equal. apply Z0. lia. }
  destruct (Z_lt_le_dec j 24) as [C|C].
  { do 1 peel. replace (614952 + j) with (0 + 614968 + Z.of_nat (Z.to_nat (j - 16))) by lia. rewrite wbytes_at_wa by (cbn; lia). apply f_equal. apply Z0. lia. }
  replace (614952 + j) with (0 + 614976 + Z.of_nat (Z.to_nat (j - 24))) by lia. rewrite wbytes_at_wa by (cbn; lia). apply f_equal. apply Z0. lia.
Qed.

#[using="Hctx"] Lemma step_unm0 : forall s m, repr_x L s (bview SEGS m) EXC -> length (st_unmap_seq s) = 32%nat ->
  repr_x L (set_unmap_seq (repeat 0 32) s) (bview SEGS (unm0m m)) EXC.
Proof. LiaFast.lf_pins (fun (Hctx : LiaFast.U) => LiaFast.u0).
  intros s m HR Hl.
  assert (Hg : mem_grows m (unm0m m)) by (unfold unm0m; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  apply (repr_x_next L s (set_unmap_seq (repeat 0 32) s) (bview SEGS m) (bview SEGS (unm0m m)) EXC (map (fun j => unm_cell j 0) (seq 0 32))
           HR eq_refl eq_refl (RS_ctx_only L s (set_unmap_seq (repeat 0 32) s) eq_refl eq_refl) (fun x E => bview_grow_n m _ x Hg E)).
  - intros c Hc. destruct (cov_ctx_only s (set_unmap_seq (repeat 0 32) s) c eq_refl eq_refl Hc) as [H|H]; [left; exact H|].
    destruct (cov_unmap s (repeat 0 32) c eq_refl H) as [H'|(j & Hj & E)]; [left; apply ctx_in_image; exact H'|].
    right. rewrite E. assert (N0 : nth j (repeat 0 32) 0 = 0) by (apply nth_repeat). rewrite N0. apply (in_map (fun j0 => unm_cell j0 0)). apply in_seq. lia.
  - intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
    pose proof (unm_cell_in (set_unmap_seq (repeat 0 32) s) j ltac:(lia)) as E. cbn [st_unmap_seq set_unmap_seq] in E.
    rewrite nth_repeat in E. exact E.
  - apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
    unfold cell_holds. cbn [unm_cell mc_loc mc_w mc_val sval_num loc_addr]. rewrite Hctx. intros k Hk. assert (k = 0%nat) as -> by lia.
    rewrite Z.add_0_r. unfold CTX_unmap_seq. replace (614104 + (848 + Z.of_nat j)) with (614952 + Z.of_nat j) by ring.
    rewrite (bview_some_byte SEGS (unm0m m) (614952 + Z.of_nat j) (Z_to_bv 8 0) ltac:(lia) (unm0_byte m (Z.of_nat j) ltac:(lia))). reflexivity.
  - intros x Hx. left. pose proof (bview_ne_range m (unm0m m) x Hx) as Rx.
    assert (A : 614952 <= x < 614984).
    { destruct (decide (614952 <= x < 614984)) as [A|A]; [exact A|]. exfalso. apply Hx. apply bview_ext. apply unm0_out; assumption. }
    exists (unm_cell (Z.to_nat (x - 614952)) 0). split; [apply (in_map (fun j0 => unm_cell j0 0)); apply in_seq; lia|].
    unfold in_rng, cell_range. cbn [unm_cell mc_loc mc_w fst snd loc_addr Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_unmap_seq. rewrite Z2Nat.id by lia. lia.
Qed.
End Steps.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ext1_id : forall b, 0 <= b <= 255 -> ext_Z false 0 1 b = b.
Proof. intros b H. unfold ext_Z. cbn -[Z.pow]. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  rewrite Z.mod_small by (change (2 ^ (8 * 1)) with 256; lia). reflexivity. Qed.

Lemma usage_dec_val : forall W USG l, 0 <= W < 2^64 -> Z.land W 31 = l -> (USG + Z.land (((-1 * W) + -1) mod 2^64) 31) + -32 = USG - (l + 1).
Proof.
  intros W USG l HW El. change 31 with (Z.ones 5) in *. rewrite Z.land_ones in * by lia. change (2^5) with 32 in *.
  rewrite mod64_32s. pose proof (Z.div_mod W 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound W 32 ltac:(lia)) as B.
  assert (E : (-1 * W + -1) mod 32 = 31 - l).
  { symmetry. apply Z.mod_unique with (- (W / 32) - 1); [lia|]. rewrite <- El. lia. }
  rewrite E. ring.
Qed.

(* [comment removed for export] *)
Lemma map_frm : forall L s1 sp0 K m m' (sc : Z), ly_ctx L = 0x95ed8 -> 0 <= sc < 64 ->
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016) ->
  length (st_usage s1) = 48%nat -> length (st_unmap_seq s1) = 32%nat -> FRM L s1 sp0 K m m'.
Proof.
  intros L s1 sp0 K m m' sc Hctx Hsc CHG Hl1 Hl2 x Hx Hne. right. destruct (CHG x Hx Hne) as [(B & A)|[A|A]].
  - exists (usg_cell (Z.to_nat sc) (nth (Z.to_nat sc) (st_usage s1) 0)). split; [apply usg_cell_in; lia|]. split; [wide_tac Hctx|].
    unfold in_rng, cell_range. cbn [usg_cell mc_loc mc_w fst snd loc_addr Z.of_nat Pos.of_succ_nat]. rewrite Hctx, Z2Nat.id by lia. unfold CTX_usage. lia.
  - exists (unm_cell (Z.to_nat (x - 614952)) (nth (Z.to_nat (x - 614952)) (st_unmap_seq s1) 0)). split; [apply unm_cell_in; lia|]. split; [unfold wide; left; cbn [unm_cell mc_loc loc_addr]; rewrite Hctx; unfold CTX_unmap_seq; rewrite Z2Nat.id by lia; lia|].
    unfold in_rng, cell_range. cbn [unm_cell mc_loc mc_w fst snd loc_addr Z.of_nat Pos.of_succ_nat]. rewrite Hctx, Z2Nat.id by lia. unfold CTX_unmap_seq. lia.
  - exists (seq_cell (st_seq s1)). split; [apply seq_cell_in|]. split; [unfold wide; left; cbn [seq_cell mc_loc loc_addr]; rewrite Hctx; unfold CTX_seq; lia|].
    unfold in_rng, cell_range. cbn [seq_cell mc_loc mc_w fst snd loc_addr Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_seq. lia.
Qed.

Lemma KS_ctx : forall s s', st_metas s' = st_metas s -> st_areas s' = st_areas s -> KS s -> KS s'.
Proof. intros s s' Em Ea [ND KO]. unfold KS, keys in *. rewrite Em, Ea. split; assumption. Qed.

Lemma ctx_seg_finish : forall L X EXC s1 s4 m m' sp0 K, NC L X EXC s1 m sp0 K -> repr_x L s4 (bview SEGS m') EXC ->
  st_metas s4 = st_metas s1 -> st_areas s4 = st_areas s1 -> mem_grows m m' -> FRM L s1 sp0 K m m' ->
  NC L X EXC s4 m' sp0 K /\ RS L s4 s1 /\ (forall x, MT s4 x = MT s1 x).
Proof.
  intros L X EXC s1 s4 m m' sp0 K N HR' Em Ea Hg FR.
  assert (HRS : RS L s4 s1) by (apply RS_ctx_only; assumption).
  assert (HZ : forall x, MT s4 x = MT s1 x) by (intros x; unfold MT; rewrite Em; reflexivity).
  split; [|split; [exact HRS | exact HZ]].
  apply (NC_next L X EXC s1 s4 m m' sp0 K N HR' HRS (KS_ctx s1 s4 Em Ea (nc_ks _ _ _ _ _ _ _ N)) (fun x _ => HZ x) Hg FR).
  unfold keys. rewrite Em. reflexivity.
Qed.

Lemma chg_wbytes : forall (m : word -> option byte) a bs x, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> 0 <= x < 2^64 ->
  wbytes m (wa a) bs (wa x) <> m (wa x) -> a <= x < a + Z.of_nat (length bs).
Proof.
  intros m a bs x H1 H2 Hx Hne. destruct bs as [|b bs']; [exfalso; apply Hne; reflexivity|]. cbn [length] in *.
  destruct (decide (a <= x < a + Z.of_nat (S (length bs')))) as [A|A]; [exact A|]. exfalso. apply Hne.
  apply MngWb.wbytes_out; [rewrite u_wa_small by lia; cbn [length]; exact H2 | exact Hx | rewrite u_wa_small by lia; cbn [length]; lia].
Qed.

Lemma chg_split : forall (m1 m2 m3 : word -> option byte) x, m3 x <> m1 x -> m3 x <> m2 x \/ m2 x <> m1 x.
Proof. intros m1 m2 m3 x H. destruct (decide (m3 x = m2 x)) as [E|E]; [right; rewrite <- E; exact H | left; exact E]. Qed.

Lemma chg_unm0 : forall m x, 0 <= x < 2^64 -> unm0m m (wa x) <> m (wa x) -> 614952 <= x < 614984.
Proof. intros m x Hx Hne. destruct (decide (614952 <= x < 614984)) as [A|A]; [exact A|]. exfalso. apply Hne. apply unm0_out; assumption. Qed.

Definition chgs (m m' : word -> option byte) (P : Z -> Prop) : Prop := forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> P x.

Lemma chgs_refl : forall m, chgs m m (fun _ => False).
Proof. intros m x _ H. exact (H eq_refl). Qed.

Lemma chgs_wbytes : forall m m1 (P : Z -> Prop) a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> chgs m m1 P ->
  chgs m (wbytes m1 (wa a) bs) (fun x => P x \/ a <= x < a + Z.of_nat (length bs)).
Proof.
  intros m m1 P a bs H1 H2 C x Hx Hne. destruct (chg_split m m1 _ (wa x) Hne) as [A|A].
  - right. exact (chg_wbytes m1 a bs x H1 H2 Hx A).
  - left. exact (C x Hx A).
Qed.

Lemma chgs_unm0 : forall m m1 (P : Z -> Prop), chgs m m1 P -> chgs m (unm0m m1) (fun x => P x \/ 614952 <= x < 614984).
Proof.
  intros m m1 P C x Hx Hne. destruct (chg_split m m1 _ (wa x) Hne) as [A|A].
  - right. exact (chg_unm0 m1 x Hx A).
  - left. exact (C x Hx A).
Qed.

Lemma chgs_mono : forall m m' (P Q : Z -> Prop), chgs m m' P -> (forall x, P x -> Q x) -> chgs m m' Q.
Proof. intros m m' P Q C H x Hx Hne. exact (H x (C x Hx Hne)). Qed.

Ltac chgs_chain HS := repeat lazymatch goal with
  | |- chgs _ (wbytes _ _ _) _ => apply chgs_wbytes; [clear - HS; cbn; lia | clear - HS; cbn; lia |]
  | |- chgs _ (unm0m _) _ => apply chgs_unm0
  | |- chgs ?m ?m _ => apply chgs_refl
  end.

Lemma rec_cond : forall sc, 0 <= sc < 48 -> (31 <? (sc + -7) mod 2^64) = negb ((7 <=? sc) && (sc <? 39)).
Proof.
  intros sc Hsc. destruct (Z_lt_le_dec sc 7) as [A|A].
  - replace ((sc + -7) mod 2^64) with (sc + -7 + 2^64) by (rewrite <- (Z.mod_small (sc + -7 + 2^64) (2^64)) by lia;
      replace (sc + -7 + 2^64) with (sc + -7 + 1 * 2^64) by ring; rewrite Z_mod_plus_full; reflexivity).
    replace ((7 <=? sc) && (sc <? 39)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
    cbn [negb]. apply Z.ltb_lt. lia.
  - rewrite (Z.mod_small (sc + -7)) by lia. destruct (Z_lt_le_dec sc 39) as [B|B].
    + replace ((7 <=? sc) && (sc <? 39)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [negb]. apply Z.ltb_ge. lia.
    + replace ((7 <=? sc) && (sc <? 39)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia). cbn [negb]. apply Z.ltb_lt. lia.
Qed.

Section SEGM.
Context {fx : FPState}.

#[using="Type"] Theorem seg_map : forall L X EXC s s1 m R rom sp0 K canary ra s0 s1v s2v s3v g am1,
  NC L X EXC s1 m sp0 K -> ntf_frame R m sp0 canary ra s0 s1v s2v s3v ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 18 = wa 0x95ed8 ->
  MT s1 g = Some (MUsed am1) -> (am_sc am1 = 63 \/ 0 <= am_sc am1 < 48) -> 0 <= am_last am1 <= 31 -> 1 <= am_maplen am1 -> meta_bits am1 <= 2^64-1 ->
  st_usage s = st_usage s1 -> (am_sc am1 < 48 -> 0 <= usage_of s1 (am_sc am1) <= 2^64-1) ->
  length (st_usage s1) = 48%nat -> length (st_unmap_seq s1) = 32%nat -> 0 <= st_seq s1 <= 255 ->
  exists R' m', msteps SEGS (mkst R (wa 0x51af8) m rom) (mkst R' (wa 0x51bb4) m' rom) /\
    NC L X EXC (s_rec (am_sc am1) (s_seq (s_usg s s1 (am_sc am1) (am_last am1)))) m' sp0 K /\
    ntf_frame R' m' sp0 canary ra s0 s1v s2v s3v /\ RS L (s_rec (am_sc am1) (s_seq (s_usg s s1 (am_sc am1) (am_last am1)))) s1 /\
    (forall x, MT (s_rec (am_sc am1) (s_seq (s_usg s s1 (am_sc am1) (am_last am1)))) x = MT s1 x) /\
    mem_grows m m' /\ FRM L s1 sp0 K m m' /\
    getr R' 10 = wa (loc_addr L (LMem g)) /\ getr R' 11 = wa (am_maplen am1 * 4096) /\ getr R' 12 = wa (loc_addr L (LMem (am_mem am1))) /\
    getr R' 18 = wa 0x95ed8 /\ keep_regs R' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s s1 m R rom sp0 K canary ra s0 s1v s2v s3v g am1 N F R10 R18 Mg Hsc Rl Rml RW Eus Rus Hlu Hlm Rseq.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s1 EXC (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s1)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  set (sc := am_sc am1) in *. set (W := meta_bits am1).
  assert (RW0 : 0 <= W) by (apply meta_bits_nonneg; lia).
  assert (ESC : SCW W = sc) by (unfold W; apply mb_scw; lia).
  assert (EL : Z.land W 31 = am_last am1) by (unfold W; apply mb_land31; lia).
  assert (EML : Z.shiftr W 12 = am_maplen am1) by (unfold W; apply mb_shr12; lia).
  assert (ESCr : 0 <= SCW W <= 63) by (rewrite ESC; lia).
  assert (HSCR : sc = 63 \/ 0 <= sc < 48) by exact Hsc.
  set (MEM := loc_addr L (LMem (am_mem am1))).
  set (CH := MCell (LMem (am_mem am1)) 8 (VP g)).
  assert (CHi : In CH (image s1)).
  { rewrite image_parts. apply in_app_iff. right. apply in_app_iff. right. apply (group_in_gpart s1 g am1 CH Mg (proj1 HK)). left. reflexivity. }
  pose proof (HC CH CHi) as (M1 & M2 & _). unfold CH in M1, M2. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in M1, M2. fold MEM in M1, M2.
  assert (MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W))) by exact (rx_bits L s1 m EXC HR HEO HK g am1 Mg).
  assert (MM : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa MEM))) by exact (rx_mem L s1 m EXC HR HEO HK g am1 Mg).
  assert (MS : rdn SEGS m (wa (0 + 615016)) 1 = Some (word_to_le_bytes 1 (wa (st_seq s1)))) by exact (rx_seq L s1 m EXC HR HEO Hctx).
  assert (WS : forall d n, 0 <= d -> d + Z.of_nat n <= 1 -> store_ok SEGS m (wa (0 + 615016 + d)) n = true) by exact (rx_seq_wr L s1 m EXC HR HEO Hctx).
  assert (WU : forall d n, 0 <= d -> d + Z.of_nat n <= 32 -> store_ok SEGS m (wa (0 + 614952 + d)) n = true) by exact (rx_unmap_wr L s1 m EXC HR HEO Hctx).
  assert (HFKH : forall m', FRM L s1 sp0 K m m' -> (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> x < 615024) -> mem_grows m m' ->
            forall R', getr R' 2 = wa (sp0 + -96) -> getr R' 9 = wa 613952 -> ntf_frame R' m' sp0 canary ra s0 s1v s2v s3v).
  { intros m' FR Hlow Hg R' P2 P9. apply (frame_keep_heap L s1 sp0 K m m' R R' canary ra s0 s1v s2v s3v FR HC Hsp1 HK1 Hsp2); try assumption.
    intros x Hx E. pose proof (Hlow x Hx E). clear - H Hsp1 HK1. lia. }
  destruct Hsc as [H63|Hsc48].
  - (* [comment removed for export] *)
    assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mp63z.mp63_pre R m G sp0 W (st_seq s1) MEM).
    { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
      constructor; try assumption; try (rewrite ESC; lia); try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia); try (clear - G3; lia);
        try (clear - M1 M2 Hsp2 HK1; lia); try (clear - Hsp1 HK1; lia).
      all: first [ (rewrite R2; f_equal; ring) | exact (stk_ok_mono' m (wa sp0) K 1024 HSTK HK1) | (rewrite ESC; lia) | (clear - RW0 RW; lia)
                 | (clear - Rseq; lia) | (clear - G3; lia) ]. }
    assert (Hs63 : s_usg s s1 sc (am_last am1) = s1) by (unfold s_usg; rewrite H63; reflexivity).
    assert (Hr63 : forall s3, s_rec sc s3 = s3) by (intros s3; unfold s_rec, bounce_idx; rewrite H63; reflexivity).
    rewrite Hs63, Hr63.
    set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mp63z.VALS_mp63 G sp0 W (st_seq s1) MEM)).
    assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (Z36 : bv_unsigned (ev E 36) = st_seq s1) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (SCML : (Z.shiftr (W mod 2^64) (12 mod 64) mod 2^64 =? 0 mod 2^64) = false).
    { rewrite (Z.mod_small W) by lia. litmods. rewrite EML. rewrite Z.mod_small by (split; [lia|]; unfold W, meta_bits in RW; lia). apply Z.eqb_neq. lia. }
    destruct (Z.eq_dec (st_seq s1) 255) as [Q255|Q255].
    + destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mp63z.mp63_pm63b R m rom G sp0 W (st_seq s1) MEM P) as (R' & Hms & P2 & P9 & P10 & P11 & P12 & P13 & P18 & Poth).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mp63.RES_pm63b fst snd]. fold E. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z36;
          rewrite ?br_eq_z, ?br_ne_z.
        - rewrite ext1_id by (clear - Rseq; lia). litmods. rewrite Q255. reflexivity.
        - exact (f_equal negb SCML). }
      assert (Eseq : s_seq s1 = set_seq 1 (set_unmap_seq (repeat 0 32) s1)) by (unfold s_seq; rewrite Q255; reflexivity). rewrite Eseq.
      change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mp63z.mp63_mem_pm63b m R G sp0 W (st_seq s1) MEM) with (wbytes (unm0m m) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1))) in Hms.
      set (m' := wbytes (unm0m m) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1))) in *.
      assert (REPR : repr_x L (set_seq 1 (set_unmap_seq (repeat 0 32) s1)) (bview SEGS m') EXC).
      { apply (step_seq L EXC Hctx _ (unm0m m) 1 (0 + 615016) 1); [apply (step_unm0 L EXC Hctx s1 m HR Hlm) | reflexivity | reflexivity]. }
      assert (Hg : mem_grows m m') by (unfold m', unm0m; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (CHG : forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016).
      { assert (C : chgs m m' (fun x => (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016)).
        { eapply chgs_mono; [unfold m'; try unfold m1; chgs_chain ESCr|]. intros x D. cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat] in D.
          rewrite ?ESC in D. first [ (clear - D ESC Hsc48 A7 A39; lia) | (clear - D ESC Hsc48; lia) | (clear - D ESCr ESC HSCR; lia) ]. }
        exact C. }
      assert (FR : FRM L s1 sp0 K m m') by (apply (map_frm L s1 sp0 K m m' sc Hctx ltac:(lia) CHG Hlu Hlm)).
      destruct (ctx_seg_finish L X EXC s1 _ m m' sp0 K N REPR eq_refl eq_refl Hg FR) as (N' & HRS & HZ).
      exists R', m'. split; [exact Hms|]. split; [exact N'|]. split.
      { apply (HFKH m' FR); [|exact Hg | exact P2 | exact P9]. intros x Hx Ex. destruct (CHG x Hx Ex) as [(B & A)|[A|A]]; [exfalso; clear - B H63; lia | clear - A; lia | clear - A; lia]. }
      split; [exact HRS|]. split; [exact HZ|]. split; [exact Hg|]. split; [exact FR|].
      split; [exact P10|]. split; [rewrite P11, EML; f_equal; ring|]. split; [exact P12|]. split; [exact P18|].
      apply (keep_of_list R' R _ Poth). reflexivity.
    + destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mp63z.mp63_pm63a R m rom G sp0 W (st_seq s1) MEM P) as (R' & Hms & P2 & P9 & P10 & P11 & P12 & P13 & P18 & Poth).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mp63.RES_pm63a fst snd]. fold E. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z36;
          rewrite ?br_eq_z, ?br_ne_z.
        - rewrite ext1_id by (clear - Rseq; lia). litmods. apply negb_true_iff. apply Z.eqb_neq. intros Eq. apply Q255.
          rewrite Z.mod_mod in Eq by lia. rewrite Z.mod_small in Eq by lia. exact Eq.
        - exact (f_equal negb SCML). }
      assert (Eseq : s_seq s1 = set_seq (st_seq s1 + 1) s1) by (unfold s_seq; replace (st_seq s1 =? 255) with false by (symmetry; apply Z.eqb_neq; exact Q255); reflexivity).
      rewrite Eseq.
      change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mp63z.mp63_mem_pm63a m R G sp0 W (st_seq s1) MEM) with (wbytes m (wa (0 + 615016)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 (st_seq s1) + 1)))) in Hms.
      set (m' := wbytes m (wa (0 + 615016)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 (st_seq s1) + 1)))) in *.
      assert (REPR : repr_x L (set_seq (st_seq s1 + 1) s1) (bview SEGS m') EXC).
      { apply (step_seq L EXC Hctx s1 m (st_seq s1 + 1) (0 + 615016) _ HR eq_refl). rewrite ext1_id by (clear - Rseq; lia). reflexivity. }
      assert (Hg : mem_grows m m') by (unfold m'; apply wbytes_grows).
      assert (CHG : forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016).
      { assert (C : chgs m m' (fun x => (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016)).
        { eapply chgs_mono; [unfold m'; try unfold m1; chgs_chain ESCr|]. intros x D. cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat] in D.
          rewrite ?ESC in D. first [ (clear - D ESC Hsc48 A7 A39; lia) | (clear - D ESC Hsc48; lia) | (clear - D ESCr ESC HSCR; lia) ]. }
        exact C. }
      assert (FR : FRM L s1 sp0 K m m') by (apply (map_frm L s1 sp0 K m m' sc Hctx ltac:(lia) CHG Hlu Hlm)).
      destruct (ctx_seg_finish L X EXC s1 _ m m' sp0 K N REPR eq_refl eq_refl Hg FR) as (N' & HRS & HZ).
      exists R', m'. split; [exact Hms|]. split; [exact N'|]. split.
      { apply (HFKH m' FR); [|exact Hg | exact P2 | exact P9]. intros x Hx Ex. destruct (CHG x Hx Ex) as [(B & A)|[A|A]]; [exfalso; clear - B H63; lia | clear - A; lia | clear - A; lia]. }
      split; [exact HRS|]. split; [exact HZ|]. split; [exact Hg|]. split; [exact FR|].
      split; [exact P10|]. split; [rewrite P11, EML; f_equal; ring|]. split; [exact P12|]. split; [exact P18|].
      apply (keep_of_list R' R _ Poth). reflexivity.
  - (* [comment removed for export] *)
    set (k := Z.to_nat sc).
    assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
    set (USG := usage_of s1 sc).
    assert (MU : rdn SEGS m (wa (8 * SCW W + 614568)) 8 = Some (word_to_le_bytes 8 (wa USG))).
    { rewrite ESC. pose proof (rx_usage L s1 m EXC HR HEO Hctx k ltac:(lia)) as E. rewrite Ek in E. replace (8 * sc + 614568) with (614568 + 8 * sc) by ring. exact E. }
    assert (WUS : forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (8 * SCW W + 614568 + d)) n = true).
    { intros d n Hd Hn. rewrite ESC. pose proof (rx_usage_wr L s1 m EXC HR HEO Hctx k ltac:(lia) d n Hd Hn) as E. rewrite Ek in E.
      replace (8 * sc + 614568 + d) with (614568 + 8 * sc + d) by ring. exact E. }
    assert (WREC : forall d n, 0 <= d -> d + Z.of_nat n <= 1 -> store_ok SEGS m (wa (SCW W + 614945 + d)) n = true).
    { intros d n Hd Hn. rewrite ESC. replace (sc + 614945 + d) with (614104 + (841 + sc + d)) by ring. apply (rx_ctx_wr L s1 m EXC HR Hctx); lia. }
    assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_pre R m G sp0 W USG (st_seq s1) MEM).
    { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
      constructor; try assumption; try (rewrite ESC; lia); try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia);
        try (clear - M1 M2 Hsp2 HK1; lia); try (clear - Hsp1 HK1; lia).
      all: first [ (rewrite R2; f_equal; ring) | exact (stk_ok_mono' m (wa sp0) K 1024 HSTK HK1) | (rewrite ESC; lia) | (clear - RW0 RW; lia)
                 | (clear - Rseq; lia) | (clear - G3; lia) | (pose proof (Rus ltac:(clear - Hsc48; lia)) as HU; clear - HU; unfold USG; lia)
                 | (rewrite ESC; clear - G3 Hsc48; lia) | (rewrite ESC; clear - Hsp1 HK1 Hsc48; lia) ]. }
    set (v := usage_of s sc - (am_last am1 + 1)).
    assert (USGW : (USG + Z.land (((-1 * W) + -1) mod 2^64) 31) + -32 = v).
    { rewrite (usage_dec_val W USG (am_last am1)) by (first [exact EL | lia]). unfold v, USG, usage_of. rewrite Eus. reflexivity. }
    set (sA := set_usage (zupd (st_usage s1) k v) s1).
    assert (EsA : s_usg s s1 sc (am_last am1) = sA).
    { unfold s_usg. replace (sc <? 48) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    rewrite EsA.
    set (m1 := wbytes m (wa (8 * SCW W + 614568)) (word_to_le_bytes 8 (wa ((USG + Z.land (((-1 * W) + -1) mod 2^64) 31) + -32)))).
    assert (RA : repr_x L sA (bview SEGS m1) EXC).
    { apply (step_usage L EXC Hctx s1 m k v _ _ HR ltac:(lia) Hlu); [rewrite ESC, Ek; ring | rewrite USGW; reflexivity]. }
    set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.VALS_mps G sp0 W USG (st_seq s1) MEM)).
    assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (Z36 : bv_unsigned (ev E 36) = st_seq s1) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (SCML : (Z.shiftr (W mod 2^64) (12 mod 64) mod 2^64 =? 0 mod 2^64) = false).
    { rewrite (Z.mod_small W) by lia. litmods. rewrite EML. rewrite Z.mod_small by (split; [lia|]; unfold W, meta_bits in RW; lia). apply Z.eqb_neq. lia. }
    assert (SCREC : (31 mod 2^64 <? (Z.shiftr ((4503599627370496 * W) mod 2^64) (58 mod 64) + -7) mod 2^64) = negb ((7 <=? sc) && (sc <? 39))).
    { litmods. change (Z.shiftr ((4503599627370496 * W) mod 2^64) 58) with (SCW W). rewrite ESC. apply rec_cond. lia. }
    assert (Hbnone : forall s3, ~ (7 <= sc < 39) -> s_rec sc s3 = s3).
    { intros s3 Hn. unfold s_rec, bounce_idx. replace ((7 <=? sc) && (sc <? 39)) with false; [reflexivity|].
      destruct (Z_lt_le_dec sc 7); [symmetry; apply andb_false_intro1; apply Z.leb_gt; lia | symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia]. }
    assert (Hbsome : forall s3, 7 <= sc < 39 -> s_rec sc s3 = set_unmap_seq (zupd (st_unmap_seq s3) (Z.to_nat (sc - 7)) (st_seq s3)) s3).
    { intros s3 Hy. unfold s_rec, bounce_idx. replace ((7 <=? sc) && (sc <? 39)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
    assert (Hm1 : forall x, 0 <= x < 2^64 -> ~ (614568 + 8 * sc <= x < 614568 + 8 * sc + 8) -> m1 (wa x) = m (wa x)).
    { intros x Hx Hn. destruct (decide (m1 (wa x) = m (wa x))) as [E0|E0]; [exact E0|]. exfalso. apply Hn.
      unfold m1 in E0. apply chg_wbytes in E0; [| clear - ESCr; lia | clear - ESCr; cbn; lia | exact Hx].
      cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat] in E0. rewrite ESC in E0. clear - E0; lia. }
    destruct (Z.eq_dec (st_seq s1) 255) as [Q255|Q255]; destruct (Z_lt_le_dec sc 7) as [A7|A7];
      [| destruct (Z_lt_le_dec sc 39) as [A39|A39] | | destruct (Z_lt_le_dec sc 39) as [A39|A39]].
    + (* [comment removed for export] *)
      assert (REC : sc < 7 \/ 39 <= sc) by lia.
      destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_pmpd R m rom G sp0 W USG (st_seq s1) MEM P) as (R' & Hms & P2 & P9 & P10 & P11 & P12 & P13 & P14 & P18 & Poth).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mps.RES_pmpd fst snd]. fold E. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z36;
          rewrite ?br_eq_z, ?br_ne_z, ?br_ltu_z.
        - rewrite SCREC. destruct REC as [REC|REC]; [replace ((7 <=? sc) && (sc <? 39)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia) | replace ((7 <=? sc) && (sc <? 39)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia)]; reflexivity.
        - rewrite ext1_id by (clear - Rseq; lia). litmods. rewrite Q255. reflexivity.
        - exact (f_equal negb SCML). }
      rewrite Hbnone by lia.
      assert (Eseq : s_seq sA = set_seq 1 (set_unmap_seq (repeat 0 32) sA)) by (unfold s_seq; cbn [st_seq sA set_usage]; rewrite Q255; reflexivity). rewrite Eseq.
      change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_mem_pmpd m R G sp0 W USG (st_seq s1) MEM) with (wbytes (unm0m m1) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1))) in Hms.
      set (m' := wbytes (unm0m m1) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1))) in *.
      assert (REPR : repr_x L (set_seq 1 (set_unmap_seq (repeat 0 32) sA)) (bview SEGS m') EXC).
      { apply (step_seq L EXC Hctx _ (unm0m m1) 1 (0 + 615016) 1); [apply (step_unm0 L EXC Hctx sA m1 RA Hlm) | reflexivity | reflexivity]. }
      assert (Hg : mem_grows m m') by (unfold m', unm0m, m1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (CHG : forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016).
      { assert (C : chgs m m' (fun x => (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016)).
        { eapply chgs_mono; [unfold m'; try unfold m1; chgs_chain ESCr|]. intros x D. cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat] in D.
          rewrite ?ESC in D. first [ (clear - D ESC Hsc48 A7 A39; lia) | (clear - D ESC Hsc48; lia) | (clear - D ESCr ESC HSCR; lia) ]. }
        exact C. }
      assert (FR : FRM L s1 sp0 K m m') by (apply (map_frm L s1 sp0 K m m' sc Hctx ltac:(lia) CHG Hlu Hlm)).
      destruct (ctx_seg_finish L X EXC s1 _ m m' sp0 K N REPR eq_refl eq_refl Hg FR) as (N' & HRS & HZ).
      exists R', m'. split; [exact Hms|]. split; [exact N'|]. split.
      { apply (HFKH m' FR); [|exact Hg | exact P2 | exact P9]. intros x Hx Ex. destruct (CHG x Hx Ex) as [(B & A)|[A|A]]; [clear - A Hsc48; lia | clear - A; lia | clear - A; lia]. }
      split; [exact HRS|]. split; [exact HZ|]. split; [exact Hg|]. split; [exact FR|].
      split; [exact P10|]. split; [rewrite P11, EML; f_equal; ring|]. split; [exact P12|]. split; [exact P18|].
      apply (keep_of_list R' R _ Poth). reflexivity.
    + destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_pmpc R m rom G sp0 W USG (st_seq s1) MEM P) as (R' & Hms & P2 & P9 & P10 & P11 & P12 & P13 & P14 & P18 & Poth).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mps.RES_pmpc fst snd]. fold E. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z36;
          rewrite ?br_eq_z, ?br_ne_z, ?br_ltu_z.
        - rewrite SCREC. replace ((7 <=? sc) && (sc <? 39)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity.
        - rewrite ext1_id by (clear - Rseq; lia). litmods. rewrite Q255. reflexivity.
        - exact (f_equal negb SCML). }
      rewrite Hbsome by lia.
      assert (Eseq : s_seq sA = set_seq 1 (set_unmap_seq (repeat 0 32) sA)) by (unfold s_seq; cbn [st_seq sA set_usage]; rewrite Q255; reflexivity). rewrite Eseq.
      change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_mem_pmpc m R G sp0 W USG (st_seq s1) MEM) with
        (wbytes (wbytes (unm0m m1) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1))) (wa (SCW W + 614945)) (word_to_le_bytes 1 (wa 1))) in Hms.
      set (m' := wbytes (wbytes (unm0m m1) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1))) (wa (SCW W + 614945)) (word_to_le_bytes 1 (wa 1))) in *.
      assert (REPR : repr_x L (set_unmap_seq (zupd (st_unmap_seq (set_seq 1 (set_unmap_seq (repeat 0 32) sA))) (Z.to_nat (sc - 7)) (st_seq (set_seq 1 (set_unmap_seq (repeat 0 32) sA))))
                               (set_seq 1 (set_unmap_seq (repeat 0 32) sA))) (bview SEGS m') EXC).
      { apply (step_unm1 L EXC Hctx _ _ (Z.to_nat (sc - 7)) 1 (SCW W + 614945) 1).
        - apply (step_seq L EXC Hctx _ (unm0m m1) 1 (0 + 615016) 1); [apply (step_unm0 L EXC Hctx sA m1 RA Hlm) | reflexivity | reflexivity].
        - lia.
        - reflexivity.
        - rewrite ESC, Z2Nat.id by lia. ring.
        - reflexivity. }
      assert (Hg : mem_grows m m') by (unfold m', unm0m, m1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (CHG : forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016).
      { assert (C : chgs m m' (fun x => (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016)).
        { eapply chgs_mono; [unfold m'; try unfold m1; chgs_chain ESCr|]. intros x D. cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat] in D.
          rewrite ?ESC in D. first [ (clear - D ESC Hsc48 A7 A39; lia) | (clear - D ESC Hsc48; lia) | (clear - D ESCr ESC HSCR; lia) ]. }
        exact C. }
      assert (FR : FRM L s1 sp0 K m m') by (apply (map_frm L s1 sp0 K m m' sc Hctx ltac:(lia) CHG Hlu Hlm)).
      destruct (ctx_seg_finish L X EXC s1 _ m m' sp0 K N REPR eq_refl eq_refl Hg FR) as (N' & HRS & HZ).
      exists R', m'. split; [exact Hms|]. split; [exact N'|]. split.
      { apply (HFKH m' FR); [|exact Hg | exact P2 | exact P9]. intros x Hx Ex. destruct (CHG x Hx Ex) as [(B & A)|[A|A]]; [clear - A Hsc48; lia | clear - A; lia | clear - A; lia]. }
      split; [exact HRS|]. split; [exact HZ|]. split; [exact Hg|]. split; [exact FR|].
      split; [exact P10|]. split; [rewrite P11, EML; f_equal; ring|]. split; [exact P12|]. split; [exact P18|].
      apply (keep_of_list R' R _ Poth). reflexivity.
    + (* [comment removed for export] *)
      assert (REC : sc < 7 \/ 39 <= sc) by lia.
      destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_pmpd R m rom G sp0 W USG (st_seq s1) MEM P) as (R' & Hms & P2 & P9 & P10 & P11 & P12 & P13 & P14 & P18 & Poth).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mps.RES_pmpd fst snd]. fold E. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z36;
          rewrite ?br_eq_z, ?br_ne_z, ?br_ltu_z.
        - rewrite SCREC. destruct REC as [REC|REC]; [replace ((7 <=? sc) && (sc <? 39)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia) | replace ((7 <=? sc) && (sc <? 39)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia)]; reflexivity.
        - rewrite ext1_id by (clear - Rseq; lia). litmods. rewrite Q255. reflexivity.
        - exact (f_equal negb SCML). }
      rewrite Hbnone by lia.
      assert (Eseq : s_seq sA = set_seq 1 (set_unmap_seq (repeat 0 32) sA)) by (unfold s_seq; cbn [st_seq sA set_usage]; rewrite Q255; reflexivity). rewrite Eseq.
      change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_mem_pmpd m R G sp0 W USG (st_seq s1) MEM) with (wbytes (unm0m m1) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1))) in Hms.
      set (m' := wbytes (unm0m m1) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1))) in *.
      assert (REPR : repr_x L (set_seq 1 (set_unmap_seq (repeat 0 32) sA)) (bview SEGS m') EXC).
      { apply (step_seq L EXC Hctx _ (unm0m m1) 1 (0 + 615016) 1); [apply (step_unm0 L EXC Hctx sA m1 RA Hlm) | reflexivity | reflexivity]. }
      assert (Hg : mem_grows m m') by (unfold m', unm0m, m1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (CHG : forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016).
      { assert (C : chgs m m' (fun x => (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016)).
        { eapply chgs_mono; [unfold m'; try unfold m1; chgs_chain ESCr|]. intros x D. cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat] in D.
          rewrite ?ESC in D. first [ (clear - D ESC Hsc48 A7 A39; lia) | (clear - D ESC Hsc48; lia) | (clear - D ESCr ESC HSCR; lia) ]. }
        exact C. }
      assert (FR : FRM L s1 sp0 K m m') by (apply (map_frm L s1 sp0 K m m' sc Hctx ltac:(lia) CHG Hlu Hlm)).
      destruct (ctx_seg_finish L X EXC s1 _ m m' sp0 K N REPR eq_refl eq_refl Hg FR) as (N' & HRS & HZ).
      exists R', m'. split; [exact Hms|]. split; [exact N'|]. split.
      { apply (HFKH m' FR); [|exact Hg | exact P2 | exact P9]. intros x Hx Ex. destruct (CHG x Hx Ex) as [(B & A)|[A|A]]; [clear - A Hsc48; lia | clear - A; lia | clear - A; lia]. }
      split; [exact HRS|]. split; [exact HZ|]. split; [exact Hg|]. split; [exact FR|].
      split; [exact P10|]. split; [rewrite P11, EML; f_equal; ring|]. split; [exact P12|]. split; [exact P18|].
      apply (keep_of_list R' R _ Poth). reflexivity.
    + (* [comment removed for export] *)
      assert (REC : sc < 7 \/ 39 <= sc) by lia.
      destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_pmpb R m rom G sp0 W USG (st_seq s1) MEM P) as (R' & Hms & P2 & P9 & P10 & P11 & P12 & P13 & P14 & P18 & Poth).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mps.RES_pmpb fst snd]. fold E. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z36;
          rewrite ?br_eq_z, ?br_ne_z, ?br_ltu_z.
        - rewrite SCREC. destruct REC as [REC|REC]; [replace ((7 <=? sc) && (sc <? 39)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia) | replace ((7 <=? sc) && (sc <? 39)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia)]; reflexivity.
        - rewrite ext1_id by (clear - Rseq; lia). litmods. apply negb_true_iff. apply Z.eqb_neq. intros Eq. apply Q255. rewrite Z.mod_mod in Eq by lia. rewrite Z.mod_small in Eq by lia. exact Eq.
        - exact (f_equal negb SCML). }
      rewrite Hbnone by lia.
      assert (Eseq : s_seq sA = set_seq (st_seq s1 + 1) sA) by (unfold s_seq; cbn [st_seq sA set_usage]; replace (st_seq s1 =? 255) with false by (symmetry; apply Z.eqb_neq; exact Q255); reflexivity).
      rewrite Eseq.
      change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_mem_pmpb m R G sp0 W USG (st_seq s1) MEM) with (wbytes m1 (wa (0 + 615016)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 (st_seq s1) + 1)))) in Hms.
      set (m' := wbytes m1 (wa (0 + 615016)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 (st_seq s1) + 1)))) in *.
      assert (REPR : repr_x L (set_seq (st_seq s1 + 1) sA) (bview SEGS m') EXC).
      { apply (step_seq L EXC Hctx sA m1 (st_seq s1 + 1) (0 + 615016) _ RA eq_refl). rewrite ext1_id by (clear - Rseq; lia). reflexivity. }
      assert (Hg : mem_grows m m') by (unfold m', m1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (CHG : forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016).
      { assert (C : chgs m m' (fun x => (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016)).
        { eapply chgs_mono; [unfold m'; try unfold m1; chgs_chain ESCr|]. intros x D. cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat] in D.
          rewrite ?ESC in D. first [ (clear - D ESC Hsc48 A7 A39; lia) | (clear - D ESC Hsc48; lia) | (clear - D ESCr ESC HSCR; lia) ]. }
        exact C. }
      assert (FR : FRM L s1 sp0 K m m') by (apply (map_frm L s1 sp0 K m m' sc Hctx ltac:(lia) CHG Hlu Hlm)).
      destruct (ctx_seg_finish L X EXC s1 _ m m' sp0 K N REPR eq_refl eq_refl Hg FR) as (N' & HRS & HZ).
      exists R', m'. split; [exact Hms|]. split; [exact N'|]. split.
      { apply (HFKH m' FR); [|exact Hg | exact P2 | exact P9]. intros x Hx Ex. destruct (CHG x Hx Ex) as [(B & A)|[A|A]]; [clear - A Hsc48; lia | clear - A; lia | clear - A; lia]. }
      split; [exact HRS|]. split; [exact HZ|]. split; [exact Hg|]. split; [exact FR|].
      split; [exact P10|]. split; [rewrite P11, EML; f_equal; ring|]. split; [exact P12|]. split; [exact P18|].
      apply (keep_of_list R' R _ Poth). reflexivity.
    + destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_pmpa R m rom G sp0 W USG (st_seq s1) MEM P) as (R' & Hms & P2 & P9 & P10 & P11 & P12 & P13 & P14 & P18 & Poth).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mps.RES_pmpa fst snd]. fold E. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z36;
          rewrite ?br_eq_z, ?br_ne_z, ?br_ltu_z.
        - rewrite SCREC. replace ((7 <=? sc) && (sc <? 39)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity.
        - rewrite ext1_id by (clear - Rseq; lia). litmods. apply negb_true_iff. apply Z.eqb_neq. intros Eq. apply Q255. rewrite Z.mod_mod in Eq by lia. rewrite Z.mod_small in Eq by lia. exact Eq.
        - exact (f_equal negb SCML). }
      rewrite Hbsome by lia.
      assert (Eseq : s_seq sA = set_seq (st_seq s1 + 1) sA) by (unfold s_seq; cbn [st_seq sA set_usage]; replace (st_seq s1 =? 255) with false by (symmetry; apply Z.eqb_neq; exact Q255); reflexivity).
      rewrite Eseq.
      change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_mem_pmpa m R G sp0 W USG (st_seq s1) MEM) with
        (wbytes (wbytes m1 (wa (0 + 615016)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 (st_seq s1) + 1)))) (wa (SCW W + 614945)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 (st_seq s1) + 1)))) in Hms.
      set (m' := wbytes (wbytes m1 (wa (0 + 615016)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 (st_seq s1) + 1)))) (wa (SCW W + 614945)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 (st_seq s1) + 1)))) in *.
      assert (REPR : repr_x L (set_unmap_seq (zupd (st_unmap_seq (set_seq (st_seq s1 + 1) sA)) (Z.to_nat (sc - 7)) (st_seq (set_seq (st_seq s1 + 1) sA)))
                               (set_seq (st_seq s1 + 1) sA)) (bview SEGS m') EXC).
      { apply (step_unm1 L EXC Hctx _ _ (Z.to_nat (sc - 7)) (st_seq s1 + 1) (SCW W + 614945) _).
        - apply (step_seq L EXC Hctx sA m1 (st_seq s1 + 1) (0 + 615016) _ RA eq_refl). rewrite ext1_id by (clear - Rseq; lia). reflexivity.
        - lia.
        - exact Hlm.
        - rewrite ESC, Z2Nat.id by lia. ring.
        - rewrite ext1_id by (clear - Rseq; lia). reflexivity. }
      assert (Hg : mem_grows m m') by (unfold m', m1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (CHG : forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016).
      { assert (C : chgs m m' (fun x => (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016)).
        { eapply chgs_mono; [unfold m'; try unfold m1; chgs_chain ESCr|]. intros x D. cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat] in D.
          rewrite ?ESC in D. first [ (clear - D ESC Hsc48 A7 A39; lia) | (clear - D ESC Hsc48; lia) | (clear - D ESCr ESC HSCR; lia) ]. }
        exact C. }
      assert (FR : FRM L s1 sp0 K m m') by (apply (map_frm L s1 sp0 K m m' sc Hctx ltac:(lia) CHG Hlu Hlm)).
      destruct (ctx_seg_finish L X EXC s1 _ m m' sp0 K N REPR eq_refl eq_refl Hg FR) as (N' & HRS & HZ).
      exists R', m'. split; [exact Hms|]. split; [exact N'|]. split.
      { apply (HFKH m' FR); [|exact Hg | exact P2 | exact P9]. intros x Hx Ex. destruct (CHG x Hx Ex) as [(B & A)|[A|A]]; [clear - A Hsc48; lia | clear - A; lia | clear - A; lia]. }
      split; [exact HRS|]. split; [exact HZ|]. split; [exact Hg|]. split; [exact FR|].
      split; [exact P10|]. split; [rewrite P11, EML; f_equal; ring|]. split; [exact P12|]. split; [exact P18|].
      apply (keep_of_list R' R _ Poth). reflexivity.
    + (* [comment removed for export] *)
      assert (REC : sc < 7 \/ 39 <= sc) by lia.
      destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_pmpb R m rom G sp0 W USG (st_seq s1) MEM P) as (R' & Hms & P2 & P9 & P10 & P11 & P12 & P13 & P14 & P18 & Poth).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mps.RES_pmpb fst snd]. fold E. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z36;
          rewrite ?br_eq_z, ?br_ne_z, ?br_ltu_z.
        - rewrite SCREC. destruct REC as [REC|REC]; [replace ((7 <=? sc) && (sc <? 39)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia) | replace ((7 <=? sc) && (sc <? 39)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia)]; reflexivity.
        - rewrite ext1_id by (clear - Rseq; lia). litmods. apply negb_true_iff. apply Z.eqb_neq. intros Eq. apply Q255. rewrite Z.mod_mod in Eq by lia. rewrite Z.mod_small in Eq by lia. exact Eq.
        - exact (f_equal negb SCML). }
      rewrite Hbnone by lia.
      assert (Eseq : s_seq sA = set_seq (st_seq s1 + 1) sA) by (unfold s_seq; cbn [st_seq sA set_usage]; replace (st_seq s1 =? 255) with false by (symmetry; apply Z.eqb_neq; exact Q255); reflexivity).
      rewrite Eseq.
      change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_mpsz.mps_mem_pmpb m R G sp0 W USG (st_seq s1) MEM) with (wbytes m1 (wa (0 + 615016)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 (st_seq s1) + 1)))) in Hms.
      set (m' := wbytes m1 (wa (0 + 615016)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 (st_seq s1) + 1)))) in *.
      assert (REPR : repr_x L (set_seq (st_seq s1 + 1) sA) (bview SEGS m') EXC).
      { apply (step_seq L EXC Hctx sA m1 (st_seq s1 + 1) (0 + 615016) _ RA eq_refl). rewrite ext1_id by (clear - Rseq; lia). reflexivity. }
      assert (Hg : mem_grows m m') by (unfold m', m1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (CHG : forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016).
      { assert (C : chgs m m' (fun x => (sc < 48 /\ 614568 + 8 * sc <= x < 614568 + 8 * sc + 8) \/ 614952 <= x < 614984 \/ x = 615016)).
        { eapply chgs_mono; [unfold m'; try unfold m1; chgs_chain ESCr|]. intros x D. cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat] in D.
          rewrite ?ESC in D. first [ (clear - D ESC Hsc48 A7 A39; lia) | (clear - D ESC Hsc48; lia) | (clear - D ESCr ESC HSCR; lia) ]. }
        exact C. }
      assert (FR : FRM L s1 sp0 K m m') by (apply (map_frm L s1 sp0 K m m' sc Hctx ltac:(lia) CHG Hlu Hlm)).
      destruct (ctx_seg_finish L X EXC s1 _ m m' sp0 K N REPR eq_refl eq_refl Hg FR) as (N' & HRS & HZ).
      exists R', m'. split; [exact Hms|]. split; [exact N'|]. split.
      { apply (HFKH m' FR); [|exact Hg | exact P2 | exact P9]. intros x Hx Ex. destruct (CHG x Hx Ex) as [(B & A)|[A|A]]; [clear - A Hsc48; lia | clear - A; lia | clear - A; lia]. }
      split; [exact HRS|]. split; [exact HZ|]. split; [exact Hg|]. split; [exact FR|].
      split; [exact P10|]. split; [rewrite P11, EML; f_equal; ring|]. split; [exact P12|]. split; [exact P18|].
      apply (keep_of_list R' R _ Poth). reflexivity.
Qed.
End SEGM.

