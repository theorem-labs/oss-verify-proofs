(* reac-pw/fuzz_segconf, ASan image A: pure facts for m_file's segment S_MF_HDRB (the HDRB segment lane of the G2 walk owner's
   G2; sub-task the HDRB facts sub-lane). No instruction is executed here and no machine state is named: the lemmas are about
   SegModel's m_file model, the byte encodings of lib/Prog/seg_spec.v, SegABase's readers, and the footprints
   M_FILE_FP (m_file_c.v) and m_refuse_W (m_refuse_c.v). The HDRB walk (m_find; found: the gen test and m_refuse;
   new: n < 32, memset, memcpy; full: overflow++ and m_refuse) uses them.

   SOURCES. Copied lemmas cite their line in the plain / image-B owner's files at commit 2cff17c0d0ee:
   - "mfu" = proofs/reac-pw/fuzz_segconf/lib/Prog/mfu_facts.v (build-independent model facts);
   - "mfp" = proofs/reac-pw/fuzz_segconf/lib/Prog/mfp_mconf.v (byte-list encoding lemmas; only its list-level
     lemmas are copied, none of its memory-level bytes_at / mconf_atp lemmas).
   mf_cur_ok, mf_rest, mf_fin and mh_find are m_file_m.v's (not redefined). The new lemmas (prefix hb_) are this
   file's own: the model steps of mh_find in each case, the field reads of an encoded block through a reader,
   the reader-level byte lemmas, and the footprint membership facts. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_refuse_c m_file_m m_file_mdl.
(* the encodings' names (mseg_enc, mconf_encp, fld, zb, ZERO, the MC_ / MS_ offsets) unqualified *)
Import seg_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================================== A. the model ======================================== *)

(* ---- the lines ---- *)

(* mfu:17 *)
Lemma break_nl_spec : forall s l q, break_nl s = (l, q) ->
  ~ In NL l /\ (s = l ++ NL :: q \/ (s = l /\ q = [])).
Proof.
  induction s as [|b r IH]; intros l q E; cbn [break_nl] in E.
  - injection E as <- <-. split; [intros []|right; split; reflexivity].
  - destruct (Z.eqb_spec b NL) as [Hb|Hb].
    + injection E as <- <-. split; [intros []|left; subst b; reflexivity].
    + revert E. destruct (break_nl r) as [l1 q1] eqn:E1. intros E. injection E as <- <-.
      destruct (IH l1 q1 eq_refl) as [N1 [S1|[S1 Q1]]].
      * split; [intros [H|H]; [lia|exact (N1 H)]|left; rewrite S1; reflexivity].
      * split; [intros [H|H]; [lia|exact (N1 H)]|right; split; [rewrite S1; reflexivity|exact Q1]].
Qed.

(* mfu:30 *)
Lemma break_nl_rest_lt : forall s, s <> [] -> (length (snd (break_nl s)) < length s)%nat.
Proof.
  intros [|b r] H; [congruence|]. pose proof (break_nl_len_cons b r) as L. cbn [length]. lia.
Qed.

(* mfu:35 *)
Lemma lines_go_S_cons : forall f b r,
  lines_go (S f) (b :: r) = let (l, q) := break_nl (b :: r) in l :: lines_go f q.
Proof. reflexivity. Qed.

(* mfu:39 *)
Lemma lines_go_fuel : forall f g p, (length p < f)%nat -> (length p < g)%nat -> lines_go f p = lines_go g p.
Proof.
  induction f as [|f IH]; intros g p Hf Hg; [lia|]. destruct g as [|g]; [lia|].
  destruct p as [|b r]; [reflexivity|]. rewrite !lines_go_S_cons.
  destruct (break_nl (b :: r)) as [l q] eqn:E.
  assert (HL : (length q <= length r)%nat)
    by (pose proof (break_nl_len_cons b r) as H; rewrite E in H; exact H).
  cbn [length] in Hf, Hg. f_equal. apply IH; lia.
Qed.

(* mfu:50 *)
Lemma lines_cons : forall s, s <> [] -> lines s = fst (break_nl s) :: lines (snd (break_nl s)).
Proof.
  intros [|b r] Hs; [congruence|]. unfold lines at 1. cbn [length]. rewrite lines_go_S_cons.
  destruct (break_nl (b :: r)) as [l q] eqn:E. cbn [fst snd].
  assert (HL : (length q <= length r)%nat)
    by (pose proof (break_nl_len_cons b r) as H; rewrite E in H; exact H).
  f_equal. unfold lines. apply lines_go_fuel; lia.
Qed.

(* mfu:59 *)
Lemma lines_nil : lines [] = [].
Proof. reflexivity. Qed.

(* mfu:64 *)
Lemma m_lines_step : forall st n s, s <> [] ->
  m_lines st n (lines s) = m_lines (m_line st (n + 1) (fst (break_nl s))) (n + 1) (lines (snd (break_nl s))).
Proof. intros st n s Hs. rewrite (lines_cons s Hs). reflexivity. Qed.

(* the text left after the line is shorter *)
Lemma hb_mf_rest_lt : forall rest, rest <> [] -> (length (mf_rest rest) < length rest)%nat.
Proof. intros rest Hr. unfold mf_rest. apply break_nl_rest_lt. exact Hr. Qed.

(* ---- sizes and the cursor: lib/A/Prog/m_file_mdl.v (the shared model file, the KEYA segment lane's text) states
   upd_nth_length, m_find_go_lt, m_find_lt, m_refuse_sizes, mf_grows (+ refl / trans), m_refuse_grows,
   m_upd_sizes, m_upd_grows, m_header_ok, m_key_grows, m_key_seg_len, m_line_ok, m_lines_ok, and besides them
   mf_cur_ok_refuse, mf_kept_le_final and mf_kept_le_refuse. This file carried copies of the first fourteen
   (from the plain / image-B owner's plain mfu_facts.v) before m_file_mdl.v existed; they are gone and m_file_mdl.v is Required
   above, so no term has two definitions. ---- *)

(* ---- the steps of mh_find ---- *)

(* every outcome of mh_find grows the model and leaves the cursor inside seg (the m_find part of m_header_ok) *)
Lemma hb_mh_find_ok : forall mc nm l,
  mf_grows mc (fst (mh_find mc nm l)) /\ mf_cur_ok (fst (mh_find mc nm l)) (snd (mh_find mc nm l)).
Proof.
  intros c nm n. unfold mh_find. cbv zeta.
  destruct (m_find c nm) as [i|] eqn:Ef.
  - pose proof (m_find_lt _ _ _ Ef) as Hi. cbn [fst snd].
    destruct (ms_gen (nth i (mc_seg c) mseg_d) =? mc_gen c).
    + pose proof (m_refuse_sizes c n false) as [E _].
      split; [eapply mf_grows_trans; [apply m_refuse_grows|apply m_upd_grows]|].
      unfold mf_cur_ok, m_upd, m_set_segs. cbn [mc_seg]. rewrite upd_nth_length, E. exact Hi.
    + split; [apply m_upd_grows|].
      unfold mf_cur_ok, m_upd, m_set_segs. cbn [mc_seg]. rewrite upd_nth_length. exact Hi.
  - destruct (32 <=? length (mc_seg c))%nat.
    + split; [|exact I]. cbn [fst].
      eapply mf_grows_trans; [|apply m_refuse_grows]. unfold mf_grows. cbn [mc_seg mc_kept]. lia.
    + cbn [fst snd]. unfold mf_grows, mf_cur_ok, m_set_segs. cbn [mc_seg mc_kept].
      rewrite length_app. cbn [length]. lia.
Qed.

(* the final model of the lines left grows from any state whose cursor is inside seg *)
Lemma hb_fin_grows : forall st line rest, mf_cur_ok (fst st) (snd st) -> mf_grows (fst st) (mf_fin st line rest).
Proof. intros st line rest Hc. unfold mf_fin. exact (proj1 (m_lines_ok (lines (mf_rest rest)) st (line + 1) Hc)). Qed.

(* what m_refuse keeps: gen, overflow, seg, reading; refused + 1 *)
Lemma hb_refuse_fields : forall c l k,
  mc_gen (m_refuse c l k) = mc_gen c /\ mc_overflow (m_refuse c l k) = mc_overflow c /\
  mc_refused (m_refuse c l k) <= mc_refused c + 1 /\ mc_seg (m_refuse c l k) = mc_seg c /\
  mc_reading (m_refuse c l k) = mc_reading c.
Proof.
  intros c l k. unfold m_refuse. cbv zeta. cbn [mc_gen mc_overflow mc_refused mc_seg mc_reading].
  split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; reflexivity.
Qed.

Lemma hb_upd_nth_last {A} : forall (s : list A) g f, upd_nth (length s) f (s ++ [g]) = s ++ [f g].
Proof. induction s as [|x s IH]; intros g f; cbn [length app upd_nth]; [reflexivity|]. f_equal. apply IH. Qed.

(* an edit of the entry just appended *)
Lemma hb_upd_last : forall c s g f, m_upd (m_set_segs c (s ++ [g])) (length s) f = m_set_segs c (s ++ [f g]).
Proof. intros c s g f. unfold m_upd. cbn [mc_seg m_set_segs]. rewrite hb_upd_nth_last. reflexivity. Qed.

(* mfp:52 *)
Definition mc_set_overflow (z : Z) (c : mconf) : mconf :=
  MConf (mc_seg c) z (mc_refused c) (mc_kept c) (mc_gen c) (mc_reading c).

(* not found, seg full: overflow++, then m_refuse *)
Lemma hb_mh_find_full : forall mc nm l, m_find mc nm = None -> (32 <= length (mc_seg mc))%nat ->
  mh_find mc nm l = (m_refuse (mc_set_overflow (mc_overflow mc + 1) mc) l false, None).
Proof.
  intros mc nm l Hf Hn. unfold mh_find. rewrite Hf.
  destruct (Nat.leb_spec 32 (length (mc_seg mc))) as [_|C]; [reflexivity|exfalso; lia].
Qed.

(* not found, room: the entry mseg0 nm appended (memset + memcpy), then its gen set (g->gen = c->gen) *)
Lemma hb_mh_find_new : forall mc nm l, m_find mc nm = None -> (length (mc_seg mc) < 32)%nat ->
  let c1 := m_set_segs mc (mc_seg mc ++ [mseg0 nm]) in
  mh_find mc nm l = (m_upd c1 (length (mc_seg mc)) (ms_with_gen (mc_gen c1)), Some (length (mc_seg mc))).
Proof.
  intros mc nm l Hf Hn. cbv zeta. unfold mh_find. rewrite Hf.
  destruct (Nat.leb_spec 32 (length (mc_seg mc))) as [C|_]; [exfalso; lia|].
  rewrite hb_upd_last. reflexivity.
Qed.

(* found, same gen: m_refuse, then g->gen = c->gen *)
Lemma hb_mh_find_eq : forall mc nm l i, m_find mc nm = Some i -> ms_gen (nth i (mc_seg mc) mseg_d) = mc_gen mc ->
  let c1 := m_refuse mc l false in
  mh_find mc nm l = (m_upd c1 i (ms_with_gen (mc_gen c1)), Some i).
Proof.
  intros mc nm l i Hf Hg. cbv zeta. unfold mh_find. rewrite Hf.
  rewrite (proj2 (Z.eqb_eq _ _) Hg). reflexivity.
Qed.

(* found, other gen: g->gen = c->gen only *)
Lemma hb_mh_find_ne : forall mc nm l i, m_find mc nm = Some i -> ms_gen (nth i (mc_seg mc) mseg_d) <> mc_gen mc ->
  mh_find mc nm l = (m_upd mc i (ms_with_gen (mc_gen mc)), Some i).
Proof.
  intros mc nm l i Hf Hg. unfold mh_find. rewrite Hf.
  rewrite (proj2 (Z.eqb_neq _ _) Hg). reflexivity.
Qed.

(* ======================================== B. the encodings ======================================== *)

(* ---- helpers (prefix mcx_): byte windows of an updated list, model lists ---- *)

(* mfp:58 *)
Lemma mcx_nth_ext : forall {A} (l l' : list A), (forall i, nth_error l i = nth_error l' i) -> l = l'.
Proof.
  intros A l. induction l as [|x l IH]; intros [|y l'] H.
  - reflexivity.
  - specialize (H 0%nat). cbn in H. discriminate H.
  - specialize (H 0%nat). cbn in H. discriminate H.
  - pose proof (H 0%nat) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros i. exact (H (S i)).
Qed.

(* mfp:67 *)
Lemma mcx_fld_nth : forall off n (L : list byte) i,
  nth_error (fld off n L) i = if (i <? n)%nat then nth_error L (off + i) else None.
Proof.
  intros off n L i. unfold fld. rewrite nth_error_firstn.
  destruct (i <? n)%nat; [|reflexivity]. rewrite nth_error_skipn. f_equal; lia.
Qed.

(* mfp:74 *)
Lemma mcx_fld_length : forall off n (L : list byte), (off + n <= length L)%nat -> length (fld off n L) = n.
Proof. intros off n L H. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.

(* mfp:78 *)
Lemma mcx_fld_upd_out : forall (L : list byte) k nb off n, (k + length nb <= length L)%nat ->
  (off + n <= k \/ k + length nb <= off)%nat -> fld off n (upd_bytes L k nb) = fld off n L.
Proof.
  intros L k nb off n H1 H2. apply mcx_nth_ext. intros i. rewrite !mcx_fld_nth.
  destruct (Nat.ltb_spec0 i n) as [Hi|Hi]; [|reflexivity].
  destruct (Nat.ltb_spec0 (off + i) (length L)) as [Hl|Hl].
  - rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k (off + i)); destruct (Nat.ltb_spec0 (off + i) (k + length nb)); cbn [andb];
      first [reflexivity | exfalso; lia].
  - rewrite (proj2 (nth_error_None L (off + i))) by lia.
    apply nth_error_None. rewrite upd_bytes_length by lia. lia.
Qed.

(* mfp:92 *)
Lemma mcx_fld_upd_same : forall (L : list byte) k n nb, n = length nb -> (k + n <= length L)%nat ->
  fld k n (upd_bytes L k nb) = nb.
Proof.
  intros L k n nb -> H. apply mcx_nth_ext. intros i. rewrite mcx_fld_nth.
  destruct (Nat.ltb_spec0 i (length nb)) as [Hi|Hi].
  - rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k (k + i)); destruct (Nat.ltb_spec0 (k + i) (k + length nb)); cbn [andb];
      first [f_equal; lia | exfalso; lia].
  - symmetry. apply nth_error_None. lia.
Qed.

(* mfp:104 *)
Lemma mcx_fld_upd_head : forall (L : list byte) k n nb, (k + n <= length L)%nat -> (length nb <= n)%nat ->
  fld k n (upd_bytes L k nb) = nb ++ fld (k + length nb) (n - length nb) L.
Proof.
  intros L k n nb H1 H2. apply mcx_nth_ext. intros i. rewrite mcx_fld_nth.
  destruct (Nat.ltb_spec0 i (length nb)) as [Hi|Hi].
  - rewrite nth_error_app1 by lia. destruct (Nat.ltb_spec0 i n); [|exfalso; lia].
    rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k (k + i)); destruct (Nat.ltb_spec0 (k + i) (k + length nb)); cbn [andb];
      first [f_equal; lia | exfalso; lia].
  - rewrite nth_error_app2 by lia. rewrite mcx_fld_nth.
    destruct (Nat.ltb_spec0 i n); destruct (Nat.ltb_spec0 (i - length nb) (n - length nb)); try (exfalso; lia).
    + rewrite upd_bytes_nth by lia.
      destruct (Nat.leb_spec0 k (k + i)); destruct (Nat.ltb_spec0 (k + i) (k + length nb)); cbn [andb];
        first [f_equal; lia | exfalso; lia].
    + reflexivity.
Qed.

(* mfp:122 *)
Lemma mcx_fld_upd_sub : forall (L : list byte) off n k nb, (k + length nb <= n)%nat -> (off + n <= length L)%nat ->
  fld off n (upd_bytes L (off + k) nb) = upd_bytes (fld off n L) k nb.
Proof.
  intros L off n k nb H1 H2. pose proof (mcx_fld_length off n L H2) as HF.
  apply mcx_nth_ext. intros i. rewrite mcx_fld_nth.
  destruct (Nat.ltb_spec0 i n) as [Hi|Hi].
  - rewrite (upd_bytes_nth (fld off n L)) by lia. rewrite upd_bytes_nth by lia. rewrite mcx_fld_nth.
    destruct (Nat.ltb_spec0 i n); [|exfalso; lia].
    destruct (Nat.leb_spec0 (off + k) (off + i)); destruct (Nat.ltb_spec0 (off + i) (off + k + length nb));
    destruct (Nat.leb_spec0 k i); destruct (Nat.ltb_spec0 i (k + length nb)); cbn [andb];
      first [reflexivity | f_equal; lia | exfalso; lia].
  - symmetry. apply nth_error_None. rewrite upd_bytes_length by lia. lia.
Qed.

(* mfp:136 *)
Lemma mcx_fld_fld : forall a n b k (L : list byte), (a + n <= k)%nat -> fld a n (fld b k L) = fld (b + a) n L.
Proof.
  intros a n b k L H. unfold fld. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min n (k - a)) with n by lia. rewrite (Nat.add_comm a b). reflexivity.
Qed.

(* mfp:142 *)
Lemma mcx_zb_length : forall s, length (zb s) = length s.
Proof. intros s. unfold zb. apply length_map. Qed.

(* mfp:145 *)
Lemma mcx_zbz_length : forall s, length (zb s ++ [ZERO]) = S (length s).
Proof. intros s. rewrite length_app, mcx_zb_length. cbn [length]. lia. Qed.

(* mfp:148 *)
Lemma mcx_zs_app : forall a b, zs (a ++ b) = zs a ++ zs b.
Proof. intros a b. unfold zs. apply map_app. Qed.

(* mfp:151 *)
Lemma mcx_zs_zb : forall s, Forall (fun x => 0 <= x < 256) s -> zs (zb s) = s.
Proof.
  induction s as [|x s IH]; intros H; [reflexivity|].
  pose proof (Forall_inv H) as Hx. pose proof (Forall_inv_tail H) as Hs. cbv beta in Hx.
  unfold zs, zb in *. cbn [map]. f_equal; [|apply IH; exact Hs].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

(* mfp:159 *)
Lemma mcx_zs_nul : forall s, Forall (fun x => 0 <= x < 256) s -> zs (zb s ++ [ZERO]) = s ++ [0].
Proof. intros s H. rewrite mcx_zs_app, mcx_zs_zb by exact H. reflexivity. Qed.

(* mfp:162 *)
Lemma mcx_firstn_app_exact : forall {A} (l1 l2 : list A) n, n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof. intros A l1 l2 n ->. induction l1 as [|x l1 IH]; [reflexivity|]. cbn. f_equal. exact IH. Qed.

(* mfp:166 *)
Lemma mcx_cstr_upd : forall (L : list byte) k cap n s, n = cap -> (k + cap <= length L)%nat ->
  (length s < cap)%nat -> ~ In 0 s -> Forall (fun x => 0 <= x < 256) s ->
  cstr_enc cap s (fld k n (upd_bytes L k (zb s ++ [ZERO]))).
Proof.
  intros L k cap n s -> H1 H2 H3 H4.
  rewrite mcx_fld_upd_head by (rewrite ?mcx_zbz_length; lia).
  rewrite mcx_zbz_length.
  split; [rewrite length_app, mcx_zbz_length, mcx_fld_length by lia; lia|].
  split; [exact H2|]. split; [exact H3|].
  rewrite mcx_zs_app, (mcx_zs_nul s H4).
  apply mcx_firstn_app_exact. rewrite length_app. cbn [length]. lia.
Qed.

(* mfp:180 *)
Lemma mcx_cstr_forall : forall cap s f, cstr_enc cap s f -> Forall (fun x => 0 <= x < 256) s.
Proof.
  intros cap s f (_ & _ & _ & Hz). apply Forall_forall. intros x Hx. cbv beta.
  assert (Hin : In x (zs f)).
  { rewrite <- (firstn_skipn (S (length s)) (zs f)). apply in_or_app. left. rewrite Hz.
    apply in_or_app. left. exact Hx. }
  unfold zs in Hin. apply in_map_iff in Hin. destruct Hin as (b & Hb & _). subst x.
  pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. lia.
Qed.

(* mfp:202 *)
Lemma mcx_upd_zeros_nul : forall n s, (length s < n)%nat ->
  upd_bytes (repeat ZERO n) 0 (zb s) = upd_bytes (repeat ZERO n) 0 (zb s ++ [ZERO]).
Proof.
  intros n s H. unfold upd_bytes. rewrite mcx_zbz_length, mcx_zb_length, !skipn_repeat_gen.
  cbn [firstn app Nat.add]. rewrite <- app_assoc. f_equal.
  replace (n - length s)%nat with (S (n - S (length s))) by lia. reflexivity.
Qed.

(* mfp:216 *)
Lemma mcx_upd_nth_same : forall {A} i (f : A -> A) (l : list A) d, (i < length l)%nat ->
  nth i (upd_nth i f l) d = f (nth i l d).
Proof.
  intros A i f l d. revert i. induction l as [|x l IH]; intros [|i] H; cbn [length] in H.
  - exfalso; lia.
  - exfalso; lia.
  - reflexivity.
  - cbn [upd_nth nth]. apply IH. lia.
Qed.

(* mfp:226 *)
Lemma mcx_upd_nth_other : forall {A} i j (f : A -> A) (l : list A) d, i <> j ->
  nth j (upd_nth i f l) d = nth j l d.
Proof.
  intros A i j f l d. revert i j. induction l as [|x l IH]; intros i j H; [destruct i; reflexivity|].
  destruct i as [|i]; destruct j as [|j].
  - exfalso. apply H. reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [upd_nth nth]. apply IH. lia.
Qed.

(* mfp:263-267 *)
Ltac mcx_lia := unfold MS_ROLE, MS_ROLE_SET, MS_IGNORE, MS_IGNORE_SET, MS_MODEL_SET, MS_MODEL, MS_ROLE_FILE,
  MS_IGNORE_FILE, MS_GEN, MC_N, MC_OVERFLOW, MC_REFUSED, MC_KEPT, MC_KNOCK, MC_NKEPT, MC_GEN, MC_READING,
  SEG_M_SIZE in *; lia.
Ltac mcx_out := rewrite mcx_fld_upd_out by mcx_lia.
Ltac mcx_keep H := mcx_out; exact H.

(* ---- what an encoding bounds ---- *)

(* mfp:270 *)
Lemma mconf_enc_bounds : forall pend mc bs, mconf_encp pend mc bs ->
  length bs = 9236%nat /\ (length (mc_seg mc) <= 32)%nat /\ (length (mc_kept mc) <= 8)%nat /\
  0 <= mc_gen mc < 2 ^ 32 /\ 0 <= mc_refused mc < 2 ^ 32 /\ 0 <= mc_overflow mc < 2 ^ 32 /\
  (length (mc_reading mc) < 96)%nat /\ ~ In 0 (mc_reading mc) /\ Forall (fun x => 0 <= x < 256) (mc_reading mc) /\
  (forall i, (i < length (mc_seg mc))%nat ->
     (length (ms_name (nth i (mc_seg mc) mseg_d)) < 16)%nat /\ ~ In 0 (ms_name (nth i (mc_seg mc) mseg_d)) /\
     Forall (fun x => 0 <= x < 256) (ms_name (nth i (mc_seg mc) mseg_d)) /\
     0 <= ms_gen (nth i (mc_seg mc) mseg_d) < 2 ^ 32).
Proof.
  intros pend mc bs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  pose proof H12 as (R1 & R2 & R3 & R4). destruct H5 as [O1 _]. destruct H6 as [F1 _]. destruct H11 as [G1 _].
  split; [apply Nat2Z.inj; rewrite H1; reflexivity|].
  split; [exact H2|]. split; [exact H7|]. split; [exact G1|]. split; [exact F1|]. split; [exact O1|].
  split; [exact R2|]. split; [exact R3|]. split; [exact (mcx_cstr_forall _ _ _ H12)|].
  intros i Hi. destruct (H3 i Hi) as (_ & N & _ & _ & _ & _ & _ & _ & _ & _ & (Gg & _)).
  pose proof N as (_ & N2 & N3 & _).
  split; [exact N2|]. split; [exact N3|]. split; [exact (mcx_cstr_forall _ _ _ N)|]. exact Gg.
Qed.

(* ---- the 256 bytes of an entry ---- *)

(* mfp:365 *)
Lemma mseg_enc_gen : forall g f z, mseg_enc g f -> 0 <= z < 2 ^ 32 ->
  mseg_enc (ms_with_gen z g) (upd_bytes f (Z.to_nat MS_GEN) (le4 (Z_to_bv 64 z))).
Proof.
  intros g f z (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) Hz.
  pose proof (length_le4 (Z_to_bv 64 z)) as Hn.
  unfold mseg_enc, fldz in *.
  cbn [ms_with_gen ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [mcx_keep H2|]. split; [mcx_keep H3|]. split; [mcx_keep H4|]. split; [mcx_keep H5|].
  split; [mcx_keep H6|]. split; [mcx_keep H7|].
  split; [mcx_keep H8|]. split; [mcx_keep H9|]. split; [mcx_keep H10|].
  rewrite mcx_fld_upd_same by mcx_lia. split; [lia | reflexivity].
Qed.

(* mfp:427: a new entry: memset(g, 0, 256), memcpy(g->name, nm, |nm|), g->gen = z *)
Lemma mseg_enc_new : forall nm z, (length nm < 16)%nat -> ~ In 0 nm -> Forall (fun x => 0 <= x < 256) nm ->
  0 <= z < 2 ^ 32 ->
  mseg_enc (ms_with_gen z (mseg0 nm))
    (upd_bytes (upd_bytes (repeat ZERO 256) 0 (zb nm)) (Z.to_nat MS_GEN) (le4 (Z_to_bv 64 z))).
Proof.
  intros nm z Hnm Hn0 Hnf Hz.
  rewrite (mcx_upd_zeros_nul 256 nm) by lia.
  pose proof (mcx_zbz_length nm) as Hnz. pose proof (length_le4 (Z_to_bv 64 z)) as Hn4.
  pose proof (repeat_length ZERO 256) as HR.
  assert (HL0 : length (upd_bytes (repeat ZERO 256) 0 (zb nm ++ [ZERO])) = 256%nat)
    by (rewrite upd_bytes_length by lia; exact HR).
  unfold mseg_enc, fldz.
  cbn [ms_with_gen mseg0 ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact HL0|].
  split; [mcx_out; apply mcx_cstr_upd; [reflexivity | lia | exact Hnm | exact Hn0 | exact Hnf]|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; split; [exact u32_enc_zero | lia]|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 24 ltac:(lia))|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 96 ltac:(lia))|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 96 ltac:(lia))|].
  rewrite mcx_fld_upd_same by mcx_lia. split; [lia | reflexivity].
Qed.

(* 256 zero bytes (memset(g, 0, 256)) encode the empty entry *)
Lemma hb_mseg_enc_zero : mseg_enc (mseg0 []) (repeat ZERO 256).
Proof.
  unfold mseg_enc, fldz.
  cbn [mseg0 ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [apply repeat_length|].
  split; [rewrite fld_repeat by lia; exact (cstr_enc_nil_zero 16 ltac:(lia))|].
  split; [rewrite fld_repeat by mcx_lia; split; [exact u32_enc_zero | lia]|].
  split; [rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 24 ltac:(lia))|].
  split; [rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 96 ltac:(lia))|].
  split; [rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 96 ltac:(lia))|].
  rewrite fld_repeat by mcx_lia. exact u32_enc_zero.
Qed.

(* memset(g, 0, 256) + memcpy(g->name, nm, |nm|) encode mseg0 nm (the gen is still 0) *)
Lemma hb_mseg_enc_name : forall nm, (length nm < 16)%nat -> ~ In 0 nm -> Forall (fun x => 0 <= x < 256) nm ->
  mseg_enc (mseg0 nm) (upd_bytes (repeat ZERO 256) 0 (zb nm)).
Proof.
  intros nm Hnm Hn0 Hnf.
  rewrite (mcx_upd_zeros_nul 256 nm) by lia.
  pose proof (mcx_zbz_length nm) as Hnz.
  pose proof (repeat_length ZERO 256) as HR.
  unfold mseg_enc, fldz.
  cbn [mseg0 ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by lia; exact HR|].
  split; [apply mcx_cstr_upd; [reflexivity | lia | exact Hnm | exact Hn0 | exact Hnf]|].
  split; [mcx_out; rewrite fld_repeat by mcx_lia; split; [exact u32_enc_zero | lia]|].
  split; [mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 24 ltac:(lia))|].
  split; [mcx_out; rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 96 ltac:(lia))|].
  split; [mcx_out; rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 96 ltac:(lia))|].
  mcx_out. rewrite fld_repeat by mcx_lia. exact u32_enc_zero.
Qed.

(* ---- the 9236 bytes of the block ---- *)

(* mfp:473 *)
Lemma mconf_enc_overflow : forall pend mc bs z, mconf_encp pend mc bs -> 0 <= z < 2 ^ 32 ->
  mconf_encp pend (mc_set_overflow z mc) (upd_bytes bs (Z.to_nat MC_OVERFLOW) (le4 (Z_to_bv 64 z))).
Proof.
  intros pend mc bs z (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hz.
  pose proof (length_le4 (Z_to_bv 64 z)) as Hn.
  unfold mconf_encp, fldz in *.
  cbn [mc_set_overflow mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [exact H2|].
  split; [intros i Hi; mcx_out; apply H3; exact Hi|].
  split; [mcx_keep H4|].
  split; [rewrite mcx_fld_upd_same by mcx_lia; split; [lia | reflexivity]|].
  split; [mcx_keep H6|].
  split; [exact H7|].
  split; [intros i Hi; destruct (H8 i Hi) as [Ha Hb]; split; [mcx_keep Ha | mcx_keep Hb]|].
  split; [intros i Hi; mcx_out; apply H9; exact Hi|].
  split; [mcx_keep H10|]. split; [mcx_keep H11|].
  mcx_keep H12.
Qed.

(* mfp:511: an edit of entry gi (k + |nb| <= 256: inside the entry), given the entry-level edit
   (mfp's mcx_upd_nth_length replaced by upd_nth_length above, the same fact) *)
Lemma mconf_enc_seg : forall pend mc bs gi (f : mseg -> mseg) k nb, mconf_encp pend mc bs ->
  (gi < length (mc_seg mc))%nat -> (k + length nb <= 256)%nat ->
  (forall fb, mseg_enc (nth gi (mc_seg mc) mseg_d) fb -> mseg_enc (f (nth gi (mc_seg mc) mseg_d)) (upd_bytes fb k nb)) ->
  mconf_encp pend (m_upd mc gi f) (upd_bytes bs (256 * gi + k) nb).
Proof.
  intros pend mc bs gi f k nb (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hgi Hk Hf.
  pose proof (upd_nth_length f (mc_seg mc) gi) as HU.
  unfold m_upd, m_set_segs, mconf_encp, fldz in *.
  cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [rewrite HU; exact H2|].
  split.
  { intros i Hi. rewrite HU in Hi. destruct (Nat.eq_dec i gi) as [->|Hne].
    - rewrite mcx_upd_nth_same by exact Hgi. rewrite mcx_fld_upd_sub by mcx_lia.
      apply Hf. apply H3. exact Hgi.
    - rewrite mcx_upd_nth_other by lia. mcx_out. apply H3. exact Hi. }
  split; [rewrite HU; mcx_keep H4|]. split; [mcx_keep H5|]. split; [mcx_keep H6|].
  split; [exact H7|].
  split; [intros i Hi; destruct (H8 i Hi) as [Ha Hb]; split; [mcx_keep Ha | mcx_keep Hb]|].
  split; [intros i Hi; mcx_out; apply H9; exact Hi|].
  split; [mcx_keep H10|]. split; [mcx_keep H11|].
  mcx_keep H12.
Qed.

(* mfp:535: a new entry at n < 32 and n++ *)
Lemma mconf_enc_append : forall pend mc bs g gb, mconf_encp pend mc bs -> (length (mc_seg mc) < 32)%nat ->
  mseg_enc g gb ->
  mconf_encp pend (m_set_segs mc (mc_seg mc ++ [g]))
    (upd_bytes (upd_bytes bs (256 * length (mc_seg mc)) gb) (Z.to_nat MC_N)
       (le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc)) + 1)))).
Proof.
  intros pend mc bs g gb (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hn32 Hg.
  pose proof Hg as (Hgl & _).
  pose proof (length_le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc)) + 1))) as Hn.
  assert (HL2 : Z.of_nat (length (upd_bytes bs (256 * length (mc_seg mc)) gb)) = SEG_M_SIZE)
    by (rewrite upd_bytes_length by mcx_lia; exact H1).
  unfold m_set_segs, mconf_encp, fldz in *.
  cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  split; [rewrite upd_bytes_length by mcx_lia; exact HL2|].
  split; [rewrite length_app; cbn [length]; lia|].
  split.
  { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. mcx_out.
    destruct (Nat.lt_ge_cases i (length (mc_seg mc))) as [Hlt|Hge].
    - rewrite app_nth1 by exact Hlt. mcx_out. apply H3. exact Hlt.
    - assert (Ei : i = length (mc_seg mc)) by lia. subst i.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      rewrite mcx_fld_upd_same by mcx_lia. exact Hg. }
  split.
  { rewrite mcx_fld_upd_same by mcx_lia. rewrite length_app. cbn [length].
    replace (Z.of_nat (length (mc_seg mc) + 1)) with (Z.of_nat (length (mc_seg mc)) + 1) by lia.
    split; [lia | reflexivity]. }
  split; [mcx_out; mcx_keep H5|]. split; [mcx_out; mcx_keep H6|].
  split; [exact H7|].
  split; [intros i Hi; destruct (H8 i Hi) as [Ha Hb]; split; [mcx_out; mcx_keep Ha | mcx_out; mcx_keep Hb]|].
  split; [intros i Hi; mcx_out; mcx_out; apply H9; exact Hi|].
  split; [mcx_out; mcx_keep H10|]. split; [mcx_out; mcx_keep H11|].
  mcx_out; mcx_keep H12.
Qed.

(* entry i replaced by g, whose 256 bytes gb are written over the entry's *)
Lemma hb_mconf_enc_set : forall pend mc bs i g gb, mconf_encp pend mc bs -> (i < length (mc_seg mc))%nat ->
  mseg_enc g gb -> length gb = 256%nat ->
  mconf_encp pend (m_upd mc i (fun _ => g)) (upd_bytes bs (256 * i) gb).
Proof.
  intros pend mc bs i g gb He Hi Hg Hgl.
  replace (256 * i)%nat with (256 * i + 0)%nat by lia.
  apply mconf_enc_seg; [exact He | exact Hi | lia |].
  intros fb Hfb. pose proof Hfb as (Hfl & _). cbv beta.
  unfold upd_bytes. cbn [firstn app Nat.add]. rewrite skipn_all2 by lia. rewrite app_nil_r. exact Hg.
Qed.

(* writing X at k over 256 zero bytes is writing the 256-byte block X ++ zeros (memset then memcpy) *)
Lemma hb_fld_upd_zero : forall bs k X, (k + 256 <= length bs)%nat -> fld k 256 bs = repeat ZERO 256 ->
  (length X <= 256)%nat -> upd_bytes bs k X = upd_bytes bs k (upd_bytes (repeat ZERO 256) 0 X).
Proof.
  intros bs k X Hk Hz HX.
  assert (HY : length (upd_bytes (repeat ZERO 256) 0 X) = 256%nat)
    by (rewrite upd_bytes_length by (rewrite repeat_length; lia); apply repeat_length).
  apply mcx_nth_ext. intros i.
  destruct (Nat.ltb_spec0 i (length bs)) as [Hi|Hi].
  - rewrite (upd_bytes_nth bs k X) by lia.
    rewrite (upd_bytes_nth bs k (upd_bytes (repeat ZERO 256) 0 X)) by lia.
    rewrite HY.
    destruct (Nat.leb_spec0 k i) as [H1|H1]; [|reflexivity].
    destruct (Nat.ltb_spec0 i (k + length X)) as [H2|H2];
      destruct (Nat.ltb_spec0 i (k + 256)) as [H3|H3]; cbn [andb]; try (exfalso; lia); [| |reflexivity].
    + rewrite upd_bytes_nth by (rewrite repeat_length; lia).
      destruct (Nat.leb_spec0 0 (i - k)) as [_|C]; [|exfalso; lia].
      destruct (Nat.ltb_spec0 (i - k) (0 + length X)) as [_|C]; [|exfalso; lia]. cbn [andb].
      rewrite Nat.sub_0_r. reflexivity.
    + rewrite upd_bytes_nth by (rewrite repeat_length; lia).
      destruct (Nat.ltb_spec0 (i - k) (0 + length X)) as [C|_]; [exfalso; lia|].
      rewrite andb_false_r. rewrite nth_error_repeat by lia.
      pose proof (f_equal (fun L => nth_error L (i - k)) Hz) as E. cbv beta in E.
      rewrite mcx_fld_nth, nth_error_repeat in E by lia. revert E.
      destruct (Nat.ltb_spec0 (i - k) 256) as [_|C]; [|exfalso; lia]. intros E.
      replace (k + (i - k))%nat with i in E by lia. exact E.
  - assert (E1 : nth_error (upd_bytes bs k X) i = None)
      by (apply nth_error_None; rewrite upd_bytes_length by lia; lia).
    assert (E2 : nth_error (upd_bytes bs k (upd_bytes (repeat ZERO 256) 0 X)) i = None)
      by (apply nth_error_None; rewrite upd_bytes_length by lia; lia).
    rewrite E1, E2. reflexivity.
Qed.

(* ======================================== C. the readers ======================================== *)

(* the bytes of le4 and of a list window *)
Lemma hb_nth_le_bytes : forall n z k, (k < n)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes n z) ZB0) = Z.shiftr z (8 * Z.of_nat k) mod 256.
Proof.
  induction n as [|n IH]; intros z k Hk; [exfalso; lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth].
  - rewrite Z_to_bv_unsigned. change (bv_wrap 8 z) with (z mod 2 ^ 8).
    replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma hb_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold le4, le_byte.
  rewrite hb_nth_le_bytes by exact Hk.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity.
  rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.

Lemma hb_nth_fld : forall off n (L : list byte) i d, (i < n)%nat -> (off + n <= length L)%nat ->
  nth i (fld off n L) d = nth (off + i) L d.
Proof.
  intros off n L i d Hi HL. apply nth_error_nth. rewrite mcx_fld_nth.
  destruct (Nat.ltb_spec0 i n) as [_|C]; [|exfalso; lia].
  apply nth_error_nth'. lia.
Qed.

Lemma hb_nth_of_error : forall (L L' : list byte) i j d, nth_error L i = nth_error L' j -> (j < length L')%nat ->
  nth i L d = nth j L' d.
Proof. intros L L' i j d E H. apply nth_error_nth. rewrite E. apply nth_error_nth'. exact H. Qed.

(* a u32 field of a block read through the reader *)
Lemma hb_val_of_u32 : forall rd c bs off v, sa_bytes rd c bs -> (off + 4 <= length bs)%nat ->
  u32_enc v (fld off 4 bs) -> sa_val rd (c + Z.of_nat off) 4 v.
Proof.
  intros rd c bs off v Hb HL [Hv Hf]. unfold sa_bytes, sa_val in *. intros k Hk.
  replace (c + Z.of_nat off + Z.of_nat k) with (c + Z.of_nat (off + k)) by lia.
  rewrite (Hb (off + k)%nat) by lia. f_equal.
  rewrite <- (hb_nth_fld off 4 bs k ZB0) by lia. rewrite Hf. apply hb_le4_byte; [exact Hv | exact Hk].
Qed.

(* n, overflow, gen of the block (the loads at c + MC_N, c + MC_OVERFLOW, c + MC_GEN) *)
Lemma hb_rd_n : forall rd c mc, sa_mconf rd c mc -> sa_val rd (c + seg_spec.MC_N) 4 (Z.of_nat (length (mc_seg mc))).
Proof.
  intros rd c mc (bs & Hb & He). pose proof He as (H1 & _ & _ & H4 & _). unfold fldz in H4.
  replace (c + MC_N) with (c + Z.of_nat (Z.to_nat MC_N)) by (unfold MC_N; lia).
  apply (hb_val_of_u32 rd c bs); [exact Hb | mcx_lia | exact H4].
Qed.

Lemma hb_rd_overflow : forall rd c mc, sa_mconf rd c mc -> sa_val rd (c + seg_spec.MC_OVERFLOW) 4 (mc_overflow mc).
Proof.
  intros rd c mc (bs & Hb & He). pose proof He as (H1 & _ & _ & _ & H5 & _). unfold fldz in H5.
  replace (c + MC_OVERFLOW) with (c + Z.of_nat (Z.to_nat MC_OVERFLOW)) by (unfold MC_OVERFLOW; lia).
  apply (hb_val_of_u32 rd c bs); [exact Hb | mcx_lia | exact H5].
Qed.

Lemma hb_rd_gen : forall rd c mc, sa_mconf rd c mc -> sa_val rd (c + seg_spec.MC_GEN) 4 (mc_gen mc).
Proof.
  intros rd c mc (bs & Hb & He). pose proof He as (H1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & H11 & _).
  unfold fldz in H11.
  replace (c + MC_GEN) with (c + Z.of_nat (Z.to_nat MC_GEN)) by (unfold MC_GEN; lia).
  apply (hb_val_of_u32 rd c bs); [exact Hb | mcx_lia | exact H11].
Qed.

(* g->gen of entry i (the load at &c->seg[i] + MS_GEN) *)
Lemma hb_rd_seg_gen : forall rd c mc i, sa_mconf rd c mc -> (i < length (mc_seg mc))%nat ->
  sa_val rd (seg_spec.mseg_addr c i + seg_spec.MS_GEN) 4 (ms_gen (nth i (mc_seg mc) mseg_d)).
Proof.
  intros rd c mc i (bs & Hb & He) Hi.
  pose proof He as (H1 & H2 & H3 & _).
  destruct (H3 i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hg).
  unfold fldz in Hg. rewrite mcx_fld_fld in Hg by (unfold MS_GEN; lia).
  replace (mseg_addr c i + MS_GEN) with (c + Z.of_nat (256 * i + Z.to_nat MS_GEN))
    by (unfold mseg_addr, MSEG_SIZE, MS_GEN; lia).
  apply (hb_val_of_u32 rd c bs); [exact Hb | mcx_lia | exact Hg].
Qed.

(* the bounds an encoded block fixes *)
Lemma hb_mconf_bounds : forall rd c mc, sa_mconf rd c mc ->
  (length (mc_seg mc) <= 32)%nat /\ (length (mc_kept mc) <= 8)%nat /\ 0 <= mc_gen mc < 2 ^ 32 /\
  0 <= mc_refused mc < 2 ^ 32 /\ 0 <= mc_overflow mc < 2 ^ 32 /\
  (forall i, (i < length (mc_seg mc))%nat -> 0 <= ms_gen (nth i (mc_seg mc) mseg_d) < 2 ^ 32).
Proof.
  intros rd c mc (bs & _ & He).
  destruct (mconf_enc_bounds _ _ _ He) as (_ & B1 & B2 & B3 & B4 & B5 & _ & _ & _ & B6).
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
  intros i Hi. destruct (B6 i Hi) as (_ & _ & _ & G). exact G.
Qed.

(* the block after a write whose part inside it is X at offset k *)
Lemma hb_bytes_upd : forall rd rd' c BS k X, sa_bytes rd c BS -> sa_bytes rd' (c + Z.of_nat k) X ->
  (k + length X <= length BS)%nat ->
  (forall a, c <= a < c + Z.of_nat (length BS) ->
     ~ (c + Z.of_nat k <= a < c + Z.of_nat k + Z.of_nat (length X)) -> rd' a = rd a) ->
  sa_bytes rd' c (upd_bytes BS k X).
Proof.
  intros rd rd' c BS k X HB HX HL HK. unfold sa_bytes in *. intros i Hi.
  rewrite upd_bytes_length in Hi by exact HL.
  pose proof (upd_bytes_nth BS k X i HL Hi) as E. revert E.
  destruct (Nat.leb_spec0 k i) as [H1|H1]; destruct (Nat.ltb_spec0 i (k + length X)) as [H2|H2];
    cbn [andb]; intros E.
  1: { rewrite (hb_nth_of_error _ X i (i - k) ZB0 E) by lia.
       replace (c + Z.of_nat i) with (c + Z.of_nat k + Z.of_nat (i - k)) by lia.
       apply HX. lia. }
  all: rewrite (hb_nth_of_error _ BS i i ZB0 E) by lia; rewrite HK by lia; apply HB; exact Hi.
Qed.

(* a 4-byte value read through the reader is the bytes le4 *)
Lemma hb_bytes_of_val : forall rd a v, 0 <= v < 2 ^ 32 -> sa_val rd a 4 v -> sa_bytes rd a (le4 (Z_to_bv 64 v)).
Proof.
  intros rd a v Hv HV. unfold sa_val, sa_bytes in *. intros i Hi. rewrite length_le4 in Hi.
  rewrite HV by exact Hi. f_equal. symmetry. apply hb_le4_byte; assumption.
Qed.

(* a list of byte values read through the reader is the bytes zb *)
Lemma hb_bytes_of_zs : forall rd a l, Forall (fun x => 0 <= x < 256) l -> sa_zs rd a l -> sa_bytes rd a (zb l).
Proof.
  intros rd a l Hf HZ. unfold sa_zs, sa_bytes in *. intros i Hi. rewrite mcx_zb_length in Hi.
  rewrite HZ by exact Hi. f_equal. unfold zb, ZB0. rewrite map_nth. rewrite Z_to_bv_unsigned.
  symmetry. apply bv_wrap_small. unfold bv_modulus.
  pose proof (proj1 (Forall_forall _ _) Hf (nth i l 0) (nth_In l 0 Hi)) as Hx. cbv beta in Hx. lia.
Qed.

(* a window of the block *)
Lemma hb_bytes_sub : forall rd c BS k n, sa_bytes rd c BS -> (k + n <= length BS)%nat ->
  sa_bytes rd (c + Z.of_nat k) (fld k n BS).
Proof.
  intros rd c BS k n HB HL. unfold sa_bytes in *. intros i Hi. rewrite mcx_fld_length in Hi by exact HL.
  rewrite hb_nth_fld by lia. replace (c + Z.of_nat k + Z.of_nat i) with (c + Z.of_nat (k + i)) by lia.
  apply HB. lia.
Qed.

(* the reader fixes the bytes *)
Lemma hb_bytes_eq : forall rd a X Y, sa_bytes rd a X -> sa_bytes rd a Y -> length X = length Y -> X = Y.
Proof.
  intros rd a X Y HX HY HL. unfold sa_bytes in *. apply mcx_nth_ext. intros i.
  destruct (Nat.ltb_spec0 i (length X)) as [Hi|Hi].
  - rewrite (nth_error_nth' X ZB0) by exact Hi. rewrite (nth_error_nth' Y ZB0) by lia. f_equal.
    pose proof (HX i Hi) as E1. pose proof (HY i ltac:(lia)) as E2. rewrite E1 in E2. injection E2 as E2.
    apply bv_eq. exact E2.
  - rewrite (proj2 (nth_error_None X i)) by lia. rewrite (proj2 (nth_error_None Y i)) by lia. reflexivity.
Qed.

(* a reader that agrees on the block's 9236 bytes holds the same model *)
Lemma hb_mconf_keep : forall rd rd' c mc, sa_mconf rd c mc ->
  (forall a, c <= a < c + seg_spec.SEG_M_SIZE -> rd' a = rd a) -> sa_mconf rd' c mc.
Proof.
  intros rd rd' c mc (bs & HB & He) HK. unfold sa_mconf, sa_mconfp. exists bs. split; [|exact He].
  pose proof He as (H1 & _). unfold sa_bytes in *. intros i Hi. rewrite HK by lia. apply HB. exact Hi.
Qed.

(* a reader that agrees on the slack keeps it mapped *)
Lemma hb_tail_keep : forall rd rd' e, sa_tail rd e -> (forall a, e < a < e - e mod 8 + 8 -> rd' a = rd a) ->
  sa_tail rd' e.
Proof.
  intros rd rd' e HT HK. unfold sa_tail in *. intros x Hx. rewrite HK by exact Hx. apply HT. exact Hx.
Qed.

(* ======================================== D. the footprint ======================================== *)

(* entry i of the final seg is in m_file's footprint *)
Lemma hb_fp_seg : forall c k0 mcf i a, (i < length (mc_seg mcf))%nat ->
  seg_spec.mseg_addr c i <= a < seg_spec.mseg_addr c i + 256 -> inFP (M_FILE_FP c k0 mcf) a.
Proof.
  intros c k0 mcf i a Hi Ha. unfold M_FILE_FP. apply inFP_cons. left.
  unfold mseg_addr, MSEG_SIZE in *. lia.
Qed.

(* n, overflow, refused are in it *)
Lemma hb_fp_cnt : forall c k0 mcf a, c + seg_spec.MC_N <= a < c + seg_spec.MC_REFUSED + 4 ->
  inFP (M_FILE_FP c k0 mcf) a.
Proof.
  intros c k0 mcf a Ha. unfold M_FILE_FP. apply inFP_cons. right. apply inFP_cons. left. exact Ha.
Qed.

(* m_refuse's writes, at a model whose kept is at least the entry's and grows to the final one, are in it *)
Lemma hb_fp_refuse : forall c k0 mc l k mcf a, (k0 <= length (mc_kept mc))%nat -> mf_grows (m_refuse mc l k) mcf ->
  inFP (m_refuse_W c mc) a -> inFP (M_FILE_FP c k0 mcf) a.
Proof.
  intros c k0 mc l k mcf a Hk0 [_ HG] HW.
  assert (HR : c + MC_REFUSED <= a < c + MC_REFUSED + 4 -> inFP (M_FILE_FP c k0 mcf) a).
  { intros Ha. unfold M_FILE_FP. apply inFP_cons. right. apply inFP_cons. left.
    unfold MC_N, MC_REFUSED in *. lia. }
  revert HW. unfold m_refuse_W.
  destruct (Z.ltb_spec (Z.of_nat (length (mc_kept mc))) 8) as [Hlt|Hge]; intros HW;
    apply inFP_app in HW; destruct HW as [HW|HW].
  - apply inFP_cons in HW. destruct HW as [HW|HW].
    + assert (HL : length (mc_kept (m_refuse mc l k)) = S (length (mc_kept mc))).
      { unfold m_refuse. cbv zeta. cbn [mc_kept].
        destruct (Z.ltb_spec (Z.of_nat (length (mc_kept mc))) 8) as [_|C]; [|exfalso; lia].
        rewrite length_app. cbn [length]. lia. }
      unfold M_FILE_FP. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left.
      unfold kept_addr, MC_KEPT_LEN in *. lia.
    + apply inFP_cons in HW. destruct HW as [HW|HW]; [|destruct (inFP_nil _ HW)].
      unfold M_FILE_FP. do 4 (apply inFP_cons; right). apply inFP_cons. left.
      unfold MC_NKEPT, MC_READING in *. lia.
  - apply inFP_cons in HW. destruct HW as [HW|HW]; [exact (HR HW)|destruct (inFP_nil _ HW)].
  - destruct (inFP_nil _ HW).
  - apply inFP_cons in HW. destruct HW as [HW|HW]; [exact (HR HW)|destruct (inFP_nil _ HW)].
Qed.
