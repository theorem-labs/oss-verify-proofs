(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the PURE part of segment B7 of
   reac_segconf_parse_file's walk (the header branch, HDR 0x883b4 -> TAIL / SEG, and the cuts HREF 0x885ec, REFTL
   0x887cc, CLR 0x885fc). No machine state, no image: every lemma is about SegModel's spine and the list functions.
   The B7 segment lane of the image-B G3 walk owner, 2026-10-30.
   ADAPTED (verbatim but for the a7_ -> b7_ prefix and the lib.B.Prog Require of pf_pieces) from the image-A G3 walk owner's
   image-A A7 segment lane lib/A/Prog/pf_a7_f.v (commit f9f4d0fcc957), whose sections 1 and 2 are the unit owner's
   plain lane pfB_p4_spine.v:19-127 at 16c6d72c0344 (p4_ -> a7_). Section 3 is that lane's facts about the header
   line; section 4 is this lane's: the bridges from the interceptor contracts' answers (lib/B/Rt/RtSeg.v first_at,
   strncase_eq) to SegModel's strchr / strncasecmp. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(** ** 1. The spine (pfB_p4_spine.v:19-113 at 16c6d72c0344, p4_ -> b7_) *)

(** The header's body (R:174, after `*close = 0`) and its name (R:184). *)
Definition b7_body (l : list Z) (ci : nat) : list Z := r_trim (slice 1 ci l).
Definition b7_name (b : list Z) : list Z := r_trim (skipn 7 b).

(** r_header from seg_get on (R:197-211). *)
Definition b7_get (rc : rconf) (nm : list Z) (ln : Z) (name : list Z) : rconf * option nat * list Z :=
  match seg_get rc name with
  | (c1, None) => (refuse c1 ln F_bound [AS name; AI 32], None, nm)
  | (c1, Some (i, is_new)) =>
    let c2 := if negb is_new && (rs_seen_gen (nth i (rc_seg c1) rseg_d) =? rc_gen c1)
              then refuse c1 ln F_twice [AS name] else c1 in
    (r_upd c2 i (rs_with_gen (rc_gen c2)), Some i, snprintf_s 16 F_s [AS name])
  end.

(** seg_get's bound branch: c->overflow + 1. *)
Definition b7_ovf (rc : rconf) : rconf :=
  RConf (rc_seg rc) (rc_refusal rc) (rc_refused rc) (rc_overflow rc + 1) (rc_reading rc) (rc_gen rc).

Lemma b7_hdr_notclosed rc nm ln l : strchr l RBR = None ->
  r_header rc nm ln l = (refuse rc ln F_notclosed [AS l], None, nm).
Proof. intros H. unfold r_header. rewrite H. reflexivity. Qed.

Lemma b7_hdr_after rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 <> 0 ->
  r_header rc nm ln l = (refuse rc ln F_after [AS l], None, nm).
Proof. intros H1 H2. unfold r_header. rewrite H1. apply Z.eqb_neq in H2. rewrite H2. reflexivity. Qed.

Lemma b7_hdr_kw rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  r_header rc nm ln l =
    if negb (strncasecmp (b7_body l ci) S_segment 7 =? 0) || negb (sp_tab (nth 7 (b7_body l ci) 0))
    then (refuse rc ln F_unknown [AS (b7_body l ci)], None, nm) else
    if hd0 (b7_name (b7_body l ci)) =? 0 then (refuse rc ln F_noname [], None, nm) else
    if (16 <=? strlen (b7_name (b7_body l ci)))%nat
    then (refuse rc ln F_toolong [AS (b7_name (b7_body l ci)); AI 15], None, nm)
    else b7_get rc nm ln (b7_name (b7_body l ci)).
Proof. intros H1 H2. unfold r_header. rewrite H1, H2. reflexivity. Qed.

Lemma b7_hdr_unknown rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  (strncasecmp (b7_body l ci) S_segment 7 <> 0 \/ sp_tab (nth 7 (b7_body l ci) 0) = false) ->
  r_header rc nm ln l = (refuse rc ln F_unknown [AS (b7_body l ci)], None, nm).
Proof.
  intros H1 H2 H3. rewrite (b7_hdr_kw rc nm ln l ci H1 H2).
  destruct H3 as [H3|H3].
  - apply Z.eqb_neq in H3. rewrite H3. reflexivity.
  - rewrite H3. cbn [negb]. rewrite orb_true_r. reflexivity.
Qed.

Lemma b7_hdr_noname rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  strncasecmp (b7_body l ci) S_segment 7 = 0 -> sp_tab (nth 7 (b7_body l ci) 0) = true ->
  hd0 (b7_name (b7_body l ci)) = 0 ->
  r_header rc nm ln l = (refuse rc ln F_noname [], None, nm).
Proof. intros H1 H2 H3 H4 H5. rewrite (b7_hdr_kw rc nm ln l ci H1 H2), H3, H4, H5. reflexivity. Qed.

Lemma b7_hdr_toolong rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  strncasecmp (b7_body l ci) S_segment 7 = 0 -> sp_tab (nth 7 (b7_body l ci) 0) = true ->
  hd0 (b7_name (b7_body l ci)) <> 0 -> (16 <= strlen (b7_name (b7_body l ci)))%nat ->
  r_header rc nm ln l = (refuse rc ln F_toolong [AS (b7_name (b7_body l ci)); AI 15], None, nm).
Proof.
  intros H1 H2 H3 H4 H5 H6. rewrite (b7_hdr_kw rc nm ln l ci H1 H2), H3, H4.
  apply Z.eqb_neq in H5. rewrite H5. apply Nat.leb_le in H6. rewrite H6. reflexivity.
Qed.

Lemma b7_hdr_get rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  strncasecmp (b7_body l ci) S_segment 7 = 0 -> sp_tab (nth 7 (b7_body l ci) 0) = true ->
  hd0 (b7_name (b7_body l ci)) <> 0 -> (strlen (b7_name (b7_body l ci)) < 16)%nat ->
  r_header rc nm ln l = b7_get rc nm ln (b7_name (b7_body l ci)).
Proof.
  intros H1 H2 H3 H4 H5 H6. rewrite (b7_hdr_kw rc nm ln l ci H1 H2), H3, H4.
  apply Z.eqb_neq in H5. rewrite H5. apply Nat.leb_gt in H6. rewrite H6. reflexivity.
Qed.

(** ** 2. b7_get is pf_pieces.v's pf_seg_step (the exit cut SEG's step), by unfolding *)
(* pf_pieces.v states SEG / NEW / FOUND with pf_seg_step; the two bodies are the same term. The equality is
   kept here as a lemma so that a change of either text is a build error, not a silent mismatch. *)
Lemma b7_get_is_seg_step : forall rc nm ln name, b7_get rc nm ln name = pf_seg_step rc nm ln name.
Proof. intros rc nm ln name. reflexivity. Qed.

(** ** 3. This lane's facts about the header line *)

(** '[' is the line's first byte, so the ']' the strchr finds is not at 0. *)
Lemma b7_ci_pos : forall l ci, hd0 l = LBR -> strchr l RBR = Some ci -> (1 <= ci)%nat.
Proof.
  intros [|x r] ci H1 H2; cbn in H1; [discriminate|]. subst x. cbn in H2.
  destruct (strchr r 93); cbn in H2; inversion H2; lia.
Qed.

(** Nothing follows the ']': the line ends there. *)
Lemma b7_close_last : forall l ci, ~ In 0 l -> strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  (ci < length l)%nat /\ S ci = length l.
Proof.
  intros l ci Hn Hs Hz.
  assert (Hci : (ci < length l)%nat).
  { rewrite (strchr_memchr l RBR Hn ltac:(lia)) in Hs. exact (memchr_lt _ _ _ Hs). }
  split; [exact Hci|].
  pose proof (nth_after_close l ci Hn Hci) as E. rewrite Hz, Z.eqb_refl in E. symmetry in E.
  apply Nat.eqb_eq in E. exact E.
Qed.

(** The body and the name stay inside the line's bytes, and hold no NUL. *)
Lemma b7_slice_len : forall l ci, (1 <= ci)%nat -> (ci <= length l)%nat ->
  length (slice 1 ci l) = (ci - 1)%nat.
Proof. intros l ci H1 H2. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma b7_body_len : forall l ci, (length (b7_body l ci) <= length l)%nat.
Proof.
  intros l ci. unfold b7_body. pose proof (r_trim_len_le (slice 1 ci l)) as H.
  unfold slice in *. rewrite length_firstn, length_skipn in H. lia.
Qed.

Lemma b7_name_len : forall b, (length (b7_name b) <= length b)%nat.
Proof.
  intros b. unfold b7_name. pose proof (r_trim_len_le (skipn 7 b)) as H. rewrite length_skipn in H. lia.
Qed.

Lemma b7_body_nul : forall l ci, ~ In 0 (b7_body l ci).
Proof.
  intros l ci. unfold b7_body, r_trim. cbv zeta.
  exact (nulfree_firstn _ _ (nulfree_dropwhile _ _ (cut_nul_nulfree _))).
Qed.

Lemma b7_name_nul : forall b, ~ In 0 (b7_name b).
Proof.
  intros b. unfold b7_name, r_trim. cbv zeta.
  exact (nulfree_firstn _ _ (nulfree_dropwhile _ _ (cut_nul_nulfree _))).
Qed.

(** strlen of the name is its length (it holds no NUL). *)
Lemma b7_strlen_name : forall b, strlen (b7_name b) = length (b7_name b).
Proof. intros b. apply strlen_id. exact (b7_name_nul b). Qed.

(** The keyword test needs seven bytes, and the blank after it an eighth. *)
Lemma b7_kw_len7 : forall b, ~ In 0 b -> strncasecmp b S_segment 7 = 0 -> (7 <= length b)%nat.
Proof.
  intros b Hn H. pose proof (strncasecmp_segment b Hn) as E.
  rewrite H, Z.eqb_refl in E. symmetry in E. apply andb_true_iff in E as [E _].
  apply Nat.leb_le in E. exact E.
Qed.

Lemma b7_kw_len8 : forall b, ~ In 0 b -> strncasecmp b S_segment 7 = 0 -> sp_tab (nth 7 b 0) = true ->
  (8 <= length b)%nat.
Proof.
  intros b Hn H HS. pose proof (b7_kw_len7 b Hn H) as H7.
  destruct (Nat.eq_dec 7 (length b)) as [E|E]; [|lia].
  rewrite (nth_overflow b 0) in HS by lia. cbn in HS. discriminate.
Qed.

(** sp_tab, as the two byte compares of 0x88308 / 0x8830c read it (s9 = 9, s4 = 0x20). *)
Lemma b7_sp_tab_true : forall x, x = 32 \/ x = 9 -> sp_tab x = true.
Proof. intros x [-> | ->]; reflexivity. Qed.

Lemma b7_sp_tab_false : forall x, x <> 32 -> x <> 9 -> sp_tab x = false.
Proof.
  intros x H1 H2. unfold sp_tab. apply orb_false_iff. split; apply Z.eqb_neq; lia.
Qed.

(** The counters' room along A7: every arm of the header either refuses once (and the line it refuses took at
    least one byte) or leaves c alone up to seg_get, which A8a / A8b account for. *)
Lemma b7_cnt_refuse_next : forall rc ln f a s o,
  (o < length s)%nat -> pf_cnt rc (length (skipn o s)) ->
  pf_cnt (refuse rc ln f a) (length (skipn (pf_next s o) s)).
Proof.
  intros rc ln f a s o Ho H.
  exact (pf_cnt_refuse rc ln f a (length (skipn o s)) (length (skipn (pf_next s o) s))
           (pf_next_skipn_lt s o Ho) H).
Qed.

Lemma b7_cnt_zero : forall rc (s : list Z) (o : nat), (o < length s)%nat ->
  pf_cnt rc (length (skipn o s)) -> pf_cnt rc 0.
Proof. intros rc s o _ H. exact (pf_cnt_mono rc (length (skipn o s)) 0 ltac:(lia) H). Qed.
