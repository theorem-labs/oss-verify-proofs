(* an answer the IMAGE gives is the RUN's answer.  [find_segment] is a
   first-match scan and the run's list is the image's list with the vDSO pair appended ([Run.run_segments]), so
   every HIT in the image is the same hit in the run.  These lemmas carry the kits' closed image-level checks to the
   open run list (whose vDSO tail mentions the launch's input / stack top / mmap base). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import StreamSim.
Import ListNotations.

Lemma find_segment_app_hit : forall segs t a n s,
  find_segment segs a n = Some s -> find_segment (segs ++ t) a n = Some s.
Proof.
  induction segs as [|g r IH]; intros t a n s H; simpl in *; [discriminate|].
  revert H; destruct (_ && _); intro H; [exact H | apply IH; exact H].
Qed.

Lemma fetch_word_run_hit : forall segs inp sp mb pc w,
  fetch_word segs pc = Some w -> fetch_word (run_segments segs inp sp mb) pc = Some w.
Proof.
  intros segs inp sp mb pc w.
  unfold fetch_word, code_read, run_segments.
  destruct (negb _); [exact (fun H => H)|].
  destruct (find_segment segs _ _) eqn:E; [|intros H; simpl in H; discriminate H].
  rewrite (find_segment_app_hit _ _ _ _ _ E). exact (fun H => H).
Qed.

Lemma wseg_ok_app : forall segs t a n,
  wseg_ok segs a n = true -> wseg_ok (segs ++ t) a n = true.
Proof.
  intros segs t a n; revert a; induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [wseg_ok] in *.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:E; [|discriminate].
  rewrite (find_segment_app_hit _ _ _ _ _ E).
  apply andb_true_iff in H as [H1 H2]. rewrite H1. apply IH. exact H2.
Qed.

Lemma wseg_ok_run : forall segs inp sp mb a n,
  wseg_ok segs a n = true -> wseg_ok (run_segments segs inp sp mb) a n = true.
Proof. intros. unfold run_segments. apply wseg_ok_app. assumption. Qed.

(* ========================================================================= *)
(* MISSES.  A MISS in the  *)
(* image is a miss in the run only OFF the vDSO pair.  The pair lies in       *)
(* [vdso_top - vdso_len, vdso_top) (Run.vdso_segments' own placement), below  *)
(* the ruled stack window [sp - 6144513, sp); it is read-only ("r--").        *)
(* ========================================================================= *)

Open Scope Z_scope.

Lemma find_segment_app_miss : forall segs t a n,
  find_segment segs a n = None -> find_segment (segs ++ t) a n = find_segment t a n.
Proof.
  induction segs as [|g r IH]; intros t a n H; simpl in *; [reflexivity|].
  revert H; destruct (_ && _); intro H; [discriminate | apply IH; exact H].
Qed.

Lemma find_segment_in_list : forall l a n s, find_segment l a n = Some s -> In s l.
Proof.
  induction l as [|g r IH]; intros a n s H; simpl in *; [discriminate|].
  revert H; destruct (_ && _); intro H; [left; congruence | right; exact (IH _ _ _ H)].
Qed.

(** The top of the pair: Run.vdso_segments' own [top]. *)
Definition vdso_top (sp mb : word) : Z :=
  page_round_down_Z (Z.min (bv_unsigned mb) (page_round_down_Z (bv_unsigned sp - stack_max_size))).

(** [a, a + n) is off the pair. *)
Definition off_vdso (inp : ProcInput) (sp mb : word) (a n : Z) : Prop :=
  (* route (A): the first disjunct is the launch with NO pair (Run.vdso_segments' own [base <
     page_size] arm), where the kernel's ledger reserves nothing either *)
  vdso_top sp mb - vdso_len (in_kernel inp) < page_size
  \/ a + n <= vdso_top sp mb - vdso_len (in_kernel inp) \/ vdso_top sp mb <= a.

(** a sub-range of an off range is off. *)
Lemma off_vdso_sub : forall inp sp mb a n x k, off_vdso inp sp mb a n -> a <= x -> x + k <= a + n ->
  off_vdso inp sp mb x k.
Proof. intros inp sp mb a n x k H H1 H2. unfold off_vdso in *. lia. Qed.

Local Transparent vdso_segments.

Lemma vdso_segments_none_out : forall kb sp mb a n, 0 < n ->
  (vdso_top sp mb - vdso_len kb < page_size \/ a + n <= vdso_top sp mb - vdso_len kb \/ vdso_top sp mb <= a) ->
  find_segment (vdso_segments kb sp mb) a n = None.
Proof.
  intros kb sp mb a n Hn Hout.
  (* draft: vdso_segments takes its top from vdso_pair_top and its text base from
     bv_unsigned (vdso_text_base kb sp mb); unfold both so the old fold matches, and unwrap the text base. *)
  unfold vdso_segments, vdso_text_base, vdso_pair_top. cbv zeta. fold (vdso_top sp mb).
  destruct (Z.ltb_spec0 (vdso_top sp mb - vdso_len kb) page_size) as [Hb|Hb]; [reflexivity|].
  pose proof (vdso_text_pages_pos kb).
  assert (Htop : vdso_top sp mb <= 2 ^ 64).
  { unfold vdso_top, page_round_down_Z, stack_max_size, page_size.
    assert (Hmb : 0 <= bv_unsigned mb < 2 ^ 64) by exact (bv_unsigned_in_range _ mb).
    pose proof (Z.le_min_l (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)).
    pose proof (Z.mul_div_le (Z.min (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)) 4096
                  ltac:(lia)).
    lia. }
  unfold vdso_len in *. unfold vdso_vvar_pages, page_size in *.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  cbn [find_segment seg_base seg_size].
  rewrite !Z2N.id by lia.
  repeat match goal with |- context [Z.leb ?x ?y] => destruct (Z.leb_spec0 x y) end;
    simpl; first [reflexivity | exfalso; lia].
Qed.

(** The pair is no reservation of the binary: [init_config (run_segments ..)]'s model reserves the image's
    segments only (TopLevel.run_segments_reserved, here under its own name). *)
Lemma segments_reserved_run : forall segs inp (sp mbase : word),
  segments_reserved (run_segments segs inp sp mbase) = segments_reserved segs.
Proof.
  intros segs inp sp mbase. unfold segments_reserved, run_segments.
  rewrite list_basics.list.filter_app.
  match goal with |- context [?F (vdso_segments ?kb ?s ?m)] =>
    replace (F (vdso_segments kb s m)) with (@nil Segment)
      by (unfold vdso_segments; cbv zeta; match goal with |- context [if ?c then _ else _] => destruct c end;
          reflexivity)
  end.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma vdso_segments_not_writable : forall kb sp mb s,
  In s (vdso_segments kb sp mb) -> seg_writable s = false.
Proof.
  intros kb sp mb s H. unfold vdso_segments in H. cbv zeta in H. revert H.
  destruct (_ <? _)%Z; intro H; [contradiction|].
  destruct H as [<- | [<- | []]]; reflexivity.
Qed.

Global Opaque vdso_segments.

Lemma run_find_segment_none : forall segs inp sp mb a n, 0 < n ->
  find_segment segs a n = None -> off_vdso inp sp mb a n ->
  find_segment (run_segments segs inp sp mb) a n = None.
Proof.
  intros segs inp sp mb a n Hn H Hoff. unfold run_segments.
  rewrite (find_segment_app_miss _ _ _ _ H). apply vdso_segments_none_out; assumption.
Qed.

(** The stack side: the ruled window [sp - 6144513, sp) lies above the pair. *)
Lemma vdso_top_below_window : forall sp mb, vdso_top sp mb <= bv_unsigned sp - 6144513.
Proof.
  intros sp mb. unfold vdso_top, page_round_down_Z, stack_max_size, page_size.
  pose proof (Z.le_min_r (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)).
  pose proof (Z.mul_div_le (bv_unsigned sp - 8 * 1024 * 1024) 4096 ltac:(lia)).
  pose proof (Z.mul_div_le (Z.min (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)) 4096
                ltac:(lia)).
  lia.
Qed.

Lemma off_vdso_window : forall inp sp mb a n, bv_unsigned sp - 6144513 <= a -> off_vdso inp sp mb a n.
Proof. intros. right; right. pose proof (vdso_top_below_window sp mb). lia. Qed.

(** Route (A)'s link: the kernel's ledger form.  A range free of [State.vdso_reserved kb top] (what KLink's
    [kl_mres] + [kl_vin] give for any live mapping) is off the pair, when [top] is the run's own top. *)
Lemma off_vdso_of_region_free : forall inp sp mb a n,
  0 < n -> 0 <= a -> a + n < 2 ^ 64 ->
  region_free (vdso_reserved (in_kernel inp) (vdso_top sp mb)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  off_vdso inp sp mb a n.
Proof.
  intros inp sp mb a n Hn Ha Han Hfree. unfold off_vdso.
  pose proof (vdso_text_pages_pos (in_kernel inp)). pose proof (vdso_text_pages_le (in_kernel inp)).
  unfold vdso_reserved in Hfree. cbv zeta in Hfree.
  destruct (Z.ltb_spec0 (vdso_top sp mb - vdso_len (in_kernel inp)) page_size) as [Hb|Hb]; [left; exact Hb|].
  right. unfold vdso_len, vdso_vvar_pages, page_size in *.
  assert (Htop : vdso_top sp mb <= 2 ^ 64).
  { unfold vdso_top, page_round_down_Z, stack_max_size, page_size.
    assert (Hmb : 0 <= bv_unsigned mb < 2 ^ 64) by exact (bv_unsigned_in_range _ mb).
    pose proof (Z.le_min_l (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)).
    pose proof (Z.mul_div_le (Z.min (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)) 4096
                  ltac:(lia)).
    lia. }
  cbn [region_free] in Hfree. apply andb_prop in Hfree as [H1 Hfree]. apply andb_prop in Hfree as [H2 _].
  apply negb_true_iff in H1. apply negb_true_iff in H2. unfold iv_overlap in H1, H2.
  rewrite !bv_unsigned_Z_to_bv_u64 in H1, H2 by (unfold two_pow_64; lia).
  apply andb_false_iff in H1. apply andb_false_iff in H2.
  destruct H1 as [H1|H1]; apply Z.ltb_ge in H1; destruct H2 as [H2|H2]; apply Z.ltb_ge in H2; lia.
Qed.

(** Route (A)'s carrier: the pair as ONE [lo, hi) range for a decision's [avoid] list (Lib/Decode [avoids]), empty
    when the launch has no pair. *)
Definition vdso_avoid (inp : ProcInput) (sp mb : word) : list (Z * Z) :=
  let top := vdso_top sp mb in
  let base := top - vdso_len (in_kernel inp) in
  if base <? page_size then [] else [(base, top)].

Lemma off_vdso_of_avoids : forall inp sp mb a n,
  forallb (fun iv => (a + n <=? fst iv) || (snd iv <=? a)) (vdso_avoid inp sp mb) = true ->
  off_vdso inp sp mb a n.
Proof.
  intros inp sp mb a n H. unfold vdso_avoid, off_vdso in *. cbv zeta in H.
  destruct (Z.ltb_spec0 (vdso_top sp mb - vdso_len (in_kernel inp)) page_size) as [Hb|Hb]; [left; exact Hb|].
  right. cbn [forallb fst snd] in H. rewrite andb_true_r in H.
  apply orb_true_iff in H as [H|H]; apply Z.leb_le in H; [left|right]; exact H.
Qed.

(** the pair as its TWO reserved ranges, mapped to [lo, hi)
    -- Spec/KLink's [vdso_avoid_of (in_kernel inp) sp mb] spelled without KLink (its [elo] / [ehi] / [vdso_top_of]
    unfold to these).  An answer that avoids both ranges is off the pair: they are adjacent and both non-empty. *)
Definition vdso_avoid2 (inp : ProcInput) (sp mb : word) : list (Z * Z) :=
  map (fun e : word * word => (bv_unsigned (fst e), bv_unsigned (fst e) + bv_unsigned (snd e)))
      (vdso_reserved (in_kernel inp) (vdso_top sp mb)).

Lemma off_vdso_of_avoids2 : forall inp sp mb a n, 0 < n ->
  forallb (fun iv => (a + n <=? fst iv) || (snd iv <=? a)) (vdso_avoid2 inp sp mb) = true ->
  off_vdso inp sp mb a n.
Proof.
  intros inp sp mb a n Hn H. unfold vdso_avoid2, off_vdso in *.
  pose proof (vdso_text_pages_pos (in_kernel inp)). pose proof (vdso_text_pages_le (in_kernel inp)).
  unfold vdso_reserved in H. cbv zeta in H.
  destruct (Z.ltb_spec0 (vdso_top sp mb - vdso_len (in_kernel inp)) page_size) as [Hb|Hb]; [left; exact Hb|].
  right. unfold vdso_len, vdso_vvar_pages, page_size in *.
  assert (Htop : vdso_top sp mb <= 2 ^ 64).
  { unfold vdso_top, page_round_down_Z, stack_max_size, page_size.
    assert (Hmb : 0 <= bv_unsigned mb < 2 ^ 64) by exact (bv_unsigned_in_range _ mb).
    pose proof (Z.le_min_l (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)).
    pose proof (Z.mul_div_le (Z.min (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)) 4096
                  ltac:(lia)).
    lia. }
  cbn [map forallb fst snd] in H. rewrite andb_true_r in H. apply andb_prop in H as [Hv1 Hv2].
  rewrite !bv_unsigned_Z_to_bv_u64 in Hv1, Hv2 by (unfold two_pow_64; lia).
  apply orb_true_iff in Hv1 as [Hv1|Hv1]; apply Z.leb_le in Hv1;
    apply orb_true_iff in Hv2 as [Hv2|Hv2]; apply Z.leb_le in Hv2; lia.
Qed.

(** the pair in the malloc MODEL's (base, LENGTH)
    format -- Spec/KLink's [vdso_resv_of (in_kernel inp) sp mb] (= [map wwZ (vdso_reserved kb (vdso_top_of sp mb))])
    spelled without KLink.  A range that the model's [ranges_free] keeps clear of it is off the pair: the predicate
    below is [ranges_free] / [iv_disjoint] (Spec/Malloc) unfolded. *)
Definition vdso_resvZ (inp : ProcInput) (sp mb : word) : list (Z * Z) :=
  map (fun e : word * word => (bv_unsigned (fst e), bv_unsigned (snd e)))
      (vdso_reserved (in_kernel inp) (vdso_top sp mb)).

Lemma off_vdso_of_resv_free : forall inp sp mb a n, 0 < n ->
  forallb (fun bm : Z * Z => (a + n <=? fst bm) || (fst bm + snd bm <=? a)) (vdso_resvZ inp sp mb) = true ->
  off_vdso inp sp mb a n.
Proof.
  intros inp sp mb a n Hn H. unfold vdso_resvZ, off_vdso in *.
  pose proof (vdso_text_pages_pos (in_kernel inp)). pose proof (vdso_text_pages_le (in_kernel inp)).
  unfold vdso_reserved in H. cbv zeta in H.
  destruct (Z.ltb_spec0 (vdso_top sp mb - vdso_len (in_kernel inp)) page_size) as [Hb|Hb]; [left; exact Hb|].
  right. unfold vdso_len, vdso_vvar_pages, page_size in *.
  assert (Htop : vdso_top sp mb <= 2 ^ 64).
  { unfold vdso_top, page_round_down_Z, stack_max_size, page_size.
    assert (Hmb : 0 <= bv_unsigned mb < 2 ^ 64) by exact (bv_unsigned_in_range _ mb).
    pose proof (Z.le_min_l (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)).
    pose proof (Z.mul_div_le (Z.min (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)) 4096
                  ltac:(lia)).
    lia. }
  cbn [map forallb fst snd] in H. rewrite andb_true_r in H. apply andb_prop in H as [Hv1 Hv2].
  rewrite !bv_unsigned_Z_to_bv_u64 in Hv1, Hv2 by (unfold two_pow_64; lia).
  apply orb_true_iff in Hv1 as [Hv1|Hv1]; apply Z.leb_le in Hv1;
    apply orb_true_iff in Hv2 as [Hv2|Hv2]; apply Z.leb_le in Hv2; lia.
Qed.

(** every entry of the pair list has a POSITIVE length (vvar 4 pages, text
    1..16 pages), as the image's literal entries do, so a region grown by one page past a disjoint old part stays
    disjoint from it. *)
Lemma vdso_resvZ_pos : forall inp sp mb b n, In (b, n) (vdso_resvZ inp sp mb) -> 0 < n.
Proof.
  intros inp sp mb b n H. unfold vdso_resvZ, vdso_reserved in H. cbv zeta in H.
  pose proof (vdso_text_pages_pos (in_kernel inp)). pose proof (vdso_text_pages_le (in_kernel inp)).
  revert H; destruct (_ <? _); intro H; cbn [map In] in H; [contradiction|].
  unfold vdso_vvar_pages, page_size in H.
  destruct H as [H|[H|[]]]; inversion H; subst;
    rewrite bv_unsigned_Z_to_bv_u64 by (unfold two_pow_64; lia); lia.
Qed.

(** The writable view needs NO pair premise: the pair is read-only, so an image miss leaves the overlay's answer. *)
Lemma run_wview_miss : forall segs inp sp mb m x,
  find_segment segs (bv_unsigned x) 1 = None ->
  wview (run_segments segs inp sp mb) m x = m x.
Proof.
  intros segs inp sp mb m x H. unfold wview. destruct (m x); [reflexivity|].
  unfold run_segments. rewrite (find_segment_app_miss _ _ _ _ H).
  destruct (find_segment (vdso_segments _ _ _) _ _) as [s|] eqn:E; [|reflexivity].
  rewrite (vdso_segments_not_writable _ _ _ s (find_segment_in_list _ _ _ _ E)). reflexivity.
Qed.

Lemma run_memory_read_miss : forall segs inp sp mb x n, (1 <= Z.of_N n) ->
  find_segment segs (bv_unsigned x) (Z.of_N n) = None -> off_vdso inp sp mb (bv_unsigned x) (Z.of_N n) ->
  memory_read (run_segments segs inp sp mb) x n = None.
Proof.
  intros segs inp sp mb x n Hn H Hoff. unfold memory_read.
  rewrite (run_find_segment_none segs inp sp mb (bv_unsigned x) (Z.of_N n) ltac:(lia) H Hoff). reflexivity.
Qed.
