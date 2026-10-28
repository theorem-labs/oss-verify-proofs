(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2 X1bn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ra X1qu X1ri X1rj X1r3 X1r4
X1og X1oi X1nt X1qz X1r0 X1rg X1rh X1re X1nv X1rf X1r1 X1od X1oe
X1rm X1o8 X1o9 X1r6 X1ns.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevel.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Definition so_ok (so : stdout_st) : Prop := zlength (so_buf so) <= STDOUT_BUFSIZ.
Definition Gso : PState -> Model -> Prop := fun s _ => so_ok (ps_so s).

Lemma frame_ok_Gso : frame_ok Gso.
Proof. intros s s' mo mo' _ Hso _ H. unfold Gso in *. rewrite Hso. exact H. Qed.

Definition GI (X : list bptr) : assn PState := OWN X Gso.

Lemma GI_minv : forall X s mo, GI X s mo -> minv mo /\ m_halted mo = None.
Proof. intros X s mo H. exact (OWN_minv _ _ _ _ H). Qed.

Lemma GI_fds : forall X s mo mo', GI X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> GI X s mo'.
Proof. intros X s mo mo' H Hvm Hmi Hh. eapply OWN_vmmaps; eauto. exact (OWN_G _ _ _ _ H). Qed.

Lemma GI_perm : forall X Y s mo, Permutation X Y -> GI X s mo -> GI Y s mo.
Proof. intros. eapply OWN_perm; eauto. Qed.

Lemma GI_after_node : forall X s mo n rsp mo' evs,
GI X s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo ->
match n with NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => True end ->
GI X s mo'.
Proof.
intros X s mo n rsp mo' evs Ho Hst Hvm Hfl. destruct (GI_minv _ _ _ Ho) as [Hmi Hh].
destruct (minv_preserved n mo rsp mo' evs Hfl Hmi Hh Hst) as [Hh' Hmi']. eapply GI_fds; eauto.
Qed.

Lemma GI_set_so : forall X s mo v, GI X s mo -> so_ok v -> GI X (set_so_ps v s) mo.
Proof. intros X s mo v H Hv. eapply OWN_other; [exact H|reflexivity|reflexivity| exact Hv]. Qed.

Lemma GI_so_ok : forall X s mo, GI X s mo -> so_ok (ps_so s).
Proof. intros X s mo H. exact (OWN_G _ _ _ _ H). Qed.

Definition reall (p : bptr) : Prop := ptop p = true.

Lemma RBIG_REALL_MIN : X1oi.RBIG = REALL_MIN.
Proof. reflexivity. Qed.

Lemma raw_malloc_GI : forall X n, 0 <= n ->
mspec (GI X) (raw_malloc n) (fun r s mo => match r with Some p => GI (p :: X) s mo | None => GI X s mo end).
Proof.
intros X n Hn. eapply mspec_post; [apply raw_malloc_spec; [apply frame_ok_Gso| exact Hn]|].
intros [p|] s mo H; [exact (proj1 H)| exact H].
Qed.

Lemma raw_malloc_GI63 : forall X n, 0 <= n ->
mspec (GI X) (raw_malloc n) (fun r s mo => match r with Some p => GI (p :: X) s mo /\ n < 2^63 | None => GI X s mo end).
Proof.
intros X n Hn. eapply mspec_post; [apply raw_malloc_spec; [apply frame_ok_Gso| exact Hn]|].
intros [p|] s mo H; [| exact H]. destruct H as (H1 & H2 & _). auto.
Qed.

Lemma raw_malloc_GI_big : forall X n, REALL_MIN <= n ->
mspec (GI X) (raw_malloc n) (fun r s mo => match r with Some p => GI (p :: X) s mo /\ reall p | None => GI X s mo end).
Proof.
intros X n Hn. eapply mspec_post; [apply raw_malloc_spec; [apply frame_ok_Gso| unfold REALL_MIN in Hn; lia]|].
intros [p|] s mo H; [| exact H]. destruct H as (H1 & _ & H3). split; [exact H1|]. apply H3. rewrite RBIG_REALL_MIN. exact Hn.
Qed.

Lemma raw_free_GI : forall X p, mspec (GI (p :: X)) (raw_free p) (fun _ => GI X).
Proof. intros. apply raw_free_spec. apply frame_ok_Gso. Qed.

Lemma raw_calloc_GI : forall X n m, 0 <= n -> 0 <= m ->
mspec (GI X) (raw_calloc n m) (fun r s mo => match r with Some p => GI (p :: X) s mo | None => GI X s mo end).
Proof.
intros X n m Hn Hm. eapply mspec_post; [apply raw_calloc_spec; [apply frame_ok_Gso| exact Hn| exact Hm]|].
intros [p|] s mo H; [exact (proj1 H)| exact H].
Qed.

Lemma raw_calloc_GI_big : forall X n m, 0 <= n -> 0 <= m -> REALL_MIN <= n * m ->
mspec (GI X) (raw_calloc n m) (fun r s mo => match r with Some p => GI (p :: X) s mo /\ reall p | None => GI X s mo end).
Proof.
intros X n m Hn Hm Hbig. eapply mspec_post; [apply raw_calloc_spec; [apply frame_ok_Gso| exact Hn| exact Hm]|].
intros [p|] s mo H; [| exact H]. destruct H as (H1 & _ & H3). split; [exact H1|]. apply H3. rewrite RBIG_REALL_MIN. lia.
Qed.

Lemma raw_realloc_GI : forall X p n, reall p -> REALL_MIN <= n < X1r2.MMAP_THRESHOLD ->
mspec (GI (p :: X)) (raw_realloc p n)
(fun r s mo => match r with Some q => GI (q :: X) s mo /\ reall q | None => GI (p :: X) s mo end).
Proof.
intros X p n Hp Hn. eapply mspec_post.
{ apply raw_realloc_spec; [apply frame_ok_Gso| exact Hp|]. unfold REALL_MIN, X1r2.MMAP_THRESHOLD in Hn. unfold X1qu.MMAP_THRESHOLD. lia. }
intros [q|] s mo H; [| exact H]. destruct H as [H1 H2]. split; [exact H1|]. apply H2. rewrite RBIG_REALL_MIN. lia.
Qed.

Lemma raw_free_opt_GI : forall X (o : option bptr),
mspec (GI (match o with Some p => p :: X | None => X end)) (raw_free_opt o) (fun _ => GI X).
Proof. intros. apply raw_free_opt_spec. apply frame_ok_Gso. Qed.

Lemma target_alloc_init_GI : forall X bm, mspec (GI X) (target_alloc_init (St:=PState) bm) (fun _ => GI X).
Proof. intros. unfold target_alloc_init. apply mspec_ret. intros s mo H; exact H. Qed.
Lemma target_alloc_count_GI : forall X, mspec (GI X) (target_alloc_count (St:=PState)) (fun _ => GI X).
Proof. intros. unfold target_alloc_count. apply mspec_ret. intros s mo H; exact H. Qed.

Lemma stdio_writev_GI : forall X fd buf s, zlength buf + zlength s <= WRITEV_MAX ->
mspec (GI X) (stdio_writev fd buf s) (fun _ => GI X).
Proof. intros X fd buf s H. apply stdio_writev_mspec. exact H. Qed.

Lemma upd_so_GI : forall X f,
mspec (fun s mo => GI X s mo /\ so_ok (f (ps_so s))) (upd_so ps_so set_so_ps f)
(fun _ s mo => GI X s mo /\ exists so0, ps_so s = f so0).
Proof.
intros X f. unfold upd_so. apply mspec_upd'. intros s mo [Ho Hok]. split; [apply GI_set_so; [exact Ho| exact Hok]|]. cbn. eauto.
Qed.

Lemma rd_so_GI : forall (P : assn PState), mspec P (rd_so ps_so) (fun so s mo => P s mo /\ so = ps_so s).
Proof.
intros P. unfold rd_so. eapply mspec_bind; [apply mspec_get|]. intros s0. apply mspec_ret.
intros s mo [-> Ho]. split; [exact Ho| reflexivity].
Qed.

Lemma stdout_stdio_write_GI : forall X s, zlength s <= WRITEV_MAX - STDOUT_BUFSIZ ->
mspec (GI X) (stdout_stdio_write ps_so set_so_ps s) (fun _ s mo => GI X s mo /\ so_buf (ps_so s) = []).
Proof.
intros X s Hs. unfold stdout_stdio_write. eapply mspec_bind; [apply (rd_so_GI (GI X))|]. intros so.
apply mspec_pointwise. intros s1 mo1 [Ho ->]. pose proof (GI_so_ok _ _ _ Ho) as Hok. unfold so_ok in Hok.
eapply mspec_seq. { eapply mspec_pre; [apply stdio_writev_GI; lia|]. intros s' mo' [-> ->]; exact Ho. }
intros _. eapply mspec_conseq; [apply upd_so_GI| |].
- intros s' mo' Ho'. split; [exact Ho'|]. unfold so_ok, zlength, STDOUT_BUFSIZ; cbn; lia.
- intros [] s' mo' [Ho' [so0 ->]]. split; [exact Ho'| reflexivity].
Qed.

Lemma stdout_writefn_GI : forall X s, zlength s <= WRITEV_MAX - STDOUT_BUFSIZ ->
mspec (GI X) (stdout_writefn ps_so set_so_ps s) (fun _ s mo => GI X s mo /\ so_buf (ps_so s) = []).
Proof.
intros X s Hs. unfold stdout_writefn. eapply mspec_bind; [apply (rd_so_GI (GI X))|]. intros so.
apply mspec_pointwise. intros s1 mo1 [Ho ->].
eapply mspec_seq with (R := GI X).
- destruct (so_first (ps_so s1)).
+ eapply mspec_seq.
{ eapply mspec_conseq; [apply upd_so_GI| |]; [intros s' mo' [-> ->]; split; [exact Ho| exact (GI_so_ok _ _ _ Ho)]| intros [] s' mo' [H _]; exact H]. }
intros _. eapply mspec_bind with (Q1 := fun r s mo => GI X s mo /\ match r with SErr _ => True | SVal _ => False end).
* apply mspec_sys. intros s' mo' Ho'. split; [exact I|]. intros rsp mo'' evs Hst.
pose proof (nstep_dec_ioctl 1 TIOCGWINSZ mo' rsp mo'' evs Hst) as (Hdec & -> & _).
eexists. split; [exact Hdec|]. split; [exact Ho'| exact I].
* intros [e|v]; [| intros s' mo' [_ []]].
eapply mspec_conseq; [apply upd_so_GI| |]; [intros s' mo' [H _]; split; [exact H| exact (GI_so_ok _ _ _ H)]| intros [] s' mo' [H _]; exact H].
+ apply mspec_ret. intros s' mo' [-> ->]; exact Ho.
- intros _. apply stdout_stdio_write_GI. exact Hs.
Qed.

Lemma zlength_skipn_le : forall {A} n (l : list A), zlength (skipn n l) <= zlength l.
Proof. intros. unfold zlength. rewrite length_skipn. lia. Qed.
Lemma zlength_firstn_le : forall {A} n (l : list A), zlength (firstn n l) <= zlength l.
Proof. intros. unfold zlength. rewrite firstn_length. lia. Qed.

Lemma stdout_towrite_GI : forall X, mspec (GI X) (stdout_towrite ps_so set_so_ps) (fun _ => GI X).
Proof.
intros X. unfold stdout_towrite. eapply mspec_conseq; [apply upd_so_GI| |].
- intros s mo Ho. split; [exact Ho|]. pose proof (GI_so_ok _ _ _ Ho) as Hok. destruct (so_active (ps_so s)); [exact Hok|].
unfold so_ok, zlength, STDOUT_BUFSIZ; cbn; lia.
- intros [] s mo [H _]; exact H.
Qed.

Definition OUT_MAX : Z := 4096.

Lemma stdout_fwritex_GI : forall X s, zlength s <= OUT_MAX ->
mspec (GI X) (stdout_fwritex ps_so set_so_ps s) (fun _ => GI X).
Proof.
intros X s Hs. unfold stdout_fwritex. unfold OUT_MAX in Hs.
eapply mspec_seq; [apply stdout_towrite_GI|]. intros _.
eapply mspec_bind; [apply (rd_so_GI (GI X))|]. intros so.
apply mspec_pointwise. intros s1 mo1 [Ho ->]. pose proof (GI_so_ok _ _ _ Ho) as Hok. unfold so_ok, STDOUT_BUFSIZ in Hok.
apply mspec_if; intros C1.
{ eapply mspec_conseq; [apply stdout_writefn_GI; unfold WRITEV_MAX, STDOUT_BUFSIZ; lia| intros s' mo' [-> ->]; exact Ho| intros [] s' mo' [H _]; exact H]. }
apply Z.ltb_ge in C1.
destruct (so_lbf_nl (ps_so s1)).
- set (i := after_last_nl s).
eapply mspec_seq with (R := fun s' mo => GI X s' mo /\ zlength (so_buf (ps_so s')) + zlength (skipn (Z.to_nat i) s) <= STDOUT_BUFSIZ).
+ destruct (0 <? i).
* eapply mspec_conseq; [apply stdout_writefn_GI; pose proof (zlength_firstn_le (Z.to_nat i) s); unfold WRITEV_MAX, STDOUT_BUFSIZ; lia| intros s' mo' [-> ->]; exact Ho|].
intros [] s' mo' [H Hb]. split; [exact H|]. rewrite Hb. pose proof (zlength_skipn_le (Z.to_nat i) s). unfold zlength, STDOUT_BUFSIZ in *; cbn; lia.
* apply mspec_ret. intros s' mo' [-> ->]. split; [exact Ho|]. pose proof (zlength_skipn_le (Z.to_nat i) s). unfold STDOUT_BUFSIZ in *; lia.
+ intros _. eapply mspec_conseq; [apply upd_so_GI| |]; [| intros [] s' mo' [H _]; exact H].
intros s' mo' [H Hb]. split; [exact H|]. unfold so_ok. cbn. rewrite zlength_app. exact Hb.
- eapply mspec_conseq; [apply upd_so_GI| |]; [| intros [] s' mo' [H _]; exact H].
intros s' mo' [-> ->]. split; [exact Ho|]. unfold so_ok. cbn. rewrite zlength_app. unfold STDOUT_BUFSIZ in *; lia.
Qed.

Lemma out_pieces_GI : forall X ps, Forall (fun p => zlength p <= OUT_MAX) ps ->
mspec (GI X) (out_pieces ps_so set_so_ps ps) (fun _ => GI X).
Proof.
intros X ps Hps. induction Hps as [|p ps Hp Hps IH]; cbn [out_pieces].
- apply mspec_ret. intros s mo H; exact H.
- eapply mspec_seq; [apply stdout_fwritex_GI; exact Hp|]. intros _. exact IH.
Qed.

Lemma stdout_vprintf_GI : forall X ps, Forall (fun p => zlength p <= OUT_MAX) ps ->
mspec (GI X) (stdout_vprintf ps_so set_so_ps ps) (fun _ => GI X).
Proof.
intros X ps Hps. unfold stdout_vprintf. eapply mspec_seq; [apply stdout_towrite_GI|]. intros _. apply out_pieces_GI. exact Hps.
Qed.

Lemma stdout_exit_flush_GI : forall X, mspec (GI X) (stdout_exit_flush ps_so set_so_ps) (fun _ => GI X).
Proof.
intros X. unfold stdout_exit_flush. eapply mspec_bind; [apply (rd_so_GI (GI X))|]. intros so.
apply mspec_pointwise. intros s1 mo1 [Ho ->]. destruct (0 <? _).
- eapply mspec_conseq; [apply stdout_writefn_GI; unfold zlength, WRITEV_MAX, STDOUT_BUFSIZ; cbn; lia| intros s' mo' [-> ->]; exact Ho| intros [] s' mo' [H _]; exact H].
- apply mspec_ret. intros s' mo' [-> ->]; exact Ho.
Qed.

Definition ERR_MAX : Z := WRITEV_MAX - INTERNAL_BUFSIZ.

Lemma stderr_fprintf_GI : forall X ps, Forall (fun p => zlength p <= ERR_MAX) ps ->
mspec (GI X) (stderr_fprintf ps) (fun _ => GI X).
Proof. intros X ps Hps. apply stderr_fprintf_mspec. exact Hps. Qed.

Lemma stderr_fwrite_GI : forall X s, zlength s <= WRITEV_MAX -> mspec (GI X) (stderr_fwrite s) (fun _ => GI X).
Proof. intros X s Hs. apply stderr_fwrite_mspec. exact Hs. Qed.

Lemma dec_text_aux_length : forall fuel x acc, (length (dec_text_aux fuel x acc) <= fuel + length acc)%nat.
Proof.
induction fuel as [|fuel IH]; intros x acc; cbn [dec_text_aux]; [lia|].
destruct (x =? 0); [cbn; lia|]. specialize (IH (x / 10) (48 + x mod 10 :: acc)). cbn [length] in IH. lia.
Qed.

Ltac zlen_lit := unfold zlength; cbn; lia.

Lemma pieces_emit_short : forall rc, Forall (fun p => zlength p <= OUT_MAX) (pieces_emit rc).
Proof.
intros rc. unfold pieces_emit, OUT_MAX.
repeat (apply Forall_app; split); repeat constructor; try zlen_lit.
- destruct (rc <? 0); zlen_lit.
- destruct (rc =? 0); repeat constructor; zlen_lit.
- destruct (rc =? 0); [zlen_lit|]. pose proof (dec_text_aux_length 20 (Z.abs rc) []). unfold zlength. cbn [length] in H. lia.
Qed.

Lemma io_emit_GI : forall X rc, mspec (GI X) (io_emit rc) (fun _ => GI X).
Proof. intros X rc. unfold io_emit, s_emit. apply stdout_vprintf_GI. apply pieces_emit_short. Qed.

Lemma io_notify_GI : forall X msg, msg_ok msg -> mspec (GI X) (io_notify msg) (fun _ => GI X).
Proof.
intros X msg Hm. unfold io_notify, s_notify. apply stderr_fprintf_GI. unfold pieces_notify, msg_ok, MSG_MAX, ERR_MAX, WRITEV_MAX, INTERNAL_BUFSIZ in *.
repeat constructor; try zlen_lit. lia.
Qed.

Lemma io_warning_GI : forall X msg, msg_ok msg -> mspec (GI X) (io_warning msg) (fun _ => GI X).
Proof.
intros X msg Hm. unfold io_warning, s_warning. apply stderr_fprintf_GI. unfold pieces_warning, msg_ok, MSG_MAX, ERR_MAX, WRITEV_MAX, INTERNAL_BUFSIZ in *.
repeat constructor; try zlen_lit. lia.
Qed.

Lemma io_diag_GI : forall X d, X1o9.diag_ok d -> mspec (GI X) (io_diag d) (fun _ => GI X).
Proof.
intros X d Hd. unfold io_diag, s_diag. destruct d; cbn in Hd.
all: try (apply stderr_fprintf_GI; unfold pieces_usage, pieces_cannot_open, pieces_read_error, pieces_too_big, ERR_MAX, WRITEV_MAX, INTERNAL_BUFSIZ;
repeat constructor; try zlen_lit; lia).
all: apply stderr_fwrite_GI; unfold pieces_oom, pieces_short_hdr, pieces_cfg_overrun, WRITEV_MAX; zlen_lit.
Qed.

Lemma io_exit_GI : forall code, mspec (fun s mo => exists X, GI X s mo) (io_exit code) (fun _ _ _ => False).
Proof.
intros code. unfold io_exit, stdio_exit_model. eapply mspec_seq with (R := fun s mo => exists X, GI X s mo).
- apply mspec_exI. intros X. eapply mspec_post; [apply stdout_exit_flush_GI|]. intros a s mo Ho. exists X. exact Ho.
- intros _. apply mspec_sys. intros s mo _. split; [exact I|]. intros rsp mo' evs Hst. destruct (nstep_exit_none _ _ _ _ _ Hst).
Qed.

Lemma startup_GI : forall X, mspec (GI X) startup (fun _ => GI X).
Proof.
intros X. unfold startup. eapply mspec_seq; [|intros _; apply mspec_ret; intros s mo H; exact H].
apply mspec_sys. intros s mo Ho. split; [exact I|]. intros rsp mo' evs Hst.
destruct (GI_minv _ _ _ Ho) as [Hmi Hh].
pose proof (nstep_dec_set_tid mo rsp mo' evs Hmi Hst) as (_ & t & Hdec & _ & Hmo).
exists t. split; [exact Hdec|]. eapply GI_after_node; [exact Ho| exact Hst| | exact I].
destruct Hmo as [[_ ->]|[_ ->]]; [reflexivity|]. autorewrite with model. reflexivity.
Qed.

Lemma size_ok_SOME_MAX : forall n, n < X1nv.SOME_MAX -> X1qu.size_overflows n = false.
Proof. intros n H. unfold X1qu.size_overflows. apply Z.leb_gt. unfold X1nv.SOME_MAX in H. lia. Qed.
Lemma raw_malloc_someG : forall n, 0 <= n < X1nv.SOME_MAX -> mspecA (raw_malloc n) (fun r => r <> None).
Proof. intros n [_ H]. apply X1ns.raw_malloc_some. apply size_ok_SOME_MAX. exact H. Qed.
Lemma raw_calloc_someG : forall n m, 0 <= n -> 0 <= m -> n * m < X1nv.SOME_MAX -> mspecA (raw_calloc n m) (fun r => r <> None).
Proof. intros n m Hn Hm H. apply X1ns.raw_calloc_some; [exact Hn| exact Hm|]. apply size_ok_SOME_MAX. lia. Qed.
Lemma raw_realloc_someG : forall p n, 0 <= n < X1nv.SOME_MAX -> mspecA (raw_realloc p n) (fun r => r <> None).
Proof. intros p n [_ H]. apply X1ns.raw_realloc_some. apply size_ok_SOME_MAX. exact H. Qed.

Theorem fuzz_one_GI : forall X payload, bytes_ok payload -> mspec (GI X) (fuzz_one payload) (fun _ => GI X).
Proof.
intros X payload Hb. unfold fuzz_one.
apply (LLVMFuzzerTestOneInput_spec GI raw_malloc raw_calloc raw_realloc raw_free io_notify io_warning
raw_calloc_GI reall raw_malloc_GI_big raw_calloc_GI_big raw_realloc_GI raw_free_GI GI_perm
io_notify_GI io_warning_GI raw_malloc_someG raw_calloc_someG raw_realloc_someG X payload Hb).
Qed.

Theorem run_GI : forall X cfg payload, bytes_ok payload -> mspec (GI X) (run cfg payload) (fun _ => GI X).
Proof.
intros X cfg payload Hb. unfold run.
apply (target_run_spec raw_malloc raw_free io_emit fuzz_one GI raw_malloc_GI raw_free_GI io_emit_GI fuzz_one_GI X cfg payload Hb).
Qed.

Lemma prog_with_GI : forall rs argv,
Forall (fun a => zlength a < 2^17) argv -> Forall X1o9.path_arg_ok (tl argv) ->
mspec (GI []) (prog_with rs argv) (fun _ _ _ => False).
Proof.
intros rs argv Hargv Htl. unfold prog_with.
eapply mspec_seq; [apply startup_GI|]. intros _.
eapply mspec_bind.
- eapply (main_model_spec io_diag raw_malloc raw_free rs (target_alloc_init (St:=PState)) run (target_alloc_count (St:=PState)) GI);
first [ exact Hargv | exact Htl | apply raw_malloc_GI63 | apply raw_free_GI | apply GI_perm
| (intros; apply io_diag_GI; assumption) | apply target_alloc_init_GI | apply target_alloc_count_GI
| apply run_GI | apply GI_minv | apply GI_fds ].
- intros code. apply io_exit_GI.
Qed.

Lemma reserved_top_ge : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

Lemma reservedZ_wwZ : forall segs, reservedZ segs = map wwZ (segments_reserved segs).
Proof. intros. unfold reservedZ, wwZ. reflexivity. Qed.

Lemma GI_init : forall segs brk0 mbase sp lim inp,
valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) -> valid_sp sp ->
reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
GI [] (ps_init (bv_unsigned sp - stack_max_size) (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
intros segs brk0 mbase sp lim inp (Hlo & Hhi & Hal) Hpos (Hsl & Hsh & _) Hceil. unfold GI, OWN.
unfold sp_window_lo in Hsl. unfold sp_window_hi in Hsh. unfold alloc_ceiling_lo in Hceil.
split; [|split; [apply List.NoDup_nil| unfold Gso, so_ok; cbn [ps_so ps_init so_buf stdout_init]; unfold zlength, STDOUT_BUFSIZ; cbn; lia]].
exists (led_init (bv_unsigned sp - stack_max_size) (reservedZ segs)). split.
{ apply creach_init. unfold stack_max_size, alloc_ceiling_lo, alloc_ceiling_hi. lia. }
split; [|intros c []].
constructor; rewrite ?m_vmmaps_init_model; cbn -[Z.pow Z.mul Z.add Z.sub init_model].
- apply minv_init.
- apply m_halted_init_model.
- unfold alloc_top, stack_max_size, alloc_ceiling_lo, alloc_ceiling_hi. cbn [vm_init_sp]. lia.
- split; [intros e []| apply pwdisj_nil].
- apply reservedZ_wwZ.
- intros e Hin. pose proof (reserved_top_ge _ _ Hin). unfold ehi. lia.
- unfold PGSZ in *. unfold page_size in Hal. unfold stack_max_size. lia.
- intros b l [].
- intros b l k [].
- apply List.NoDup_nil.
- intros b l H. discriminate.
- split; reflexivity.
Qed.

Lemma argv_Z_short : forall argv, valid_argv argv -> Forall (fun a => zlength a < 2^17) (argv_Z argv).
Proof.
intros argv (_ & _ & HF & _). unfold argv_Z. apply Forall_map. eapply Forall_impl; [|exact HF].
intros a Ha. unfold zlength in *. rewrite length_map. lia.
Qed.

Lemma argv_Z_paths : forall argv, valid_argv argv -> Forall X1o9.path_arg_ok (tl (argv_Z argv)).
Proof.
intros argv (_ & _ & _ & _ & HF). unfold argv_Z. destruct argv as [|a0 rest]; [constructor|]. cbn [map tl] in *.
apply Forall_map. eapply Forall_impl; [|exact HF]. intros a [H1 H2]. unfold X1o9.path_arg_ok.
rewrite map_map, (map_ext _ id), map_id; [split; assumption|]. intros b. apply Z_to_bv_bv_unsigned.
Qed.

Theorem prog_model_ok : forall segs rs pc ph lim en inp,
0 < reserved_top (segments_reserved segs) ->
reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
valid_entry (mkImage segs pc ph) en inp -> valid_input_core inp ->

tsafe nstep no_enomem (prog segs rs (ceil_of en) (in_argv inp)) (mo0 segs lim en inp) ->
leaves_unreachable_m nstep (prog segs rs (ceil_of en) (in_argv inp)) (mo0 segs lim en inp)
/\ tsafe nstep nsafe (prog segs rs (ceil_of en) (in_argv inp)) (mo0 segs lim en inp).
Proof.
intros segs rs pc ph lim [sp brk0 mbase dr] inp Hpos Hceil VE VI Hne.
pose proof (valid_entry_parts _ _ _ _ _ _ _ _ VI VE) as (Hsp & Hbrk & _). pose proof VI as (Hargv & _).
unfold prog, mo0, ceil_of in Hne |- *. cbn [en_brk en_mmap_base en_sp] in Hne |- *.
apply (mspec_program (GI []) (prog_with rs (argv_Z (in_argv inp)))).
- apply prog_with_GI; [apply argv_Z_short; exact Hargv| apply argv_Z_paths; exact Hargv].
- apply GI_init; [exact Hbrk| exact Hpos| exact Hsp| exact Hceil].
- exact Hne.
Qed.

From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.

Local Notation psegs := Plain.M.loaded_segments.
Local Notation usegs := Ubsan.M.loaded_segments.

Lemma reserved_top_psegs : 0 < reserved_top (segments_reserved psegs).
Proof.
unfold segments_reserved, segment_reservation, Plain.M.loaded_segments, Plain_loaded_segments.
cbn [map reserved_top fst snd]. rewrite !Z_to_bv_unsigned.
cbn [seg_base seg_size Plain_segment_000 Plain_segment_001 Plain_segment_002 Plain_segment_003]. vm_compute. reflexivity.
Qed.
Lemma ceil_psegs : reserved_top (segments_reserved psegs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo.
Proof.
unfold segments_reserved, segment_reservation, Plain.M.loaded_segments, Plain_loaded_segments.
cbn [map reserved_top fst snd]. rewrite !Z_to_bv_unsigned.
cbn [seg_base seg_size Plain_segment_000 Plain_segment_001 Plain_segment_002 Plain_segment_003]. vm_compute. discriminate.
Qed.

Lemma sbk_psegs : reserved_top (segments_reserved psegs) + brk_aslr_max + PGSZ <= 2^40.
Proof.
unfold segments_reserved, segment_reservation, Plain.M.loaded_segments, Plain_loaded_segments.
cbn [map reserved_top fst snd]. rewrite !Z_to_bv_unsigned.
cbn [seg_base seg_size Plain_segment_000 Plain_segment_001 Plain_segment_002 Plain_segment_003]. vm_compute. discriminate.
Qed.
Lemma reserved_top_usegs : 0 < reserved_top (segments_reserved usegs).
Proof.
unfold segments_reserved, segment_reservation, Ubsan.M.loaded_segments, Ubsan_loaded_segments.
cbn [map reserved_top fst snd]. rewrite !Z_to_bv_unsigned.
cbn [seg_base seg_size Ubsan_segment_000 Ubsan_segment_001 Ubsan_segment_002 Ubsan_segment_003].
vm_compute. reflexivity.
Qed.
Lemma ceil_usegs : reserved_top (segments_reserved usegs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo.
Proof.
unfold segments_reserved, segment_reservation, Ubsan.M.loaded_segments, Ubsan_loaded_segments.
cbn [map reserved_top fst snd]. rewrite !Z_to_bv_unsigned.
cbn [seg_base seg_size Ubsan_segment_000 Ubsan_segment_001 Ubsan_segment_002 Ubsan_segment_003].
vm_compute. discriminate.
Qed.

Lemma sbk_usegs : reserved_top (segments_reserved usegs) + brk_aslr_max + PGSZ <= 2^40.
Proof.
unfold segments_reserved, segment_reservation, Ubsan.M.loaded_segments, Ubsan_loaded_segments.
cbn [map reserved_top fst snd]. rewrite !Z_to_bv_unsigned.
cbn [seg_base seg_size Ubsan_segment_000 Ubsan_segment_001 Ubsan_segment_002 Ubsan_segment_003].
vm_compute. discriminate.
Qed.

Theorem prog_plain_model_okN : forall en inp,
valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_core inp ->
tsafe nstep no_enomem (prog_plain psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs source_alloc_limit en inp) ->
leaves_unreachable_m nstep (prog_plain psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs source_alloc_limit en inp)
/\ tsafe nstep nsafe (prog_plain psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs source_alloc_limit en inp).
Proof. intros en inp Hv Hi Hne. unfold prog_plain in *. eapply prog_model_ok; [apply reserved_top_psegs| apply ceil_psegs| exact Hv| exact Hi| exact Hne]. Qed.

Theorem prog_ubsan_model_okN : forall en inp,
valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp -> valid_input_core inp ->
tsafe nstep no_enomem (prog_ubsan usegs RSTAGE_ubsan (ceil_of en) (in_argv inp)) (mo0 usegs target_alloc_limit en inp) ->
leaves_unreachable_m nstep (prog_ubsan usegs RSTAGE_ubsan (ceil_of en) (in_argv inp)) (mo0 usegs target_alloc_limit en inp)
/\ tsafe nstep nsafe (prog_ubsan usegs RSTAGE_ubsan (ceil_of en) (in_argv inp)) (mo0 usegs target_alloc_limit en inp).
Proof. intros en inp Hv Hi Hne. unfold prog_ubsan in *. eapply prog_model_ok; [apply reserved_top_usegs| apply ceil_usegs| exact Hv| exact Hi| exact Hne]. Qed.
