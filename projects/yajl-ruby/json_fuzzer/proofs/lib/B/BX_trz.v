(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad StdioBase Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz TrzNodes TrzStdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA LazyModel ITreeA NodesA ImplRzA TrzNodesA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation trzN := trzA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition mokA (mo : Model) : Prop := minvA mo /\ m_halted mo = None.

(* [comment removed for export] *)
Lemma mokA_step : forall n mo rsp mo' evs, mokA mo -> tree_node n -> nstep n mo rsp mo' evs -> mokA mo'.
Proof.
  intros n mo rsp mo' evs [Hmi Hh] Htn Hst.
  destruct Htn as [Hn | [c ->]]; [| destruct Hst].
  destruct n; try contradiction; cbn -[fd_lookup fs_lookup Z.pow Z.le Z.lt] in Hst.
  - destruct Hst as [-> _]. split; assumption.
  - destruct Hst as [-> _]. split; assumption.
  - pose proof (open_presA mo _ _ _ _ Hmi Hh Hst) as (A & B & _). split; assumption.
  - destruct Hst as [_ H]. destruct (fd_lookup (m_fds mo) _) as [e|] eqn:Hlk; [| destruct H as [_ ->]; split; assumption].
    destruct e; try contradiction; [ | destruct H as [_ ->]; split; assumption].
    destruct (fs_lookup (m_fs mo) _); [| contradiction]. destruct H as [_ ->].
    split; [eapply minvA_update_file; [exact Hmi | exact Hlk] | macc; exact Hh].
  - destruct Hst as (_ & Hfd & H). destruct (fd_lookup (m_fds mo) _); destruct H as [_ ->]; [| split; assumption].
    split; [apply minvA_remove; assumption | macc; exact Hh].
  - destruct Hst as (_ & _ & ->). split; assumption.
  - destruct Hst as (_ & t & _ & Ht). destruct (m_tid mo); destruct Ht as [Hr ->]; [split; assumption|].
    split; [apply minvA_with_tid; assumption | macc; exact Hh].
Qed.


Lemma trzA_teq : forall {R} (t t' : itree node R) mo K T,
  trzN t mo K T -> teq t t' -> trzN t' mo K T.
Proof.
  intros R t t' mo K T H. revert t'.
  induction H as [r mo K | n k mo K TT i0 Hmi Hsafe Hk IH | t mo K T T' Ht IH Heq]; intros t' E.
  - inversion E; subst. apply trzA_ret.
  - inversion E; subst.
    match goal with H : forall x, teq (k x) (?k2 x) |- _ => rename H into HK2 end.
    apply (trzA_vis n _ mo K TT i0 Hmi Hsafe).
    intros rsp mo' evs H. apply (IH rsp mo' evs H). apply HK2.
  - eapply trzA_conseq; [apply IH; exact E | exact Heq].
Qed.





Lemma trzA_bind_leaf : forall {A B} (t : itree node A) (f : A -> itree node B) mo (K1 : A -> Model -> TSet) K T,
  trzN t mo K1 T -> mokA mo ->
  (forall a mo', mokA mo' -> leaf t mo a mo' -> trzN (f a) mo' K (K1 a mo')) ->
  trzN (ITree.bind node t f) mo K T.
Proof.
  intros A B t f mo K1 K T Ht. induction Ht as [r mo K1 | n k mo K1 TT i0 Hmi Hsafe Hk IH | t mo K1 T T' Ht IH Heq];
    intros Hok Hf.
  - cbn. apply Hf; [exact Hok | constructor].
  - cbn. apply (trzA_vis n (fun x => ITree.bind node (k x) f) mo K TT i0 Hmi Hsafe).
    intros rsp mo' evs H. apply (IH rsp mo' evs H).
    * eapply mokA_step; eassumption.
    * intros a mo'' Hok'' L. apply Hf; [exact Hok''|]. eapply leaf_vis; [exact H | exact L].
  - eapply trzA_conseq; [apply IH; assumption | exact Heq].
Qed.


Section Glue.

Context {St : Type}.


Lemma trzA_mbind : forall {A B} (m : @M St A) (f : A -> @M St B) (s : St) mo
    (K : exc (B * St) -> Model -> TSet) (Q : A -> St -> Model -> TSet) (T : TSet),
  trzN (m s) mo (kbind Q K) T -> mokA mo ->
  (forall a s' mo', mokA mo' -> leaf (m s) mo (Ok (a, s')) mo' -> trzN (f a s') mo' K (Q a s' mo')) ->
  trzN (mbind m f s) mo K T.
Proof.
  intros A B m f s mo K Q T Hm Hok Hf. unfold mbind, ebind.
  eapply (trzA_bind_leaf (m s) _ mo (kbind Q K) K T Hm Hok).
  intros [|[a s']] mo' Hok' L; cbn; [apply trzA_ret | apply Hf; [exact Hok' | exact L]].
Qed.


Lemma trzA_mbind_assoc : forall {A B C} (m : @M St A) (g : A -> @M St B) (f : B -> @M St C) (s : St) mo K T,
  trzN (mbind m (fun a => mbind (g a) f) s) mo K T ->
  trzN (mbind (mbind m g) f s) mo K T.
Proof.
  intros A B C m g f s mo K T H. unfold mbind in *.
  eapply trzA_teq; [exact H|]. apply teq_sym.
  apply (ebind_assoc_teq (m s) (fun p => g (fst p) (snd p)) (fun p => f (fst p) (snd p))).
Qed.


Lemma trzA_mret : forall {A} (a : A) (s : St) mo (K : exc (A * St) -> Model -> TSet),
  trzN (mret a s) mo K (K (Ok (a, s)) mo).
Proof. intros. unfold mret. apply trzA_ret. Qed.


Lemma trzA_upd : forall (f : St -> St) (s : St) mo (K : exc (unit * St) -> Model -> TSet),
  trzN (mupd f s) mo K (K (Ok (tt, f s)) mo).
Proof. intros. unfold mupd. apply trzA_ret. Qed.


Lemma trzA_eq : forall {R} (t : itree node R) mo K T T', trzN t mo K T -> T = T' -> trzN t mo K T'.
Proof. intros R t mo K T T' H <-. exact H. Qed.


Lemma trzA_mbind_ret : forall {A B} (a : A) (f : A -> @M St B) (s : St) mo K T,
  trzN (f a s) mo K T -> trzN (mbind (mret a) f s) mo K T.
Proof. intros A B a f s mo K T H. exact H. Qed.

Lemma trzA_mbind_upd : forall {B} (g : St -> St) (f : unit -> @M St B) (s : St) mo K T,
  trzN (f tt (g s)) mo K T -> trzN (mbind (mupd g) f s) mo K T.
Proof. intros B g f s mo K T H. exact H. Qed.

Lemma trzA_mbind_get : forall {B} (f : St -> @M St B) (s : St) mo K T,
  trzN (f s s) mo K T -> trzN (mbind mget f s) mo K T.
Proof. intros B f s mo K T H. exact H. Qed.

End Glue.


Section PrimK.

Context {St : Type}.


Lemma trzA_stdio_writev_k : forall {B} fd (buf bs : list Z) (f : unit -> @M St B) (st : St) mo K T,
  mokA mo -> (fd = 1 \/ fd = 2) -> zlength buf + zlength bs <= WRITEV_MAX ->
  trzN (f tt st) mo K T -> T [] ->
  trzN (mbind (stdio_writev fd buf bs) f st) mo K (t_emit (Wz fd (buf ++ bs)) T).
Proof.
  intros B fd buf bs f st mo K T Hok Hfd Hlen Hf HT.
  apply (trzA_mbind (stdio_writev fd buf bs) f st mo K (fun _ _ _ => T)); [| exact Hok |].
  - apply (trzA_stdio_writev fd buf bs st mo (kbind (fun _ _ _ => T) K) (proj1 Hok) Hfd Hlen). exact HT.
  - intros [] s' mo' _ L. apply leaf_stdio_writev in L as [-> [E|E]]; [discriminate|]. inversion E; subst. exact Hf.
Qed.


Lemma trzA_msys_det_k : forall {A B} n (dec : resp -> option A) (a0 : A) (f : A -> @M St B) (st : St) mo K T,
  mokA mo -> tree_node n ->
  (exists rsp mo' evs, nstep n mo rsp mo' evs) ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> evs = [] /\ mo' = mo /\ dec rsp = Some a0) ->
  (forall code mo', ~ nexit n mo code mo') ->
  trzN (f a0 st) mo K T -> T [] ->
  trzN (mbind (msys n dec) f st) mo K T.
Proof.
  intros A B n dec a0 f st mo K T Hok Hsafe Hex Hdet Hnx Hf HT.
  apply (trzA_mbind (msys n dec) f st mo K (fun _ _ _ => T)); [| exact Hok |].
  - apply trzA_msys_silent; try assumption. exact (proj1 Hok).
    intros rsp mo' evs H. destruct (Hdet _ _ _ H) as (-> & -> & D). rewrite D. split; [reflexivity | apply t_eq_refl].
  - intros a s' mo' _ L. apply leaf_msys in L as (rsp & evs & Hst & Er).
    destruct (Hdet _ _ _ Hst) as (_ & -> & D). rewrite D in Er. inversion Er; subst. exact Hf.
Qed.


Lemma trzA_ioctl_k : forall {B} fd req (f : sret -> @M St B) (st : St) mo K T,
  mokA mo -> trzN (f (SErr ENOTTY) st) mo K T -> T [] ->
  trzN (mbind (msys (NIoctl fd req) dec_ioctl) f st) mo K T.
Proof.
  intros B fd req f st mo K T Hok Hf HT.
  apply (trzA_msys_det_k (NIoctl fd req) dec_ioctl (SErr ENOTTY) f st mo K T Hok (or_introl I)); try assumption.
  - exists (efferr ENOTTY), mo, []. cbn. auto.
  - intros rsp mo' evs H. destruct (nstep_dec_ioctl _ _ _ _ _ _ H) as (D & -> & ->). auto.
  - intros code mo' H. exact H.
Qed.

End PrimK.


Section Stderr.

Context {St : Type}.


Lemma trzA_stderr_fwrite : forall (s : list Z) (st : St) mo (K : exc (unit * St) -> Model -> TSet),
  minvA mo -> zlength s <= WRITEV_MAX -> K (Ok (tt, st)) mo [] ->
  trzN (stderr_fwrite s st) mo K (t_emit (Wz 2 s) (K (Ok (tt, st)) mo)).
Proof.
  intros s st mo K Hmi Hlen HK. unfold stderr_fwrite.
  destruct (Z.ltb_spec 0 (zlength s)).
  - apply (trzA_stdio_writev 2 [] s st mo K Hmi); [right; reflexivity | change (zlength (@nil Z)) with 0; lia | exact HK].
  - assert (s = []) as -> by (destruct s; [reflexivity | unfold zlength in *; cbn in *; lia]).
    cbn [Wz to_bytes map]. eapply trzA_conseq; [apply trzA_mret | apply t_eq_sym, t_emit_nil_eq; exact HK].
Qed.


Lemma trzA_stderr_pieces : forall {B} (ps : list (list Z)) (buf : list Z) (f : list Z -> @M St B) (st : St) mo
    (K : exc (B * St) -> Model -> TSet) (Q : list Z -> St -> Model -> TSet),
  mokA mo ->
  zlength buf <= INTERNAL_BUFSIZ -> Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) ps ->
  (forall b st' mo', Q b st' mo' []) ->
  (forall b st' mo', mokA mo' -> zlength b <= INTERNAL_BUFSIZ -> trzN (f b st') mo' K (Q b st' mo')) ->
  trzN (mbind (stderr_pieces buf ps) f st) mo K (t_emit (Wz 2 (sp_out buf ps)) (Q (sp_final buf ps) st mo)).
Proof.
  induction ps as [|p ps IH]; intros buf f st mo K Q Hok Hbuf Hps HQ Hf.
  - cbn [stderr_pieces sp_out sp_final]. apply trzA_mbind_ret. rewrite Wz_nil.
    eapply trzA_conseq; [apply Hf; [exact Hok | exact Hbuf] | apply t_eq_sym, t_emit_nil_eq; apply HQ].
  - apply Forall_cons_iff in Hps. destruct Hps as [Hp Hps].
    cbn [stderr_pieces sp_out sp_final]. destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength p)).
    + (* [comment removed for export] *)
      apply trzA_mbind_assoc.
      eapply trzA_conseq.
      * apply (trzA_mbind (stdio_writev 2 buf p) (fun _ => mbind (stderr_pieces [] ps) f) st mo K
                 (fun _ st' mo' => t_emit (Wz 2 (sp_out [] ps)) (Q (sp_final [] ps) st' mo'))); [| exact Hok |].
        -- apply (trzA_stdio_writev 2 buf p st mo _ (proj1 Hok)); [right; reflexivity | unfold INTERNAL_BUFSIZ, WRITEV_MAX in *; lia |].
           cbn [kbind fst snd]. apply t_emit_has_nil.
        -- intros [] st' mo' Hok' _. cbn [kbind fst snd].
           apply IH; [exact Hok' | unfold zlength, INTERNAL_BUFSIZ; cbn; lia | exact Hps | exact HQ | exact Hf].
      * cbn [kbind fst snd]. fold (Wz 2 (buf ++ p)). rewrite !Wz_app.
        apply (t_eq_trans _ _ _ (t_eq_emit_app (Wz 2 buf) (Wz 2 p) _)).
        apply t_eq_sym.
        apply (t_eq_trans _ _ _ (t_eq_emit_app (Wz 2 buf) (Wz 2 p ++ Wz 2 (sp_out [] ps)) _)).
        apply t_eq_emit. apply t_eq_emit_app.
    + apply IH; [exact Hok | unfold INTERNAL_BUFSIZ in *; unfold zlength in *; rewrite length_app; lia | exact Hps | exact HQ | exact Hf].
Qed.


Lemma trzA_stderr_fprintf : forall (ps : list (list Z)) (st : St) mo (K : exc (unit * St) -> Model -> TSet),
  mokA mo -> Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) ps ->
  (forall st' mo', K (Ok (tt, st')) mo' []) ->
  trzN (stderr_fprintf ps st) mo K (t_emit (Wz 2 (concat ps)) (K (Ok (tt, st)) mo)).
Proof.
  intros ps st mo K Hok Hps HK. unfold stderr_fprintf.
  eapply trzA_conseq.
  - apply (trzA_stderr_pieces ps [] (fun b => stdio_writev 2 b []) st mo K
             (fun b st' mo' => t_emit (Wz 2 b) (K (Ok (tt, st')) mo'))); try assumption.
    + change (zlength (@nil Z)) with 0. unfold INTERNAL_BUFSIZ. lia.
    + intros; apply t_emit_has_nil.
    + intros b st' mo' Hok' Hb.
      eapply trzA_eq; [apply (trzA_stdio_writev 2 b [] st' mo' K (proj1 Hok')); [right; reflexivity | | apply HK] |].
      * change (zlength (@nil Z)) with 0. unfold INTERNAL_BUFSIZ, WRITEV_MAX in *. lia.
      * rewrite app_nil_r. reflexivity.
  - change (concat ps) with ([] ++ concat ps). rewrite <- (sp_bytes ps []). rewrite Wz_app. apply t_eq_sym. apply t_eq_emit_app.
Qed.

End Stderr.


Section Stdout.

Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Hypothesis GS : forall so x, get_so (set_so so x) = so.

Hypothesis SS : forall so so' x, set_so so' (set_so so x) = set_so so' x.


Lemma trzA_rdso : forall {B} (f : stdout_st -> @M St B) (s : St) mo K T,
  trzN (f (get_so s) s) mo K T -> trzN (mbind (rd_so get_so) f s) mo K T.
Proof. intros B f s mo K T H. exact H. Qed.

Lemma trzA_updso : forall {B} (g : stdout_st -> stdout_st) (f : unit -> @M St B) (s : St) mo K T,
  trzN (f tt (set_so (g (get_so s)) s)) mo K T -> trzN (mbind (upd_so get_so set_so g) f s) mo K T.
Proof. intros B g f s mo K T H. exact H. Qed.

Lemma trzA_updso_last : forall (g : stdout_st -> stdout_st) (s : St) mo (K : exc (unit * St) -> Model -> TSet),
  trzN (upd_so get_so set_so g s) mo K (K (Ok (tt, set_so (g (get_so s)) s)) mo).
Proof. intros g s mo K. unfold upd_so. apply (trzA_upd (fun s0 => set_so (g (get_so s0)) s0) s mo K). Qed.


Lemma trzA_stdout_stdio_write : forall (s : list Z) (st : St) mo (K : exc (unit * St) -> Model -> TSet),
  mokA mo -> zlength (so_buf (get_so st)) + zlength s <= WRITEV_MAX -> (forall st' mo', K (Ok (tt, st')) mo' []) ->
  trzN (stdout_stdio_write get_so set_so s st) mo K
       (t_emit (Wz 1 (so_buf (get_so st) ++ s))
               (K (Ok (tt, set_so (mkStdout true [] (so_lbf_nl (get_so st)) (so_first (get_so st))) st)) mo)).
Proof.
  intros s st mo K Hok Hlen HK. unfold stdout_stdio_write. apply trzA_rdso.
  set (Q := fun (_ : unit) (st' : St) (mo' : Model) => K (Ok (tt, set_so (mkStdout true [] (so_lbf_nl (get_so st')) (so_first (get_so st'))) st')) mo').
  apply (trzA_mbind (stdio_writev 1 (so_buf (get_so st)) s) _ st mo K Q); [| exact Hok |].
  - apply (trzA_stdio_writev 1 _ s st mo (kbind Q K) (proj1 Hok)); [left; reflexivity | exact Hlen | cbn [kbind fst snd]; apply HK].
  - intros [] st' mo' _ _. apply trzA_updso_last.
Qed.


Lemma trzA_stdout_writefn : forall (s : list Z) (st : St) mo (K : exc (unit * St) -> Model -> TSet),
  mokA mo -> zlength (so_buf (get_so st)) + zlength s <= WRITEV_MAX -> (forall st' mo', K (Ok (tt, st')) mo' []) ->
  trzN (stdout_writefn get_so set_so s st) mo K
       (t_emit (Wz 1 (so_buf (get_so st) ++ s)) (K (Ok (tt, set_so (snd (writefn_pure (get_so st) s)) st)) mo)).
Proof.
  intros s st mo K Hok Hlen HK. unfold stdout_writefn, writefn_pure, ioctl_pure. apply trzA_rdso.
  destruct (so_first (get_so st)) eqn:EF.
  - (* [comment removed for export] *)
    apply trzA_mbind_assoc. apply trzA_updso. apply trzA_mbind_assoc.
    set (st1 := set_so _ st).
    set (Q := fun (r : sret) (st' : St) (mo' : Model) => match r with
              | SErr _ => t_emit (Wz 1 (so_buf (get_so st) ++ s)) (K (Ok (tt, set_so (mkStdout true [] false false) st)) mo')
              | SVal _ => K Unr mo' end).
    eapply trzA_eq; [apply (trzA_mbind (msys (NIoctl 1 TIOCGWINSZ) dec_ioctl) _ _ mo K Q); [| exact Hok |] |].
    + apply (trzA_ioctl 1 TIOCGWINSZ st1 mo (kbind Q K) (proj1 Hok)). cbn [kbind fst snd]. apply t_emit_has_nil.
    + intros r st' mo' Hok' L. apply leaf_msys in L as (rsp & evs & Hst & Er).
      destruct (nstep_dec_ioctl _ _ _ _ _ _ Hst) as (D & -> & ->). rewrite D in Er. inversion Er; subst r st'.
      apply trzA_updso. subst st1. rewrite !GS. cbn [so_active so_buf so_first]. rewrite SS.
      match goal with |- trzN (stdout_stdio_write _ _ _ ?st2) _ _ _ =>
        pose proof (trzA_stdout_stdio_write s st2 mo K Hok) as T end.
      rewrite !GS in T. cbn [so_buf so_lbf_nl so_first so_active] in T. rewrite !SS in T.
      apply T; [exact Hlen | exact HK].
    + reflexivity.
  - (* [comment removed for export] *)
    apply trzA_mbind_ret. cbv zeta. cbn [snd]. eapply trzA_eq; [apply trzA_stdout_stdio_write; assumption | now rewrite EF].
Qed.


Lemma trzA_stdout_fwritex : forall (s : list Z) (st : St) mo (K : exc (unit * St) -> Model -> TSet),
  mokA mo -> zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> zlength s + STDOUT_BUFSIZ <= WRITEV_MAX ->
  (forall st' mo', K (Ok (tt, st')) mo' []) ->
  trzN (stdout_fwritex get_so set_so s st) mo K
       (t_emit (Wz 1 (fst (fwritex_pure (get_so st) s))) (K (Ok (tt, set_so (snd (fwritex_pure (get_so st) s)) st)) mo)).
Proof.
  intros s st mo K Hok Hbuf Hs HK. unfold stdout_fwritex, fwritex_pure. unfold stdout_towrite. apply trzA_updso. apply trzA_rdso.
  rewrite !GS.
  set (so := towrite_pure (get_so st)).
  change (if so_active (get_so st) then get_so st else {| so_active := true; so_buf := []; so_lbf_nl := so_lbf_nl (get_so st); so_first := so_first (get_so st) |}) with so.
  assert (Hb2 : zlength (so_buf so) <= STDOUT_BUFSIZ) by (subst so; unfold towrite_pure; destruct (so_active (get_so st)); [exact Hbuf | unfold zlength, STDOUT_BUFSIZ; cbn; lia]).
  destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength (so_buf so)) (zlength s)).
  - (* [comment removed for export] *)
    pose proof (trzA_stdout_writefn s (set_so so st) mo K Hok) as T. rewrite !GS, !SS in T.
    eapply trzA_eq; [apply T; [unfold STDOUT_BUFSIZ in *; lia | exact HK] | rewrite writefn_pure_fst; reflexivity].
  - destruct (so_lbf_nl so) eqn:EL.
    + (* [comment removed for export] *)
      set (i := after_last_nl s). destruct (Z.ltb_spec 0 i).
      * destruct (writefn_pure so (firstn (Z.to_nat i) s)) as [e so'] eqn:EW. cbn [fst snd].
        set (Q := fun (_ : unit) (st' : St) (mo' : Model) =>
               K (Ok (tt, set_so (mkStdout (so_active (get_so st')) (so_buf (get_so st') ++ skipn (Z.to_nat i) s)
                                           (so_lbf_nl (get_so st')) (so_first (get_so st'))) st')) mo').
        eapply trzA_eq; [apply (trzA_mbind (stdout_writefn get_so set_so (firstn (Z.to_nat i) s)) _ (set_so so st) mo K Q); [| exact Hok |] |].
        -- pose proof (trzA_stdout_writefn (firstn (Z.to_nat i) s) (set_so so st) mo (kbind Q K) Hok) as T.
           rewrite !GS, !SS, EW in T. cbn [snd] in T. apply T.
           ++ assert (length (firstn (Z.to_nat i) s) <= length s)%nat by (rewrite firstn_length; lia). unfold zlength, STDOUT_BUFSIZ in *. lia.
           ++ intros; cbn [kbind fst snd]; apply HK.
        -- intros [] st' mo' _ _. apply trzA_updso_last.
        -- cbn [kbind fst snd]. subst Q. cbn beta. rewrite GS, SS. apply (f_equal fst) in EW. rewrite writefn_pure_fst in EW. cbn [fst] in EW.
           rewrite EW. reflexivity.
      * apply trzA_mbind_ret. eapply trzA_conseq; [apply trzA_updso_last|]. rewrite GS, SS, EL. cbn [fst snd Wz to_bytes map].
        apply t_eq_sym. apply t_emit_nil_eq. apply HK.
    + (* [comment removed for export] *)
      eapply trzA_conseq; [apply trzA_updso_last|]. rewrite GS, SS, EL. cbn [fst snd Wz to_bytes map].
      apply t_eq_sym. apply t_emit_nil_eq. apply HK.
Qed.

End Stdout.


Section StderrK.

Context {St : Type}.


Lemma trzA_stderr_fwrite_k : forall {B} (s : list Z) (f : unit -> @M St B) (st : St) mo K T,
  mokA mo -> zlength s <= WRITEV_MAX -> trzN (f tt st) mo K T -> T [] ->
  trzN (mbind (stderr_fwrite s) f st) mo K (t_emit (Wz 2 s) T).
Proof.
  intros B s f st mo K T Hok Hlen Hf HT. unfold stderr_fwrite.
  destruct (Z.ltb_spec 0 (zlength s)).
  - apply (trzA_stdio_writev_k 2 [] s f st mo K T Hok); [right; reflexivity | change (zlength (@nil Z)) with 0; lia | exact Hf | exact HT].
  - assert (s = []) as -> by (destruct s; [reflexivity | unfold zlength in *; cbn in *; lia]).
    apply trzA_mbind_ret. cbn [Wz to_bytes map]. eapply trzA_conseq; [exact Hf | apply t_eq_sym, t_emit_nil_eq; exact HT].
Qed.


Lemma trzA_stderr_pieces_k : forall {B} (ps : list (list Z)) (buf : list Z) (f : list Z -> @M St B) (st : St) mo K (Q : list Z -> TSet),
  mokA mo ->
  zlength buf <= INTERNAL_BUFSIZ -> Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) ps ->
  (forall b, Q b []) ->
  (forall b, zlength b <= INTERNAL_BUFSIZ -> trzN (f b st) mo K (Q b)) ->
  trzN (mbind (stderr_pieces buf ps) f st) mo K (t_emit (Wz 2 (sp_out buf ps)) (Q (sp_final buf ps))).
Proof.
  induction ps as [|p ps IH]; intros buf f st mo K Q Hok Hbuf Hps HQ Hf.
  - cbn [stderr_pieces sp_out sp_final]. apply trzA_mbind_ret. rewrite Wz_nil.
    eapply trzA_conseq; [apply Hf; exact Hbuf | apply t_eq_sym, t_emit_nil_eq; apply HQ].
  - apply Forall_cons_iff in Hps. destruct Hps as [Hp Hps].
    cbn [stderr_pieces sp_out sp_final]. destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength p)).
    + apply trzA_mbind_assoc.
      eapply trzA_conseq.
      * apply (trzA_stdio_writev_k 2 buf p (fun _ => mbind (stderr_pieces [] ps) f) st mo K
                 (t_emit (Wz 2 (sp_out [] ps)) (Q (sp_final [] ps))) Hok);
          [right; reflexivity | unfold INTERNAL_BUFSIZ, WRITEV_MAX in *; lia | | apply t_emit_has_nil].
        cbv beta. apply IH; [exact Hok | change (zlength (@nil Z)) with 0; unfold INTERNAL_BUFSIZ; lia | exact Hps | exact HQ | exact Hf].
      * rewrite !Wz_app.
        apply (t_eq_trans _ _ _ (t_eq_emit_app (Wz 2 buf) (Wz 2 p) _)). apply t_eq_sym.
        apply (t_eq_trans _ _ _ (t_eq_emit_app (Wz 2 buf) (Wz 2 p ++ Wz 2 (sp_out [] ps)) _)).
        apply t_eq_emit. apply t_eq_emit_app.
    + apply IH; [exact Hok | unfold INTERNAL_BUFSIZ in *; unfold zlength in *; rewrite length_app; lia | exact Hps | exact HQ | exact Hf].
Qed.


Lemma trzA_stderr_fprintf_k : forall {B} (ps : list (list Z)) (f : unit -> @M St B) (st : St) mo K T,
  mokA mo -> Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) ps ->
  trzN (f tt st) mo K T -> T [] ->
  trzN (mbind (stderr_fprintf ps) f st) mo K (t_emit (Wz 2 (concat ps)) T).
Proof.
  intros B ps f st mo K T Hok Hps Hf HT. unfold stderr_fprintf. apply trzA_mbind_assoc.
  eapply trzA_conseq.
  - apply (trzA_stderr_pieces_k ps [] (fun b => mbind (stdio_writev 2 b []) f) st mo K (fun b => t_emit (Wz 2 b) T) Hok).
    + change (zlength (@nil Z)) with 0. unfold INTERNAL_BUFSIZ. lia.
    + exact Hps.
    + intros; apply t_emit_has_nil.
    + intros b Hb. eapply trzA_eq; [apply (trzA_stdio_writev_k 2 b [] f st mo K T Hok); [right; reflexivity | | exact Hf | exact HT] |].
      * change (zlength (@nil Z)) with 0. unfold INTERNAL_BUFSIZ, WRITEV_MAX in *. lia.
      * rewrite app_nil_r. reflexivity.
  - change (concat ps) with ([] ++ concat ps). rewrite <- (sp_bytes ps []). rewrite Wz_app. apply t_eq_sym. apply t_eq_emit_app.
Qed.

End StderrK.


Section StdoutK.

Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Hypothesis GS : forall so x, get_so (set_so so x) = so.

Hypothesis SS : forall so so' x, set_so so' (set_so so x) = set_so so' x.


Lemma trzA_stdout_stdio_write_k : forall {B} (s : list Z) (f : unit -> @M St B) (st : St) mo K T,
  mokA mo -> zlength (so_buf (get_so st)) + zlength s <= WRITEV_MAX ->
  trzN (f tt (set_so (mkStdout true [] (so_lbf_nl (get_so st)) (so_first (get_so st))) st)) mo K T -> T [] ->
  trzN (mbind (stdout_stdio_write get_so set_so s) f st) mo K (t_emit (Wz 1 (so_buf (get_so st) ++ s)) T).
Proof.
  intros B s f st mo K T Hok Hlen Hf HT. unfold stdout_stdio_write.
  apply trzA_mbind_assoc. apply (trzA_rdso get_so). apply trzA_mbind_assoc.
  apply (trzA_stdio_writev_k 1 _ s _ st mo K T Hok); [left; reflexivity | exact Hlen | | exact HT].
  apply (trzA_updso get_so set_so). exact Hf.
Qed.


Lemma trzA_stdout_writefn_k : forall {B} (s : list Z) (f : unit -> @M St B) (st : St) mo K T,
  mokA mo -> zlength (so_buf (get_so st)) + zlength s <= WRITEV_MAX ->
  trzN (f tt (set_so (snd (writefn_pure (get_so st) s)) st)) mo K T -> T [] ->
  trzN (mbind (stdout_writefn get_so set_so s) f st) mo K (t_emit (Wz 1 (so_buf (get_so st) ++ s)) T).
Proof.
  intros B s f st mo K T Hok Hlen Hf HT. unfold stdout_writefn. unfold writefn_pure, ioctl_pure in Hf.
  apply trzA_mbind_assoc. apply (trzA_rdso get_so).
  destruct (so_first (get_so st)) eqn:EF.
  - apply trzA_mbind_assoc. apply trzA_mbind_assoc. apply (trzA_updso get_so set_so). apply trzA_mbind_assoc.
    apply (trzA_ioctl_k 1 TIOCGWINSZ _ _ mo K _ Hok); [| apply t_emit_has_nil]. cbv beta.
    apply (trzA_updso get_so set_so). rewrite !GS. cbn [so_active so_buf so_first]. rewrite SS.
    match goal with |- trzN (mbind _ _ ?st2) _ _ _ => pose proof (trzA_stdout_stdio_write_k s f st2 mo K T Hok) as W end.
    rewrite !GS in W. cbn [so_buf so_lbf_nl so_first so_active] in W. rewrite !SS in W.
    cbn [snd so_lbf_nl so_first] in Hf. apply W; [exact Hlen | exact Hf | exact HT].
  - apply trzA_mbind_assoc. apply trzA_mbind_ret. cbn [snd] in Hf. rewrite EF in Hf.
    apply trzA_stdout_stdio_write_k; try assumption. rewrite EF. exact Hf.
Qed.


Lemma trzA_stdout_fwritex_k : forall {B} (s : list Z) (f : unit -> @M St B) (st : St) mo K T,
  mokA mo -> zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> zlength s + STDOUT_BUFSIZ <= WRITEV_MAX ->
  trzN (f tt (set_so (snd (fwritex_pure (get_so st) s)) st)) mo K T -> T [] ->
  trzN (mbind (stdout_fwritex get_so set_so s) f st) mo K (t_emit (Wz 1 (fst (fwritex_pure (get_so st) s))) T).
Proof.
  intros B s f st mo K T Hok Hbuf Hs Hf HT. unfold stdout_fwritex. unfold fwritex_pure in *. unfold stdout_towrite.
  apply trzA_mbind_assoc. apply (trzA_updso get_so set_so). apply trzA_mbind_assoc. apply (trzA_rdso get_so).
  rewrite !GS.
  set (so := towrite_pure (get_so st)) in *.
  change (if so_active (get_so st) then get_so st else {| so_active := true; so_buf := []; so_lbf_nl := so_lbf_nl (get_so st); so_first := so_first (get_so st) |}) with so.
  assert (Hb2 : zlength (so_buf so) <= STDOUT_BUFSIZ) by (subst so; unfold towrite_pure; destruct (so_active (get_so st)); [exact Hbuf | unfold zlength, STDOUT_BUFSIZ; cbn; lia]).
  destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength (so_buf so)) (zlength s)).
  - pose proof (trzA_stdout_writefn_k s f (set_so so st) mo K T Hok) as W. rewrite !GS, !SS in W.
    eapply trzA_eq; [apply W; [unfold STDOUT_BUFSIZ in *; lia | exact Hf | exact HT] | rewrite writefn_pure_fst; reflexivity].
  - destruct (so_lbf_nl so) eqn:EL.
    + set (i := after_last_nl s) in *. destruct (Z.ltb_spec 0 i).
      * apply trzA_mbind_assoc.
        destruct (writefn_pure so (firstn (Z.to_nat i) s)) as [e so'] eqn:EW. cbn [fst snd] in Hf |- *.
        pose proof (trzA_stdout_writefn_k (firstn (Z.to_nat i) s) (fun _ => mbind (upd_so get_so set_so
                      (fun so0 => mkStdout (so_active so0) (so_buf so0 ++ skipn (Z.to_nat i) s) (so_lbf_nl so0) (so_first so0))) f)
                      (set_so so st) mo K T Hok) as W.
        rewrite !GS, !SS, EW in W. cbn [snd] in W. cbv beta in W.
        eapply trzA_eq; [apply W | apply (f_equal fst) in EW; rewrite writefn_pure_fst in EW; cbn [fst] in EW; rewrite EW; reflexivity].
        -- assert (length (firstn (Z.to_nat i) s) <= length s)%nat by (rewrite firstn_length; lia). unfold zlength, STDOUT_BUFSIZ in *. lia.
        -- apply (trzA_updso get_so set_so). rewrite GS, SS. exact Hf.
        -- exact HT.
      * apply trzA_mbind_ret. try apply (trzA_updso get_so set_so). cbn [fst snd Wz to_bytes map] in Hf |- *.
        eapply trzA_conseq; [| apply t_eq_sym, t_emit_nil_eq; exact HT]. rewrite !GS, !SS, EL. exact Hf.
    + try apply (trzA_updso get_so set_so). cbn [fst snd Wz to_bytes map] in Hf |- *.
      eapply trzA_conseq; [| apply t_eq_sym, t_emit_nil_eq; exact HT]. rewrite !GS, !SS, EL. exact Hf.
Qed.


Lemma trzA_out_pieces_k : forall {B} (ps : list (list Z)) (f : unit -> @M St B) (st : St) mo K T,
  mokA mo -> zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> Forall (fun p => zlength p + STDOUT_BUFSIZ <= WRITEV_MAX) ps ->
  trzN (f tt (set_so (snd (pieces_pure (get_so st) ps)) st)) mo K T -> T [] ->
  (forall x, set_so (get_so x) x = x) ->
  trzN (mbind (out_pieces get_so set_so ps) f st) mo K (t_emit (Wz 1 (fst (pieces_pure (get_so st) ps))) T).
Proof.
  induction ps as [|p ps IH]; intros f st mo K T Hok Hb Hps Hf HT SG; cbn [out_pieces pieces_pure fst snd].
  - apply trzA_mbind_ret. cbn [pieces_pure fst snd] in Hf. rewrite SG in Hf. cbn [Wz to_bytes map]. eapply trzA_conseq; [exact Hf | apply t_eq_sym, t_emit_nil_eq; exact HT].
  - apply Forall_cons_iff in Hps. destruct Hps as [Hp Hps].
    apply trzA_mbind_assoc. rewrite Wz_app.
    eapply trzA_conseq; [| apply t_eq_sym; apply t_eq_emit_app].
    apply (trzA_stdout_fwritex_k p _ st mo K _ Hok Hb Hp); [| apply t_emit_has_nil]. cbv beta.
    pose proof (IH f (set_so (snd (fwritex_pure (get_so st) p)) st) mo K T Hok) as W. rewrite !GS, !SS in W.
    apply W; [apply fwritex_pure_buf_bound; exact Hb | exact Hps | exact Hf | exact HT | exact SG].
Qed.


Lemma trzA_stdout_vprintf_k : forall {B} (ps : list (list Z)) (f : unit -> @M St B) (st : St) mo K T,
  mokA mo -> zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> Forall (fun p => zlength p + STDOUT_BUFSIZ <= WRITEV_MAX) ps ->
  trzN (f tt (set_so (snd (vprintf_pure (get_so st) ps)) st)) mo K T -> T [] ->
  (forall x, set_so (get_so x) x = x) ->
  trzN (mbind (stdout_vprintf get_so set_so ps) f st) mo K (t_emit (Wz 1 (fst (vprintf_pure (get_so st) ps))) T).
Proof.
  intros B ps f st mo K T Hok Hb Hps Hf HT SG. unfold stdout_vprintf, vprintf_pure in *. unfold stdout_towrite.
  apply trzA_mbind_assoc. apply (trzA_updso get_so set_so).
  pose proof (trzA_out_pieces_k ps f (set_so (towrite_pure (get_so st)) st) mo K T Hok) as W. rewrite !GS, !SS in W.
  unfold towrite_pure in W at 1.
  apply W; [| exact Hps | exact Hf | exact HT | exact SG].
  unfold towrite_pure. destruct (so_active (get_so st)); [exact Hb | unfold zlength, STDOUT_BUFSIZ; cbn; lia].
Qed.


Lemma trzA_stdout_exit_flush_k : forall {B} (f : unit -> @M St B) (st : St) mo K T,
  mokA mo -> zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ ->
  trzN (f tt (set_so (snd (exit_flush_pure (get_so st))) st)) mo K T -> T [] ->
  (forall x, set_so (get_so x) x = x) ->
  trzN (mbind (stdout_exit_flush get_so set_so) f st) mo K (t_emit (Wz 1 (fst (exit_flush_pure (get_so st)))) T).
Proof.
  intros B f st mo K T Hok Hb Hf HT SG. unfold stdout_exit_flush, exit_flush_pure in *.
  apply trzA_mbind_assoc. apply (trzA_rdso get_so).
  destruct (Z.ltb_spec 0 (zlength (so_buf (get_so st)))).
  - eapply trzA_eq; [apply (trzA_stdout_writefn_k [] f st mo K T Hok); [| exact Hf | exact HT] | rewrite writefn_pure_fst; reflexivity].
    change (zlength (@nil Z)) with 0. unfold STDOUT_BUFSIZ, WRITEV_MAX in *. lia.
  - apply trzA_mbind_ret. cbn [fst snd Wz to_bytes map] in Hf |- *. rewrite SG in Hf. eapply trzA_conseq; [exact Hf | apply t_eq_sym, t_emit_nil_eq; exact HT].
Qed.

End StdoutK.

End RC__1.
