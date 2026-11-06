(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad StdioBase Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz TrzNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition Wz (fd : Z) (bs : list Z) : list event := map (WriteEv (Z_to_bv 64 fd)) (to_bytes bs).

Lemma Wz_app : forall fd a b, Wz fd (a ++ b) = Wz fd a ++ Wz fd b.
Proof. intros. unfold Wz, to_bytes. rewrite !map_app. reflexivity. Qed.
Lemma Wz_nil : forall fd, Wz fd [] = []. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive teq {R : Type} : itree node R -> itree node R -> Prop :=
| teq_ret : forall r, teq (Ret r) (Ret r)
| teq_vis : forall n k k', (forall x, teq (k x) (k' x)) -> teq (Vis n k) (Vis n k').

Lemma teq_refl : forall {R} (t : itree node R), teq t t.
Proof. induction t; constructor; auto. Qed.
Lemma teq_sym : forall {R} (t t' : itree node R), teq t t' -> teq t' t.
Proof. intros R t t' H; induction H; constructor; auto. Qed.

Lemma bind_teq : forall {A B} (t t' : itree node A) (f f' : A -> itree node B),
  teq t t' -> (forall a, teq (f a) (f' a)) -> teq (ITree.bind node t f) (ITree.bind node t' f').
Proof.
  intros A B t t' f f' H Hf. induction H as [r | n k k' Hk IH]; cbn [ITree.bind]; [apply Hf|].
  constructor. intros x. apply IH.
Qed.

Lemma bind_assoc_teq : forall {A B C} (t : itree node A) (g : A -> itree node B) (f : B -> itree node C),
  teq (ITree.bind node (ITree.bind node t g) f) (ITree.bind node t (fun x => ITree.bind node (g x) f)).
Proof.
  intros A B C t g f. induction t as [r | n k IH]; cbn [ITree.bind]; [apply teq_refl|].
  constructor. intros x. apply IH.
Qed.

Lemma ebind_assoc_teq : forall {A B C} (t : itree node (exc A)) (g : A -> itree node (exc B)) (f : B -> itree node (exc C)),
  teq (ebind (ebind t g) f) (ebind t (fun a => ebind (g a) f)).
Proof.
  intros A B C t g f. unfold ebind.
  induction t as [r | n k IH]; cbn [ITree.bind].
  - destruct r as [|a]; cbn [ITree.bind]; apply teq_refl.
  - constructor. intros x. apply IH.
Qed.

Lemma trz_teq : forall {R} (t t' : itree node R) mo K T,
  trzN t mo K T -> teq t t' -> trzN t' mo K T.
Proof.
  intros R t t' mo K T H. revert t'.
  induction H as [r mo K | n k mo K TT i0 Hmi Hsafe Hk IH Hex | t mo K T T' Ht IH Heq]; intros t' E.
  - inversion E; subst. apply trz_ret.
  - inversion E; subst.
    match goal with H : forall x, teq (k x) (?k2 x) |- _ => rename H into HK2 end.
    apply (trz_vis node nstep nexit minv nsafe n _ mo K TT i0 Hmi Hsafe).
    + intros rsp mo' evs H. apply (IH rsp mo' evs H). apply HK2.
    + exact Hex.
  - eapply trz_conseq; [apply IH; exact E | exact Heq].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mok (mo : Model) : Prop := minv mo /\ m_halted mo = None.

Lemma nsafe_lazy_free : forall n mo, nsafe n mo -> lazy_free_node n.
Proof. intros n mo H. destruct n; cbn in *; try exact I. exact (proj1 H). Qed.

Lemma mok_step : forall n mo rsp mo' evs, mok mo -> nsafe n mo -> nstep n mo rsp mo' evs -> mok mo'.
Proof.
  intros n mo rsp mo' evs [Hmi Hh] Hs Hst.
  destruct (minv_preserved n mo rsp mo' evs (nsafe_lazy_free n mo Hs) Hmi Hh Hst) as [Hh' Hmi']. split; assumption.
Qed.

(* [comment removed for export] *)
Inductive leaf {R : Type} : itree node R -> Model -> R -> Model -> Prop :=
| leaf_ret : forall r mo, leaf (Ret r) mo r mo
| leaf_vis : forall n k mo rsp mo1 evs r mo', nstep n mo rsp mo1 evs -> leaf (k rsp) mo1 r mo' -> leaf (Vis n k) mo r mo'.

Lemma leaf_ret_inv : forall {R} (r0 r : R) mo mo', leaf (Ret r0) mo r mo' -> r = r0 /\ mo' = mo.
Proof. intros R r0 r mo mo' H. inversion H; subst; auto. Qed.

Lemma leaf_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo r mo'',
  leaf (ITree.bind node t f) mo r mo'' -> exists a mo', leaf t mo a mo' /\ leaf (f a) mo' r mo''.
Proof.
  intros A B t. induction t as [a | n k IH]; intros f mo r mo'' H; cbn [ITree.bind] in H.
  - exists a, mo. split; [constructor | exact H].
  - inversion H; subst.
    match goal with Hn : nstep _ _ _ _ _, Hl : leaf _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ _ Hl) as (a & mo' & L1 & L2); exists a, mo'; split; [eapply leaf_vis; [exact Hn | exact L1] | exact L2] end.
Qed.

Lemma trz_bind_leaf : forall {A B} (t : itree node A) (f : A -> itree node B) mo (K1 : A -> Model -> TSet) K T,
  trzN t mo K1 T -> mok mo ->
  (forall a mo', mok mo' -> leaf t mo a mo' -> trzN (f a) mo' K (K1 a mo')) ->
  trzN (ITree.bind node t f) mo K T.
Proof.
  intros A B t f mo K1 K T Ht. induction Ht as [r mo K1 | n k mo K1 TT i0 Hmi Hsafe Hk IH Hex | t mo K1 T T' Ht IH Heq];
    intros Hok Hf.
  - cbn. apply Hf; [exact Hok | constructor].
  - cbn. apply (trz_vis node nstep nexit minv nsafe n (fun x => ITree.bind node (k x) f) mo K TT i0 Hmi Hsafe).
    + intros rsp mo' evs H. apply (IH rsp mo' evs H).
      * eapply mok_step; eassumption.
      * intros a mo'' Hok'' L. apply Hf; [exact Hok''|]. eapply leaf_vis; [exact H | exact L].
    + exact Hex.
  - eapply trz_conseq; [apply IH; assumption | exact Heq].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glue.
Context {St : Type}.

(* [comment removed for export] *)
Definition kbind {A B : Type} (Q : A -> St -> Model -> TSet) (K : exc (B * St) -> Model -> TSet)
    : exc (A * St) -> Model -> TSet :=
  fun r mo' => match r with Ok p => Q (fst p) (snd p) mo' | Unr => K Unr mo' end.

Lemma trz_mbind : forall {A B} (m : @M St A) (f : A -> @M St B) (s : St) mo
    (K : exc (B * St) -> Model -> TSet) (Q : A -> St -> Model -> TSet) (T : TSet),
  trzN (m s) mo (kbind Q K) T -> mok mo ->
  (forall a s' mo', mok mo' -> leaf (m s) mo (Ok (a, s')) mo' -> trzN (f a s') mo' K (Q a s' mo')) ->
  trzN (mbind m f s) mo K T.
Proof.
  intros A B m f s mo K Q T Hm Hok Hf. unfold mbind, ebind.
  eapply (trz_bind_leaf (m s) _ mo (kbind Q K) K T Hm Hok).
  intros [|[a s']] mo' Hok' L; cbn; [apply trz_ret | apply Hf; [exact Hok' | exact L]].
Qed.

(* [comment removed for export] *)
Lemma leaf_msys : forall {A} n (dec : resp -> option A) (s : St) mo r mo',
  leaf (msys n dec s) mo r mo' ->
  exists rsp evs, nstep n mo rsp mo' evs /\ r = match dec rsp with Some a => Ok (a, s) | None => Unr end.
Proof.
  intros A n dec s mo r mo' H. rewrite msys_unfold in H. inversion H; subst.
  match goal with Hn : nstep _ _ ?rsp _ ?evs, Hl : leaf _ _ _ _ |- _ =>
    exists rsp, evs; destruct (dec rsp); apply leaf_ret_inv in Hl as [-> ->]; auto end.
Qed.

(* [comment removed for export] *)
Lemma leaf_mbind : forall {A B} (m : @M St A) (g : A -> @M St B) (s : St) mo p mo'',
  leaf (mbind m g s) mo (Ok p) mo'' -> exists a s' mo', leaf (m s) mo (Ok (a, s')) mo' /\ leaf (g a s') mo' (Ok p) mo''.
Proof.
  intros A B m g s mo p mo'' H. unfold mbind, ebind in H. apply leaf_bind in H as ([|[a s']] & mo' & L1 & L2).
  - apply leaf_ret_inv in L2 as [E _]. discriminate.
  - exists a, s', mo'. auto.
Qed.

(* [comment removed for export] *)
Lemma trz_mbind_assoc : forall {A B C} (m : @M St A) (g : A -> @M St B) (f : B -> @M St C) (s : St) mo K T,
  trzN (mbind m (fun a => mbind (g a) f) s) mo K T ->
  trzN (mbind (mbind m g) f s) mo K T.
Proof.
  intros A B C m g f s mo K T H. unfold mbind in *.
  eapply trz_teq; [exact H|]. apply teq_sym.
  apply (ebind_assoc_teq (m s) (fun p => g (fst p) (snd p)) (fun p => f (fst p) (snd p))).
Qed.

Lemma trz_mret : forall {A} (a : A) (s : St) mo (K : exc (A * St) -> Model -> TSet),
  trzN (mret a s) mo K (K (Ok (a, s)) mo).
Proof. intros. unfold mret. apply trz_ret. Qed.

Lemma trz_upd : forall (f : St -> St) (s : St) mo (K : exc (unit * St) -> Model -> TSet),
  trzN (mupd f s) mo K (K (Ok (tt, f s)) mo).
Proof. intros. unfold mupd. apply trz_ret. Qed.

Lemma trz_eq : forall {R} (t : itree node R) mo K T T', trzN t mo K T -> T = T' -> trzN t mo K T'.
Proof. intros R t mo K T T' H <-. exact H. Qed.

(* [comment removed for export] *)
Lemma trz_mbind_ret : forall {A B} (a : A) (f : A -> @M St B) (s : St) mo K T,
  trzN (f a s) mo K T -> trzN (mbind (mret a) f s) mo K T.
Proof. intros A B a f s mo K T H. exact H. Qed.
Lemma trz_mbind_upd : forall {B} (g : St -> St) (f : unit -> @M St B) (s : St) mo K T,
  trzN (f tt (g s)) mo K T -> trzN (mbind (mupd g) f s) mo K T.
Proof. intros B g f s mo K T H. exact H. Qed.
Lemma trz_mbind_get : forall {B} (f : St -> @M St B) (s : St) mo K T,
  trzN (f s s) mo K T -> trzN (mbind mget f s) mo K T.
Proof. intros B f s mo K T H. exact H. Qed.
End Glue.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section PrimK.
Context {St : Type}.

Lemma leaf_writev_loop : forall fuel fd iovs (st : St) mo r mo',
  leaf (writev_loop fuel fd iovs st) mo r mo' -> mo' = mo /\ (r = Unr \/ r = Ok (tt, st)).
Proof.
  induction fuel as [|fuel IH]; intros fd iovs st mo r mo' H;
    cbn [writev_loop] in H; unfold mbind, ebind in H; rewrite msys_unfold in H; cbn [ITree.bind] in H;
    inversion H; subst.
  all: match goal with Hn : nstep _ _ _ _ _ |- _ => destruct Hn as [EM _]; subst end.
  all: match goal with Hl : leaf _ _ _ _ |- _ => revert Hl end.
  all: match goal with |- leaf (ITree.bind _ (match (match ?d with _ => _ end) with _ => _ end) _) _ _ _ -> _ => destruct d as [k|]; cbn [ITree.bind] end.
  all: try (intros Hl; apply leaf_ret_inv in Hl as [-> ->]; auto; fail).
  all: match goal with |- leaf ((if ?c then _ else _) _) _ _ _ -> _ => destruct c end; unfold mret, munr; intros Hl.
  - apply leaf_ret_inv in Hl as [-> ->]; auto.
  - apply leaf_ret_inv in Hl as [-> ->]; auto.
  - apply leaf_ret_inv in Hl as [-> ->]; auto.
  - exact (IH _ _ _ _ _ _ Hl).
Qed.

Lemma leaf_stdio_writev : forall fd buf bs (st : St) mo r mo',
  leaf (stdio_writev fd buf bs st) mo r mo' -> mo' = mo /\ (r = Unr \/ r = Ok (tt, st)).
Proof.
  intros fd buf bs st mo r mo' H. unfold stdio_writev in H.
  destruct (WRITEV_MAX <? zlength buf + zlength bs); [apply leaf_ret_inv in H as [-> ->]; auto | exact (leaf_writev_loop _ _ _ _ _ _ _ H)].
Qed.

Lemma trz_stdio_writev_k : forall {B} fd (buf bs : list Z) (f : unit -> @M St B) (st : St) mo K T,
  mok mo -> (fd = 1 \/ fd = 2) -> zlength buf + zlength bs <= WRITEV_MAX ->
  trzN (f tt st) mo K T -> T [] ->
  trzN (mbind (stdio_writev fd buf bs) f st) mo K (t_emit (Wz fd (buf ++ bs)) T).
Proof.
  intros B fd buf bs f st mo K T Hok Hfd Hlen Hf HT.
  apply (trz_mbind (stdio_writev fd buf bs) f st mo K (fun _ _ _ => T)); [| exact Hok |].
  - apply (trz_stdio_writev fd buf bs st mo (kbind (fun _ _ _ => T) K) (proj1 Hok) Hfd Hlen). exact HT.
  - intros [] s' mo' _ L. apply leaf_stdio_writev in L as [-> [E|E]]; [discriminate|]. inversion E; subst. exact Hf.
Qed.

(* [comment removed for export] *)
Lemma trz_msys_det_k : forall {A B} n (dec : resp -> option A) (a0 : A) (f : A -> @M St B) (st : St) mo K T,
  mok mo -> nsafe n mo ->
  (exists rsp mo' evs, nstep n mo rsp mo' evs) ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> evs = [] /\ mo' = mo /\ dec rsp = Some a0) ->
  (forall code mo', ~ nexit n mo code mo') ->
  trzN (f a0 st) mo K T -> T [] ->
  trzN (mbind (msys n dec) f st) mo K T.
Proof.
  intros A B n dec a0 f st mo K T Hok Hsafe Hex Hdet Hnx Hf HT.
  apply (trz_mbind (msys n dec) f st mo K (fun _ _ _ => T)); [| exact Hok |].
  - apply trz_msys_silent; try assumption; [exact (proj1 Hok)|].
    intros rsp mo' evs H. destruct (Hdet _ _ _ H) as (-> & -> & D). rewrite D. split; [reflexivity | apply t_eq_refl].
  - intros a s' mo' _ L. apply leaf_msys in L as (rsp & evs & Hst & Er).
    destruct (Hdet _ _ _ Hst) as (_ & -> & D). rewrite D in Er. inversion Er; subst. exact Hf.
Qed.

Lemma trz_ioctl_k : forall {B} fd req (f : sret -> @M St B) (st : St) mo K T,
  mok mo -> trzN (f (SErr ENOTTY) st) mo K T -> T [] ->
  trzN (mbind (msys (NIoctl fd req) dec_ioctl) f st) mo K T.
Proof.
  intros B fd req f st mo K T Hok Hf HT.
  apply (trz_msys_det_k (NIoctl fd req) dec_ioctl (SErr ENOTTY) f st mo K T Hok I); try assumption.
  - exists (efferr ENOTTY), mo, []. cbn. auto.
  - intros rsp mo' evs H. destruct (nstep_dec_ioctl _ _ _ _ _ _ H) as (D & -> & ->). auto.
  - intros code mo' H. exact H.
Qed.
End PrimK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stderr.
Context {St : Type}.

(* [comment removed for export] *)
Lemma trz_stderr_fwrite : forall (s : list Z) (st : St) mo (K : exc (unit * St) -> Model -> TSet),
  minv mo -> zlength s <= WRITEV_MAX -> K (Ok (tt, st)) mo [] ->
  trzN (stderr_fwrite s st) mo K (t_emit (Wz 2 s) (K (Ok (tt, st)) mo)).
Proof.
  intros s st mo K Hmi Hlen HK. unfold stderr_fwrite.
  destruct (Z.ltb_spec 0 (zlength s)).
  - apply (trz_stdio_writev 2 [] s st mo K Hmi); [right; reflexivity | change (zlength (@nil Z)) with 0; lia | exact HK].
  - assert (s = []) as -> by (destruct s; [reflexivity | unfold zlength in *; cbn in *; lia]).
    cbn [Wz to_bytes map]. eapply trz_conseq; [apply trz_mret | apply t_eq_sym, t_emit_nil_eq; exact HK].
Qed.

(* [comment removed for export] *)
Fixpoint sp_final (buf : list Z) (ps : list (list Z)) : list Z :=
  match ps with
  | [] => buf
  | p :: ps' => if INTERNAL_BUFSIZ - zlength buf <? zlength p then sp_final [] ps' else sp_final (buf ++ p) ps'
  end.
Fixpoint sp_out (buf : list Z) (ps : list (list Z)) : list Z :=
  match ps with
  | [] => []
  | p :: ps' => if INTERNAL_BUFSIZ - zlength buf <? zlength p then buf ++ p ++ sp_out [] ps' else sp_out (buf ++ p) ps'
  end.

Lemma sp_bytes : forall ps buf, sp_out buf ps ++ sp_final buf ps = buf ++ concat ps.
Proof.
  induction ps as [|p ps IH]; intros buf; cbn [sp_out sp_final concat]; [rewrite app_nil_r; reflexivity|].
  destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p).
  - rewrite <- !app_assoc, IH. reflexivity.
  - rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma sp_final_bound : forall ps buf, zlength buf <= INTERNAL_BUFSIZ -> zlength (sp_final buf ps) <= INTERNAL_BUFSIZ.
Proof.
  induction ps as [|p ps IH]; intros buf Hb; cbn [sp_final]; [exact Hb|].
  destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength p)); apply IH.
  - unfold zlength; cbn; unfold INTERNAL_BUFSIZ; lia.
  - unfold zlength in *. rewrite length_app. lia.
Qed.

Lemma trz_stderr_pieces : forall {B} (ps : list (list Z)) (buf : list Z) (f : list Z -> @M St B) (st : St) mo
    (K : exc (B * St) -> Model -> TSet) (Q : list Z -> St -> Model -> TSet),
  mok mo ->
  zlength buf <= INTERNAL_BUFSIZ -> Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) ps ->
  (forall b st' mo', Q b st' mo' []) ->
  (forall b st' mo', mok mo' -> zlength b <= INTERNAL_BUFSIZ -> trzN (f b st') mo' K (Q b st' mo')) ->
  trzN (mbind (stderr_pieces buf ps) f st) mo K (t_emit (Wz 2 (sp_out buf ps)) (Q (sp_final buf ps) st mo)).
Proof.
  induction ps as [|p ps IH]; intros buf f st mo K Q Hok Hbuf Hps HQ Hf.
  - cbn [stderr_pieces sp_out sp_final]. apply trz_mbind_ret. rewrite Wz_nil.
    eapply trz_conseq; [apply Hf; [exact Hok | exact Hbuf] | apply t_eq_sym, t_emit_nil_eq; apply HQ].
  - apply Forall_cons_iff in Hps. destruct Hps as [Hp Hps].
    cbn [stderr_pieces sp_out sp_final]. destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength p)).
    + (* [comment removed for export] *)
      apply trz_mbind_assoc.
      eapply trz_conseq.
      * apply (trz_mbind (stdio_writev 2 buf p) (fun _ => mbind (stderr_pieces [] ps) f) st mo K
                 (fun _ st' mo' => t_emit (Wz 2 (sp_out [] ps)) (Q (sp_final [] ps) st' mo'))); [| exact Hok |].
        -- apply (trz_stdio_writev 2 buf p st mo _ (proj1 Hok)); [right; reflexivity | unfold INTERNAL_BUFSIZ, WRITEV_MAX in *; lia |].
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

(* [comment removed for export] *)
Lemma trz_stderr_fprintf : forall (ps : list (list Z)) (st : St) mo (K : exc (unit * St) -> Model -> TSet),
  mok mo -> Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) ps ->
  (forall st' mo', K (Ok (tt, st')) mo' []) ->
  trzN (stderr_fprintf ps st) mo K (t_emit (Wz 2 (concat ps)) (K (Ok (tt, st)) mo)).
Proof.
  intros ps st mo K Hok Hps HK. unfold stderr_fprintf.
  eapply trz_conseq.
  - apply (trz_stderr_pieces ps [] (fun b => stdio_writev 2 b []) st mo K
             (fun b st' mo' => t_emit (Wz 2 b) (K (Ok (tt, st')) mo'))); try assumption.
    + change (zlength (@nil Z)) with 0. unfold INTERNAL_BUFSIZ. lia.
    + intros; apply t_emit_has_nil.
    + intros b st' mo' Hok' Hb.
      eapply trz_eq; [apply (trz_stdio_writev 2 b [] st' mo' K (proj1 Hok')); [right; reflexivity | | apply HK] |].
      * change (zlength (@nil Z)) with 0. unfold INTERNAL_BUFSIZ, WRITEV_MAX in *. lia.
      * rewrite app_nil_r. reflexivity.
  - change (concat ps) with ([] ++ concat ps). rewrite <- (sp_bytes ps []). rewrite Wz_app. apply t_eq_sym. apply t_eq_emit_app.
Qed.
End Stderr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stdout.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis GS : forall so x, get_so (set_so so x) = so.
Hypothesis SS : forall so so' x, set_so so' (set_so so x) = set_so so' x.

(* [comment removed for export] *)
Definition towrite_pure (so : stdout_st) : stdout_st :=
  if so_active so then so else mkStdout true [] (so_lbf_nl so) (so_first so).
(* [comment removed for export] *)
Definition ioctl_pure (so : stdout_st) : stdout_st :=
  if so_first so then mkStdout (so_active so) (so_buf so) false false else so.
Definition writefn_pure (so : stdout_st) (s : list Z) : list Z * stdout_st :=
  let so1 := ioctl_pure so in (so_buf so1 ++ s, mkStdout true [] (so_lbf_nl so1) (so_first so1)).

(* [comment removed for export] *)
Lemma trz_rdso : forall {B} (f : stdout_st -> @M St B) (s : St) mo K T,
  trzN (f (get_so s) s) mo K T -> trzN (mbind (rd_so get_so) f s) mo K T.
Proof. intros B f s mo K T H. exact H. Qed.
Lemma trz_updso : forall {B} (g : stdout_st -> stdout_st) (f : unit -> @M St B) (s : St) mo K T,
  trzN (f tt (set_so (g (get_so s)) s)) mo K T -> trzN (mbind (upd_so get_so set_so g) f s) mo K T.
Proof. intros B g f s mo K T H. exact H. Qed.
Lemma trz_updso_last : forall (g : stdout_st -> stdout_st) (s : St) mo (K : exc (unit * St) -> Model -> TSet),
  trzN (upd_so get_so set_so g s) mo K (K (Ok (tt, set_so (g (get_so s)) s)) mo).
Proof. intros g s mo K. unfold upd_so. apply (trz_upd (fun s0 => set_so (g (get_so s0)) s0) s mo K). Qed.

Lemma trz_stdout_stdio_write : forall (s : list Z) (st : St) mo (K : exc (unit * St) -> Model -> TSet),
  mok mo -> zlength (so_buf (get_so st)) + zlength s <= WRITEV_MAX -> (forall st' mo', K (Ok (tt, st')) mo' []) ->
  trzN (stdout_stdio_write get_so set_so s st) mo K
       (t_emit (Wz 1 (so_buf (get_so st) ++ s))
               (K (Ok (tt, set_so (mkStdout true [] (so_lbf_nl (get_so st)) (so_first (get_so st))) st)) mo)).
Proof.
  intros s st mo K Hok Hlen HK. unfold stdout_stdio_write. apply trz_rdso.
  set (Q := fun (_ : unit) (st' : St) (mo' : Model) => K (Ok (tt, set_so (mkStdout true [] (so_lbf_nl (get_so st')) (so_first (get_so st'))) st')) mo').
  apply (trz_mbind (stdio_writev 1 (so_buf (get_so st)) s) _ st mo K Q); [| exact Hok |].
  - apply (trz_stdio_writev 1 _ s st mo (kbind Q K) (proj1 Hok)); [left; reflexivity | exact Hlen | cbn [kbind fst snd]; apply HK].
  - intros [] st' mo' _ _. apply trz_updso_last.
Qed.

Lemma trz_stdout_writefn : forall (s : list Z) (st : St) mo (K : exc (unit * St) -> Model -> TSet),
  mok mo -> zlength (so_buf (get_so st)) + zlength s <= WRITEV_MAX -> (forall st' mo', K (Ok (tt, st')) mo' []) ->
  trzN (stdout_writefn get_so set_so s st) mo K
       (t_emit (Wz 1 (so_buf (get_so st) ++ s)) (K (Ok (tt, set_so (snd (writefn_pure (get_so st) s)) st)) mo)).
Proof.
  intros s st mo K Hok Hlen HK. unfold stdout_writefn, writefn_pure, ioctl_pure. apply trz_rdso.
  destruct (so_first (get_so st)) eqn:EF.
  - (* [comment removed for export] *)
    apply trz_mbind_assoc. apply trz_updso. apply trz_mbind_assoc.
    set (st1 := set_so _ st).
    set (Q := fun (r : sret) (st' : St) (mo' : Model) => match r with
              | SErr _ => t_emit (Wz 1 (so_buf (get_so st) ++ s)) (K (Ok (tt, set_so (mkStdout true [] false false) st)) mo')
              | SVal _ => K Unr mo' end).
    eapply trz_eq; [apply (trz_mbind (msys (NIoctl 1 TIOCGWINSZ) dec_ioctl) _ _ mo K Q); [| exact Hok |] |].
    + apply (trz_ioctl 1 TIOCGWINSZ st1 mo (kbind Q K) (proj1 Hok)). cbn [kbind fst snd]. apply t_emit_has_nil.
    + intros r st' mo' Hok' L. apply leaf_msys in L as (rsp & evs & Hst & Er).
      destruct (nstep_dec_ioctl _ _ _ _ _ _ Hst) as (D & -> & ->). rewrite D in Er. inversion Er; subst r st'.
      apply trz_updso. subst st1. rewrite !GS. cbn [so_active so_buf so_first]. rewrite SS.
      match goal with |- trzN (stdout_stdio_write _ _ _ ?st2) _ _ _ =>
        pose proof (trz_stdout_stdio_write s st2 mo K Hok) as T end.
      rewrite !GS in T. cbn [so_buf so_lbf_nl so_first so_active] in T. rewrite !SS in T.
      apply T; [exact Hlen | exact HK].
    + reflexivity.
  - (* [comment removed for export] *)
    apply trz_mbind_ret. cbv zeta. cbn [snd]. eapply trz_eq; [apply trz_stdout_stdio_write; assumption | now rewrite EF].
Qed.

Lemma writefn_pure_fst : forall so s, fst (writefn_pure so s) = so_buf so ++ s.
Proof. intros so s. unfold writefn_pure, ioctl_pure. destruct (so_first so); reflexivity. Qed.

(* [comment removed for export] *)
Definition fwritex_pure (so0 : stdout_st) (s : list Z) : list Z * stdout_st :=
  let so := towrite_pure so0 in
  if STDOUT_BUFSIZ - zlength (so_buf so) <? zlength s then writefn_pure so s
  else if so_lbf_nl so then
    let i := after_last_nl s in
    if 0 <? i then
      let '(e, so') := writefn_pure so (firstn (Z.to_nat i) s) in
      (e, mkStdout (so_active so') (so_buf so' ++ skipn (Z.to_nat i) s) (so_lbf_nl so') (so_first so'))
    else ([], mkStdout (so_active so) (so_buf so ++ skipn (Z.to_nat i) s) (so_lbf_nl so) (so_first so))
  else ([], mkStdout (so_active so) (so_buf so ++ s) (so_lbf_nl so) (so_first so)).

Lemma trz_stdout_fwritex : forall (s : list Z) (st : St) mo (K : exc (unit * St) -> Model -> TSet),
  mok mo -> zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> zlength s + STDOUT_BUFSIZ <= WRITEV_MAX ->
  (forall st' mo', K (Ok (tt, st')) mo' []) ->
  trzN (stdout_fwritex get_so set_so s st) mo K
       (t_emit (Wz 1 (fst (fwritex_pure (get_so st) s))) (K (Ok (tt, set_so (snd (fwritex_pure (get_so st) s)) st)) mo)).
Proof.
  intros s st mo K Hok Hbuf Hs HK. unfold stdout_fwritex, fwritex_pure. unfold stdout_towrite. apply trz_updso. apply trz_rdso.
  rewrite !GS.
  set (so := towrite_pure (get_so st)).
  change (if so_active (get_so st) then get_so st else {| so_active := true; so_buf := []; so_lbf_nl := so_lbf_nl (get_so st); so_first := so_first (get_so st) |}) with so.
  assert (Hb2 : zlength (so_buf so) <= STDOUT_BUFSIZ) by (subst so; unfold towrite_pure; destruct (so_active (get_so st)); [exact Hbuf | unfold zlength, STDOUT_BUFSIZ; cbn; lia]).
  destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength (so_buf so)) (zlength s)).
  - (* [comment removed for export] *)
    pose proof (trz_stdout_writefn s (set_so so st) mo K Hok) as T. rewrite !GS, !SS in T.
    eapply trz_eq; [apply T; [unfold STDOUT_BUFSIZ in *; lia | exact HK] | rewrite writefn_pure_fst; reflexivity].
  - destruct (so_lbf_nl so) eqn:EL.
    + (* [comment removed for export] *)
      set (i := after_last_nl s). destruct (Z.ltb_spec 0 i).
      * destruct (writefn_pure so (firstn (Z.to_nat i) s)) as [e so'] eqn:EW. cbn [fst snd].
        set (Q := fun (_ : unit) (st' : St) (mo' : Model) =>
               K (Ok (tt, set_so (mkStdout (so_active (get_so st')) (so_buf (get_so st') ++ skipn (Z.to_nat i) s)
                                           (so_lbf_nl (get_so st')) (so_first (get_so st'))) st')) mo').
        eapply trz_eq; [apply (trz_mbind (stdout_writefn get_so set_so (firstn (Z.to_nat i) s)) _ (set_so so st) mo K Q); [| exact Hok |] |].
        -- pose proof (trz_stdout_writefn (firstn (Z.to_nat i) s) (set_so so st) mo (kbind Q K) Hok) as T.
           rewrite !GS, !SS, EW in T. cbn [snd] in T. apply T.
           ++ assert (length (firstn (Z.to_nat i) s) <= length s)%nat by (rewrite firstn_length; lia). unfold zlength, STDOUT_BUFSIZ in *. lia.
           ++ intros; cbn [kbind fst snd]; apply HK.
        -- intros [] st' mo' _ _. apply trz_updso_last.
        -- cbn [kbind fst snd]. subst Q. cbn beta. rewrite GS, SS. apply (f_equal fst) in EW. rewrite writefn_pure_fst in EW. cbn [fst] in EW.
           rewrite EW. reflexivity.
      * apply trz_mbind_ret. eapply trz_conseq; [apply trz_updso_last|]. rewrite GS, SS, EL. cbn [fst snd Wz to_bytes map].
        apply t_eq_sym. apply t_emit_nil_eq. apply HK.
    + (* [comment removed for export] *)
      eapply trz_conseq; [apply trz_updso_last|]. rewrite GS, SS, EL. cbn [fst snd Wz to_bytes map].
      apply t_eq_sym. apply t_emit_nil_eq. apply HK.
Qed.
End Stdout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StderrK.
Context {St : Type}.

Lemma trz_stderr_fwrite_k : forall {B} (s : list Z) (f : unit -> @M St B) (st : St) mo K T,
  mok mo -> zlength s <= WRITEV_MAX -> trzN (f tt st) mo K T -> T [] ->
  trzN (mbind (stderr_fwrite s) f st) mo K (t_emit (Wz 2 s) T).
Proof.
  intros B s f st mo K T Hok Hlen Hf HT. unfold stderr_fwrite.
  destruct (Z.ltb_spec 0 (zlength s)).
  - apply (trz_stdio_writev_k 2 [] s f st mo K T Hok); [right; reflexivity | change (zlength (@nil Z)) with 0; lia | exact Hf | exact HT].
  - assert (s = []) as -> by (destruct s; [reflexivity | unfold zlength in *; cbn in *; lia]).
    apply trz_mbind_ret. cbn [Wz to_bytes map]. eapply trz_conseq; [exact Hf | apply t_eq_sym, t_emit_nil_eq; exact HT].
Qed.

Lemma trz_stderr_pieces_k : forall {B} (ps : list (list Z)) (buf : list Z) (f : list Z -> @M St B) (st : St) mo K (Q : list Z -> TSet),
  mok mo ->
  zlength buf <= INTERNAL_BUFSIZ -> Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) ps ->
  (forall b, Q b []) ->
  (forall b, zlength b <= INTERNAL_BUFSIZ -> trzN (f b st) mo K (Q b)) ->
  trzN (mbind (stderr_pieces buf ps) f st) mo K (t_emit (Wz 2 (sp_out buf ps)) (Q (sp_final buf ps))).
Proof.
  induction ps as [|p ps IH]; intros buf f st mo K Q Hok Hbuf Hps HQ Hf.
  - cbn [stderr_pieces sp_out sp_final]. apply trz_mbind_ret. rewrite Wz_nil.
    eapply trz_conseq; [apply Hf; exact Hbuf | apply t_eq_sym, t_emit_nil_eq; apply HQ].
  - apply Forall_cons_iff in Hps. destruct Hps as [Hp Hps].
    cbn [stderr_pieces sp_out sp_final]. destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength p)).
    + apply trz_mbind_assoc.
      eapply trz_conseq.
      * apply (trz_stdio_writev_k 2 buf p (fun _ => mbind (stderr_pieces [] ps) f) st mo K
                 (t_emit (Wz 2 (sp_out [] ps)) (Q (sp_final [] ps))) Hok);
          [right; reflexivity | unfold INTERNAL_BUFSIZ, WRITEV_MAX in *; lia | | apply t_emit_has_nil].
        cbv beta. apply IH; [exact Hok | change (zlength (@nil Z)) with 0; unfold INTERNAL_BUFSIZ; lia | exact Hps | exact HQ | exact Hf].
      * rewrite !Wz_app.
        apply (t_eq_trans _ _ _ (t_eq_emit_app (Wz 2 buf) (Wz 2 p) _)). apply t_eq_sym.
        apply (t_eq_trans _ _ _ (t_eq_emit_app (Wz 2 buf) (Wz 2 p ++ Wz 2 (sp_out [] ps)) _)).
        apply t_eq_emit. apply t_eq_emit_app.
    + apply IH; [exact Hok | unfold INTERNAL_BUFSIZ in *; unfold zlength in *; rewrite length_app; lia | exact Hps | exact HQ | exact Hf].
Qed.

Lemma trz_stderr_fprintf_k : forall {B} (ps : list (list Z)) (f : unit -> @M St B) (st : St) mo K T,
  mok mo -> Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) ps ->
  trzN (f tt st) mo K T -> T [] ->
  trzN (mbind (stderr_fprintf ps) f st) mo K (t_emit (Wz 2 (concat ps)) T).
Proof.
  intros B ps f st mo K T Hok Hps Hf HT. unfold stderr_fprintf. apply trz_mbind_assoc.
  eapply trz_conseq.
  - apply (trz_stderr_pieces_k ps [] (fun b => mbind (stdio_writev 2 b []) f) st mo K (fun b => t_emit (Wz 2 b) T) Hok).
    + change (zlength (@nil Z)) with 0. unfold INTERNAL_BUFSIZ. lia.
    + exact Hps.
    + intros; apply t_emit_has_nil.
    + intros b Hb. eapply trz_eq; [apply (trz_stdio_writev_k 2 b [] f st mo K T Hok); [right; reflexivity | | exact Hf | exact HT] |].
      * change (zlength (@nil Z)) with 0. unfold INTERNAL_BUFSIZ, WRITEV_MAX in *. lia.
      * rewrite app_nil_r. reflexivity.
  - change (concat ps) with ([] ++ concat ps). rewrite <- (sp_bytes ps []). rewrite Wz_app. apply t_eq_sym. apply t_eq_emit_app.
Qed.
End StderrK.

Section StdoutK.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis GS : forall so x, get_so (set_so so x) = so.
Hypothesis SS : forall so so' x, set_so so' (set_so so x) = set_so so' x.

Lemma trz_stdout_stdio_write_k : forall {B} (s : list Z) (f : unit -> @M St B) (st : St) mo K T,
  mok mo -> zlength (so_buf (get_so st)) + zlength s <= WRITEV_MAX ->
  trzN (f tt (set_so (mkStdout true [] (so_lbf_nl (get_so st)) (so_first (get_so st))) st)) mo K T -> T [] ->
  trzN (mbind (stdout_stdio_write get_so set_so s) f st) mo K (t_emit (Wz 1 (so_buf (get_so st) ++ s)) T).
Proof.
  intros B s f st mo K T Hok Hlen Hf HT. unfold stdout_stdio_write.
  apply trz_mbind_assoc. apply (trz_rdso get_so). apply trz_mbind_assoc.
  apply (trz_stdio_writev_k 1 _ s _ st mo K T Hok); [left; reflexivity | exact Hlen | | exact HT].
  apply (trz_updso get_so set_so). exact Hf.
Qed.

Lemma trz_stdout_writefn_k : forall {B} (s : list Z) (f : unit -> @M St B) (st : St) mo K T,
  mok mo -> zlength (so_buf (get_so st)) + zlength s <= WRITEV_MAX ->
  trzN (f tt (set_so (snd (writefn_pure (get_so st) s)) st)) mo K T -> T [] ->
  trzN (mbind (stdout_writefn get_so set_so s) f st) mo K (t_emit (Wz 1 (so_buf (get_so st) ++ s)) T).
Proof.
  intros B s f st mo K T Hok Hlen Hf HT. unfold stdout_writefn. unfold writefn_pure, ioctl_pure in Hf.
  apply trz_mbind_assoc. apply (trz_rdso get_so).
  destruct (so_first (get_so st)) eqn:EF.
  - apply trz_mbind_assoc. apply trz_mbind_assoc. apply (trz_updso get_so set_so). apply trz_mbind_assoc.
    apply (trz_ioctl_k 1 TIOCGWINSZ _ _ mo K _ Hok); [| apply t_emit_has_nil]. cbv beta.
    apply (trz_updso get_so set_so). rewrite !GS. cbn [so_active so_buf so_first]. rewrite SS.
    match goal with |- trzN (mbind _ _ ?st2) _ _ _ => pose proof (trz_stdout_stdio_write_k s f st2 mo K T Hok) as W end.
    rewrite !GS in W. cbn [so_buf so_lbf_nl so_first so_active] in W. rewrite !SS in W.
    cbn [snd so_lbf_nl so_first] in Hf. apply W; [exact Hlen | exact Hf | exact HT].
  - apply trz_mbind_assoc. apply trz_mbind_ret. cbn [snd] in Hf. rewrite EF in Hf.
    apply trz_stdout_stdio_write_k; try assumption. rewrite EF. exact Hf.
Qed.

Lemma trz_stdout_fwritex_k : forall {B} (s : list Z) (f : unit -> @M St B) (st : St) mo K T,
  mok mo -> zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> zlength s + STDOUT_BUFSIZ <= WRITEV_MAX ->
  trzN (f tt (set_so (snd (fwritex_pure (get_so st) s)) st)) mo K T -> T [] ->
  trzN (mbind (stdout_fwritex get_so set_so s) f st) mo K (t_emit (Wz 1 (fst (fwritex_pure (get_so st) s))) T).
Proof.
  intros B s f st mo K T Hok Hbuf Hs Hf HT. unfold stdout_fwritex. unfold fwritex_pure in *. unfold stdout_towrite.
  apply trz_mbind_assoc. apply (trz_updso get_so set_so). apply trz_mbind_assoc. apply (trz_rdso get_so).
  rewrite !GS.
  set (so := towrite_pure (get_so st)) in *.
  change (if so_active (get_so st) then get_so st else {| so_active := true; so_buf := []; so_lbf_nl := so_lbf_nl (get_so st); so_first := so_first (get_so st) |}) with so.
  assert (Hb2 : zlength (so_buf so) <= STDOUT_BUFSIZ) by (subst so; unfold towrite_pure; destruct (so_active (get_so st)); [exact Hbuf | unfold zlength, STDOUT_BUFSIZ; cbn; lia]).
  destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength (so_buf so)) (zlength s)).
  - pose proof (trz_stdout_writefn_k s f (set_so so st) mo K T Hok) as W. rewrite !GS, !SS in W.
    eapply trz_eq; [apply W; [unfold STDOUT_BUFSIZ in *; lia | exact Hf | exact HT] | rewrite writefn_pure_fst; reflexivity].
  - destruct (so_lbf_nl so) eqn:EL.
    + set (i := after_last_nl s) in *. destruct (Z.ltb_spec 0 i).
      * apply trz_mbind_assoc.
        destruct (writefn_pure so (firstn (Z.to_nat i) s)) as [e so'] eqn:EW. cbn [fst snd] in Hf |- *.
        pose proof (trz_stdout_writefn_k (firstn (Z.to_nat i) s) (fun _ => mbind (upd_so get_so set_so
                      (fun so0 => mkStdout (so_active so0) (so_buf so0 ++ skipn (Z.to_nat i) s) (so_lbf_nl so0) (so_first so0))) f)
                      (set_so so st) mo K T Hok) as W.
        rewrite !GS, !SS, EW in W. cbn [snd] in W. cbv beta in W.
        eapply trz_eq; [apply W | apply (f_equal fst) in EW; rewrite writefn_pure_fst in EW; cbn [fst] in EW; rewrite EW; reflexivity].
        -- assert (length (firstn (Z.to_nat i) s) <= length s)%nat by (rewrite firstn_length; lia). unfold zlength, STDOUT_BUFSIZ in *. lia.
        -- apply (trz_updso get_so set_so). rewrite GS, SS. exact Hf.
        -- exact HT.
      * apply trz_mbind_ret. try apply (trz_updso get_so set_so). cbn [fst snd Wz to_bytes map] in Hf |- *.
        eapply trz_conseq; [| apply t_eq_sym, t_emit_nil_eq; exact HT]. rewrite !GS, !SS, EL. exact Hf.
    + try apply (trz_updso get_so set_so). cbn [fst snd Wz to_bytes map] in Hf |- *.
      eapply trz_conseq; [| apply t_eq_sym, t_emit_nil_eq; exact HT]. rewrite !GS, !SS, EL. exact Hf.
Qed.

(* [comment removed for export] *)
Lemma fold_nl_range : forall (l : list (Z * Z)) acc lo hi,
  lo <= acc <= hi -> Forall (fun ib => lo <= fst ib + 1 <= hi) l ->
  lo <= fold_left (fun acc ib => if snd ib =? 10 then fst ib + 1 else acc) l acc <= hi.
Proof.
  induction l as [|[a b] l IH]; intros acc lo hi Hacc Hl; cbn [fold_left]; [exact Hacc|].
  apply Forall_cons_iff in Hl. destruct Hl as [H1 Hl]. cbn [fst snd] in *.
  apply IH; [| exact Hl]. destruct (b =? 10); lia.
Qed.
Lemma after_last_nl_range : forall s, 0 <= after_last_nl s <= zlength s.
Proof.
  intros s. unfold after_last_nl. apply fold_nl_range; [unfold zlength; lia|].
  apply Forall_forall. intros [a b] Hin. cbn [fst]. apply in_combine_l in Hin.
  apply in_map_iff in Hin as (k & <- & Hk). apply in_seq in Hk. unfold zlength. lia.
Qed.

(* [comment removed for export] *)
Lemma fwritex_pure_bytes : forall so s, fst (fwritex_pure so s) ++ so_buf (snd (fwritex_pure so s)) = so_buf (towrite_pure so) ++ s.
Proof.
  intros so s. unfold fwritex_pure. set (so1 := towrite_pure so).
  destruct (STDOUT_BUFSIZ - zlength (so_buf so1) <? zlength s).
  - unfold writefn_pure. cbn [fst snd so_buf]. rewrite app_nil_r. unfold ioctl_pure. destruct (so_first so1); reflexivity.
  - destruct (so_lbf_nl so1).
    + destruct (Z.ltb_spec 0 (after_last_nl s)).
      * destruct (writefn_pure so1 (firstn (Z.to_nat (after_last_nl s)) s)) as [e so'] eqn:EW. cbn [fst snd so_buf].
        pose proof (f_equal fst EW) as E1. pose proof (f_equal snd EW) as E2. rewrite writefn_pure_fst in E1. cbn [fst snd] in E1, E2. subst e so'.
        unfold writefn_pure. cbn [snd so_buf]. rewrite <- app_assoc, firstn_skipn. reflexivity.
      * cbn [fst snd so_buf]. pose proof (after_last_nl_range s).
        replace (Z.to_nat (after_last_nl s)) with 0%nat by lia. reflexivity.
    + reflexivity.
Qed.

Lemma fwritex_pure_buf_bound : forall so s,
  zlength (so_buf so) <= STDOUT_BUFSIZ -> zlength (so_buf (snd (fwritex_pure so s))) <= STDOUT_BUFSIZ.
Proof.
  intros so s Hb. unfold fwritex_pure. set (so1 := towrite_pure so).
  assert (Hb1 : zlength (so_buf so1) <= STDOUT_BUFSIZ) by (subst so1; unfold towrite_pure; destruct (so_active so); [exact Hb | unfold zlength, STDOUT_BUFSIZ; cbn; lia]).
  destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength (so_buf so1)) (zlength s)).
  - unfold writefn_pure. cbn [snd so_buf]. unfold zlength, STDOUT_BUFSIZ; cbn; lia.
  - destruct (so_lbf_nl so1).
    + destruct (Z.ltb_spec 0 (after_last_nl s)).
      * destruct (writefn_pure so1 (firstn (Z.to_nat (after_last_nl s)) s)) as [e so'] eqn:EW. cbn [snd so_buf].
        pose proof (f_equal snd EW) as E2. unfold writefn_pure in E2. cbn [snd] in E2. subst so'. cbn [so_buf app].
        unfold zlength in *. rewrite length_skipn. lia.
      * cbn [snd so_buf]. unfold zlength in *. rewrite length_app, length_skipn. lia.
    + cbn [snd so_buf]. unfold zlength in *. rewrite length_app. lia.
Qed.

(* [comment removed for export] *)
Fixpoint pieces_pure (so : stdout_st) (ps : list (list Z)) : list Z * stdout_st :=
  match ps with
  | [] => ([], so)
  | p :: ps' => let r1 := fwritex_pure so p in let r2 := pieces_pure (snd r1) ps' in (fst r1 ++ fst r2, snd r2)
  end.

Lemma pieces_pure_bytes : forall ps so,
  so_active so = true ->
  fst (pieces_pure so ps) ++ so_buf (snd (pieces_pure so ps)) = so_buf so ++ concat ps
  /\ so_active (snd (pieces_pure so ps)) = true.
Proof.
  induction ps as [|p ps IH]; intros so Ha; cbn [pieces_pure fst snd concat].
  - rewrite app_nil_r. auto.
  - assert (A1 : so_active (snd (fwritex_pure so p)) = true).
    { unfold fwritex_pure. destruct (_ <? _); [unfold writefn_pure; reflexivity|].
      destruct (so_lbf_nl _); [destruct (0 <? _); [destruct (writefn_pure _ _) as [e so'] eqn:EW; cbn; pose proof (f_equal snd EW) as E; unfold writefn_pure in E; cbn in E; subst so'; reflexivity | cbn]|cbn];
      unfold towrite_pure; rewrite Ha; exact Ha. }
    destruct (IH _ A1) as [E A2]. split; [| exact A2].
    rewrite <- app_assoc, E, app_assoc, fwritex_pure_bytes. unfold towrite_pure. rewrite Ha, <- app_assoc. reflexivity.
Qed.

Lemma pieces_pure_buf_bound : forall ps so,
  zlength (so_buf so) <= STDOUT_BUFSIZ -> zlength (so_buf (snd (pieces_pure so ps))) <= STDOUT_BUFSIZ.
Proof. induction ps as [|p ps IH]; intros so Hb; cbn [pieces_pure snd]; [exact Hb | apply IH, fwritex_pure_buf_bound, Hb]. Qed.

Lemma trz_out_pieces_k : forall {B} (ps : list (list Z)) (f : unit -> @M St B) (st : St) mo K T,
  mok mo -> zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> Forall (fun p => zlength p + STDOUT_BUFSIZ <= WRITEV_MAX) ps ->
  trzN (f tt (set_so (snd (pieces_pure (get_so st) ps)) st)) mo K T -> T [] ->
  (forall x, set_so (get_so x) x = x) ->
  trzN (mbind (out_pieces get_so set_so ps) f st) mo K (t_emit (Wz 1 (fst (pieces_pure (get_so st) ps))) T).
Proof.
  induction ps as [|p ps IH]; intros f st mo K T Hok Hb Hps Hf HT SG; cbn [out_pieces pieces_pure fst snd].
  - apply trz_mbind_ret. cbn [pieces_pure fst snd] in Hf. rewrite SG in Hf. cbn [Wz to_bytes map]. eapply trz_conseq; [exact Hf | apply t_eq_sym, t_emit_nil_eq; exact HT].
  - apply Forall_cons_iff in Hps. destruct Hps as [Hp Hps].
    apply trz_mbind_assoc. rewrite Wz_app.
    eapply trz_conseq; [| apply t_eq_sym; apply t_eq_emit_app].
    apply (trz_stdout_fwritex_k p _ st mo K _ Hok Hb Hp); [| apply t_emit_has_nil]. cbv beta.
    pose proof (IH f (set_so (snd (fwritex_pure (get_so st) p)) st) mo K T Hok) as W. rewrite !GS, !SS in W.
    apply W; [apply fwritex_pure_buf_bound; exact Hb | exact Hps | exact Hf | exact HT | exact SG].
Qed.

Definition vprintf_pure (so : stdout_st) (ps : list (list Z)) : list Z * stdout_st := pieces_pure (towrite_pure so) ps.

(* [comment removed for export] *)
Lemma trz_stdout_vprintf_k : forall {B} (ps : list (list Z)) (f : unit -> @M St B) (st : St) mo K T,
  mok mo -> zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ -> Forall (fun p => zlength p + STDOUT_BUFSIZ <= WRITEV_MAX) ps ->
  trzN (f tt (set_so (snd (vprintf_pure (get_so st) ps)) st)) mo K T -> T [] ->
  (forall x, set_so (get_so x) x = x) ->
  trzN (mbind (stdout_vprintf get_so set_so ps) f st) mo K (t_emit (Wz 1 (fst (vprintf_pure (get_so st) ps))) T).
Proof.
  intros B ps f st mo K T Hok Hb Hps Hf HT SG. unfold stdout_vprintf, vprintf_pure in *. unfold stdout_towrite.
  apply trz_mbind_assoc. apply (trz_updso get_so set_so).
  pose proof (trz_out_pieces_k ps f (set_so (towrite_pure (get_so st)) st) mo K T Hok) as W. rewrite !GS, !SS in W.
  unfold towrite_pure in W at 1.
  apply W; [| exact Hps | exact Hf | exact HT | exact SG].
  unfold towrite_pure. destruct (so_active (get_so st)); [exact Hb | unfold zlength, STDOUT_BUFSIZ; cbn; lia].
Qed.

(* [comment removed for export] *)
Definition exit_flush_pure (so : stdout_st) : list Z * stdout_st :=
  if 0 <? zlength (so_buf so) then writefn_pure so [] else ([], so).

Lemma trz_stdout_exit_flush_k : forall {B} (f : unit -> @M St B) (st : St) mo K T,
  mok mo -> zlength (so_buf (get_so st)) <= STDOUT_BUFSIZ ->
  trzN (f tt (set_so (snd (exit_flush_pure (get_so st))) st)) mo K T -> T [] ->
  (forall x, set_so (get_so x) x = x) ->
  trzN (mbind (stdout_exit_flush get_so set_so) f st) mo K (t_emit (Wz 1 (fst (exit_flush_pure (get_so st)))) T).
Proof.
  intros B f st mo K T Hok Hb Hf HT SG. unfold stdout_exit_flush, exit_flush_pure in *.
  apply trz_mbind_assoc. apply (trz_rdso get_so).
  destruct (Z.ltb_spec 0 (zlength (so_buf (get_so st)))).
  - eapply trz_eq; [apply (trz_stdout_writefn_k [] f st mo K T Hok); [| exact Hf | exact HT] | rewrite writefn_pure_fst; reflexivity].
    change (zlength (@nil Z)) with 0. unfold STDOUT_BUFSIZ, WRITEV_MAX in *. lia.
  - apply trz_mbind_ret. cbn [fst snd Wz to_bytes map] in Hf |- *. rewrite SG in Hf. eapply trz_conseq; [exact Hf | apply t_eq_sym, t_emit_nil_eq; exact HT].
Qed.
End StdoutK.
End RC__1.
