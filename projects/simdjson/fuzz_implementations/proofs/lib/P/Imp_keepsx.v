(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode MonadX.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc MallocCtrl Monad Stdio Driver Prog.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section Leaves.
  Context {St : Type}.

  Fixpoint leaves_sat {R} (t : itree node R) (P : R -> Prop) : Prop :=
    match t with
    | Ret r => P r
    | Vis n k => forall rsp, leaves_sat (k rsp) P
    | Cho k => forall z, leaves_sat (k z) P
    end.

  Lemma leaves_sat_mono : forall {R} (t : itree node R) (P P' : R -> Prop),
    leaves_sat t P -> (forall r, P r -> P' r) -> leaves_sat t P'.
  Proof.
    induction t as [r|n k IH|kc IHc]; intros P P' H HP; cbn in *; [apply HP; exact H| |].
    - intros rsp. eapply IH; [apply H| exact HP].
    - intros z. eapply IHc; [apply H| exact HP].
  Qed.

  Lemma leaves_sat_bind : forall {A B} (t : itree node A) (f : A -> itree node B) (P1 : A -> Prop) (P : B -> Prop),
    leaves_sat t P1 -> (forall a, P1 a -> leaves_sat (f a) P) -> leaves_sat (ITree.bind node t f) P.
  Proof.
    induction t as [r|n k IH|kc IHc]; intros f P1 P H Hf; cbn in *.
    - apply Hf. exact H.
    - intros rsp. eapply IH; [apply H| exact Hf].
    - intros z. eapply IHc; [apply H| exact Hf].
  Qed.

  Lemma impl_conj_leaves : forall segs {R} (t : itree node R) (P : R -> Prop) (Q : R -> machine_state -> Prop) ms,
    leaves_sat t P -> impl segs (at_node segs) t Q ms -> impl segs (at_node segs) t (fun r ms' => Q r ms' /\ P r) ms.
  Proof.
    intros segs R t. induction t as [r|n k IH|kc IHc]; intros P Q ms HL H; cbn in *.
    - eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| exact HL].
    - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply HL| apply Hk].
    - destruct H as [z H]. exists z. apply IHc; [apply HL| exact H].
  Qed.

  Definition mleaves {A} (c : @M St A) (s : St) (P : A -> St -> Prop) : Prop :=
    leaves_sat (c s) (fun r => match r with Unr => True | Ok p => P (fst p) (snd p) end).

  Lemma implM_conj : forall segs {A} (c : @M St A) s (P : A -> St -> Prop) (Q : A -> St -> machine_state -> Prop) ms,
    mleaves c s P -> implM segs c s Q ms -> implM segs c s (fun a s' ms' => Q a s' ms' /\ P a s') ms.
  Proof.
    intros segs A c s P Q ms HL H. unfold implM, mleaves in *.
    eapply impl_mono; [eapply impl_conj_leaves; [exact HL| exact H]|].
    intros [|[a s']] ms'; cbn; [tauto|]. intros [H1 H2]. split; assumption.
  Qed.

  Lemma mleaves_mono : forall {A} (c : @M St A) s (P P' : A -> St -> Prop),
    mleaves c s P -> (forall a s', P a s' -> P' a s') -> mleaves c s P'.
  Proof. intros A c s P P' H HP. unfold mleaves in *. eapply leaves_sat_mono; [exact H|]. intros [|[a s']]; cbn; auto. Qed.

  Lemma mleaves_ret : forall {A} (a : A) s (P : A -> St -> Prop), P a s -> mleaves (mret a) s P.
  Proof. intros A a s P H. exact H. Qed.
  Lemma mleaves_unr : forall {A} s (P : A -> St -> Prop), mleaves (munr (A:=A)) s P.
  Proof. intros A s P. exact I. Qed.
  Lemma mleaves_get : forall s (P : St -> St -> Prop), P s s -> mleaves mget s P.
  Proof. intros s P H. exact H. Qed.
  Lemma mleaves_upd : forall f s (P : unit -> St -> Prop), P tt (f s) -> mleaves (mupd f) s P.
  Proof. intros f s P H. exact H. Qed.
  Lemma mleaves_put : forall s s1 (P : unit -> St -> Prop), P tt s1 -> mleaves (mput s1) s P.
  Proof. intros s s1 P H. exact H. Qed.
  Lemma mleaves_sys : forall {A} n (dec : resp -> option A) s (P : A -> St -> Prop),
    (forall rsp a, dec rsp = Some a -> P a s) -> mleaves (msys n dec) s P.
  Proof.
    intros A n dec s P H. unfold mleaves, msys. cbn. intros rsp.
    destruct (dec rsp) as [a|] eqn:E; cbn; [| exact I]. apply (H rsp a E).
  Qed.
  Lemma mleaves_cho : forall s (P : Z -> St -> Prop), (forall z, P z s) -> mleaves mcho s P.
  Proof. intros s P H. unfold mleaves, mcho. cbn. intros z. apply H. Qed.

  Lemma mleaves_bind : forall {A B} (m : @M St A) (f : A -> @M St B) s (P1 : A -> St -> Prop) (P : B -> St -> Prop),
    mleaves m s P1 -> (forall a s1, P1 a s1 -> mleaves (f a) s1 P) -> mleaves (mbind m f) s P.
  Proof.
    intros A B m f s P1 P H Hf. unfold mleaves, mbind, ebind in *.
    eapply leaves_sat_bind; [exact H|]. intros [|[a s1]] Ha; cbn in *; [exact I|]. apply Hf. exact Ha.
  Qed.

  Lemma mleaves_loop : forall {X R} fuel (body : X -> @M St (X + R)) (I : St -> Prop) (P : R -> St -> Prop),
    (forall x s, I s -> mleaves (body x) s (fun r s' => match r with inl _ => I s' | inr r' => P r' s' end)) ->
    forall x s, I s -> mleaves (mloop fuel body x) s P.
  Proof.
    intros X R fuel body I P HB. induction fuel as [|fuel IH]; intros x s HI; cbn [mloop].
    - apply mleaves_unr.
    - eapply mleaves_bind; [apply HB; exact HI|]. intros [x'|r] s1 H1; cbn in H1.
      + apply IH. exact H1.
      + apply mleaves_ret. exact H1.
  Qed.
End Leaves.

Section Keeps.
  Context {St V : Type} (proj : St -> V).

  Definition keeps {A} (c : @M St A) : Prop := forall s, mleaves c s (fun _ s' => proj s' = proj s).

  Lemma keeps_ret : forall {A} (a : A), keeps (mret a).
  Proof. intros A a s. apply mleaves_ret. reflexivity. Qed.
  Lemma keeps_unr : forall {A}, keeps (munr (A:=A)).
  Proof. intros A s. apply mleaves_unr. Qed.
  Lemma keeps_get : keeps mget.
  Proof. intros s. apply mleaves_get. reflexivity. Qed.
  Lemma keeps_sys : forall {A} n (dec : resp -> option A), keeps (msys n dec).
  Proof. intros A n dec s. apply mleaves_sys. intros; reflexivity. Qed.
  Lemma keeps_cho : keeps mcho.
  Proof. intros s. apply mleaves_cho. intros; reflexivity. Qed.
  Lemma keeps_upd : forall f, (forall s, proj (f s) = proj s) -> keeps (mupd f).
  Proof. intros f Hf s. apply mleaves_upd. apply Hf. Qed.
  Lemma keeps_bind : forall {A B} (m : @M St A) (f : A -> @M St B), keeps m -> (forall a, keeps (f a)) -> keeps (mbind m f).
  Proof.
    intros A B m f Hm Hf s. eapply mleaves_bind; [apply Hm|]. intros a s1 E1; cbn in E1.
    eapply mleaves_mono; [apply (Hf a s1)|]. intros b s2 E2; cbn in *. congruence.
  Qed.
  Lemma keeps_seq : forall {A B} (m : @M St A) (k : @M St B), keeps m -> keeps k -> keeps (mbind m (fun _ => k)).
  Proof. intros A B m k Hm Hk. apply keeps_bind; [exact Hm| intros; exact Hk]. Qed.
  Lemma keeps_if : forall {A} (b : bool) (c1 c2 : @M St A), keeps c1 -> keeps c2 -> keeps (if b then c1 else c2).
  Proof. intros A [|] c1 c2 H1 H2; assumption. Qed.
  Lemma keeps_loop : forall {X R} fuel (body : X -> @M St (X + R)), (forall x, keeps (body x)) -> forall x, keeps (mloop fuel body x).
  Proof.
    intros X R fuel body HB x s.
    eapply mleaves_mono.
    - apply (mleaves_loop fuel body (fun s' => proj s' = proj s) (fun _ s' => proj s' = proj s)); [| reflexivity].
      intros x0 s0 H0. eapply mleaves_mono; [apply HB|]. intros [x'|r] s1 E; cbn in *; congruence.
    - intros r s' H; exact H.
  Qed.

  Lemma implM_keeps : forall segs {A} (c : @M St A) s Q ms,
    keeps c -> implM segs c s Q ms -> implM segs c s (fun a s' ms' => Q a s' ms' /\ proj s' = proj s) ms.
  Proof. intros segs A c s Q ms K H. apply implM_conj; [apply K| exact H]. Qed.
End Keeps.

Section KeepsX.
  Context {CE__ : Ceiling}.
  Notation keepsx := (keeps ps_x).

  Lemma upd_so_keepsx : forall f, keepsx (upd_so ps_so set_so_ps f).
  Proof. intros f. unfold upd_so. apply keeps_upd. intros s. reflexivity. Qed.

  Lemma ev_step_keepsx : forall e, keepsx (ev_step e).
  Proof.
    intros e. destruct e; cbn [ev_step];
      repeat first [ apply keeps_bind; [| intros] | apply keeps_sys | apply keeps_ret | apply keeps_unr | apply keeps_get
                   | apply keeps_upd; intros; reflexivity | apply keeps_if ].
    all: try (intros; destruct _; first [apply keeps_ret | apply keeps_unr | apply keeps_bind; [apply keeps_upd; intros; reflexivity| intros; apply keeps_ret]]).
  Qed.

  Lemma membed_keepsx : forall {R} (t : stree ev Z R), keepsx (membed t).
  Proof.
    intros R t. induction t as [r|e k IH]; cbn [membed].
    - apply keeps_ret.
    - apply keeps_bind; [apply ev_step_keepsx| intros z; apply IH].
  Qed.

  Lemma raw_malloc_keepsx : forall n, keepsx (raw_malloc n).
  Proof.
    intros n. unfold raw_malloc. apply keeps_bind; [apply keeps_get|]. intros s0.
    apply keeps_bind; [apply membed_keepsx|]. intros [st' p].
    apply keeps_bind; [apply keeps_upd; intros; reflexivity|]. intros []. apply keeps_ret.
  Qed.

  Lemma raw_free_keepsx : forall p, keepsx (raw_free p).
  Proof.
    intros p. unfold raw_free. apply keeps_bind; [apply keeps_get|]. intros s0.
    apply keeps_bind; [apply membed_keepsx|]. intros st'. apply keeps_upd. intros; reflexivity.
  Qed.

  Lemma stdio_writev_keepsx : forall fd a b, keepsx (stdio_writev (St:=PState) fd a b).
  Proof.
    intros fd a b. unfold stdio_writev.
    repeat first [ apply keeps_loop; intros | apply keeps_bind; [| intros] | apply keeps_sys | apply keeps_ret | apply keeps_unr | apply keeps_get | apply upd_so_keepsx
                 | apply keeps_if | progress cbn beta iota | match goal with |- keeps _ (match ?x with _ => _ end) => destruct x end ].
  Qed.

  Lemma stderr_fwrite_keepsx : forall l, keepsx (stderr_fwrite (St:=PState) l).
  Proof. intros l. unfold stderr_fwrite. apply keeps_if; [apply stdio_writev_keepsx| apply keeps_ret]. Qed.

  Lemma stderr_pieces_keepsx : forall ps buf, keepsx (stderr_pieces (St:=PState) buf ps).
  Proof.
    induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces].
    - apply keeps_ret.
    - destruct (_ <? _); [| apply IH]. apply keeps_bind; [apply stdio_writev_keepsx| intros; apply IH].
  Qed.

  Lemma stderr_fprintf_keepsx : forall ps, keepsx (stderr_fprintf (St:=PState) ps).
  Proof. intros ps. unfold stderr_fprintf. apply keeps_bind; [apply stderr_pieces_keepsx| intros; apply stdio_writev_keepsx]. Qed.

  Lemma s_diag_keepsx : forall d, keepsx (s_diag (St:=PState) d).
  Proof. intros d. destruct d; cbn [s_diag]; first [apply stderr_fprintf_keepsx | apply stderr_fwrite_keepsx]. Qed.

  Lemma io_diag_keepsx : forall d, keepsx (io_diag io d).
  Proof. intros d. unfold io, io_S. cbn [io_diag]. apply s_diag_keepsx. Qed.

  Lemma read_loop_body_keepsx : forall (stage : Z) fd path st, keepsx (read_loop_body io raw_malloc raw_free stage fd path st).
  Proof.
    intros stage fd path st. unfold read_loop_body.
    apply keeps_bind.
    - destruct (_ =? _); [| apply keeps_ret]. destruct (_ <=? _).
      + apply keeps_seq; [apply io_diag_keepsx| apply keeps_ret].
      + apply keeps_bind; [apply raw_malloc_keepsx|]. intros [nb|]; [| apply keeps_seq; [apply io_diag_keepsx| apply keeps_ret]].
        apply keeps_seq; [apply raw_free_keepsx| apply keeps_ret].
    - intros [st1|]; [| apply keeps_ret].
      apply keeps_bind; [apply keeps_get|]. intros s0.
      apply keeps_bind; [apply keeps_sys|]. intros [e|bs].
      + apply keeps_seq; [apply io_diag_keepsx| apply keeps_ret].
      + destruct (_ =? _)%nat; apply keeps_ret.
  Qed.

  Lemma read_all_keepsx : forall (stage : Z) path, keepsx (read_all io raw_malloc raw_free stage path).
  Proof.
    intros stage path. unfold read_all.
    apply keeps_bind; [apply keeps_sys|]. intros [e|fd].
    - apply keeps_seq; [apply io_diag_keepsx| apply keeps_ret].
    - apply keeps_bind; [apply raw_malloc_keepsx|]. intros [buf|].
      + apply keeps_bind; [apply keeps_loop; intros; apply read_loop_body_keepsx|]. intros [|buf' content]; [apply keeps_ret|].
        apply keeps_bind; [apply keeps_sys| intros; apply keeps_ret].
      + apply keeps_seq; [apply io_diag_keepsx| apply keeps_ret].
  Qed.

  Lemma diag_free_ret_keepsx : forall d buf (code : Z), keepsx (io_diag io d ;;; raw_free buf ;;; mret code).
  Proof. intros d buf code. apply keeps_seq; [apply io_diag_keepsx|]. apply keeps_seq; [apply raw_free_keepsx| apply keeps_ret]. Qed.
End KeepsX.
