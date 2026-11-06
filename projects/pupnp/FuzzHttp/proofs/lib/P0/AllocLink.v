(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mremap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.

Definition is_mm (n : node) : Prop :=
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ => True | _ => False end.

Fixpoint mm_tree {R} (t : itree node R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => is_mm n /\ forall r, mm_tree (k r)
  end.

Lemma mm_tree_bind {A B} : forall (t : itree node A) (f : A -> itree node B),
  mm_tree t -> (forall a, mm_tree (f a)) -> mm_tree (bind node t f).
Proof.
  induction t as [r|n k IH]; intros f Ht Hf; cbn in *; [apply Hf|].
  destruct Ht as [Hn Hk]. split; [exact Hn|]. intros r. apply IH; auto.
Qed.

Lemma mm_tree_ebind {A B} : forall (t : itree node (exc A)) (f : A -> itree node (exc B)),
  mm_tree t -> (forall a, mm_tree (f a)) -> mm_tree (ebind t f).
Proof.
  intros t f Ht Hf. unfold ebind. apply mm_tree_bind; [exact Ht|]. intros [|a]; cbn; auto.
Qed.

Lemma nstep_mm_silent : forall n mo rsp mo' evs, is_mm n -> nstep n mo rsp mo' evs -> evs = [].
Proof.
  intros n mo rsp mo' evs Hn H. destruct n; try contradiction; cbn [nstep] in H; LiaTuning.ctauto.
Qed.

Lemma nexit_mm : forall n mo code mo', is_mm n -> ~ nexit n mo code mo'.
Proof. intros n mo code mo' Hn H. destruct n; try contradiction; exact H. Qed.

Lemma twf_mm_stwf {R} : forall (t : itree node R) mo (P : R -> Model -> Prop),
  twf t mo P -> mm_tree t -> stwf node nstep nexit nsafe t mo P.
Proof.
  induction t as [r|n k IH]; intros mo P Hw Hm; cbn in *; [exact Hw|].
  destruct Hw as [Hs Hk]. destruct Hm as [Hn Hmk]. split; [exact Hs|]. split.
  - intros code mo'. apply nexit_mm. exact Hn.
  - intros rsp mo' evs Hst. split; [eapply nstep_mm_silent; eauto|]. apply IH; [eapply Hk; eauto| apply Hmk].
Qed.

Definition P0_mrel (mo mo' : Model) : Prop := m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo.
Lemma P0_mrel_refl : forall mo, P0_mrel mo mo. Proof. intros; split; reflexivity. Qed.
Lemma P0_mrel_trans : forall a b c, P0_mrel a b -> P0_mrel b c -> P0_mrel a c.
Proof. intros a b c [A1 A2] [B1 B2]; split; congruence. Qed.
Lemma P0_mrel_fs : forall mo mo', P0_mrel mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo.
Proof. intros mo mo' H; exact H. Qed.
Lemma P0_mrel_of_frame mo mo' : mm_frame mo mo' -> P0_mrel mo mo'. Proof. intros (A & B & _). split; auto. Qed.
Lemma P0_mrel_with_vmmaps h m : P0_mrel m (with_vmmaps h m). Proof. split; reflexivity. Qed.
Lemma P0_mrel_with_vm_backing l1 l2 m : P0_mrel m (with_vm_backing l1 l2 m). Proof. split; reflexivity. Qed.
Lemma P0_mrel_with_mmap_backing fl a n m m0 : P0_mrel m0 m -> P0_mrel m0 (with_mmap_backing fl a n m).
Proof. intros H. unfold with_mmap_backing. destruct (mmap_noreserve_b fl); [| exact H]. unfold vm_add_lazy. eapply P0_mrel_trans; [exact H| apply P0_mrel_with_vm_backing]. Qed.
Lemma P0_mrel_mremap m old on dst nn : P0_mrel m (mremap_model_next m old on dst nn).
Proof. unfold mremap_model_next, vm_resize_backing. eapply P0_mrel_trans; [apply P0_mrel_with_vmmaps|]. apply P0_mrel_with_vm_backing. Qed.

Lemma nstep_mm_rel : forall n mo eff mo' evs, is_mm n -> nstep n mo eff mo' evs -> P0_mrel mo mo'.
Proof.
  intros n mo eff mo' evs Hn H. destruct n; try contradiction; cbn [nstep] in H.
  - destruct H as (-> & (r & _ & _ & ->) & _). apply P0_mrel_of_frame, mm_frame_with_brk_next.
  - destruct H as [-> H]. cbv zeta in H.
    destruct H as [(e & _ & _ & ->)|[(_ & a & _ & _ & _ & ->)|[(_ & _ & a & _ & _ & ->)|(_ & _ & _ & [(_ & ->)|(e & _ & _ & ->)])]]].
    + apply P0_mrel_refl.
    + apply P0_mrel_with_mmap_backing, P0_mrel_with_vmmaps.
    + apply P0_mrel_with_mmap_backing, P0_mrel_with_vmmaps.
    + unfold with_mmap_replacement. apply P0_mrel_with_mmap_backing. apply P0_mrel_of_frame. eapply mm_frame_trans; [| apply mm_frame_vm_forget_range]. apply mm_frame_with_vmmaps. reflexivity.
    + apply P0_mrel_of_frame, mm_frame_with_mmap_destroyed. reflexivity.
  - destruct H as (-> & _ & ->). apply P0_mrel_of_frame, mm_frame_with_mmap_destroyed. reflexivity.
  - destruct H as [-> [(e & _ & _ & ->)|(_ & _ & ->)]]; [apply P0_mrel_refl| apply P0_mrel_of_frame, mm_frame_mprotect_model_next].
  - destruct H as (-> & (core & _ & Hout) & _).
    apply mremap_out_shape in Hout as (_ & _ & [->|(dst & nn & ->)]); [apply P0_mrel_refl|]. apply P0_mrel_mremap.
Qed.

Lemma twf_mm_stwfR {R} : forall (t : itree node R) mo (P : R -> Model -> Prop),
  twf t mo P -> mm_tree t -> stwfR node nstep nexit nsafe P0_mrel t mo P.
Proof.
  induction t as [r|n k IH]; intros mo P Hw Hm; cbn in *; [exact Hw|].
  destruct Hw as [Hs Hk]. destruct Hm as [Hn Hmk]. split; [exact Hs|]. split.
  - intros code mo'. apply nexit_mm. exact Hn.
  - intros rsp mo' evs Hst. split; [eapply nstep_mm_silent; eauto|]. split; [eapply nstep_mm_rel; eauto|].
    apply IH; [eapply Hk; eauto| apply Hmk].
Qed.

Local Open Scope mspec_scope.

Lemma msys_mm {St A} : forall n (dec : resp -> option A) (s : St), is_mm n -> mm_tree (msys n dec s).
Proof. intros n dec s Hn. cbn. split; [exact Hn|]. intros r. destruct (dec r); exact I. Qed.

Lemma mbind_mm {St A B} : forall (m : Monad.M St A) (f : A -> Monad.M St B) (s : St),
  mm_tree (m s) -> (forall a s', mm_tree (f a s')) -> mm_tree (mbind m f s).
Proof. intros m f s Hm Hf. unfold mbind. apply mm_tree_ebind; [exact Hm|]. intros [a s']. apply Hf. Qed.

Lemma mret_mm {St A} : forall (a : A) (s : St), mm_tree (mret a s).
Proof. intros. exact I. Qed.
Lemma mupd_mm {St} : forall f (s : St), mm_tree (mupd f s).
Proof. intros. exact I. Qed.
Lemma mget_mm {St} : forall (s : St), mm_tree (mget s).
Proof. intros. exact I. Qed.

Ltac mm_solve :=
  repeat first [ apply mbind_mm; [| intros]
               | apply msys_mm; exact I
               | apply mret_mm | apply mupd_mm | apply mget_mm
               | exact I
               | match goal with |- mm_tree (match ?x with _ => _ end _) => destruct x end
               | match goal with |- mm_tree ((if ?b then _ else _) _) => destruct b end ].

Lemma ev_step_mm : forall e s, mm_tree (ev_step e s).
Proof.
  intros e s. destruct e as [req|addr len prot flags|addr len|addr len prot|p c h|w];
    cbn -[mbind msys mret mupd mget munr Z.eqb Z.land negb]; mm_solve.
Qed.

Lemma membed_mm {R} : forall (t : stree ev Z R) s, mm_tree (membed t s).
Proof.
  induction t as [r|e k IH]; intros s; cbn -[mbind ev_step mret]; [exact I|].
  apply mbind_mm; [apply ev_step_mm|]. intros z s'. apply IH.
Qed.

Lemma raw_malloc_mm : forall n s, mm_tree (raw_malloc n s).
Proof.
  intros n s. unfold raw_malloc. apply mbind_mm; [exact I|]. intros s0 s1.
  apply mbind_mm; [apply membed_mm|]. intros [st' p] s2. apply mbind_mm; [exact I|]. intros; exact I.
Qed.

Lemma raw_free_mm : forall p s, mm_tree (raw_free p s).
Proof.
  intros p s. unfold raw_free. apply mbind_mm; [exact I|]. intros s0 s1.
  apply mbind_mm; [apply membed_mm|]. intros; exact I.
Qed.

Section Link.
Variable segs : list Segment.

#[using="Type"] Lemma implM_mspec_safe_reach {A} : forall (c : Monad.M PState A) (s : PState) ms mo
    (Qm : A -> PState -> machine_state -> Prop) (P : @assn PState) (Qs : A -> @assn PState),
  implM segs c s Qm ms ->
  mspec P c Qs -> P s mo -> mm_tree (c s) ->
  m_halted mo = None -> minv mo ->
  safe_reach segs (fun cfg => exists a s', Qm a s' (cfg_ms cfg) /\ Qs a s' (cfg_model cfg) /\ Bridge.mframe minv (cfg_model cfg)
                               /\ P0_mrel mo (cfg_model cfg))
             (mkCfg ms mo).
Proof.
  intros c s ms mo Qm P Qs Hi Hsp HP Hmm Hh Hminv.
  pose proof (Hsp s mo HP) as Hw. unfold etwf in Hw.
  pose proof (twf_mm_stwfR (c s) mo _ Hw Hmm) as Hst.
  eapply sr_mono.
  - eapply (impl_stwfR_safe_reach node segs (at_node segs) nstep nexit minv nsafe (nodes_sound segs) P0_mrel P0_mrel_refl P0_mrel_trans);
      [exact Hi| exact Hst| split; assumption].
  - intros cfg (r & HQ & HPr & HF & HM). destruct r as [|[a s']]; cbn in HQ, HPr; [destruct HPr|].
    exists a, s'. auto.
Qed.

End Link.
