(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Frame Exec Cfg ITree Nodes RegsEquiv HaltsTree.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs',
              syscall_spec i m (Monad.Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false)) as [H|H].
  - left. exact H.
  - right. intros eff' m' evs' Hs. destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity|].
    exfalso. apply H. exists eff', m', evs'. split; [exact Hs | exact E].
Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

Lemma run_decided_classic : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof. intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp. cbn [run_decided]. apply decided_from_classic. Qed.

(* [comment removed for export] *)
Lemma must_exit_in_scfg_of_may_fail : forall cfg S img lim en inp,
  cfg_le cfg ACFG ->
  must_exit_in_scfg ACFG S img lim en inp -> must_exit_in_scfg cfg S img lim en inp.
Proof.
  intros cfg S img lim en inp Hle H.
  apply (must_exit_in_scfg_mono cfg ACFG S img lim en inp).
  - exact Hle.
  - apply run_decided_classic.
  - exact H.
Qed.

(* [comment removed for export] *)
Lemma haltsB_of_must_exit_may_fail : forall cfg S img lim,
  cfg_le cfg ACFG ->
  (forall en inp, valid_entry img en inp -> valid_input inp -> must_exit_in_scfg ACFG S img lim en inp) ->
  halts_allowed_T_scfg_budgets cfg lim S img.
Proof.
  intros cfg S img lim Hle H en inp Hve Hvi _. apply (must_exit_in_scfg_of_may_fail cfg); [exact Hle|]. exact (H en inp Hve Hvi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TExits.
  Variable node : Type.
  Variable nexit : node -> Model -> word -> Model -> Prop.
  Variable S : list word.

  Fixpoint texits {R} (t : itree node R) : Prop :=
    match t with
    | Ret _ => True
    | Vis n k => (forall mo code mo', nexit n mo code mo' -> In code S) /\ (forall r, texits (k r))
    end.

  Lemma texits_ret : forall {R} (r : R), texits (Ret r).
  Proof. intros; exact I. Qed.

  Lemma texits_vis : forall {R} n (k : resp -> itree node R),
    (forall mo code mo', nexit n mo code mo' -> In code S) -> (forall r, texits (k r)) -> texits (Vis n k).
  Proof. intros R n k Hn Hk. split; assumption. Qed.

  Lemma texits_bind : forall {A B} (t : itree node A) (f : A -> itree node B),
    texits t -> (forall a, texits (f a)) -> texits (ITree.bind node t f).
  Proof.
    intros A B t. induction t as [r | n k IH]; intros f Ht Hf; cbn.
    - apply Hf.
    - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros r. apply IH; [apply Hk | exact Hf].
  Qed.

  (* [comment removed for export] *)
  Fixpoint tleaves {R} (P : R -> Prop) (t : itree node R) : Prop :=
    match t with
    | Ret r => P r
    | Vis n k => forall r, tleaves P (k r)
    end.

  Lemma tleaves_mono : forall {R} (P P' : R -> Prop) (t : itree node R),
    tleaves P t -> (forall r, P r -> P' r) -> tleaves P' t.
  Proof.
    intros R P P' t. induction t as [r | n k IH]; intros Ht HP; cbn in *.
    - apply HP. exact Ht.
    - intros r. apply IH; [apply Ht | exact HP].
  Qed.

  Lemma tleaves_true : forall {R} (t : itree node R), tleaves (fun _ => True) t.
  Proof. intros R t. induction t as [r | n k IH]; cbn; auto. Qed.

  Lemma tleaves_bind : forall {A B} (P1 : A -> Prop) (P : B -> Prop) (t : itree node A) (f : A -> itree node B),
    tleaves P1 t -> (forall a, P1 a -> tleaves P (f a)) -> tleaves P (ITree.bind node t f).
  Proof.
    intros A B P1 P t. induction t as [r | n k IH]; intros f Ht Hf; cbn.
    - apply Hf. exact Ht.
    - intros r. apply IH; [apply Ht | exact Hf].
  Qed.

  (* [comment removed for export] *)
  Lemma texits_bind_P : forall {A B} (P : A -> Prop) (t : itree node A) (f : A -> itree node B),
    texits t -> tleaves P t -> (forall a, P a -> texits (f a)) -> texits (ITree.bind node t f).
  Proof.
    intros A B P t. induction t as [r | n k IH]; intros f Ht Hr Hf; cbn.
    - apply Hf. exact Hr.
    - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros r. apply IH; [apply Hk | apply Hr | exact Hf].
  Qed.
End TExits.
Arguments texits {node} nexit S {R} t.
Arguments tleaves {node} {R} P t.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BridgeS.
  Variable node : Type.
  Variable segs : list Segment.
  Variable at_node : node -> machine_state -> Prop.
  Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
  Variable nexit : node -> Model -> word -> Model -> Prop.
  Variable minv : Model -> Prop.
  Variable nsafe : node -> Model -> Prop.
  Hypothesis NS : node_sound node segs at_node nstep nexit minv nsafe.
  Hypothesis NK : forall n mo code mo', nexit n mo code mo' -> m_killed mo' = None.
  Variable S : list word.

  Theorem tree_at_must_exit_in_S : forall {R} (t : itree node R) Q ms mo,
    texits nexit S t ->
    tree_at segs at_node nstep minv nsafe t Q ms mo ->
    must_exit_in_at_cfg ACFG segs S (mkCfg ms mo).
  Proof using node segs at_node nstep nexit minv nsafe NS NK S.
    intros R t. induction t as [r | n k IH]; intros Q ms mo HX HT.
    - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret node nstep r mo Hl).
    - destruct HX as [HXn HXk].
      pose proof HT as (Ht & Hl & Hh & Hinv & Hsf).
      cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
      apply (msteps_must_exit_in node segs at_node nstep nexit minv nsafe NS S ms ms1 mo Hm Hh Hinv).
      apply must_exit_in_at_cfg_running.
      + exact Hh.
      + destruct (ns_progress _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & evs & Hst) | (code & mo' & Hex)].
        * destruct (ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (_ & _ & Hss). eauto.
        * destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss). eauto.
      + intros evs Hss.
        destruct (ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs SError Hat Hh Hinv (proj1 Hsf) Hss)
          as [(rsp & mo' & E & _) | (code & mo' & E & _)]; discriminate E.
      + intros evs c' Hss.
        destruct (ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs (SNext c') Hat Hh Hinv (proj1 Hsf) Hss)
          as [(rsp & mo' & E & Hst) | (code & mo' & E & Hex & _)].
        * injection E as ->.
          destruct (tree_at_step node segs at_node nstep nexit minv nsafe NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
          exact (IH rsp Q (nret ms1 rsp) mo' (HXk rsp) HT').
        * injection E as ->.
          destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (Hh' & _).
          apply (must_exit_in_at_cfg_halted ACFG segs S _ code); cbn [cfg_model];
            [exact Hh' | exact (HXn mo code mo' Hex) | exact (NK n mo code mo' Hex)].
  Qed.
End BridgeS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma texits_NExit : forall S c {R} (k : resp -> itree node R),
  In (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) S -> (forall r, texits nexit S (k r)) -> texits nexit S (Vis (NExit c) k).
Proof.
  intros S c R k Hin Hk. split; [|exact Hk].
  intros mo code mo' H. cbn [nexit] in H. destruct H as [-> _]. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma texits_vis_noexit : forall S n {R} (k : resp -> itree node R),
  match n with NExit _ => False | _ => True end -> (forall r, texits nexit S (k r)) -> texits nexit S (Vis n k).
Proof.
  intros S n R k Hn Hk. split; [|exact Hk].
  intros mo code mo' H. destruct n; cbn [nexit] in H; contradiction.
Qed.

Theorem halts_of_impl_tree_S : forall segs pc ph lim S {R} (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  valid_entry (mkImage segs pc ph) en inp ->
  in_va_size inp = Sv48 ->
  texits nexit S t ->
  impl segs (at_node segs) t Q
       (init_ms segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) ->
  leaves_unreachable_m nstep t (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp) ->
  tsafe nstep nsafe t (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp) ->
  must_exit_in_scfg ACFG S (mkImage segs pc ph) lim en inp.
Proof.
  intros segs pc ph lim S R t Q [sp brk0 mbase rnd] inp Hve Hsv48 HX Himpl Hleaves Hsafe.
  cbn [en_sp en_brk en_mmap_base en_draw] in Himpl, Hleaves, Hsafe.
  cbn [must_exit_in_scfg]. unfold init_config.
  set (mo := init_model (segments_reserved segs) brk0 mbase sp lim inp) in *.
  assert (Hminv : minv mo).
  { rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve. destruct Hve as (Vsp & _ & _ & _).
    apply minv_init. destruct Vsp as (L & H & _). lia. }
  apply (must_exit_in_at_eqv segs S
           (mkCfg (init_ms segs pc ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd) mo)).
  - apply (tree_at_must_exit_in_S node segs (at_node segs) nstep nexit minv nsafe (nodes_sound segs)
             hx_nexit_not_killed S t Q _ _ HX).
    split; [exact Himpl | split; [exact Hleaves | split; [reflexivity | split; [exact Hminv | exact Hsafe]]]].
  - split; [| reflexivity]. cbn [cfg_ms]. apply ms_eqv_sym. apply init_machine_state_eqv.
Qed.
