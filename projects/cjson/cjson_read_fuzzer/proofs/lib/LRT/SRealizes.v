(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ExitSim.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim.SimInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ExitSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RealizesEqv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RealizesEqv.RegsEqv0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RealizesEqv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)

Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (forall i, srealizes (nx i) (T i)) ->
    srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes c t_nil
| srz_jspin : forall c,
    jspinning segs c ->
    srealizes c t_nil
| srz_conseq : forall c T T',
    srealizes c T -> t_eq T T' -> srealizes c T'.

Lemma srealizes_of_realizes : forall c T,
  realizes segs c T -> srealizes c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz_node c I evs nx T i0 Hnode IH).
  - exact (srz_halt c Hh).
  - exact (srz_conseq c T T' IH Heq).
Qed.

(* [comment removed for export] *)
Lemma srz_spin : forall c,
  to_jself segs (cfg_ms c) (cfg_model c) -> m_halted (cfg_model c) = None -> srealizes c t_nil.
Proof. intros [ms mo] Hs Hh. apply srz_jspin. split; assumption. Qed.

(* [comment removed for export] *)

Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hc | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma srealizes_pclosed : forall c T, srealizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hc | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* [comment removed for export] *)

Lemma srealizes_star_only : forall c T, srealizes c T ->
  forall tr c', star_cfg segs ACFG c tr c' -> T tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hc | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2.
      split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs ACFG c tr c' Hh Hstar) as [-> _]. reflexivity.
  - exact (silent_loop_star_nil segs _ c tr c' (jspinning_silent_loop segs) Hc (star_cfg_sub segs ACFG _ _ _ Hstar)).
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma srealizes_admits : forall c T, srealizes c T ->
  forall tr, T tr -> obs_trace_cfg segs ACFG c tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hc | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar]
             | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
Qed.

Theorem srealizes_obs_iff : forall c T, srealizes c T ->
  forall tr, obs_trace_cfg segs ACFG c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply srealizes_pclosed;
      [exact H | eapply srealizes_star_only; eauto | exact Hp].
  - apply srealizes_admits; exact H.
Qed.

(* [comment removed for export] *)

Lemma srealizes_step : forall c T e c',
  srealizes c T -> sstep_cfg segs ACFG c e (SNext c') -> exists T', srealizes c' T'.
Proof.
  intros c T e c' H; revert e c';
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hc | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
  - destruct (silent_loop_sstep segs _ c e (SNext c') (jspinning_silent_loop segs) Hc (sstep_cfg_sub segs ACFG _ _ _ Hss)) as (_ & c'' & Heq2 & Hc'').
    injection Heq2 as ->. exists t_nil. exact (srz_jspin _ Hc'').
  - eapply IH; exact Hss.
Qed.

Lemma srealizes_no_sserror : forall c T e,
  srealizes c T -> ~ sstep_cfg segs ACFG c e SError.
Proof.
  intros c T e H; revert e;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hc | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_halted_none; exact Hss.
  - destruct (silent_loop_sstep segs _ c e SError (jspinning_silent_loop segs) Hc (sstep_cfg_sub segs ACFG _ _ _ Hss)) as (_ & c' & Heq & _). discriminate Heq.
  - eapply IH; exact Hss.
Qed.

Definition srz_path (c : config) : Prop := exists T, srealizes c T.

Lemma srealizes_star : forall c T tr c',
  srealizes c T -> star_cfg segs ACFG c tr c' -> exists T', srealizes c' T'.
Proof.
  intros c T tr c' H Hstar. revert T H.
  induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros T H.
  - exists T. exact H.
  - destruct (srealizes_step c1 T evs c2 H Hss) as [T2 H2]. exact (IH T2 H2).
Qed.

Theorem srealizes_no_error : forall c T,
  srealizes c T -> ~ reaches_error_cfg segs ACFG c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  destruct (srealizes_star c T tr c' H Hstar) as [T' H'].
  exact (srealizes_no_sserror c' T' evs H' Herr).
Qed.

(* [comment removed for export] *)

Lemma srz_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  srealizes c' T ->
  srealizes c T.
Proof.
  intros c c' T Hnode Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.

Lemma srz_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  srealizes c' T ->
  srealizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (srz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

Lemma srz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  (forall i, srealizes (nx (inl i)) A) ->
  (forall i, srealizes (nx (inr i)) B) ->
  srealizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply srealizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  apply (srz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end)
             (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)
Lemma srz_silent : forall c (I : Type) (nx : I -> config) (B : TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, srealizes (nx i) B) ->
  srealizes c B.
Proof.
  intros c I nx B i0 Hnode HB.
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB i0)).
  apply (srz_conseq c (t_alt (fun i : I => t_emit [] B))).
  - apply (srz_node c I (fun _ => []) nx (fun _ => B) i0 Hnode). exact HB.
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
    + intro H. exists i0. exact (proj2 (t_emit_nil_eq B HB0 tr) H).
Qed.

(* [comment removed for export] *)
Lemma srz_silent_spin : forall c (I : Type) (nx : I -> config) (sp : I -> bool) (B : TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  sp i0 = false ->
  (forall i, sp i = true -> jspinning segs (nx i)) ->
  (forall i, sp i = false -> srealizes (nx i) B) ->
  srealizes c B.
Proof.
  intros c I nx sp B i0 Hnode Hi0 Hsp HB.
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB i0 Hi0)).
  apply (srz_conseq c (t_alt (fun i : I => t_emit [] (if sp i then t_nil else B)))).
  - apply (srz_node c I (fun _ => []) nx (fun i => if sp i then t_nil else B) i0 Hnode).
    intros i. destruct (sp i) eqn:E.
    + apply srz_jspin. apply Hsp. exact E.
    + apply HB. exact E.
  - intro tr. split.
    + intros [i Hi]. destruct (sp i).
      * apply (t_emit_nil_eq t_nil eq_refl tr) in Hi. unfold t_nil in Hi. subst tr. exact HB0.
      * exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
    + intro H. exists i0. rewrite Hi0. exact (proj2 (t_emit_nil_eq B HB0 tr) H).
Qed.

(* [comment removed for export] *)
Lemma srz_silent_spin_sum : forall c (IA IB : Type) (nx : IA + IB -> config) (B : TSet) (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  (forall i, jspinning segs (nx (inl i))) ->
  (forall i, srealizes (nx (inr i)) B) ->
  srealizes c B.
Proof.
  intros c IA IB nx B b0 Hnode HA HB.
  apply (srz_silent_spin c (IA + IB) nx (fun i => match i with inl _ => true | inr _ => false end) B (inr b0));
    [exact Hnode | reflexivity | |].
  - intros [i|i]; [intros _; apply HA | discriminate].
  - intros [i|i]; [discriminate | intros _; apply HB].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma to_jself_eqv : forall ms mo, to_jself segs ms mo -> forall ms', ms_eqv ms ms' -> to_jself segs ms' mo.
Proof.
  intros ms mo H. induction H as [ms mo Hsvc Hf | ms mo ms1 mo1 Hsvc Hacc H IH]; intros ms' Heqv.
  - pose proof Heqv as (_ & _ & Hpc & Hsv & _). apply tj_here; [congruence|].
    unfold ms_pc in *. rewrite <- Hpc. exact Hf.
  - pose proof Heqv as (_ & _ & _ & Hsv & _).
    pose proof (mi_account_step_eqv segs ms ms' mo Heqv) as Hres. rewrite Hacc in Hres.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; cbn in Hres; try contradiction.
    destruct Hres as [Hms <-].
    eapply tj_step; [congruence| exact E| apply IH; exact Hms].
Qed.

Lemma jspinning_eqv : forall c c', jspinning segs c -> cfg_eqv c c' -> jspinning segs c'.
Proof.
  intros [ms mo] [ms' mo'] [Hj Hh] [Heqv Hmo]; cbn in *. subst mo'. split; [eapply to_jself_eqv; eassumption| exact Hh].
Qed.

Theorem srealizes_cfg_eqv : forall c T,
  srealizes c T -> forall c', cfg_eqv c c' -> srealizes c' T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 Hnode Hk IH | c Hh | c Hc | c T T' H IH Heq];
    intros c' Heqv.
  - destruct c as [ms mo], c' as [ms' mo']. destruct Heqv as [Hms Hmo]; simpl in Hms, Hmo; subst mo'.
    destruct (node_ok_xfer segs ms ms' mo I evs nx Hms Hnode) as [Hnode' Hx].
    apply (srz_node (mkCfg ms' mo) I evs (fun i => xfer segs ms' mo (nx i)) T i0 Hnode').
    intros i. apply (IH i). apply Hx.
  - apply srz_halt. destruct Heqv as [_ <-]. exact Hh.
  - apply srz_jspin. eapply jspinning_eqv; eassumption.
  - apply (srz_conseq c' T T'); [apply IH; exact Heqv | exact Heq].
Qed.

Theorem srealizes_ms_eqv : forall ms1 ms2 mo T,
  ms_eqv ms1 ms2 ->
  srealizes (mkCfg ms1 mo) T -> srealizes (mkCfg ms2 mo) T.
Proof.
  intros ms1 ms2 mo T Heqv H. apply (srealizes_cfg_eqv _ _ H). split; [exact Heqv | reflexivity].
Qed.

End WithSegs.
