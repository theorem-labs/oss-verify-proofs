(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kclosed (K : config -> Prop) : Prop :=
  forall (c : config) (I : Type) (i0 : I) (nx : I -> config),
    node_ok segs c I (fun _ => []) nx -> (forall i, K (nx i)) -> K c.

Lemma t_alt_const_emit_nil : forall (I : Type) (i0 : I) (T : TSet),
  T [] -> t_eq (t_alt (fun _ : I => t_emit [] T)) T.
Proof.
  intros I i0 T HT tr. split.
  - intros [i [Hp | (tr' & -> & Ht)]].
    + apply is_prefix_nil_r in Hp. subst tr. exact HT.
    + exact Ht.
  - intros Ht. exists i0. right. exists tr. split; [reflexivity | exact Ht].
Qed.

Lemma kclosed_realizes : forall T, kclosed (fun c => realizes segs c T).
Proof.
  intros T c I i0 nx Hn HK.
  apply (rz_conseq segs c (t_alt (fun _ : I => t_emit [] T))).
  - apply (rz_node segs c I (fun _ => []) nx (fun _ => T) i0 Hn). exact HK.
  - apply (t_alt_const_emit_nil I i0). eapply realizes_nonempty. exact (HK i0).
Qed.



Lemma kclosed_true : kclosed (fun _ => True).
Proof. intros c J j0 nx _ _. exact Logic.I. Qed.




(* [comment removed for export] *)
Definition kat (c : config) (Q : config -> Prop) : Prop :=
  forall K, kclosed K -> (forall c', Q c' -> K c') -> K c.

Lemma kat_refl : forall c (Q : config -> Prop), Q c -> kat c Q.
Proof. intros c Q Hq K _ Hk. apply Hk. exact Hq. Qed.

Lemma kat_conseq : forall c (Q Q' : config -> Prop),
  kat c Q -> (forall c', Q c' -> Q' c') -> kat c Q'.
Proof. intros c Q Q' H HQ K HK Hk. apply (H K HK). intros c' Hq. apply Hk, HQ, Hq. Qed.




(* [comment removed for export] *)
Lemma node_ok_reindex : forall c (I J : Type) (evs : I -> list event) (nx : I -> config)
    (evs' : J -> list event) (nx' : J -> config) (f : J -> I) (g : I -> J),
  node_ok segs c I evs nx ->
  (forall j, evs (f j) = evs' j /\ nx (f j) = nx' j) ->
  (forall i, evs i = evs' (g i) /\ nx i = nx' (g i)) ->
  node_ok segs c J evs' nx'.
Proof.
  intros c I J evs nx evs' nx' f g [N1 N2] Hf Hg. split.
  - intros j. destruct (Hf j) as [E1 E2]. rewrite <- E1, <- E2. apply N1.
  - intros e st Hss. destruct (N2 e st Hss) as (i & -> & ->). exists (g i).
    destruct (Hg i) as [E1 E2]. rewrite E1, E2. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kat_node : forall c (I : Type) (i0 : I) (nx : I -> config) (Q : config -> Prop),
  node_ok segs c I (fun _ => []) nx -> (forall i, kat (nx i) Q) -> kat c Q.
Proof.
  intros c I i0 nx Q Hn Hi K HK Hk. apply (HK c I i0 nx Hn). intros i. apply (Hi i K HK). exact Hk.
Qed.

(* [comment removed for export] *)
Definition qor (Q1 Q2 : config -> Prop) : config -> Prop := fun c => Q1 c \/ Q2 c.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kat_step : forall ms model ms' (Q : config -> Prop),
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  kat (mkCfg ms' model) Q -> kat (mkCfg ms model) Q.
Proof.
  intros ms model ms' Q Hh Hl Hsvc Hst Hk.
  apply (kat_node (mkCfg ms model) unit tt (fun _ => mkCfg ms' model)).
  - apply node_instr; assumption.
  - intros []. exact Hk.
Qed.

Lemma kat_msteps : forall ms ms' model (Q : config -> Prop),
  m_halted model = None -> m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  kat (mkCfg ms' model) Q -> kat (mkCfg ms model) Q.
Proof.
  intros ms ms' model Q Hh Hl Hms.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hst Hms IH]; intros Hk; [exact Hk|].
  eapply kat_step; [exact Hh | exact Hl | exact Hsvc | exact Hst | apply IH; exact Hk].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kat_munmap : forall ms model x8 (Q : config -> Prop),
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 215 ->
  munmap_args_ok ms model ->
  kat (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
             (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) Q ->
  kat (mkCfg ms model) Q.
Proof.
  intros ms model x8 Q Hh Hlazy Hsvc Hno Hargs Hk.
  apply (kat_node _ unit tt _ Q (node_munmap segs ms model x8 Hh Hlazy Hsvc Hno Hargs)).
  intros []. exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record kfam := KF { Kok : config -> Prop ; Kf : config -> Prop ; Kp : config -> Prop ; Kw : config -> Prop }.

(* [comment removed for export] *)
Record kfam_laws (F : kfam) : Prop := KL {
  kl_ok : kclosed (Kok F);
  kl_f : kclosed (Kf F);
  kl_p : kclosed (Kp F);
  kl_w : kclosed (Kw F);
  kl_okw : forall c, Kok F c -> Kw F c;
  kl_pw : forall c, Kp F c -> Kw F c;
  kl_wp : forall c, Kw F c -> Kp F c }.

(* [comment removed for export] *)
Definition kfam1 (K : config -> Prop) : kfam := KF K K K K.


(* [comment removed for export] *)
Definition kfam_ok (K : config -> Prop) : kfam := KF K (fun _ => True) K K.

Lemma kfam_ok_laws : forall K, kclosed K -> kfam_laws (kfam_ok K).
Proof.
  intros K HK. constructor; cbn; try exact HK; try (intros c X; exact X).
  exact kclosed_true.
Qed.

(* [comment removed for export] *)
Definition kats (c : config) (Qok Qf : config -> Prop) : Prop :=
  forall F, kfam_laws F -> (forall c', Qok c' -> Kok F c') -> (forall c', Qf c' -> Kf F c') -> Kp F c.

(* [comment removed for export] *)
Definition katw (c : config) (Qok Qf : config -> Prop) : Prop :=
  forall F, kfam_laws F -> (forall c', Qok c' -> Kok F c') -> (forall c', Qf c' -> Kf F c') -> Kw F c.

Lemma kats_katw : forall c Qok Qf, kats c Qok Qf -> katw c Qok Qf.
Proof. intros c Qok Qf H F HL Hok Hf. apply (kl_pw F HL). exact (H F HL Hok Hf). Qed.









(* [comment removed for export] *)
Lemma katw_ok_only : forall c Qok Qf, katw c Qok Qf -> kat c Qok.
Proof.
  intros c Qok Qf H K HK Hk.
  exact (H (kfam_ok K) (kfam_ok_laws K HK) Hk (fun _ _ => Logic.I)).
Qed.







End WithSegs.

Arguments kclosed segs K%_function_scope.
