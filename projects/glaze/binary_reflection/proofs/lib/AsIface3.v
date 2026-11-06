(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.MhK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsK.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MhK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

#[local] Notation kclosed := (kclosed segs).
#[local] Notation kat := (kat segs).
#[local] Notation kats := (kats segs).
#[local] Notation katw := (katw segs).
#[local] Notation kfam_laws := (kfam_laws segs).
#[local] Notation node_ok := (node_ok segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition doomed (c : config) : Prop := kat c (spinning segs).

Lemma doomed_spinning : forall c, spinning segs c -> doomed c.
Proof. intros c H. apply kat_refl. exact H. Qed.

Lemma doomed_to_spin : forall ms model,
  to_spin segs ms model -> m_halted model = None -> doomed (mkCfg ms model).
Proof. intros ms model Hs Hh. apply doomed_spinning. split; assumption. Qed.


(* [comment removed for export] *)
Lemma doomed_node : forall c (I : Type) (i0 : I) (nx : I -> config),
  node_ok c I (fun _ => []) nx -> (forall i, doomed (nx i)) -> doomed c.
Proof. intros c I i0 nx Hn Hd. exact (kat_node segs c I i0 nx _ Hn Hd). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kclosedD (K : config -> Prop) : Prop :=
  forall (c : config) (I : Type) (i0 : I) (nx : I -> config),
    node_ok c I (fun _ => []) nx ->
    K (nx i0) ->
    (forall i, K (nx i) \/ False) ->
    K c.



Lemma kclosedD_true : kclosedD (fun _ => True).
Proof. intros c J j0 nx _ _ _. exact Logic.I. Qed.

(* [comment removed for export] *)
Lemma kclosedD_of_kclosed : forall K, kclosed K -> kclosedD K.
Proof.
  intros K HK c I i0 nx Hn _ Hall. apply (HK c I i0 nx Hn).
  intros i. destruct (Hall i) as [X|[]]; exact X.
Qed.


Definition katD (c : config) (Q : config -> Prop) : Prop :=
  forall K, kclosedD K -> (forall c', Q c' -> K c') -> K c.




Lemma katD_refl : forall c (Q : config -> Prop), Q c -> katD c Q.
Proof. intros c Q Hq K _ Hk. apply Hk. exact Hq. Qed.

Lemma katD_conseq : forall c (Q Q' : config -> Prop),
  katD c Q -> (forall c', Q c' -> Q' c') -> katD c Q'.
Proof. intros c Q Q' H HQ K HK Hk. apply (H K HK). intros c' Hq. apply Hk, HQ, Hq. Qed.

Lemma katD_bind : forall c (Q R : config -> Prop),
  katD c Q -> (forall c', Q c' -> katD c' R) -> katD c R.
Proof.
  intros c Q R H1 H2 K HK Hk. apply (H1 K HK). intros c' Hq. apply (H2 c' Hq K HK). exact Hk.
Qed.




(* [comment removed for export] *)
Lemma katD_node : forall c (I : Type) (i0 : I) (nx : I -> config) (Q : config -> Prop),
  node_ok c I (fun _ => []) nx -> (forall i, katD (nx i) Q) -> katD c Q.
Proof.
  intros c I i0 nx Q Hn Hi K HK Hk. apply (HK c I i0 nx Hn).
  - exact (Hi i0 K HK Hk).
  - intros i. left. exact (Hi i K HK Hk).
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record kfamD_laws (F : kfam) : Prop := KLD {
  klD_ok : kclosedD (Kok F);
  klD_f : kclosedD (Kf F);
  klD_p : kclosedD (Kp F);
  klD_w : kclosedD (Kw F);
  klD_okw : forall c, Kok F c -> Kw F c;
  klD_pw : forall c, Kp F c -> Kw F c;
  klD_wp : forall c, Kw F c -> Kp F c }.



(* [comment removed for export] *)
Lemma kfamD1_laws : forall K, kclosedD K -> kfamD_laws (kfam1 K).
Proof. intros K HK. constructor; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); try exact HK; intros c X; exact X. Qed.

(* [comment removed for export] *)
Lemma kfamD_ok_laws : forall K, kclosedD K -> kfamD_laws (kfam_ok K).
Proof.
  intros K HK. constructor; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); try exact HK; try (intros c X; exact X).
  exact kclosedD_true.
Qed.

(* [comment removed for export] *)
Definition katsD (c : config) (Qok Qf : config -> Prop) : Prop :=
  forall F, kfamD_laws F -> (forall c', Qok c' -> Kok F c') -> (forall c', Qf c' -> Kf F c') -> Kp F c.

(* [comment removed for export] *)
Definition katwD (c : config) (Qok Qf : config -> Prop) : Prop :=
  forall F, kfamD_laws F -> (forall c', Qok c' -> Kok F c') -> (forall c', Qf c' -> Kf F c') -> Kw F c.





Lemma katsD_katwD : forall c Qok Qf, katsD c Qok Qf -> katwD c Qok Qf.
Proof. intros c Qok Qf H F HL Hok Hf. apply (klD_pw F HL). exact (H F HL Hok Hf). Qed.

(* [comment removed for export] *)
Lemma katwD_katD : forall c Qok Qf, katwD c Qok Qf -> katD c (qor Qok Qf).
Proof.
  intros c Qok Qf H K HK Hk.
  exact (H (kfam1 K) (kfamD1_laws K HK) (fun c' X => Hk c' (or_introl X)) (fun c' X => Hk c' (or_intror X))).
Qed.


(* [comment removed for export] *)
Lemma katsD_of_katwD : forall c Qok Qf, katwD c Qok Qf -> katsD c Qok Qf.
Proof. intros c Qok Qf H F HL Hok Hf. apply (klD_wp F HL). exact (H F HL Hok Hf). Qed.

(* [comment removed for export] *)
Lemma katwD_ok_only : forall c Qok Qf, katwD c Qok Qf -> katD c Qok.
Proof.
  intros c Qok Qf H K HK Hk.
  exact (H (kfam_ok K) (kfamD_ok_laws K HK) Hk (fun _ _ => Logic.I)).
Qed.

Lemma katsD_ok_only : forall c Qok Qf, katsD c Qok Qf -> katD c Qok.
Proof. intros c Qok Qf H. apply (katwD_ok_only c Qok Qf), katsD_katwD, H. Qed.

(* [comment removed for export] *)
Lemma katwD_of_katD : forall c (Qok Qf : config -> Prop), katD c Qok -> katwD c Qok Qf.
Proof.
  intros c Qok Qf H F HL Hok Hf. apply (klD_okw F HL). apply (H (Kok F) (klD_ok F HL)). exact Hok.
Qed.

Lemma katsD_conseq : forall c (Qok Qok' Qf Qf' : config -> Prop),
  katsD c Qok Qf -> (forall c', Qok c' -> Qok' c') -> (forall c', Qf c' -> Qf' c') -> katsD c Qok' Qf'.
Proof. intros c Qok Qok' Qf Qf' H H1 H2 F HL Hok Hf. apply (H F HL); intros c' X; [apply Hok, H1, X | apply Hf, H2, X]. Qed.

Lemma katwD_conseq : forall c (Qok Qok' Qf Qf' : config -> Prop),
  katwD c Qok Qf -> (forall c', Qok c' -> Qok' c') -> (forall c', Qf c' -> Qf' c') -> katwD c Qok' Qf'.
Proof. intros c Qok Qok' Qf Qf' H H1 H2 F HL Hok Hf. apply (H F HL); intros c' X; [apply Hok, H1, X | apply Hf, H2, X]. Qed.







(* [comment removed for export] *)
Lemma katwD_node : forall c (I : Type) (i0 : I) (nx : I -> config) (Qok Qf : config -> Prop),
  node_ok c I (fun _ => []) nx -> (forall i, katwD (nx i) Qok Qf) -> katwD c Qok Qf.
Proof.
  intros c I i0 nx Qok Qf Hn Hi F HL Hok Hf. apply (klD_w F HL c I i0 nx Hn).
  - exact (Hi i0 F HL Hok Hf).
  - intros i. left. exact (Hi i F HL Hok Hf).
Qed.



End WithSegs.
End AsK.
Module MhKInst.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.MhK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.










Definition Tr (c : config) : TSet := obs_trace_cfg segs CfgStep.kit_cfg c.

Lemma Tr_nil : forall c, Tr c []. Proof. intros c. apply obs_trace_cfg_nil. Qed.




(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sr_exactness (R : shape_rel segs) : Prop := forall c T, R c T -> t_eq (Tr c) T.

Lemma exact_realizes : sr_exactness (SR_realizes segs).
Proof. intros c T H tr. exact (realizes_obs_iff segs c T H tr). Qed.





Section Exact.
  Variable R : shape_rel segs.
  Hypothesis SRX : sr_exactness R.
  Variables Tok Tnull : TSet.
  Hypothesis Tok0 : Tok [].
  Hypothesis Tnull0 : Tnull [].




  Lemma kclosed_R : forall T, kclosed segs (fun c => R c T).
  Proof.
    intros T c I i0 nx Hn HK.
    assert (T0 : T []).
    { apply (proj1 (SRX (nx i0) T (HK i0) [])). apply Tr_nil. }
    apply (sr_conseq segs R c (t_alt (fun _ : I => t_emit [] T))).
    - apply (sr_node segs R c I (fun _ => []) nx (fun _ => T) i0 Hn). exact HK.
    - apply (t_alt_const_emit_nil I i0). exact T0.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem kat_exact : forall c (Q : config -> Prop) (T : TSet),
    kat segs c Q -> (forall c', Q c' -> R c' T) -> R c T.
  Proof. intros c Q T H HQ. exact (H (fun c => R c T) (kclosed_R T) HQ). Qed.

  (* [comment removed for export] *)
  Theorem kat_ok_exact : forall c (Qok Qf : config -> Prop) (T : TSet),
    katw segs c Qok Qf -> (forall c', Qok c' -> R c' T) -> R c T.
  Proof. intros c Qok Qf T H HQ. exact (kat_exact c Qok T (katw_ok_only segs c Qok Qf H) HQ). Qed.

  Theorem kats_ok_exact : forall c (Qok Qf : config -> Prop) (T : TSet),
    kats segs c Qok Qf -> (forall c', Qok c' -> R c' T) -> R c T.
  Proof. intros c Qok Qf T H HQ. exact (kat_ok_exact c Qok Qf T (kats_katw segs c Qok Qf H) HQ). Qed.
End Exact.

End WithSegs.
End MhKInst.
Module AsKInst.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.MhK MhKInst AsK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import MhK.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

#[local] Notation Tr := (Tr segs).
#[local] Notation doomed := (doomed segs).
#[local] Notation kclosedD := (kclosedD segs).
#[local] Notation katD := (katD segs).
#[local] Notation katwD := (katwD segs).
#[local] Notation katsD := (katsD segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sr_spin (R : shape_rel segs) : Prop := forall c, spinning segs c -> R c t_nil.




(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Exact.
  Variable R : shape_rel segs.
  Hypothesis SRX : sr_exactness segs R.

  (* [comment removed for export] *)
  Theorem kclosedD_R : forall T, kclosedD (fun c => R c T).
  Proof. intros T. exact (kclosedD_of_kclosed segs (fun c => R c T) (kclosed_R segs R SRX T)). Qed.





  (* [comment removed for export] *)
  Section Spin.
    Hypothesis SRS : sr_spin R.


  End Spin.
End Exact.

(* [comment removed for export] *)
Corollary kclosedD_realizes : forall T, kclosedD (fun c => realizes segs c T).
Proof. exact (kclosedD_R (SR_realizes segs) (exact_realizes segs)). Qed.













(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Progress.
  Variables P Q : config -> Prop.




End Progress.







End WithSegs.
End AsKInst.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtK.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct AsK.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

#[local] Notation kclosedD := (kclosedD segs).
#[local] Notation katD := (katD segs).
#[local] Notation katwD := (katwD segs).
#[local] Notation katsD := (katsD segs).

Lemma node_ok_same : AsVocab.AsanAcct.node_ok segs = StoreOk.ShapeAlg.node_ok segs.
Proof using. reflexivity. Qed.

(* [comment removed for export] *)
Lemma kclosedD_silent1 : forall K, kclosedD K ->
  forall c c', AsVocab.AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') -> K c' -> K c.
Proof using.
  intros K HK c c' Hn Hk. rewrite node_ok_same in Hn.
  apply (HK c unit tt (fun _ => c') Hn Hk). intros _; left; exact Hk.
Qed.

(* [comment removed for export] *)
Lemma K_step_acct : forall (K : config -> Prop) A ms msr' model,
  kclosedD K ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  K (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  K (mkCfg ms model).
Proof using Hwx HH.
  intros K A ms msr' model HK.
  exact (rz_step_restricted segs H HH Hwx K (kclosedD_silent1 K HK) A ms msr' model).
Qed.

Lemma K_msteps_acct : forall (K : config -> Prop) A ms msr' model,
  kclosedD K ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      K (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  K (mkCfg ms model).
Proof using Hwx HH.
  intros K A ms msr' model HK.
  exact (rz_msteps_restricted' segs H HH Hwx K (kclosedD_silent1 K HK) A ms msr' model).
Qed.

(* [comment removed for export] *)
Theorem katD_step_acct : forall A ms msr' model (Q : config -> Prop),
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  katD (mkCfg (unrestrict H (ms_mem ms) msr') model') Q) ->
  katD (mkCfg ms model) Q.
Proof using Hwx HH.
  intros A ms msr' model Q Hcov Hwf Hinv Hh Hsvc Hs Hk K HK HQ.
  apply (K_step_acct K A ms msr' model HK Hcov Hwf Hinv Hh Hsvc Hs).
  intros model' Hinv' Hsame'. exact (Hk model' Hinv' Hsame' K HK HQ).
Qed.

Theorem katD_msteps_acct : forall A ms msr' model (Q : config -> Prop),
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      katD (mkCfg (unrestrict H (ms_mem ms) msr') model') Q) ->
  katD (mkCfg ms model) Q.
Proof using Hwx HH.
  intros A ms msr' model Q Hcov Hwf Hinv Hh Hms Hk K HK HQ.
  apply (K_msteps_acct K A ms msr' model HK Hcov Hwf Hinv Hh Hms).
  intros model' Hinv' Hsame' Hcl. exact (Hk model' Hinv' Hsame' Hcl K HK HQ).
Qed.

(* [comment removed for export] *)
Theorem katwD_msteps_acct : forall A ms msr' model (Qok Qf : config -> Prop),
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      katwD (mkCfg (unrestrict H (ms_mem ms) msr') model') Qok Qf) ->
  katwD (mkCfg ms model) Qok Qf.
Proof using Hwx HH.
  intros A ms msr' model Qok Qf Hcov Hwf Hinv Hh Hms Hk F HF Hok Hf.
  apply (K_msteps_acct (MhK.Kw F) A ms msr' model (klD_w segs F HF) Hcov Hwf Hinv Hh Hms).
  intros model' Hinv' Hsame' Hcl. exact (Hk model' Hinv' Hsame' Hcl F HF Hok Hf).
Qed.

Theorem katwD_step_acct : forall A ms msr' model (Qok Qf : config -> Prop),
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  katwD (mkCfg (unrestrict H (ms_mem ms) msr') model') Qok Qf) ->
  katwD (mkCfg ms model) Qok Qf.
Proof using Hwx HH.
  intros A ms msr' model Qok Qf Hcov Hwf Hinv Hh Hsvc Hs Hk F HF Hok Hf.
  apply (K_step_acct (MhK.Kw F) A ms msr' model (klD_w segs F HF) Hcov Hwf Hinv Hh Hsvc Hs).
  intros model' Hinv' Hsame'. exact (Hk model' Hinv' Hsame' F HF Hok Hf).
Qed.

Theorem katsD_msteps_acct : forall A ms msr' model (Qok Qf : config -> Prop),
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      katsD (mkCfg (unrestrict H (ms_mem ms) msr') model') Qok Qf) ->
  katsD (mkCfg ms model) Qok Qf.
Proof using Hwx HH.
  intros A ms msr' model Qok Qf Hcov Hwf Hinv Hh Hms Hk F HF Hok Hf.
  apply (K_msteps_acct (MhK.Kp F) A ms msr' model (klD_p segs F HF) Hcov Hwf Hinv Hh Hms).
  intros model' Hinv' Hsame' Hcl. exact (Hk model' Hinv' Hsame' Hcl F HF Hok Hf).
Qed.

Theorem katsD_step_acct : forall A ms msr' model (Qok Qf : config -> Prop),
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  katsD (mkCfg (unrestrict H (ms_mem ms) msr') model') Qok Qf) ->
  katsD (mkCfg ms model) Qok Qf.
Proof using Hwx HH.
  intros A ms msr' model Qok Qf Hcov Hwf Hinv Hh Hsvc Hs Hk F HF Hok Hf.
  apply (K_step_acct (MhK.Kp F) A ms msr' model (klD_p segs F HF) Hcov Hwf Hinv Hh Hsvc Hs).
  intros model' Hinv' Hsame'. exact (Hk model' Hinv' Hsame' F HF Hok Hf).
Qed.

(* [comment removed for export] *)
Theorem doomed_msteps_acct : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      doomed segs (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  doomed segs (mkCfg ms model).
Proof using Hwx HH.
  intros A ms msr' model Hcov Hwf Hinv Hh Hms Hk.
  (lazymatch goal with |- ?G => let G' := eval unfold AsK.doomed, MhK.kat in G in change_no_check G' end). intros K HK HQ.
  refine (rz_msteps_restricted' segs H HH Hwx K _ A ms msr' model Hcov Hwf Hinv Hh Hms _).
  - intros c c' Hn Hc'. rewrite node_ok_same in Hn. apply (HK c unit tt (fun _ => c') Hn). intros _; exact Hc'.
  - intros model' Hinv' Hsame' Hcl. exact (Hk model' Hinv' Hsame' Hcl K HK HQ).
Qed.

End WithSegs.
End AsRtK.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Contracts.
  Variable SEGS : list Segment.
  Context {RC : run_ceil}.
  (* [comment removed for export] *)
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  (* [comment removed for export] *)
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Definition hole_ok (h : option Z) (n : Z) : Prop := h = None \/ h = Some n.
  (* [comment removed for export] *)
  Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Z -> Prop.
  (* [comment removed for export] *)
  Variable fsbase : Z.

  #[local] Notation u := bv_unsigned.
  Definition cfg (fx : FPState) (R : bvmap 5 word) (p : Z) (M : mem) (mdl : Model) : config :=
    mkCfg (@mkst fx R (Z_to_bv 64 p) M (seg_rom SEGS)) mdl.

  (* [comment removed for export] *)
  Definition call_pre (R : bvmap 5 word) (M : mem) (ret sp stk : Z) : Prop :=
    getr R 1 = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0
    /\ u (getr R 2) = sp /\ sp mod 16 = 0 /\ CEIL + stk <= sp /\ sp + 16 <= PTRHI
    /\ getr R 4 = Z_to_bv 64 (ia_tp IA)
    /\ (forall a : word, sp - stk <= u a < sp -> store_ok SEGS M a 1%nat = true).
  Definition regs_kept (R R' : bvmap 5 word) : Prop :=
    forall r, In r as_callee_saved -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).
  Definition scratch_ok (M' : mem) (sp stk : Z) : Prop :=
    forall a : word, sp - stk <= u a < sp -> M' a <> None /\ store_ok SEGS M' a 1%nat = true.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition malloc_pre (h : option Z) (stk : Z) (fpcreq : bool) (fx : FPState) (R : bvmap 5 word) (M : mem) (mdl : Model)
             (Lc FF : list (Z * Z)) (B C K ret n sp : Z) : Prop :=
    m_halted mdl = None /\ FXOK fx /\ AAINVH h Lc FF B C K M mdl /\ hole_ok h n /\ call_pre R M ret sp stk
    /\ u (getr R 10) = n /\ 1 <= n <= NMAX
    /\ (fpcreq = true -> fpc M (u (getr R 8)) sp DMAX)          (* [comment removed for export] *)
    /\ B + (n + MBLK) <= GBUDGET /\ C + 1 <= LMAX /\ K + kcost_malloc n <= KCAP.

  (* [comment removed for export] *)
  Definition malloc_ok (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z)
             (c' : config) : Prop :=
    exists fx' R' M' mdl' (p : word),
      c' = cfg fx' R' ret M' mdl' /\ FXOK fx' /\ regs_kept R R' /\ getr R' 10 = p
      /\ u p mod 16 = 0 /\ ablk_ok IA (u p) n
      /\ (64512 < n -> u p mod 4096 = 2048)                                        (* [comment removed for export] *)
      /\ (forall b m, In (b, m) Lc -> u p + n <= b \/ b + m <= u p)
      /\ (forall f k, In (f, k) FF -> u p + n <= f \/ f + FS k <= u p)
      /\ (forall a : word, u p <= u a < u p + n -> M' a <> None /\ store_ok SEGS M' a 1%nat = true)
      (* [comment removed for export] *)
      /\ (forall i, 0 <= i < n / 8 -> M' (Z_to_bv 64 (sh_lo (u p) + i)) = Some (Z_to_bv 8 0))
      /\ (n mod 8 <> 0 -> M' (Z_to_bv 64 (sh_lo (u p) + n / 8)) = Some (Z_to_bv 8 (n mod 8)))
      /\ (forall a : word, sh_lo (u p) <= u a < sh_hi (u p) n -> store_ok SEGS M' a 1%nat = true)
      /\ (forall a : word, M' a <> M a -> as_changed IA stk Lc FF sp a) /\ errno_kept IA M M'
      /\ scratch_ok M' sp stk
      /\ AAINVH None ((u p, n) :: Lc) FF (B + (n + MBLK)) (C + 1) (K + kcost_malloc n) M' mdl'
      /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ m_halted mdl' = None.

  (* [comment removed for export] *)
  Definition malloc_null (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z)
             (c' : config) : Prop :=
    exists fx' R' M' mdl',
      c' = cfg fx' R' ret M' mdl' /\ FXOK fx' /\ regs_kept R R' /\ getr R' 10 = Z_to_bv 64 0
      /\ (forall a : word, M' a <> M a -> as_changed IA stk Lc FF sp a) /\ errno_kept IA M M'
      /\ scratch_ok M' sp stk
      /\ AAINVH (Some n) Lc FF B C K M' mdl'
      /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ m_halted mdl' = None.

  (* [comment removed for export] *)
  Definition MALLOC_KATW (stk entry : Z) (fpcreq : bool) : Prop :=
    forall h fx R M mdl Lc FF B C K ret n sp,
      malloc_pre h stk fpcreq fx R M mdl Lc FF B C K ret n sp ->
      katwD SEGS (cfg fx R entry M mdl)
            (malloc_ok stk R M mdl Lc FF B C K ret n sp) (malloc_null stk R M mdl Lc FF B C K ret n sp).

  (* [comment removed for export] *)
  Definition MALLOC_ALT (stk entry : Z) (fpcreq : bool) : Prop :=
    forall h fx R M mdl Lc FF B C K ret n sp,
      malloc_pre h stk fpcreq fx R M mdl Lc FF B C K ret n sp ->
      FRESH Lc FF B C K M mdl n ->
      katsD SEGS (cfg fx R entry M mdl)
            (malloc_ok stk R M mdl Lc FF B C K ret n sp) (malloc_null stk R M mdl Lc FF B C K ret n sp).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_pre (h : option Z) (stk : Z) (fx : FPState) (R : bvmap 5 word) (M : mem) (mdl : Model)
             (Lc Lc' FF : list (Z * Z)) (B C K B' C' K' ret sp : Z) (p : word) : Prop :=
    m_halted mdl = None /\ FXOK fx /\ AAINVH h Lc FF B C K M mdl /\ call_pre R M ret sp stk
    /\ getr R 10 = p /\ fpc M (u (getr R 8)) sp DMAX
    /\ ((p = Z_to_bv 64 0 /\ Lc' = Lc /\ B' = B /\ C' = C /\ K' = K)
        \/ exists m L1 L2, Lc = L1 ++ (u p, m) :: L2 /\ Lc' = L1 ++ L2
                            /\ B' = Z.max 0 (B - (m + MBLK)) /\ C' = Z.max 0 (C - 1) /\ K' = K + kcost_free /\ K' <= KCAP).
  Definition free_post (h : option Z) (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc' FF : list (Z * Z)) (B' C' K' ret sp : Z)
             (c' : config) : Prop :=
    exists fx' R' M' mdl',
      c' = cfg fx' R' ret M' mdl' /\ FXOK fx' /\ regs_kept R R'
      /\ (forall a : word, M' a <> M a -> as_changed IA stk Lc' FF sp a) /\ errno_kept IA M M'
      /\ scratch_ok M' sp stk
      /\ AAINVH h Lc' FF B' C' K' M' mdl'
      /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc' FF mdl mdl' /\ m_halted mdl' = None.
  Definition FREE_KAT (stk entry : Z) : Prop :=
    forall h fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p,
      free_pre h stk fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p ->
      katD SEGS (cfg fx R entry M mdl) (free_post h stk R M mdl Lc' FF B' C' K' ret sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stkmal_pre (h : option Z) (k : Z) (fx : FPState) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp : Z) : Prop :=
    0 <= k <= KMAXCLASS /\ m_halted mdl = None /\ FXOK fx /\ AAINVH h Lc FF B C K M mdl /\ call_pre R M ret sp MSTK_F
    /\ fcount k FF + 1 <= FCAP k.
  Definition stkmal_post (h : option Z) (k : Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp : Z)
             (c' : config) : Prop :=
    exists fx' R' M' mdl' (f : word) (flag : Z),
      c' = cfg fx' R' ret M' mdl' /\ FXOK fx' /\ regs_kept R R' /\ getr R' 10 = f
      /\ u f mod FS k = 0 /\ ablk_ok IA (u f) (FS k)
      /\ fsbase + 0x9000 <= u f /\ u f + FS k <= fsbase + FAKE_SIZE
      /\ (forall b m, In (b, m) Lc -> u f + FS k <= b \/ b + m <= u f)
      /\ (forall f' k', In (f', k') FF -> u f + FS k <= f' \/ f' + FS k' <= u f)
      /\ (forall a : word, u f <= u a < u f + FS k -> M' a <> None /\ store_ok SEGS M' a 1%nat = true)
      /\ m64 M' (u f + FS k - 8) flag                                                     (* [comment removed for export] *)
      /\ (forall i, 0 <= i < FS k / 8 -> M' (Z_to_bv 64 (sh_lo (u f) + i)) = Some (Z_to_bv 8 0))   (* [comment removed for export] *)
      /\ (forall a : word, sh_lo (u f) <= u a < sh_hi (u f) (FS k) -> store_ok SEGS M' a 1%nat = true)
      /\ (forall a : word, M' a <> M a -> as_changed IA MSTK_F Lc FF sp a) /\ errno_kept IA M M'
      /\ scratch_ok M' sp MSTK_F
      /\ AAINVH h Lc ((u f, k) :: FF) B C K M' mdl'
      /\ same_but_materialized mdl mdl'.
  Definition STKMAL (k : Z) : Prop :=
    forall h fx R M mdl Lc FF B C K ret sp,
      stkmal_pre h k fx R M mdl Lc FF B C K ret sp ->
      katD SEGS (cfg fx R (ia_stkmal IA k) M mdl) (stkmal_post h k R M mdl Lc FF B C K ret sp).

  (* [comment removed for export] *)
  Definition FAKEREL : Prop :=
    forall h (pc rs : Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF F1 F2 : list (Z * Z)) (B C K f k flag : Z),
      FXOK fx -> m_halted mdl = None ->
      AAINVH h Lc FF B C K M mdl ->
      FF = F1 ++ (f, k) :: F2 ->
      m64 M (f + FS k - 8) flag ->
      fetch_word SEGS (Z_to_bv 64 pc) = Some (Z_to_bv 32 (0x23 + rs * 2 ^ 15)) ->      (* [comment removed for export] *)
      1 <= rs <= 31 -> u (getr R (Z_to_bv 5 rs)) = flag -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
      katD SEGS (cfg fx R pc M mdl)
           (fun c' => exists M' mdl',
              c' = cfg fx R (pc + 4) M' mdl'
              /\ (forall a : word, M' a <> M a ->
                    u a = flag /\ flag < CEIL /\ ~ (ia_img_lo IA <= flag < ia_img_hi IA) /\ ~ app_visible IA Lc (F1 ++ F2) flag)
              /\ AAINVH h Lc (F1 ++ F2) B C K M' mdl'
              /\ same_but_materialized mdl mdl').

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rd1 (M : mem) (a : Z) : option (list byte) := rdn SEGS M (Z_to_bv 64 a) 1%nat.

  Definition dst_owned (W Lc FF : list (Z * Z)) (dst n : Z) : Prop :=
    as_wins_ok IA W /\ forall a, dst <= a < dst + n -> as_app_owned IA W Lc FF a.
  Definition off_scratch (sp lo hi : Z) : Prop := forall a, lo <= a < hi -> ~ (sp - MSTK_M <= a < sp).

  (* [comment removed for export] *)
  Definition mem_post (h : option Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp dst n : Z)
             (bytes : Z -> option byte) (c' : config) : Prop :=
    exists fx' R' M' mdl',
      c' = cfg fx' R' ret M' mdl' /\ FXOK fx' /\ regs_kept R R' /\ u (getr R' 10) = dst
      /\ (forall i, 0 <= i < n -> M' (Z_to_bv 64 (dst + i)) = bytes i)
      /\ (forall a : word, M' a <> M a -> (dst <= u a < dst + n) \/ (sp - MSTK_M <= u a < sp))
      /\ scratch_ok M' sp MSTK_M
      /\ AAINVH h Lc FF B C K M' mdl' /\ same_but_materialized mdl mdl'.

  Definition MEMCPY_AT (entry : Z) : Prop :=
    forall h fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF W : list (Z * Z)) (B C K ret sp dst src n : Z) (bs : list byte),
      FXOK fx -> m_halted mdl = None ->
      AAINVH h Lc FF B C K M mdl ->
      call_pre R M ret sp MSTK_M ->
      u (getr R 10) = dst -> u (getr R 11) = src -> u (getr R 12) = n -> 0 <= n <= NMAX ->
      (n = 0 \/ dst + n <= src \/ src + n <= dst) ->
      addr_is_mem dst -> addr_is_mem (dst + n) -> addr_is_mem src -> addr_is_mem (src + n) ->
      accessible M src n -> accessible M dst n ->
      shadow_visible IA Lc FF src n -> shadow_visible IA Lc FF dst n ->
      rdn SEGS M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
      dst_owned W Lc FF dst n -> off_scratch sp dst (dst + n) -> off_scratch sp src (src + n) ->
      (forall a : word, dst <= u a < dst + n -> store_ok SEGS M a 1%nat = true) ->
      katD SEGS (cfg fx R entry M mdl)
           (mem_post h R M mdl Lc FF B C K ret sp dst n (fun i => Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)))).

  Definition MEMSET_AT (entry : Z) : Prop :=
    forall h fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF W : list (Z * Z)) (B C K ret sp dst c n : Z),
      FXOK fx -> m_halted mdl = None ->
      AAINVH h Lc FF B C K M mdl ->
      call_pre R M ret sp MSTK_M ->
      u (getr R 10) = dst -> u (getr R 11) mod 256 = c -> u (getr R 12) = n -> 0 <= n <= NMAX ->
      addr_is_mem dst -> addr_is_mem (dst + n) -> accessible M dst n -> shadow_visible IA Lc FF dst n ->
      dst_owned W Lc FF dst n -> off_scratch sp dst (dst + n) ->
      (forall a : word, dst <= u a < dst + n -> store_ok SEGS M a 1%nat = true) ->
      katD SEGS (cfg fx R entry M mdl)
           (mem_post h R M mdl Lc FF B C K ret sp dst n (fun _ => Some (Z_to_bv 8 c))).

  (* [comment removed for export] *)
  Definition MEMMOVE_AT (entry : Z) : Prop :=
    forall h fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF W : list (Z * Z)) (B C K ret sp dst src n : Z) (bs : list byte),
      FXOK fx -> m_halted mdl = None ->
      AAINVH h Lc FF B C K M mdl ->
      call_pre R M ret sp MSTK_M ->
      u (getr R 10) = dst -> u (getr R 11) = src -> u (getr R 12) = n -> 0 <= n <= NMAX ->
      addr_is_mem dst -> addr_is_mem (dst + n) -> addr_is_mem src -> addr_is_mem (src + n) ->
      accessible M src n -> accessible M dst n -> shadow_visible IA Lc FF src n -> shadow_visible IA Lc FF dst n ->
      rdn SEGS M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
      (dst <> src \/ (forall i, 0 <= i < n -> M (Z_to_bv 64 (src + i)) <> None)) ->
      dst_owned W Lc FF dst n -> off_scratch sp dst (dst + n) -> off_scratch sp src (src + n) ->
      (forall a : word, dst <= u a < dst + n -> store_ok SEGS M a 1%nat = true) ->
      katD SEGS (cfg fx R entry M mdl)
           (mem_post h R M mdl Lc FF B C K ret sp dst n (fun i => Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)))).

  (* [comment removed for export] *)
  Definition STRLEN_AT (entry : Z) : Prop :=
    forall h fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp s len : Z),
      FXOK fx -> m_halted mdl = None ->
      AAINVH h Lc FF B C K M mdl ->
      call_pre R M ret sp MSTK_M ->
      u (getr R 10) = s -> 0 <= len -> len + 1 <= NMAX ->
      (forall i, 0 <= i < len -> exists b, rd1 M (s + i) = Some [b] /\ b <> Z_to_bv 8 0) ->
      rd1 M (s + len) = Some [Z_to_bv 8 0] ->
      (forall i, s - s mod 8 <= i < (s + len + 8) - (s + len) mod 8 -> rd1 M i <> None) ->
      addr_is_mem s -> addr_is_mem (s + len + 1) -> accessible M s (len + 1) -> shadow_visible IA Lc FF s (len + 1) ->
      off_scratch sp s (s + len + 1) ->
      katD SEGS (cfg fx R entry M mdl)
           (fun c' => exists fx' R' M' mdl',
              c' = cfg fx' R' ret M' mdl' /\ FXOK fx' /\ regs_kept R R' /\ u (getr R' 10) = len
              /\ (forall a : word, M' a <> M a -> sp - MSTK_M <= u a < sp)
              /\ scratch_ok M' sp MSTK_M
              /\ AAINVH h Lc FF B C K M' mdl' /\ same_but_materialized mdl mdl').

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition last_gran_ok (M : mem) (beg n : Z) : Prop :=
    n mod 8 <> 0 -> sbyte M (SB + (beg + n) / 8) <> 0 /\ sbyte M (SB + (beg + n) / 8) <= (beg + n) mod 8.
  Definition annot_post (h : option Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z))
             (B C K ret sp beg n om nm : Z) (c' : config) : Prop :=
    exists fx' R' M' mdl',
      c' = cfg fx' R' ret M' mdl' /\ FXOK fx' /\ regs_kept R R'
      /\ accessible M' beg (nm - beg)                                             (* [comment removed for export] *)
      /\ last_gran_ok M' beg n
      /\ (forall a : word, M' a <> M a -> (SB + Z.min om nm / 8 <= u a < sh_hi beg n) \/ (sp - MSTK_C <= u a < sp))
      /\ (forall a : word, M' a <> M a -> M' a <> None)
      /\ scratch_ok M' sp MSTK_C
      /\ AAINVH h Lc FF B C K M' mdl'
      /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ m_halted mdl' = None.
  Definition ANNOTATE_AT (entry : Z) : Prop :=
    forall h fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp beg n om nm : Z),
      FXOK fx -> m_halted mdl = None ->
      AAINVH h Lc FF B C K M mdl ->
      call_pre R M ret sp MSTK_C ->
      In (beg, n) Lc ->
      u (getr R 10) = beg -> u (getr R 11) = beg + n -> u (getr R 12) = om -> u (getr R 13) = nm ->
      beg <= om <= beg + n -> beg <= nm <= beg + n ->
      accessible M beg (om - beg) ->                                                (* [comment removed for export] *)
      last_gran_ok M beg n ->
      katD SEGS (cfg fx R entry M mdl) (annot_post h R M mdl Lc FF B C K ret sp beg n om nm).

  (* [comment removed for export] *)
  Definition annot_postw (h : option Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z))
             (B C K ret sp beg n om nm : Z) (c' : config) : Prop :=
    exists fx' R' M' mdl',
      c' = cfg fx' R' ret M' mdl' /\ FXOK fx' /\ regs_kept R R'
      /\ accessible M' beg (nm - beg)
      /\ (forall a : word, M' a <> M a -> (SB + Z.min om nm / 8 <= u a < sh_hi beg n) \/ (sp - MSTK_C <= u a < sp))
      /\ (forall a : word, M' a <> M a -> M' a <> None)
      /\ scratch_ok M' sp MSTK_C
      /\ AAINVH h Lc FF B C K M' mdl'
      /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ m_halted mdl' = None.
  Definition ANNOTATE_ATW (entry : Z) : Prop :=
    forall h fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp beg n om nm : Z),
      FXOK fx -> m_halted mdl = None ->
      AAINVH h Lc FF B C K M mdl ->
      call_pre R M ret sp MSTK_C ->
      In (beg, n) Lc ->
      u (getr R 10) = beg -> u (getr R 11) = beg + n -> u (getr R 12) = om -> u (getr R 13) = nm ->
      beg <= om <= beg + n -> beg <= nm <= beg + n ->
      accessible M beg (om - beg) ->
      katD SEGS (cfg fx R entry M mdl) (annot_postw h R M mdl Lc FF B C K ret sp beg n om nm).

  (* [comment removed for export] *)
  Record as_contracts : Prop := ASC {
    asc_weaken : forall h Lc FF B C K M mdl, AAINVH None Lc FF B C K M mdl -> AAINVH h Lc FF B C K M mdl;
    asc_malloc : MALLOC_KATW MSTK_A (ia_malloc IA) true;
    asc_malloc_thunk : MALLOC_KATW MSTK_A (ia_malloc_thunk IA) true;
    asc_malloc_alt : MALLOC_ALT MSTK_A (ia_malloc IA) true;
    asc_malloc_alt_thunk : MALLOC_ALT MSTK_A (ia_malloc_thunk IA) true;
    asc_free : FREE_KAT MSTK_A (ia_free IA);
    asc_free_thunk : FREE_KAT MSTK_A (ia_free_thunk IA);
    asc_opdel : FREE_KAT MSTK_A (ia_opdel IA);
    asc_opdel_sz : FREE_KAT MSTK_A (ia_opdel_sz IA);
    asc_stkmal : forall k, 0 <= k <= KMAXCLASS -> STKMAL k;
    asc_fakerel : FAKEREL;
    asc_memcpy_icpt : MEMCPY_AT (ia_memcpy_icpt IA);   asc_asan_memcpy : MEMCPY_AT (ia_asan_memcpy IA);
    asc_memset_icpt : MEMSET_AT (ia_memset_icpt IA);   asc_asan_memset : MEMSET_AT (ia_asan_memset IA);
    asc_memmove_icpt : MEMMOVE_AT (ia_memmove_icpt IA); asc_asan_memmove : MEMMOVE_AT (ia_asan_memmove IA);
    asc_strlen : STRLEN_AT (ia_strlen_icpt IA) }.
End Contracts.
