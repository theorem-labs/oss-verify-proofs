(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
Module ImplRz.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tcan {R} : itree node R -> Model -> (R -> Model -> Prop) -> Prop :=
| tcan_ret : forall (r : R) mo (P : R -> Model -> Prop), P r mo -> tcan (Ret r) mo P
| tcan_vis : forall n k mo (P : R -> Model -> Prop) rsp mo',
    anstep n mo rsp mo' -> tcan (k rsp) mo' P -> tcan (Vis n k) mo P.

Lemma tcan_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  tcan t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> tcan t mo P'.
Proof.
  intros R t mo P P' H HP. induction H as [r mo P H | n k mo P rsp mo' Ha H IH].
  - constructor. apply HP. exact H.
  - econstructor; [exact Ha|]. apply IH. exact HP.
Qed.

Lemma tcan_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  tcan t mo (fun a mo1 => tcan (f a) mo1 P) -> tcan (ITree.bind node t f) mo P.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn.
  - inversion H; subst. assumption.
  - inversion H; subst. econstructor; [eassumption|]. apply IH. assumption.
Qed.

Lemma tcan_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo (P : exc B -> Model -> Prop),
  tcan t mo (fun r mo1 => match r with Ok a => tcan (f a) mo1 P | Unr => P Unr mo1 end) ->
  tcan (ebind t f) mo P.
Proof.
  intros A B t f mo P H. unfold ebind. apply tcan_bind.
  eapply tcan_mono; [exact H|]. intros [|a] mo1 Hr; cbn; [constructor; exact Hr | exact Hr].
Qed.

(* [comment removed for export] *)
Lemma tcan_ret_inv : forall {R} (r : R) mo (P : R -> Model -> Prop), tcan (Ret r) mo P -> P r mo.
Proof.
  intros R r mo P H.
  assert (G : forall t, tcan t mo P -> t = Ret r -> P r mo).
  { intros t Ht. destruct Ht as [r0 mo0 P0 HP | n k mo0 P0 rsp mo' Ha Hk]; intros E; [injection E as ->; exact HP | discriminate E]. }
  exact (G _ H eq_refl).
Qed.

Lemma tcan_vis_inv : forall {R} n (k : resp -> itree node R) mo (P : R -> Model -> Prop),
  tcan (Vis n k) mo P -> exists rsp mo', anstep n mo rsp mo' /\ tcan (k rsp) mo' P.
Proof.
  intros R n k mo P H.
  assert (G : forall t, tcan t mo P -> t = Vis n k -> exists rsp mo', anstep n mo rsp mo' /\ tcan (k rsp) mo' P).
  { intros t Ht. destruct Ht as [r0 mo0 P0 HP | n0 k0 mo0 P0 rsp mo' Ha Hk]; intros E; [discriminate E|].
    injection E as -> ->. exists rsp, mo'. split; assumption. }
  exact (G _ H eq_refl).
Qed.

Lemma tcan_bind_inv : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  tcan (ITree.bind node t f) mo P -> tcan t mo (fun a mo1 => tcan (f a) mo1 P).
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn in H.
  - constructor. exact H.
  - apply tcan_vis_inv in H as (rsp & mo' & Ha & Hk). econstructor; [exact Ha|]. apply IH. exact Hk.
Qed.

Lemma tcan_ebind_inv : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo (P : exc B -> Model -> Prop),
  tcan (ebind t f) mo P ->
  tcan t mo (fun r mo1 => match r with Ok a => tcan (f a) mo1 P | Unr => P Unr mo1 end).
Proof.
  intros A B t f mo P H. unfold ebind in H. apply tcan_bind_inv in H.
  eapply tcan_mono; [exact H|]. intros [|a] mo1 Hr; cbn in Hr; [exact (tcan_ret_inv _ _ _ Hr)| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma twf_tcan : forall {R} (t : itree node R) mo (P Q : R -> Model -> Prop),
  twf t mo P -> tcan t mo Q -> tcan t mo (fun r mo1 => P r mo1 /\ Q r mo1).
Proof.
  intros R t mo P Q Hw Hc. induction Hc as [r mo Q H | n k mo Q rsp mo' Ha H IH]; cbn in Hw.
  - constructor. split; assumption.
  - destruct Hw as (_ & _ & Hk). econstructor; [exact Ha|]. apply IH. apply Hk. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma twf_tcan_ex : forall {R} (t : itree node R) mo (P : R -> Model -> Prop),
  twf t mo P -> tcan t mo P.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P Hw; cbn in Hw.
  - constructor. exact Hw.
  - destruct Hw as (Hn & Hs & Hk).
    destruct (anstep_inhabited n mo Hn Hs) as (rsp & mo' & Ha).
    econstructor; [exact Ha|]. apply IH. apply Hk. exact Ha.
Qed.

Lemma tcan_ex : forall {R} (t : itree node R) mo (P : R -> Model -> Prop),
  tcan t mo P -> exists r mo', P r mo' /\ tcan t mo (fun r1 mo1 => r1 = r /\ mo1 = mo').
Proof.
  intros R t mo P H. induction H as [r mo P H | n k mo P rsp mo' Ha H IH].
  - exists r, mo. split; [exact H| constructor; auto].
  - destruct IH as (r & mo1 & HP & Hc). exists r, mo1. split; [exact HP|]. econstructor; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Theorem impl_rz_same : forall {A} (t : itree node (exc A)) (Q : A -> machine_state -> Prop)
                              (R : A -> Model -> Prop) (T : TSet) ms mo,
  impl segs (at_node segs) t (epost Q) ms -> MOK mo -> etwf t mo R ->
  (forall a ms' mo', Q a ms' -> R a mo' -> MOK mo' -> realizes segs (mkCfg ms' mo') T) ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros A t. unfold etwf.
  induction t as [r|n k IH]; intros Q R T ms mo Himpl HM Hwf HK; cbn in Himpl, Hwf.
  - destruct r as [|a]; [destruct Hwf|].
    eapply rz_evt; [exact HM | exact Himpl |]. intros ms' HQ. apply (HK a); auto.
  - destruct Hwf as (Hn & Hs & Hk).
    eapply rz_evt; [exact HM | exact Himpl |].
    intros ms1 [Hat Hk1].
    apply (rz_alloc_node segs n ms1 mo T Hn Hat HM Hs).
    intros rsp mo' Ha.
    apply (IH rsp Q R T (nret ms1 rsp) mo' (Hk1 rsp) (anstep_MOK n mo rsp mo' HM Ha) (Hk rsp mo' Ha) HK).
Qed.

(* [comment removed for export] *)
Lemma twf_and : forall {R} (t : itree node R) mo (P Q : R -> Model -> Prop),
  twf t mo P -> twf t mo Q -> twf t mo (fun r mo1 => P r mo1 /\ Q r mo1).
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P Q HP HQ; cbn in *.
  - split; assumption.
  - destruct HP as (Hn & Hs & HkP). destruct HQ as (_ & _ & HkQ).
    split; [exact Hn|]. split; [exact Hs|]. intros rsp mo' Ha. apply IH; [apply HkP| apply HkQ]; exact Ha.
Qed.

Lemma etwf_and : forall {A} (t : itree node (exc A)) mo (P Q : A -> Model -> Prop),
  etwf t mo P -> etwf t mo Q -> etwf t mo (fun a mo1 => P a mo1 /\ Q a mo1).
Proof.
  intros A t mo P Q HP HQ. unfold etwf in *. eapply twf_mono; [exact (twf_and t mo _ _ HP HQ)|].
  intros [|a] mo1 [H1 H2]; [exact H1| split; assumption].
Qed.

Lemma twf_reach : forall {R} (t : itree node R) mo (P Q : R -> Model -> Prop),
  twf t mo P ->
  (forall r mo', tcan t mo (fun r1 mo1 => r1 = r /\ mo1 = mo') -> Q r mo') ->
  twf t mo (fun r mo1 => P r mo1 /\ Q r mo1).
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P Q HP HQ; cbn in *.
  - split; [exact HP|]. apply HQ. constructor. auto.
  - destruct HP as (Hn & Hs & Hk). split; [exact Hn|]. split; [exact Hs|].
    intros rsp mo' Ha. apply IH; [exact (Hk rsp mo' Ha)|].
    intros r mo2 Hc. apply HQ. econstructor; [exact Ha| exact Hc].
Qed.

Lemma etwf_reach : forall {A} (t : itree node (exc A)) mo (P Q : A -> Model -> Prop),
  etwf t mo P ->
  (forall a mo', tcan t mo (fun r1 mo1 => r1 = Ok a /\ mo1 = mo') -> Q a mo') ->
  etwf t mo (fun a mo1 => P a mo1 /\ Q a mo1).
Proof.
  intros A t mo P Q HP HQ. unfold etwf in *.
  eapply twf_mono; [apply (twf_reach t mo _ (fun r mo1 => match r with Unr => True | Ok a => Q a mo1 end) HP)|].
  - intros [|a] mo' Hc; [exact I| apply HQ; exact Hc].
  - intros [|a] mo1 [H1 H2]; [exact H1| split; assumption].
Qed.

Theorem impl_rz_only : forall {A} (t : itree node (exc A)) (Q : A -> machine_state -> Prop)
                              (R : A -> Model -> Prop) (isA : A -> bool) (TB : TSet) ms mo,
  impl segs (at_node segs) t (epost Q) ms -> MOK mo -> etwf t mo R ->
  etwf t mo (fun a _ => isA a = false) ->
  (forall a ms' mo', Q a ms' -> R a mo' -> MOK mo' -> isA a = false -> realizes segs (mkCfg ms' mo') TB) ->
  realizes segs (mkCfg ms mo) TB.
Proof.
  intros A t Q R isA TB ms mo Hi HM Hw Hno HB.
  eapply (impl_rz_same t Q (fun a mo1 => R a mo1 /\ isA a = false) TB ms mo Hi HM (etwf_and t mo _ _ Hw Hno)).
  intros a ms' mo' HQ [HR HA] HM'. eapply HB; eauto.
Qed.

Theorem implM_rz_only : forall {St A} (c : M St A) (s : St) (Q : A -> St -> machine_state -> Prop)
                               (R : A * St -> Model -> Prop) (isA : A * St -> bool) (TB : TSet) ms mo,
  implM segs c s Q ms -> MOK mo -> etwf (c s) mo R ->
  etwf (c s) mo (fun p _ => isA p = false) ->
  (forall a s' ms' mo', Q a s' ms' -> R (a, s') mo' -> MOK mo' -> isA (a, s') = false -> realizes segs (mkCfg ms' mo') TB) ->
  realizes segs (mkCfg ms mo) TB.
Proof.
  intros St A c s Q R isA TB ms mo Hc HM Hw Hno HB.
  eapply (impl_rz_only (c s) (fun p => Q (fst p) (snd p)) R isA TB ms mo Hc HM Hw Hno).
  intros [a s'] ms' mo'; cbn; eauto.
Qed.

Theorem implM_rz_same : forall {St A} (c : M St A) (s : St) (Q : A -> St -> machine_state -> Prop)
                               (R : A * St -> Model -> Prop) (T : TSet) ms mo,
  implM segs c s Q ms -> MOK mo -> etwf (c s) mo R ->
  (forall a s' ms' mo', Q a s' ms' -> R (a, s') mo' -> MOK mo' -> realizes segs (mkCfg ms' mo') T) ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros St A c s Q R T ms mo Hc HM Hw HK.
  eapply (impl_rz_same (c s) (fun p => Q (fst p) (snd p)) R T ms mo Hc HM Hw).
  intros [a s'] ms' mo'; cbn; eauto.
Qed.

End WithSegs.
End ImplRz.

(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mprotect.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require AsanCeil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cfg.
Module KB_Can.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MmapSim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cfg.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.NodesSoundDec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS ImplRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MonadCan.
Context {St : Type}.

Lemma tcan_mbind {A B} (m : Monad.M St A) (f : A -> Monad.M St B) s mo (P : exc (B * St) -> Model -> Prop) a s' mo' :
  tcan (m s) mo (fun r mo1 => r = Ok (a, s') /\ mo1 = mo') -> tcan (f a s') mo' P -> tcan (mbind m f s) mo P.
Proof.
  intros Hm Hf. unfold mbind. apply tcan_ebind. eapply tcan_mono; [exact Hm|].
  intros [|[a1 s1]] mo1 [E ->]; [discriminate|]. injection E as -> ->. cbn. exact Hf.
Qed.

Lemma tcan_mret {A} (a : A) (s : St) mo (P : exc (A * St) -> Model -> Prop) : P (Ok (a, s)) mo -> tcan (mret a s) mo P.
Proof. intros H. unfold mret. constructor. exact H. Qed.

Lemma tcan_mget (s : St) mo (P : exc (St * St) -> Model -> Prop) : P (Ok (s, s)) mo -> tcan (mget s) mo P.
Proof. intros H. unfold mget. constructor. exact H. Qed.

Lemma tcan_mupd (f : St -> St) (s : St) mo (P : exc (unit * St) -> Model -> Prop) : P (Ok (tt, f s)) mo -> tcan (mupd f s) mo P.
Proof. intros H. unfold mupd. constructor. exact H. Qed.

Lemma tcan_msys {A} n (dec : resp -> option A) (s : St) mo rsp mo' a (P : exc (A * St) -> Model -> Prop) :
  anstep n mo rsp mo' -> dec rsp = Some a -> P (Ok (a, s)) mo' -> tcan (msys n dec s) mo P.
Proof.
  intros Ha Hd HP. unfold msys, enode. econstructor; [exact Ha|]. cbn. rewrite Hd. constructor. exact HP.
Qed.
End MonadCan.

(* [comment removed for export] *)
Definition evres (e : ev) (s : PState) (mo : Model) (z : Z) (s' : PState) (mo' : Model) : Prop :=
  tcan (ev_step e s) mo (fun r mo1 => r = Ok (z, s') /\ mo1 = mo').

Lemma tcan_membed_vis {R} : forall e (k : Z -> stree ev Z R) s mo z s' mo' P,
  evres e s mo z s' mo' -> tcan (membed (k z) s') mo' P -> tcan (membed (SVis e k) s) mo P.
Proof. intros e k s mo z s' mo' P He Hk. cbn [membed]. eapply tcan_mbind; [exact He| exact Hk]. Qed.

Lemma tcan_membed_ret {R} : forall (r : R) s mo (P : exc (R * PState) -> Model -> Prop),
  P (Ok (r, s)) mo -> tcan (membed (SRet r) s) mo P.
Proof. intros r s mo P H. cbn [membed]. apply tcan_mret. exact H. Qed.

(* [comment removed for export] *)
Lemma tcan_raw_malloc : forall n s mo (W : option cptr -> Prop),
  tcan (membed (cmalloc (ps_m s) n) s) mo (fun r _ => exists st' rc s1, r = Ok ((st', rc), s1) /\ W rc) ->
  tcan (raw_malloc n s) mo (fun r _ => exists p s1, r = Ok (p, s1) /\ W (match p with Some q => Some (fst q) | None => None end)).
Proof.
  intros n s mo W H. unfold raw_malloc. unfold mbind at 1. apply tcan_ebind. unfold mget. constructor. cbn [fst snd].
  unfold mbind. apply tcan_ebind. destruct (tcan_ex _ _ _ H) as (r & mo' & (st' & rc & s1 & -> & HW) & Hc).
  eapply tcan_mono; [exact Hc|]. intros r1 mo1 [-> ->]. cbn [fst snd].
  apply tcan_ebind. unfold mupd. constructor. cbn [fst snd]. unfold mret. constructor.
  destruct rc as [c|]; [exists (Some (c, fresh_off st' c n))| exists None]; exists (set_m st' s1); auto.
Qed.

Lemma tcan_raw_free : forall p s mo (P : exc (unit * PState) -> Model -> Prop),
  tcan (membed (cfree (ps_m s) (Some (fst p))) s) mo (fun r mo1 => exists st' s1, r = Ok (st', s1) /\ P (Ok (tt, set_m st' s1)) mo1) ->
  tcan (raw_free p s) mo P.
Proof.
  intros p s mo P H. unfold raw_free. unfold mbind at 1. apply tcan_ebind. unfold mget. constructor. cbn [fst snd].
  unfold mbind. apply tcan_ebind. eapply tcan_mono; [exact H|]. intros r1 mo1 (st' & s1 & -> & HP). cbn [fst snd].
  unfold mupd. constructor. exact HP.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
Lemma evcan_brk0 : forall s mo,
  let h := m_vmmaps mo in
  exists mo', evres (EBrk 0) s mo (bv_unsigned (vm_brk h)) (set_brk_ps (bv_unsigned (vm_brk h)) s) mo'
    /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
    /\ vm_only mo mo' /\ (m_vm_lazy mo = [] -> m_vm_lazy mo' = []) /\ (m_vm_materialized mo = [] -> m_vm_lazy mo = [] -> m_vm_materialized mo' = []).
Proof.
  intros s mo h.
  destruct (anstep_inhabited (NBrk 0) mo eq_refl ltac:(cbn; lia)) as (rsp & mo' & Ha).
  pose proof (anstep_dec_brk0 mo rsp mo' Ha) as [Hd Evm].
  exists mo'. splits.
  - unfold evres, ev_step. cbn [Z.eqb]. eapply tcan_mbind; [eapply tcan_msys; [exact Ha| exact Hd| split; reflexivity]|].
    eapply tcan_mbind; [apply tcan_mupd; split; reflexivity|]. apply tcan_mret. split; reflexivity.
  - exact Evm.
  - eapply anstep_vm_only; exact Ha.
  - intros Hl. eapply anstep_lazy_nil; eauto.
  - intros Hm Hl. eapply anstep_materialized_nil; eauto.
Qed.

(* [comment removed for export] *)
Lemma evcan_brk_refuse : forall req s mo,
  let h := m_vmmaps mo in let b := bv_unsigned (vm_brk h) in
  req <> 0 -> ps_brk s = b -> 0 < b -> bv_unsigned (vm_start_brk h) <= b -> b < req < 2^64 ->
  exists mo', evres (EBrk req) s mo (ps_brk s) s mo'
    /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
    /\ vm_only mo mo' /\ (m_vm_lazy mo = [] -> m_vm_lazy mo' = []) /\ (m_vm_materialized mo = [] -> m_vm_lazy mo = [] -> m_vm_materialized mo' = []).
Proof.
  intros req s mo h b Hreq Hpb Hb Hsb Hr.
  set (rq := Z_to_bv 64 req). set (mo' := with_brk_next mo rq (vm_brk h)).
  assert (Ha : anstep (NBrk req) mo (mkEffectU (vm_brk h) [] (brk_zeros rq (vm_brk h) (vm_brk h)) (brk_unmaps (vm_brk h) (vm_brk h)) [] []) mo').
  { cbn [anstep]. exists (vm_brk h). split; [apply brk_r_ok_refuse|]. split; reflexivity. }
  pose proof (anstep_dec_brk mo req _ mo' Hb Hsb Hr Ha) as (a & Hd & Hx). fold h b in Hd, Hx.
  destruct a.
  { exfalso. destruct Hx as (_ & E & _). apply (f_equal eff_ret) in E. unfold eff0 in E. cbn [eff_ret] in E.
    apply (f_equal bv_unsigned) in E. rewrite unsigned_lit in E by lia. fold b in E. lia. }
  destruct Hx as [_ Evm].
  exists mo'. splits.
  - unfold evres, ev_step. rewrite (proj2 (Z.eqb_neq req 0) Hreq).
    unfold mbind at 1. apply tcan_ebind. unfold mget. constructor. cbn [fst snd].
    eapply tcan_mbind; [eapply tcan_msys; [exact Ha| rewrite Hpb; exact Hd| split; reflexivity]|].
    apply tcan_mret. split; reflexivity.
  - exact Evm.
  - eapply anstep_vm_only; exact Ha.
  - intros Hl. eapply anstep_lazy_nil; eauto.
  - intros Hm Hl. eapply anstep_materialized_nil; eauto.
Qed.

(* [comment removed for export] *)
Lemma evcan_brk_grant : forall req s mo,
  let h := m_vmmaps mo in let b := bv_unsigned (vm_brk h) in
  req <> 0 -> ps_brk s = b -> 0 < b -> bv_unsigned (vm_start_brk h) <= b -> b < req < 2^64 ->
  brk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true ->
  exists mo', evres (EBrk req) s mo req (set_brk_ps req s) mo'
    /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((vm_brk h, (Z_to_bv 64 req - vm_brk h)%bv) :: vm_maps h) (vm_noaccess h)
                     (vm_start_brk h) (Z_to_bv 64 req) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
    /\ vm_only mo mo' /\ (m_vm_lazy mo = [] -> m_vm_lazy mo' = []) /\ (m_vm_materialized mo = [] -> m_vm_lazy mo = [] -> m_vm_materialized mo' = []).
Proof.
  intros req s mo h b Hreq Hpb Hb Hsb Hr Hg.
  set (rq := Z_to_bv 64 req). set (mo' := with_brk_next mo rq rq).
  assert (Ha : anstep (NBrk req) mo (mkEffectU rq [] (brk_zeros rq rq (vm_brk h)) (brk_unmaps rq (vm_brk h)) [] []) mo').
  { cbn [anstep]. exists rq. split; [|split; reflexivity].
    unfold brk_r_ok. fold h. rewrite (w_is0_false req) by lia. unfold min_brk. subst rq. rewrite unsigned_lit by lia.
    rewrite (proj2 (Z.ltb_ge req _)) by lia. cbn [orb]. fold b. rewrite (proj2 (Z.ltb_ge req b)) by lia.
    rewrite bv_eqb_refl. cbn [orb]. exact Hg. }
  pose proof (anstep_dec_brk mo req _ mo' Hb Hsb Hr Ha) as (a & Hd & Hx). fold h b in Hd, Hx.
  destruct a.
  2:{ exfalso. destruct Hx as [E _]. apply (f_equal eff_ret) in E. unfold eff0 in E. cbn [eff_ret] in E. subst rq.
      apply (f_equal bv_unsigned) in E. rewrite unsigned_lit in E by lia. fold b in E. lia. }
  destruct Hx as (_ & _ & Evm).
  exists mo'. splits.
  - unfold evres, ev_step. rewrite (proj2 (Z.eqb_neq req 0) Hreq).
    unfold mbind at 1. apply tcan_ebind. unfold mget. constructor. cbn [fst snd].
    eapply tcan_mbind; [eapply tcan_msys; [exact Ha| rewrite Hpb; exact Hd| split; reflexivity]|].
    eapply tcan_mbind; [apply tcan_mupd; split; reflexivity|]. apply tcan_mret. split; reflexivity.
  - exact Evm.
  - eapply anstep_vm_only; exact Ha.
  - intros Hl. eapply anstep_lazy_nil; eauto.
  - intros Hm Hl. eapply anstep_materialized_nil; eauto.
Qed.

(* [comment removed for export] *)
Lemma evcan_mmap_refuse : forall a len prot flags s mo,
  mm_refusable mo prot flags (mmap_len len) = true ->
  evres (EMmap a len prot flags) s mo (neg_errno ENOMEM) s mo.
Proof.
  intros a len prot flags s mo Hforced.
  assert (Ha : anstep (NMmap a len prot flags) mo (efferr ENOMEM) mo).
  { cbn [anstep]. left. exists ENOMEM. split; [split; [left; reflexivity| exact Hforced]| split; reflexivity]. }
  assert (He : errno_of (errno_ret ENOMEM) = Some ENOMEM) by (apply errno_of_errno_ret; unfold ENOMEM; lia).
  unfold evres, ev_step.
  destruct (negb (Z.land flags MAP_FIXED_Z =? 0)).
  - eapply tcan_mbind; [eapply tcan_msys; [exact Ha| unfold dec_mmap_fixed, efferr, eff0; rewrite He; reflexivity| split; reflexivity]|].
    apply tcan_mret. split; reflexivity.
  - destruct (prot =? 0).
    + eapply tcan_mbind; [eapply tcan_msys; [exact Ha| unfold dec_mmap_none, efferr, eff0; rewrite He; reflexivity| split; reflexivity]|].
      apply tcan_mret. split; reflexivity.
    + eapply tcan_mbind; [eapply tcan_msys; [exact Ha| unfold dec_mmap, efferr, eff0; rewrite He; reflexivity| split; reflexivity]|].
      apply tcan_mret. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma evcan_mmap_rw_grant : forall len s mo (g : word),
  let h := m_vmmaps mo in let n := Z_to_bv 64 (mmap_len len) in
  0 < len -> mm_grant_rw mo (Z_to_bv 64 0) g (mmap_len len) ->
  alloc_top h <= alloc_ceiling ->   (* [comment removed for export] *)
  evres (EMmap 0 len PROT_RW MAPF) s mo (bv_unsigned g) s (mm_anon_model mo g n).
Proof.
  intros len s mo g h n Hlen Hg Hlink.
  assert (Ha : anstep (NMmap 0 len mm_prot_rw mm_flags_anon) mo (mkEffect g [] [(g, n)]) (mm_anon_model mo g n)).
  { cbn [anstep]. right; left. split; [reflexivity|]. split; [reflexivity|]. exists g. split; [exact Hg|]. split; reflexivity. }
  pose proof (anstep_dec_mmap mo len [] _ _ Hlen (Forall_nil _) Hlink Ha) as (x & Hd & Hx).
  destruct x as [e|a]. { destruct Hx as [_ E]. exfalso.
    pose proof (f_equal (fun m => length (vm_maps (m_vmmaps m))) E) as L. unfold mm_anon_model in L. rewrite m_vmmaps_with_vmmaps in L. cbn [vm_maps length] in L. lia. }
  assert (Ea : a = bv_unsigned g).
  { unfold dec_mmap in Hd. cbn [eff_ret eff_zeros] in Hd. destruct (_ && _ && _); [|discriminate]. injection Hd as <-. reflexivity. }
  subst a. unfold evres, ev_step. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false. change (PROT_RW =? 0) with false. cbv iota.
  rewrite PROT_RW_eq, MAPF_eq.
  eapply tcan_mbind; [eapply tcan_msys; [exact Ha| exact Hd| split; reflexivity]|]. apply tcan_mret. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma evcan_mmap_none_grant : forall len s mo (g : word),
  let h := m_vmmaps mo in let n := Z_to_bv 64 (mmap_len len) in
  0 < len -> mm_grant_none mo (Z_to_bv 64 0) g (mmap_len len) ->
  alloc_top h <= alloc_ceiling ->   (* [comment removed for export] *)
  evres (EMmap 0 len PROT_NONE MAPF) s mo (bv_unsigned g) s (mm_none_model mo g n).
Proof.
  intros len s mo g h n Hlen Hg Hlink.
  assert (Ha : anstep (NMmap 0 len mm_prot_none mm_flags_anon) mo (mkEffectU g [] [] [(g, n)] [] []) (mm_none_model mo g n)).
  { cbn [anstep]. right; right; left. split; [reflexivity|]. split; [reflexivity|]. exists g. split; [exact Hg|]. split; reflexivity. }
  pose proof (anstep_dec_mmap_none mo len [] _ _ Hlen (Forall_nil _) Hlink Ha) as (x & Hd & Hx).
  destruct x as [e|a]. { destruct Hx as [_ E]. exfalso.
    pose proof (f_equal (fun m => length (vm_maps (m_vmmaps m))) E) as L. unfold mm_none_model in L. rewrite m_vmmaps_with_vmmaps in L. cbn [vm_maps length] in L. lia. }
  assert (Ea : a = bv_unsigned g).
  { unfold dec_mmap_none in Hd. cbn [eff_ret eff_unmaps] in Hd. destruct (_ && _ && _); [|discriminate]. injection Hd as <-. reflexivity. }
  subst a. unfold evres, ev_step. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false. change (PROT_NONE =? 0) with true. cbv iota.
  rewrite PROT_NONE_eq, MAPF_eq.
  eapply tcan_mbind; [eapply tcan_msys; [exact Ha| exact Hd| split; reflexivity]|]. apply tcan_mret. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma evcan_munmap : forall a len s mo,
  let aw := Z_to_bv 64 a in let n := Z_to_bv 64 (mmap_len len) in
  evres (EMunmap a len) s mo 0 s (mm_unmapped_model mo aw n).
Proof.
  intros a len s mo aw n.
  assert (Ha : anstep (NMunmap a len) mo (mkEffectU (Z_to_bv 64 0) [] [] [(aw, n)] [] []) (mm_unmapped_model mo aw n)).
  { cbn [anstep]. split; reflexivity. }
  pose proof (anstep_dec_munmap mo a len _ _ Ha) as [Hd _].
  unfold evres, ev_step. eapply tcan_mbind; [eapply tcan_msys; [exact Ha| exact Hd| split; reflexivity]|]. apply tcan_mret. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma evcan_mprotect_grant : forall a len s mo,
  let aw := Z_to_bv 64 a in let n := Z_to_bv 64 (mmap_len len) in
  mprotect_budget_ok mo aw n = true ->
  evres (EMprotect a len PROT_RW) s mo 0 s (mprotect_model_next mo aw n).
Proof.
  intros a len s mo aw n Hb.
  assert (Ha : anstep (NMprotect a len PROT_RW) mo (mkEffect (Z_to_bv 64 0) [] [(aw, n)]) (mprotect_model_next mo aw n)).
  { cbn [anstep]. right. split; [exact Hb|]. split; reflexivity. }
  assert (Hd : dec_mprotect_rw a len (mkEffect (Z_to_bv 64 0) [] [(aw, n)]) = Some (RgDone true)).
  { unfold dec_mprotect_rw, dec_mprotect. cbn [eff_ret eff_zeros eff_writes]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    rewrite Z.eqb_refl, !bv_eqb_refl. reflexivity. }
  unfold evres, ev_step.
  eapply tcan_mbind; [eapply tcan_msys; [exact Ha| exact Hd| split; reflexivity]|]. apply tcan_mret. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section MonadInv.
Context {St : Type}.

Lemma tcan_mbind_inv {A B} (m : Monad.M St A) (f : A -> Monad.M St B) s mo (P : exc (B * St) -> Model -> Prop) :
  tcan (mbind m f s) mo P ->
  tcan (m s) mo (fun r mo1 => match r with Ok p => tcan (f (fst p) (snd p)) mo1 P | Unr => P Unr mo1 end).
Proof. intros H. unfold mbind in H. exact (tcan_ebind_inv _ _ _ _ H). Qed.

Lemma tcan_msys_inv {A} n (dec : resp -> option A) (s : St) mo (P : exc (A * St) -> Model -> Prop) :
  tcan (msys n dec s) mo P ->
  exists rsp mo', anstep n mo rsp mo' /\ match dec rsp with Some a => P (Ok (a, s)) mo' | None => P Unr mo' end.
Proof.
  intros H. unfold msys, enode in H. apply tcan_vis_inv in H as (rsp & mo' & Ha & Hk).
  exists rsp, mo'. split; [exact Ha|]. destruct (dec rsp); exact (tcan_ret_inv _ _ _ Hk).
Qed.
End MonadInv.

(* [comment removed for export] *)
Lemma tcan_membed_vis_inv {R} : forall e (k : Z -> stree ev Z R) s mo (r : R) sf mof,
  tcan (membed (SVis e k) s) mo (fun x mo1 => x = Ok (r, sf) /\ mo1 = mof) ->
  exists z s1 mo1, evres e s mo z s1 mo1 /\ tcan (membed (k z) s1) mo1 (fun x mo2 => x = Ok (r, sf) /\ mo2 = mof).
Proof.
  intros e k s mo r sf mof H. cbn [membed] in H. apply tcan_mbind_inv in H.
  destruct (tcan_ex _ _ _ H) as (x & mo1 & Hx & Hc). destruct x as [|[z s1]]; [destruct Hx as [Hx _]; discriminate Hx|].
  exists z, s1, mo1. split; [exact Hc| exact Hx].
Qed.

Lemma tcan_membed_ret_inv {R} : forall (r0 : R) s mo (P : exc (R * PState) -> Model -> Prop),
  tcan (membed (SRet r0) s) mo P -> P (Ok (r0, s)) mo.
Proof. intros r0 s mo P H. cbn [membed] in H. unfold mret in H. exact (tcan_ret_inv _ _ _ H). Qed.

Lemma tcan_raw_malloc_inv : forall n s mo p sf mof,
  tcan (raw_malloc n s) mo (fun x mo1 => x = Ok (p, sf) /\ mo1 = mof) ->
  exists st' rc s1, tcan (membed (cmalloc (ps_m s) n) s) mo (fun x mo1 => x = Ok ((st', rc), s1) /\ mo1 = mof)
    /\ p = match rc with Some slot => Some (slot, fresh_off st' slot n) | None => None end.
Proof.
  intros n s mo p sf mof H. unfold raw_malloc in H.
  apply tcan_mbind_inv in H. unfold mget in H. apply tcan_ret_inv in H. cbn [fst snd] in H.
  apply tcan_mbind_inv in H. destruct (tcan_ex _ _ _ H) as (x & mo1 & Hx & Hc).
  destruct x as [|[[st' rc] s1]]; [destruct Hx as [Hx _]; discriminate Hx|]. cbn [fst snd] in Hx.
  apply tcan_mbind_inv in Hx. unfold mupd in Hx. apply tcan_ret_inv in Hx. cbn [fst snd] in Hx.
  unfold mret in Hx. apply tcan_ret_inv in Hx. destruct Hx as [E ->]. injection E as <- <-.
  exists st', rc, s1. split; [exact Hc| reflexivity].
Qed.

(* [comment removed for export] *)
Definition ev_forced (e : ev) (mo : Model) (z : Z) : Prop :=
  match e with
  | EMmap a len prot flags =>
      if negb (Z.land flags MAP_FIXED_Z =? 0) then True
      else is_err z = true -> mm_refusable mo prot flags (mmap_len len) = true
  | EMprotect a len prot => z <> 0 -> mprotect_refusable mo (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
  | _ => True
  end.

Lemma is_err_mmap_addr_ok : forall len avoid a, mmap_addr_ok len avoid a = true -> 0 < len -> is_err a = false.
Proof.
  intros len avoid a H Hlen. unfold mmap_addr_ok in H. repeat (apply andb_prop in H as [H ?]).
  match goal with HH : (_ <=? alloc_ceiling) = true |- _ => apply Z.leb_le in HH; rename HH into Hce end.
  pose proof (@alloc_ceiling_lt ACEIL). pose proof (mmap_len_ge len). unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

Theorem evres_forced : forall e s mo z s' mo',
  match e with EMmap _ len _ _ => 0 < len | _ => True end ->
  evres e s mo z s' mo' -> ev_forced e mo z.
Proof.
  intros e s mo z s' mo' Hlen H. unfold evres in H.
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [ev_forced]; try exact I.
  - (* [comment removed for export] *)
    unfold ev_step in H.
    destruct (negb (Z.land flags MAP_FIXED_Z =? 0)) eqn:Efx; [exact I|].
    destruct (prot =? 0) eqn:Ep.
    + (* [comment removed for export] *)
      apply tcan_mbind_inv in H. apply tcan_msys_inv in H as (rsp & mo1 & Ha & Hd).
      destruct (dec_mmap_none len [] rsp) as [x|] eqn:Ed; [| destruct Hd as [Hd _]; discriminate Hd].
      cbn [fst snd] in Hd. unfold mret in Hd. apply tcan_ret_inv in Hd. destruct Hd as [Hd _]. injection Hd as <- _.
      intros Herr. cbn [anstep] in Ha.
      destruct Ha as [(e & [_ Hf] & _) | [(_ & _ & a & _ & -> & _) | [(_ & _ & a & _ & -> & _) | (_ & -> & _)]]].
      * exact Hf.
      * exfalso. unfold dec_mmap_none in Ed. cbn in Ed. discriminate Ed.
      * exfalso. unfold dec_mmap_none in Ed.
        destruct (bv_eqb a a && bv_eqb (Z_to_bv 64 (mmap_len len)) (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len [] (bv_unsigned a)) eqn:Eok;
          [| discriminate Ed]. injection Ed as <-.
        apply andb_prop in Eok as [_ Eok]. rewrite (is_err_mmap_addr_ok _ _ _ Eok Hlen) in Herr. discriminate Herr.
      * exfalso. discriminate Efx.
    + (* [comment removed for export] *)
      apply tcan_mbind_inv in H. apply tcan_msys_inv in H as (rsp & mo1 & Ha & Hd).
      destruct (dec_mmap len [] rsp) as [x|] eqn:Ed; [| destruct Hd as [Hd _]; discriminate Hd].
      cbn [fst snd] in Hd. unfold mret in Hd. apply tcan_ret_inv in Hd. destruct Hd as [Hd _]. injection Hd as <- _.
      intros Herr. cbn [anstep] in Ha.
      destruct Ha as [(e & [_ Hf] & _) | [(_ & _ & a & _ & -> & _) | [(-> & _) | (-> & _)]]].
      * exact Hf.
      * exfalso. unfold dec_mmap in Ed.
        destruct (bv_eqb a a && bv_eqb (Z_to_bv 64 (mmap_len len)) (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len [] (bv_unsigned a)) eqn:Eok;
          [| discriminate Ed]. injection Ed as <-.
        apply andb_prop in Eok as [_ Eok]. rewrite (is_err_mmap_addr_ok _ _ _ Eok Hlen) in Herr. discriminate Herr.
      * exfalso. discriminate Ep.
      * exfalso. discriminate Ep.
  - (* [comment removed for export] *)
    unfold ev_step in H. apply tcan_mbind_inv in H. apply tcan_msys_inv in H as (rsp & mo1 & Ha & Hd).
    destruct (dec_mprotect_rw addr len rsp) as [x|] eqn:Ed; [| destruct Hd as [Hd _]; discriminate Hd].
    cbn [fst snd] in Hd. unfold mret in Hd. apply tcan_ret_inv in Hd. destruct Hd as [Hd _]. injection Hd as <- _.
    intros Hnz. cbn [anstep] in Ha.
    destruct Ha as [(e & [_ Hf] & _) | (_ & -> & _)]; [exact Hf|].
    exfalso. unfold dec_mprotect_rw, dec_mprotect in Ed. cbn [eff_ret eff_zeros eff_writes] in Ed.
    change (bv_unsigned (Z_to_bv 64 0)) with 0 in Ed. rewrite Z.eqb_refl, !bv_eqb_refl in Ed. cbn [andb] in Ed.
    injection Ed as <-. apply Hnz. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma grant_ok_mm_grant_rw : forall mo hint a n, grant_ok hint mo a n = true -> mm_grant_rw mo hint a n.
Proof.
  intros mo hint a n H. unfold grant_ok in H. unfold mm_grant_rw.
  repeat (apply andb_prop in H as [H ?]).
  apply Z.eqb_eq in H. repeat split; auto; try (apply Z.ltb_lt; assumption); try (apply Z.leb_le; assumption).
Qed.

(* [comment removed for export] *)
Lemma grant_ok_na_mm_grant_none : forall mo hint a n, grant_ok_na_pin mo a n = true -> mm_grant_none mo hint a n.
Proof.
  intros mo hint a n H. unfold grant_ok_na_pin in H. unfold mm_grant_none.
  repeat (apply andb_prop in H as [H ?]).
  apply Z.eqb_eq in H. repeat split; auto; try (apply Z.ltb_lt; assumption); try (apply Z.leb_le; assumption).
Qed.

(* [comment removed for export] *)
Theorem grant_rw_exists : forall mo hint (N C nZ : Z),
  let h := m_vmmaps mo in
  0 < N -> N mod 4096 = 0 -> 0 <= nZ <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved h ++ vm_maps h) ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= C ->
  AsanCeil.bottomup_floor + C * (2 * N) + N <= alloc_top h ->
  vm_backing_used mo + nZ <= vm_limit h ->
  exists g, mm_grant_rw mo hint g nZ.
Proof.
  intros mo hint N C nZ h HN HNa Hn HF HC Hband Hbud.
  destruct (grant_exists_gen hint mo N nZ C HN HNa Hn HF HC Hband Hbud) as [g Hg].
  exists g. apply grant_ok_mm_grant_rw. exact Hg.
Qed.

Theorem grant_none_exists : forall mo hint (N C nZ : Z),
  let h := m_vmmaps mo in
  0 < N -> N mod 4096 = 0 -> 0 <= nZ <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved h ++ vm_maps h) ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= C ->
  AsanCeil.bottomup_floor + C * (2 * N) + N <= alloc_top h ->
  exists g, mm_grant_none mo hint g nZ.
Proof.
  intros mo hint N C nZ h HN HNa Hn HF HC Hband.
  destruct (grant_exists_na_gen mo N nZ C HN HNa Hn HF HC Hband) as [g Hg].
  exists g. apply grant_ok_na_mm_grant_none. exact Hg.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_bound : forall maps N, Forall (fun p => bv_unsigned (snd p) <= N) maps -> live_bytes maps <= Z.of_nat (length maps) * N.
Proof.
  induction maps as [|[a n] maps IH]; intros N HF; [cbn; lia|]. inversion HF; subst. cbn [live_bytes length]. cbn [snd] in H1.
  specialize (IH N H2). rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma backing_bound : forall mo N,
  m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_maps (m_vmmaps mo)) ->
  vm_backing_used mo <= Z.of_nat (length (vm_maps (m_vmmaps mo))) * N.
Proof.
  intros mo N Hl Hm HF. pose proof (vm_backing_used_le_live mo Hl Hm). unfold vm_live_bytes in H.
  pose proof (live_bytes_bound _ _ HF). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brk_grow_ok_intro : forall mo req,
  let h := m_vmmaps mo in let b := bv_unsigned (vm_brk h) in
  m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  b mod 4096 = 0 -> req mod 4096 = 0 -> 0 < b -> b < req -> req <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (vm_brk h) (Z_to_bv 64 (req - b + page_size)) = true ->
  vm_live_bytes h + (req - b) <= vm_limit h ->
  brk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true.
Proof.
  intros mo req h b Hl Hm Hba Hra Hb Hlt Hce Hrf Hbud.
  pose proof (alloc_top_lt h) as Htl. unfold two_pow_64 in Htl.
  pose proof (bv_unsigned_in_range 64 (vm_brk h)) as Hbr. unfold bv_modulus in Hbr. change (2 ^ Z.of_N 64) with (2^64) in Hbr.
  assert (Hureq : bv_unsigned (Z_to_bv 64 req) = req) by (apply unsigned_lit; lia).
  unfold brk_grow_ok, Mmap.brk_budget_ok. fold h. rewrite Hureq. fold b.  (* [comment removed for export] *)
  rewrite (proj2 (Z.ltb_lt 0 _) Hb), (proj2 (Z.ltb_lt b req) Hlt). cbn [andb].
  assert (Epb : page_round_up_Z b = b).
  { unfold page_round_up_Z, page_size. pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096).
    pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
  assert (Epr : page_round_up_Z req = req).
  { unfold page_round_up_Z, page_size. pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096).
    pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  rewrite Epb, Epr, (proj2 (Z.ltb_lt b req) Hlt), (proj2 (Z.leb_le _ _) Hce). cbn [andb].
  replace (Z_to_bv 64 b) with (vm_brk h) by (unfold b; symmetry; apply Z_to_bv_bv_unsigned).
  replace (req + page_size - b) with (req - b + page_size) by lia. rewrite Hrf. cbn [andb].
  replace (bv_unsigned (Z_to_bv 64 req - vm_brk h)) with (req - b).
  2:{ rewrite bv_sub_unsigned, Hureq. rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia). fold b. lia. }
  apply Z.leb_le. apply grant_budget_intro; assumption.
Qed.

(* [comment removed for export] *)
Lemma init_sp_ok_of_link : forall h, alloc_top h = alloc_ceiling -> AsanCeil.init_sp_ok h.
Proof.
  intros h H. unfold AsanCeil.init_sp_ok, alloc_top in *. pose proof (@alloc_ceiling_lo ACEIL).
  unfold sp_window_lo, stack_max_size in *. lia.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
End KB_Can.

(* [comment removed for export] *)
Module KB_Room.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition brk_count (L : mled) : Z :=
  match ld_brkreg L with
  | Some (b, l) => l / PGSZ
  | None => match ld_brk L with BPGuard _ => 1 | _ => 0 end
  end.

Definition led_small (L : mled) (N K : Z) : Prop :=
  (forall b l, In (b, l) (ld_groups L) -> mmap_len l <= N)
  /\ (forall b l k, In (b, l, k) (ld_metas L) -> mmap_len l <= N)
  /\ 2 * PGSZ <= N
  /\ Z.of_nat (length (ld_groups L)) + Z.of_nat (length (ld_metas L)) + brk_count L <= K.

(* [comment removed for export] *)
Definition brk_canon (L : mled) : list (word * word) :=
  match ld_brkreg L with
  | Some (b, l) => went b (2 * PGSZ) :: map (fun j => went (b + Z.of_nat j * PGSZ) PGSZ) (seq 1 (Z.to_nat (l / PGSZ) - 1))
  | None => match ld_brk L with BPGuard cur => [went cur (2 * PGSZ)] | _ => [] end
  end.

Definition canon (L : mled) : list (word * word) :=
  map (fun g : Z * Z => went (fst g) (mmap_len (snd g))) (ld_groups L)
  ++ map (fun m : Z * Z * Z => went (fst (fst m)) (mmap_len (snd (fst m)))) (ld_metas L)
  ++ brk_canon L.

Lemma vmwf_NoDup : forall maps, vmwf maps -> List.NoDup maps.
Proof.
  intros maps [Hb Hp]. induction Hp as [|e l Hd Hp IH]; [constructor|]. constructor.
  - intros Hin. pose proof (Hd e Hin) as D. pose proof (Hb e (or_introl eq_refl)). unfold edisj in D. lia.
  - apply IH. intros e' He'. apply Hb. right. exact He'.
Qed.

Lemma brk_canon_length : forall L pbrk mo, KL L pbrk mo -> Z.of_nat (length (brk_canon L)) <= brk_count L.
Proof.
  intros L pbrk mo HK. unfold brk_canon, brk_count. destruct (ld_brkreg L) as [[b l]|] eqn:E.
  - pose proof (kl_brkreg _ _ _ HK b l E) as (R1 & R2 & R3 & R4 & R5 & _). cbn [length]. rewrite length_map, length_seq.
    assert (2 <= l / PGSZ) by (unfold PGSZ in *; clear -R3; lia). lia.
  - destruct (ld_brk L); cbn; lia.
Qed.

Lemma canon_length : forall L pbrk mo N K, KL L pbrk mo -> led_small L N K -> Z.of_nat (length (canon L)) <= K.
Proof.
  intros L pbrk mo N K HK (_ & _ & _ & HK2). unfold canon. rewrite !length_app, !length_map.
  pose proof (brk_canon_length _ _ _ HK). lia.
Qed.

Lemma KL_maps_incl_canon : forall L pbrk mo, KL L pbrk mo -> incl (vm_maps (m_vmmaps mo)) (canon L).
Proof.
  intros L pbrk mo HK e He. unfold canon. destruct (kl_cov _ _ _ HK e He) as [(b & l & Hin & ->)|[(b & l & k & Hin & ->)|B]].
  - apply in_or_app. left. apply in_map_iff. exists (b, l). auto.
  - apply in_or_app. right. apply in_or_app. left. apply in_map_iff. exists (b, l, k). auto.
  - apply in_or_app. right. apply in_or_app. right. unfold brk_piece in B. unfold brk_canon.
    destruct (ld_brkreg L) as [[b l]|] eqn:E.
    + destruct B as [->|(j & J1 & J2 & ->)]; [left; reflexivity| right].
      pose proof (kl_brkreg _ _ _ HK b l E) as (R1 & R2 & R3 & R4 & R5 & _).
      apply in_map_iff. exists (Z.to_nat j). split; [rewrite Z2Nat.id by lia; reflexivity|].
      apply in_seq. unfold PGSZ in *. clear -J1 J2 R3 R4. lia.
    + destruct (ld_brk L); try contradiction. left. symmetry. exact B.
Qed.

(* [comment removed for export] *)
Theorem KL_room : forall L pbrk mo N K,
  KL L pbrk mo -> led_small L N K ->
  let h := m_vmmaps mo in
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_maps h)
  /\ Z.of_nat (length (vm_maps h)) <= K.
Proof.
  intros L pbrk mo N K HK HS h. pose proof HS as (G1 & G2 & G3 & G4). pose proof alloc_ceiling_lt as Hcl. split.
  - apply Forall_forall. intros e He. destruct (kl_cov _ _ _ HK e He) as [(b & l & Hin & ->)|[(b & l & k & Hin & ->)|B]].
    + pose proof (went_In_bounds _ _ _ b l HK (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
      replace (bv_unsigned (snd (went b (mmap_len l)))) with (ehi (went b (mmap_len l)) - elo (went b (mmap_len l))) by (unfold ehi, elo; lia). rewrite B5, B6.
      pose proof (G1 b l Hin). lia.
    + pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
      replace (bv_unsigned (snd (went b (mmap_len l)))) with (ehi (went b (mmap_len l)) - elo (went b (mmap_len l))) by (unfold ehi, elo; lia). rewrite B5, B6.
      pose proof (G2 b l k Hin). lia.
    + unfold brk_piece in B. destruct (ld_brkreg L) as [[b l]|] eqn:E.
      * destruct B as [->|(j & J1 & J2 & ->)]; cbn [snd went]; rewrite unsigned_lit by (unfold PGSZ; lia); unfold PGSZ in *; lia.
      * destruct (ld_brk L); try contradiction. subst e. cbn [snd went]. rewrite unsigned_lit by (unfold PGSZ; lia). unfold PGSZ in *; lia.
  - pose proof (NoDup_incl_length (vmwf_NoDup _ (kl_wf _ _ _ HK)) (KL_maps_incl_canon _ _ _ HK)) as Hlen.
    pose proof (canon_length _ _ _ _ _ HK HS). subst h. lia.
Qed.

Theorem KL_room_app : forall L pbrk mo N K NR,
  KL L pbrk mo -> led_small L N K ->
  let h := m_vmmaps mo in
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved h) -> Z.of_nat (length (vm_reserved h)) <= NR ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved h ++ vm_maps h)
  /\ Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= NR + K
  /\ vm_live_bytes h <= K * N.
Proof.
  intros L pbrk mo N K NR HK HS h HR HRl. destruct (KL_room L pbrk mo N K HK HS) as [F C]. fold h in F, C.
  split; [apply Forall_app; split; assumption|]. split; [rewrite length_app; lia|].
  unfold vm_live_bytes. clear HR HRl. revert F C. generalize (vm_maps h) as maps. intros maps F C.
  assert (HB : forall ms, Forall (fun p : word * word => bv_unsigned (snd p) <= N) ms -> live_bytes ms <= Z.of_nat (length ms) * N).
  { induction ms as [|[a n] ms IH]; intros HF; [cbn; lia|]. inversion HF; subst. cbn [live_bytes length]. cbn [snd] in H1.
    specialize (IH H2). rewrite Nat2Z.inj_succ. lia. }
  pose proof (HB maps F). destruct HS as (_ & _ & G3 & _). unfold PGSZ in G3. nia.
Qed.


End CeilWrap.
End KB_Room.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Contracts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_Simrel.
Module KB_Sites.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cfg.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.NodesSoundDec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS ImplRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MEX_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_konts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_m0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw KB_Can KB_Room OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_Simrel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma evres_post : forall L e s mo z s' mo',
  event_pre L e -> KL L (ps_brk s) mo -> evres e s mo z s' mo' -> ev_step_post L e s mo z s' mo'.
Proof.
  intros L e s mo z s' mo' Hpre HK Hev.
  assert (Hp : s = s /\ mo = mo /\ KL L (ps_brk s) mo) by auto.
  pose proof (ev_step_spec L e s mo Hpre s mo Hp) as Hwf. unfold etwf in Hwf.
  destruct (tcan_ex _ _ _ (twf_tcan _ _ _ _ Hwf Hev)) as (r & mo1 & [HP [-> ->]] & _). exact HP.
Qed.

Lemma ctree_ok_not_rejects {R} : forall L (t : stree ev Z R) Post, ctree_ok L t Post -> ~ rejects t.
Proof. intros L t Post H Hr. destruct t as [r|e k]; [exact Hr|]. destruct e; try exact Hr. cbn in H. exact (proj1 H). Qed.

Lemma neg_errno_ENOMEM : neg_errno ENOMEM = ENOMEM_ans.
Proof. reflexivity. Qed.

Definition is_none {A} (o : option A) : bool := match o with None => true | Some _ => false end.

(* [comment removed for export] *)
Definition never_none (cs : mstate) (n : Z) (mo : Model) : Prop :=
  forall s L, ps_m s = cs -> MI_Contracts.SIMREL cs L -> KL L (ps_brk s) mo ->
  forall p sf mof, tcan (raw_malloc n s) mo (fun x mo1 => x = Ok (p, sf) /\ mo1 = mof) -> is_none p = false.
Definition can_some (cs : mstate) (n : Z) (mo : Model) : Prop :=
  forall s L, ps_m s = cs -> MI_Contracts.SIMREL cs L -> KL L (ps_brk s) mo ->
  tcan (raw_malloc n s) mo (fun r _ => exists p, r = Ok p /\ is_none (fst p) = false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem site_never_none : forall cs n lo hi mo (N C : Z),
  one_mmap_site cs n lo hi -> 0 <= n -> 0 < lo -> hi + 4096 <= N -> N mod 4096 = 0 ->
  let h := m_vmmaps mo in
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved h ++ vm_maps h) ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= C ->
  AsanCeil.bottomup_floor + C * (2 * N) + N <= alloc_top h ->
  vm_backing_used mo + N <= vm_limit h ->
  never_none cs n mo.
Proof.
  intros cs n lo hi mo N C (len & k & Et & Hlen & _ & _ & _ & Hok) Hn Hlo HN HNa h HF HC Hband Hbud s L Hcs Hc HK p sf mof Hcan.
  pose proof (simrel_malloc_contract _ _ _ Hc Hn) as CT. rewrite Et in CT. cbn [ctree_ok] in CT. destruct CT as [Hpre Hk].
  assert (Hlen0 : 0 < len) by lia. pose proof (mmap_len_ge' len Hlen0) as Hml.
  assert (A1 : 0 < N) by lia. assert (A2 : 0 <= mmap_len len <= N) by lia. assert (A3 : vm_backing_used mo + mmap_len len <= vm_limit h) by lia.
  destruct (grant_rw_exists mo (Z_to_bv 64 0) N C (mmap_len len) A1 HNa A2 HF HC Hband A3) as [g Hg].
  apply tcan_raw_malloc_inv in Hcan as (st' & rc & s1 & Hc1 & ->). rewrite Hcs, Et in Hc1.
  apply tcan_membed_vis_inv in Hc1 as (z & s2 & mo2 & Hev & Hc2).
  pose proof (evres_post L _ s mo _ _ _ Hpre HK Hev) as (Hans & _).
  pose proof (evres_forced (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) _ _ _ _ _ Hlen0 Hev) as Hf. cbn [ev_forced] in Hf.
  change (negb (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED_Z =? 0)) with false in Hf. cbv iota in Hf.
  assert (Herr : is_err z = false).
  { destruct (is_err z) eqn:E; [|reflexivity]. specialize (Hf eq_refl).
    change (MAP_PRIVATE + MAP_ANON) with mm_flags_anon in Hf. rewrite PROT_RW_eq in Hf.
    rewrite (mm_grant_rw_not_refusable _ _ _ _ Hg) in Hf. discriminate Hf. }
  specialize (Hk _ Hans). pose proof (ctree_ok_not_rejects _ _ _ Hk) as NR.
  destruct (Hok z NR Herr) as (cs' & c & Ek). rewrite Ek in Hc2.
  apply tcan_membed_ret_inv in Hc2 as [E _]. injection E as <- <- <-. reflexivity.
Qed.

Theorem site_can_some : forall cs n lo hi mo (N C : Z),
  one_mmap_site cs n lo hi -> 0 <= n -> 0 < lo -> hi + 4096 <= N -> N mod 4096 = 0 ->
  let h := m_vmmaps mo in
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved h ++ vm_maps h) ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= C ->
  AsanCeil.bottomup_floor + C * (2 * N) + N <= alloc_top h ->   (* [comment removed for export] *)
  alloc_top h <= alloc_ceiling ->   (* [comment removed for export] *)
  vm_backing_used mo + N <= vm_limit h ->
  can_some cs n mo.
Proof.
  intros cs n lo hi mo N C (len & k & Et & Hlen & _ & _ & _ & Hok) Hn Hlo HN HNa h HF HC Hband Hlink Hbud s L Hcs Hc HK.
  pose proof (simrel_malloc_contract _ _ _ Hc Hn) as CT. rewrite Et in CT. cbn [ctree_ok] in CT. destruct CT as [Hpre Hk].
  assert (Hlen2 : 0 < len < LEN_MAX).
  { cbn [event_pre] in Hpre. destruct Hpre as [(_ & _ & _ & _ & H)|(cur & _ & _ & _ & E & _)]; [exact H| discriminate]. }
  assert (Hlen0 : 0 < len) by lia. pose proof (mmap_len_ge' len Hlen0) as Hml.
  assert (A1 : 0 < N) by lia. assert (A2 : 0 <= mmap_len len <= N) by lia. assert (A3 : vm_backing_used mo + mmap_len len <= vm_limit h) by lia.
  destruct (grant_rw_exists mo (Z_to_bv 64 0) N C (mmap_len len) A1 HNa A2 HF HC Hband A3) as [g Hg].
  pose proof (evcan_mmap_rw_grant len s mo g Hlen0 Hg Hlink) as Hev. cbv zeta in Hev.
  pose proof (evres_post L _ s mo _ _ _ Hpre HK Hev) as (Hans & HK' & _).
  specialize (Hk _ Hans). pose proof (ctree_ok_not_rejects _ _ _ Hk) as NR.
  destruct Hg as (G1 & G2 & G3 & _). pose proof alloc_ceiling_lt as Hcl. fold h in G3.
  destruct (Hok (bv_unsigned g) NR ltac:(unfold is_err, TWO64; apply Z.ltb_ge; lia)) as (cs' & c & Ek).
  eapply tcan_mono; [apply (tcan_raw_malloc n s mo (fun rc => rc <> None))|].
  - rewrite Hcs, Et. eapply tcan_membed_vis; [exact Hev|]. rewrite Ek. apply tcan_membed_ret. exists cs', (Some c), s. split; [reflexivity| discriminate].
  - intros r mo1 (p & s1 & -> & W). exists (p, s1). split; [reflexivity|]. cbn [fst]. destruct p as [q|]; [reflexivity| exfalso; apply W; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma filter_length_disj {A} (p q : A -> bool) (l : list A) :
  (forall x, In x l -> p x = true -> q x = true -> False) ->
  (length (List.filter p l) + length (List.filter q l) <= length l)%nat.
Proof.
  induction l as [|x l IH]; intros H; [cbn; lia|]. cbn.
  specialize (IH ltac:(intros y Hy; apply H; right; exact Hy)).
  destruct (p x) eqn:Ep, (q x) eqn:Eq; cbn; try lia. exfalso. apply (H x); [left; reflexivity| exact Ep| exact Eq].
Qed.

Theorem led_small_of_cs : forall cs L NN K,
  MI_Contracts.SIMREL cs L ->
  (forall rid r, s_regions cs !! rid = Some r -> mmap_len (r_len r) <= NN /\ (r_kind r = RKBrk -> r_len r <= 2 * PGSZ)) ->
  2 * PGSZ <= NN -> Z.of_nat (size (s_regions cs)) + 2 <= K ->
  led_small L NN K.
Proof.
  intros cs L NN K Hc HR HN HK.
  destruct Hc as (st & BL & LS & Hst & INV & _).
  pose proof (proj1 INV) as IR.
  assert (Ereg : s_regions st = s_regions cs) by (rewrite <- Hst; reflexivity).
  pose proof (ir_groups _ _ _ IR) as PG. pose proof (ir_metas _ _ _ IR) as PM. rewrite Ereg in PG, PM.
  split; [|split; [|split; [exact HN|]]].
  - intros b l Hin. apply (Permutation_in _ PG) in Hin. apply in_map_iff in Hin as ([rid r] & E & Hin). cbn in E. injection E as <- <-.
    apply List.filter_In in Hin as [Hin _]. apply list_elem_of_In, elem_of_map_to_list in Hin. exact (proj1 (HR _ _ Hin)).
  - intros b l k Hin. apply (Permutation_in _ PM) in Hin. apply in_map_iff in Hin as ([rid r] & E & Hin). cbn in E. injection E as <- <- _.
    apply List.filter_In in Hin as [Hin _]. apply list_elem_of_In, elem_of_map_to_list in Hin. exact (proj1 (HR _ _ Hin)).
  - rewrite (Permutation_length PG), (Permutation_length PM), !length_map.
    pose proof (filter_length_disj (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end)
                                   (fun kr : N * region => match r_kind (snd kr) with RKMeta => true | _ => false end)
                                   (map_to_list (s_regions cs)) ltac:(intros [? r] _; cbn; destruct (r_kind r); discriminate)) as HL.
    rewrite length_map_to_list in HL.
    assert (HB : brk_count L <= 2).
    { unfold brk_count. destruct (ld_brkreg L) as [[b l]|] eqn:E.
      - destruct (proj1 (ir_brkreg _ _ _ IR b l) E) as (rid & r & Hr & Kr & Eb & El). rewrite Ereg in Hr.
        destruct (HR _ _ Hr) as [_ H2]. specialize (H2 Kr). rewrite El in H2. unfold PGSZ in *. clear -H2. lia.
      - destruct (ld_brk L); lia. }
    lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cs_small (cs : mstate) : Prop :=
  (forall rid r, s_regions cs !! rid = Some r -> mmap_len (r_len r) <= 2^27 - 4096 /\ (r_kind r = RKBrk -> r_len r <= 2 * PGSZ))
  /\ (size (s_regions cs) <= 6)%nat.

Lemma rp_bounds_small : rp_bounds_stmt -> forall cs D fl lo, MEX_defs.RP cs D fl lo -> cs_small cs.
Proof.
  intros RB cs D fl lo HRP. destruct (RB cs D fl lo HRP) as (R1 & R2 & R3 & R4). split; [| lia].
  intros rid r Hr. destruct (R1 rid r Hr) as [(-> & El & Hk)|(d & Hd & -> & ->)].
  - rewrite El. split; [| intros _; lia]. unfold PGSZ. rewrite NodesSound.mmap_len_of_aligned by reflexivity. lia.
  - cbn [r_len r_kind]. split; [| discriminate]. pose proof (R2 d Hd). pose proof (mmap_len_ge' (db_len d) ltac:(lia)). lia.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
End KB_Sites.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require AsanCeil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes Decode SCPS NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.NodesSoundDec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS.
Import ImplRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim STree Malloc MallocCtrl Prog KInv KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Contracts Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MEX_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_konts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_iface.MEX_m0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MEX_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KInv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KRaw.
Import KB_Can.
Import KB_Room.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KB_Simrel.
Import KB_Sites.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
Lemma walk_inv {R0 R} : forall (t : stree ev Z R0) (f : R0 -> stree ev Z R) e k L s mo Post (r : R) sf mof,
  t = SVis e k ->
  ctree_ok L (sbind t f) Post -> KL L (ps_brk s) mo ->
  match e with EMmap _ len _ _ => 0 < len | _ => True end ->
  tcan (membed (sbind t f) s) mo (fun x mo1 => x = Ok (r, sf) /\ mo1 = mof) ->
  exists z s' mo', answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s') mo' /\ ev_forced e mo z
    /\ ctree_ok (event_post L e z) (sbind (k z) f) Post
    /\ tcan (membed (sbind (k z) f) s') mo' (fun x mo1 => x = Ok (r, sf) /\ mo1 = mof).
Proof.
  intros t f e k L s mo Post r sf mof -> Hok HK Hlen Hc. cbn [sbind] in Hok, Hc. destruct Hok as [Hpre Hk].
  apply tcan_membed_vis_inv in Hc as (z & s' & mo' & Hev & Hc).
  pose proof (evres_post L e s mo z s' mo' Hpre HK Hev) as (Hans & HK' & _).
  exists z, s', mo'. split; [exact Hans|]. split; [exact HK'|]. split; [exact (evres_forced e s mo z s' mo' Hlen Hev)|].
  split; [exact (Hk z Hans)| exact Hc].
Qed.

(* [comment removed for export] *)
Lemma KL_small_room : forall L pbrk mo,
  KL L pbrk mo -> led_small L (2^17) 4 ->
  Forall (fun p => bv_unsigned (snd p) <= 2^18) (vm_reserved (m_vmmaps mo)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps mo))) <= 16 ->
  forall nZ, 0 <= nZ <= 2^17 ->
    mm_refusable mo mm_prot_rw mm_flags_anon nZ = false /\ mm_refusable mo mm_prot_none mm_flags_anon nZ = false.
Proof.
  intros L pbrk mo HK HS HRs HRl nZ HnZ.
  assert (HS' : led_small L (2^18) 4).
  { destruct HS as (S1 & S2 & S3 & S4). split; [intros b l Hi; pose proof (S1 b l Hi); lia|].
    split; [intros b l k Hi; pose proof (S2 b l k Hi); lia|]. split; lia. }
  destruct (KL_room_app L pbrk mo (2^18) 4 16 HK HS' HRs HRl) as (F1 & F2 & F3).
  assert (Hband : AsanCeil.bottomup_floor + 20 * (2 * 2^18) + 2^18 <= alloc_top (m_vmmaps mo)).
  { rewrite (kl_top _ _ _ HK), AsanCeil.bottomup_floor_val. pose proof (@alloc_ceiling_lo ACEIL). lia. }
  assert (Hbud : vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo)).
  { pose proof (vm_backing_used_le_live mo (kl_lazy _ _ _ HK) (kl_mat _ _ _ HK)). pose proof (kl_lim _ _ _ HK). unfold drv_limit in *. lia. }
  split.
  - destruct (grant_rw_exists mo (Z_to_bv 64 0) (2^18) 20 nZ ltac:(lia) eq_refl ltac:(lia) F1 ltac:(lia) Hband Hbud) as [g Hg].
    exact (mm_grant_rw_not_refusable _ _ _ _ Hg).
  - destruct (grant_none_exists mo (Z_to_bv 64 0) (2^18) 20 nZ ltac:(lia) eq_refl ltac:(lia) F1 ltac:(lia) Hband) as [g Hg].
    exact (mm_grant_none_not_refusable _ _ _ _ Hg).
Qed.

Lemma KL_small_mprotect : forall L pbrk mo a n,
  KL L pbrk mo -> led_small L (2^17) 4 -> mprotect_refusable mo a n = false.
Proof.
  intros L pbrk mo a n HK HS.
  assert (HRs : Forall (fun p : word * word => bv_unsigned (snd p) <= 2^17) (@nil (word * word))) by constructor.
  unfold mprotect_refusable, mprotect_budget_ok, vm_backing_within_limit. apply negb_false_iff. apply Z.leb_le.
  set (mo' := mprotect_model_next mo a n).
  assert (Hl : m_vm_lazy mo' = []) by exact (kl_lazy _ _ _ HK).
  assert (Hm : m_vm_materialized mo' = []) by exact (kl_mat _ _ _ HK).
  pose proof (vm_backing_used_le_live mo' Hl Hm) as HB.
  destruct (KL_room L pbrk mo (2^17) 4 HK HS) as [F C].
  assert (HLB : vm_live_bytes (m_vmmaps mo') <= 4 * 2^17).
  { unfold vm_live_bytes. change (vm_maps (m_vmmaps mo')) with (vm_maps (m_vmmaps mo)).
    pose proof (live_bytes_bound _ _ F). nia. }
  change (vm_limit (m_vmmaps mo')) with (vm_limit (m_vmmaps mo)).
  pose proof (kl_lim _ _ _ HK). unfold drv_limit in *. lia.
Qed.

(* [comment removed for export] *)
Lemma site_grant_69632 : forall mo,
  Forall (fun p => bv_unsigned (snd p) <= 2^17) (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))) <= 17 ->
  vm_backing_used mo + 2^17 <= vm_limit (m_vmmaps mo) ->
  alloc_top (m_vmmaps mo) = alloc_ceiling ->   (* [comment removed for export] *)
  exists g, mm_grant_rw mo (Z_to_bv 64 0) g (mmap_len 69632).
Proof.
  intros mo HF HC HB Hlink. apply (grant_rw_exists mo (Z_to_bv 64 0) (2^17) 17 (mmap_len 69632)); try assumption.
  - lia. - reflexivity. - change (mmap_len 69632) with 69632. lia.
  - rewrite AsanCeil.bottomup_floor_val, Hlink. pose proof (@alloc_ceiling_lo ACEIL). lia.
  - change (mmap_len 69632) with 69632. lia.
Qed.

Section M0.
Variable resv : list (Z * Z).
Let cs0 := cs0 resv.
Let T0 := M0c resv.

Lemma cmalloc0_eq : cmalloc cs0 65536 = sbind T0 cm_fin.
Proof. unfold T0, M0c. exact (cmalloc_eq cs0 65536). Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma T0_shape : exists k1, T0 = SVis (EBrk 0) k1 /\ forall cur, brk0_answer_ok cur = true -> exists k2,
  k1 cur = SVis (EBrk (round_up_pg cur + 2 * PGSZ)) k2
  /\ (exists k3, k2 cur = SVis (EMmap 0 8192 PROT_NONE MAPF) k3
       /\ k3 ENOMEM_ans = SRet (upd_ctx (set_brk BrkDead) (m0_st1 resv), None))
  /\ (brk_pages_ok (m0_st1 resv) (round_up_pg cur) (2 * PGSZ) = false -> rejects (k2 (round_up_pg cur + 2 * PGSZ)))
  /\ (brk_pages_ok (m0_st1 resv) (round_up_pg cur) (2 * PGSZ) = true -> exists k3,
        k2 (round_up_pg cur + 2 * PGSZ) = SVis (EMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) k3
        /\ forall rg, mmap_fixed_answer_ok (round_up_pg cur) rg = true -> exists k4,
             k3 rg = SVis (EMmap 0 69632 PROT_RW MAPF) k4
             /\ (forall r, mmap_answer_ok (live_ranges (m0_st7 resv (VA cur))) 69632 r = false -> rejects (k4 r))
             /\ (forall r, mmap_answer_ok (live_ranges (m0_st7 resv (VA cur))) 69632 r = true -> is_err r = false ->
                   k4 r = SRet (m0_pre resv (VA cur) r, Some (m0 , 0)))).
Proof.
  pose proof (M0c_eq resv) as E0. fold T0 in E0.
  eexists. split; [exact E0|]. intros cur Hc.
  pose proof (M0c_1 resv cur Hc) as E1. fold T0 in E1. rewrite E0 in E1. cbn [tsub] in E1. eexists. split; [exact E1|].
  split; [|split].
  - pose proof (M0c_2B resv cur Hc) as E2. fold T0 in E2. cbn [tsubs] in E2. rewrite E0 in E2. cbn [tsub] in E2. rewrite E1 in E2. cbn [tsub] in E2.
    eexists. split; [exact E2|].
    pose proof (M0c_3B_err resv cur ENOMEM_ans Hc (ENOMEM_ans_ok _ _) ENOMEM_ans_err) as E3.
    fold T0 in E3. cbn [tsubs] in E3. rewrite E0 in E3. cbn [tsub] in E3. rewrite E1 in E3. cbn [tsub] in E3. rewrite E2 in E3. cbn [tsub] in E3. exact E3.
  - intros HP. pose proof (M0c_2A_bad resv cur Hc HP) as E2. fold T0 in E2. cbn [tsubs] in E2. rewrite E0 in E2. cbn [tsub] in E2. rewrite E1 in E2. cbn [tsub] in E2. exact E2.
  - intros HP. pose proof (M0c_2A resv cur Hc HP) as E2. fold T0 in E2. cbn [tsubs] in E2. rewrite E0 in E2. cbn [tsub] in E2. rewrite E1 in E2. cbn [tsub] in E2.
    eexists. split; [exact E2|]. intros rg Hrg.
    pose proof (M0c_3A resv cur rg Hc HP Hrg) as E3. fold T0 in E3. cbn [tsubs] in E3. rewrite E0 in E3. cbn [tsub] in E3. rewrite E1 in E3. cbn [tsub] in E3. rewrite E2 in E3. cbn [tsub] in E3.
    eexists. split; [exact E3|]. split.
    + intros r Hr. apply ag_kmm_m0_bad. exact Hr.
    + intros r Hr He. apply ag_kmm_m0_ok; assumption.
Qed.

Lemma mmap_fixed_answer_ok_ENOMEM : forall a, mmap_fixed_answer_ok a ENOMEM_ans = true.
Proof. intros a. unfold mmap_fixed_answer_ok. replace (is_errno_form ENOMEM_ans) with true by reflexivity. reflexivity. Qed.

Lemma not_rejects_sbind {R S} : forall (t : stree ev Z R) (f : R -> stree ev Z S), ~ rejects (sbind t f) -> ~ rejects t.
Proof. intros t f H Hr. apply H. apply rejects_sbind. exact Hr. Qed.

(* [comment removed for export] *)
Lemma T0_shape_B : forall k1, T0 = SVis (EBrk 0) k1 -> forall cur k2, brk0_answer_ok cur = true ->
  k1 cur = SVis (EBrk (round_up_pg cur + 2 * PGSZ)) k2 ->
  exists k3, k2 cur = SVis (EMmap 0 8192 PROT_NONE MAPF) k3
   /\ (forall am, mmap_answer_ok (resv ++ []) 8192 am = false -> rejects (k3 am))
   /\ (forall am, mmap_answer_ok (resv ++ []) 8192 am = true -> is_err am = false -> exists k4,
         k3 am = SVis (EMprotect (am + 4096) PGSZ PROT_RW) k4
         /\ (forall mp, mprotect_answer_ok mp = true -> mp = 0 -> exists k5,
               k4 mp = SVis (EMmap 0 69632 PROT_RW MAPF) k5
               /\ (forall r, mmap_answer_ok (live_ranges (m0_st7 resv (VB am))) 69632 r = false -> rejects (k5 r))
               /\ (forall r, mmap_answer_ok (live_ranges (m0_st7 resv (VB am))) 69632 r = true -> is_err r = false ->
                     k5 r = SRet (m0_pre resv (VB am) r, Some (m0 , 0))))).
Proof.
  intros k1 E0 cur k2 Hc E1.
  pose proof (M0c_2B resv cur Hc) as E2. fold T0 in E2. cbn [tsubs] in E2. rewrite E0 in E2. cbn [tsub] in E2. rewrite E1 in E2. cbn [tsub] in E2.
  eexists. split; [exact E2|]. split.
  - intros am HV. pose proof (M0c_3B_bad resv cur am Hc HV) as E3.
    fold T0 in E3. cbn [tsubs] in E3. rewrite E0 in E3. cbn [tsub] in E3. rewrite E1 in E3. cbn [tsub] in E3. rewrite E2 in E3. cbn [tsub] in E3. exact E3.
  - intros am HV HE. pose proof (M0c_3B resv cur am Hc HV HE) as E3.
    fold T0 in E3. cbn [tsubs] in E3. rewrite E0 in E3. cbn [tsub] in E3. rewrite E1 in E3. cbn [tsub] in E3. rewrite E2 in E3. cbn [tsub] in E3.
    eexists. split; [exact E3|]. intros mp HM Hmp.
    (* [comment removed for export] *)
    pose proof (M0c_4B resv cur am mp Hc HV HE HM (or_introl Hmp)) as E4.
    fold T0 in E4. cbn [tsubs] in E4. rewrite E0 in E4. cbn [tsub] in E4. rewrite E1 in E4. cbn [tsub] in E4. rewrite E2 in E4. cbn [tsub] in E4.
    rewrite E3 in E4. cbn [tsub] in E4.
    eexists. split; [exact E4|]. split.
    + intros r Hr. apply ag_kmm_m0_bad. exact Hr.
    + intros r Hr He. apply ag_kmm_m0_ok; assumption.
Qed.

Lemma led_resv_event_post : forall L e z, ld_resv (event_post L e z) = ld_resv L.
Proof.
  intros L e z. destruct e; cbn; repeat (destruct (_ =? _)); try reflexivity;
  try (destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[? ?]|]; reflexivity);
  try (destruct (is_err z); reflexivity); try (destruct (_ || _); reflexivity).
Qed.

(* [comment removed for export] *)
Lemma m0_group_step : forall v k L s mo Post (r : mstate * option cptr) sf mof,
  (forall z, mmap_answer_ok (live_ranges (m0_st7 resv v)) 69632 z = false -> rejects (k z)) ->
  (forall z, mmap_answer_ok (live_ranges (m0_st7 resv v)) 69632 z = true -> is_err z = false ->
     k z = SRet (m0_pre resv v z, Some (m0 , 0))) ->
  ctree_ok L (sbind (SVis (EMmap 0 69632 PROT_RW MAPF) k) cm_fin) Post -> KL L (ps_brk s) mo ->
  mm_refusable mo mm_prot_rw mm_flags_anon (mmap_len 69632) = false ->
  tcan (membed (sbind (SVis (EMmap 0 69632 PROT_RW MAPF) k) cm_fin) s) mo (fun x mo1 => x = Ok (r, sf) /\ mo1 = mof) ->
  snd r <> None.
Proof.
  intros v k L s mo Post r sf mof Hbad Hgood CT HK Hroom Hc.
  destruct (walk_inv _ cm_fin _ _ L s mo Post r sf mof eq_refl CT HK ltac:(cbn; lia) Hc) as (z & s' & mo' & Hans & HK' & Hf & CT' & Hc').
  change (is_err z = true -> mm_refusable mo mm_prot_rw mm_flags_anon (mmap_len 69632) = true) in Hf.
  rewrite Hroom in Hf.
  assert (Herr : is_err z = false) by (destruct (is_err z); [specialize (Hf eq_refl); discriminate Hf| reflexivity]).
  pose proof (not_rejects_sbind _ _ (ctree_ok_not_rejects _ _ _ CT')) as NR.
  destruct (mmap_answer_ok (live_ranges (m0_st7 resv v)) 69632 z) eqn:HA; [| exfalso; apply NR; apply Hbad; exact HA].
  rewrite (Hgood z HA Herr) in Hc'. cbn [sbind cm_fin] in Hc'.
  apply tcan_membed_ret_inv in Hc' as [E _]. injection E as <- _. cbn [snd]. discriminate.
Qed.

(* [comment removed for export] *)
Theorem m0_never_none : forall s mo,
  ps_m s = cs0 -> ps_brk s = 0 -> KL (led_init resv) 0 mo ->
  let h := m_vmmaps mo in
  Forall (fun p => bv_unsigned (snd p) <= 2^18) (vm_reserved h) -> Z.of_nat (length (vm_reserved h)) <= 16 ->
  forall p sf mof, tcan (raw_malloc 65536 s) mo (fun x mo1 => x = Ok (p, sf) /\ mo1 = mof) -> is_none p = false.
Proof.
  intros s mo Hcs Hpb HK h HRs HRl p sf mof Hcan. pose proof alloc_ceiling_lt as Hcl.
  pose proof (simrel_malloc_contract _ _ 65536 (simrel_init resv) ltac:(lia)) as CT.
  change (strip (minit 0 resv)) with cs0 in CT. rewrite cmalloc0_eq in CT.
  destruct T0_shape as (k1 & E0 & Hsh).
  apply tcan_raw_malloc_inv in Hcan as (st' & rc & sfin & Hc0 & ->). rewrite Hcs, cmalloc0_eq in Hc0.
  assert (G : rc <> None); [| destruct rc; [reflexivity| exfalso; apply G; reflexivity]].
  change rc with (snd (st', rc)). revert Hc0. generalize (st', rc). intros r Hc0.
  (* [comment removed for export] *)
  assert (RES : forall L' pb' mo', KL L' pb' mo' -> ld_resv L' = resv ->
            Forall (fun p => bv_unsigned (snd p) <= 2^18) (vm_reserved (m_vmmaps mo')) /\ Z.of_nat (length (vm_reserved (m_vmmaps mo'))) <= 16).
  { intros L' pb' mo' HK' E. rewrite (KL_resv_eq _ _ _ _ _ _ HK HK' E). split; assumption. }
  (* [comment removed for export] *)
  rewrite <- Hpb in HK.
  destruct (walk_inv _ cm_fin _ _ _ s mo _ r sfin mof E0 CT HK I Hc0) as (cur & s1' & mo1 & Hans1 & HK1 & _ & CT1 & Hc1).
  cbn [answer_ok Z.eqb] in Hans1. cbn [event_post Z.eqb] in HK1, CT1.
  destruct (Hsh cur Hans1) as (k2 & E1 & _ & Hbad & Hgood).
  destruct (T0_shape_B k1 E0 cur k2 Hans1 E1) as (k3B & E2B & HbadB & HgoodB).
  pose proof (brk0_ok_facts cur Hans1) as (B1 & B2 & B3). rewrite B3 in *.
  (* [comment removed for export] *)
  destruct (walk_inv _ cm_fin _ _ _ s1' mo1 _ r sfin mof E1 CT1 HK1 I Hc1) as (z2 & s2 & mo2 & Hans2 & HK2 & _ & CT2 & Hc2).
  assert (Eq0 : (cur + 2 * PGSZ =? 0) = false) by (apply Z.eqb_neq; unfold PGSZ; lia).
  cbn [answer_ok] in Hans2. rewrite Eq0 in Hans2. cbn [ld_brk set_brkph led_init] in Hans2.
  cbn [event_post] in HK2, CT2. rewrite Eq0 in HK2, CT2. cbn [ld_brk set_brkph led_init] in HK2, CT2.
  apply andb_prop in Hans2 as [Hans2 Hpg]. unfold brk_answer_ok in Hans2. apply orb_prop in Hans2 as [Ez|Ez]; apply Z.eqb_eq in Ez; subst z2.
  - (* [comment removed for export] *)
    rewrite Z.eqb_refl in HK2, CT2, Hpg. cbn [negb orb] in Hpg.
    destruct (brk_pages_ok (m0_st1 resv) cur (2 * PGSZ)) eqn:HP.
    2:{ exfalso. apply (ctree_ok_not_rejects _ _ _ CT2). apply rejects_sbind. apply Hbad. reflexivity. }
    destruct (Hgood eq_refl) as (k3 & E2 & Hk3).
    (* [comment removed for export] *)
    destruct (walk_inv _ cm_fin _ _ _ s2 mo2 _ r sfin mof E2 CT2 HK2 ltac:(unfold PGSZ; lia) Hc2) as (rg & s3 & mo3 & Hans3 & HK3 & _ & CT3 & Hc3).
    cbn [answer_ok] in Hans3. change (Z.land MAPFX MAP_FIXED =? 0) with false in Hans3. cbv iota in Hans3.
    destruct (Hk3 rg Hans3) as (k4 & E3 & Hk4bad & Hk4ok). rewrite E3 in CT3, Hc3.
    (* [comment removed for export] *)
    cbn [event_post] in HK3. change (Z.land MAPFX MAP_FIXED =? 0) with false in HK3. cbv iota in HK3.
    eapply (m0_group_step (VA cur) k4 _ s3 mo3 _ r sfin mof Hk4bad Hk4ok CT3 HK3); [| exact Hc3].
    destruct (RES _ _ _ HK3 eq_refl) as [R1 R2].
    refine (proj1 (KL_small_room _ _ _ HK3 _ R1 R2 (mmap_len 69632) ltac:(change (mmap_len 69632) with 69632; lia))).
    split; [intros b l []|]. split; [intros b l k0 []|]. split; [unfold PGSZ; lia|].
    unfold brk_count. cbn. change (2 * PGSZ / PGSZ) with 2. lia.
  - (* [comment removed for export] *)
    replace (cur =? cur + 2 * PGSZ) with false in HK2, CT2 by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia).
    rewrite E2B in CT2, Hc2.
    destruct (RES _ _ _ HK2 eq_refl) as [R1 R2].
    assert (HS2 : led_small (set_brkph BPDead (set_brkph (BPQueried cur) (led_init resv))) (2^17) 4).
    { split; [intros b l []|]. split; [intros b l k0 []|]. split; [unfold PGSZ; lia|]. unfold brk_count. cbn. lia. }
    destruct (walk_inv _ cm_fin (EMmap 0 8192 PROT_NONE MAPF) k3B _ s2 mo2 _ r sfin mof eq_refl CT2 HK2 ltac:(cbn; lia) Hc2) as (am & s3 & mo3 & Hans3 & HK3 & Hf3 & CT3 & Hc3).
    change (is_err am = true -> mm_refusable mo2 mm_prot_none mm_flags_anon (mmap_len 8192) = true) in Hf3.
    rewrite (proj2 (KL_small_room _ _ _ HK2 HS2 R1 R2 (mmap_len 8192) ltac:(change (mmap_len 8192) with 8192; lia))) in Hf3.
    assert (Herr3 : is_err am = false) by (destruct (is_err am); [specialize (Hf3 eq_refl); discriminate Hf3| reflexivity]).
    pose proof (not_rejects_sbind _ _ (ctree_ok_not_rejects _ _ _ CT3)) as NR3.
    destruct (mmap_answer_ok (resv ++ []) 8192 am) eqn:HA3; [| exfalso; apply NR3; apply HbadB; exact HA3].
    destruct (HgoodB am HA3 Herr3) as (k4 & E3 & Hk4). rewrite E3 in CT3, Hc3.
    cbn [event_post] in HK3, CT3. change (Z.land MAPF MAP_FIXED =? 0) with true in HK3, CT3. cbv iota in HK3, CT3.
    rewrite Herr3 in HK3, CT3. change (PROT_NONE =? PROT_NONE) with true in HK3, CT3. cbv iota in HK3, CT3.
    set (L3 := set_metas ((am, 8192, 0) :: ld_metas (set_brkph BPDead (set_brkph (BPQueried cur) (led_init resv))))
                 (set_brkph BPDead (set_brkph (BPQueried cur) (led_init resv)))) in *.
    assert (HS3 : led_small L3 (2^17) 4).
    { split; [intros b l []|]. split; [intros b l k0 [E|[]]; injection E as <- <- <-; change (mmap_len 8192) with 8192; lia|].
      split; [unfold PGSZ; lia|]. unfold brk_count. cbn. lia. }
    (* [comment removed for export] *)
    destruct (walk_inv _ cm_fin (EMprotect (am + 4096) PGSZ PROT_RW) k4 _ s3 mo3 _ r sfin mof eq_refl CT3 HK3 I Hc3) as (mp & s4 & mo4 & Hans4 & HK4 & Hf4 & CT4 & Hc4).
    cbn [ev_forced] in Hf4. rewrite (KL_small_mprotect _ _ _ _ _ HK3 HS3) in Hf4.
    assert (Emp : mp = 0) by (destruct (Z.eq_dec mp 0) as [E|NE]; [exact E| specialize (Hf4 NE); discriminate Hf4]). subst mp.
    cbn [answer_ok] in Hans4.
    destruct (Hk4 0 Hans4 eq_refl) as (k5 & E4 & Hk5bad & Hk5ok). rewrite E4 in CT4, Hc4.
    (* [comment removed for export] *)
    eapply (m0_group_step (VB am) k5 _ s4 mo4 _ r sfin mof Hk5bad Hk5ok CT4 HK4); [| exact Hc4].
    destruct (RES _ _ _ HK4 ltac:(rewrite led_resv_event_post; reflexivity)) as [R1' R2'].
    refine (proj1 (KL_small_room _ _ _ HK4 _ R1' R2' (mmap_len 69632) ltac:(change (mmap_len 69632) with 69632; lia))).
    cbn [event_post]. change ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true. cbv iota.
    split; [intros b l []|]. split.
    + intros b l k0 Hin. cbn [ld_metas set_metas L3 map] in Hin. destruct Hin as [E|[]].
      unfold bump_meta in E. cbn [fst snd] in E. destruct (_ =? _) in E; injection E as <- <- _; change (mmap_len 8192) with 8192; lia.
    + split; [unfold PGSZ; lia|]. unfold brk_count. cbn. lia.
Qed.
End M0.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
