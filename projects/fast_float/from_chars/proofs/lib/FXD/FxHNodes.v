(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMchr FxMNode.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive hnode : Type :=
| HQC (j : nat)      (* [comment removed for export] *)
| HMC (j : nat).     (* [comment removed for export] *)

Section H.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable img : tree Z.
Variable qsites : list qsite.
Variable mcsites : list Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Himg : img_ok segs img.
Hypothesis Hqs : Forall (qsite_ok segs) qsites.
Hypothesis Hms : Forall (msite_ok segs) mcsites.
Context {A : Type}.
Variable HA : valu -> smodel -> A -> (word -> option byte) -> Prop.
Variable awf : positive -> A -> bool.
Hypothesis HA_agree : forall n E E' M a m0, sm_wf n M = true -> awf n a = true -> agree n E E' -> HA E M a m0 -> HA E' M a m0.

Definition hpost (nk : hnode) (S : sst) (M : smodel) (a : A) : option (sst * smodel * A) :=
  match nk with
  | HQC j => match nth_error qsites j with
             | Some q => if qc_chk img q S M then Some (qc_post q S, M, a) else None
             | None => None
             end
  | HMC j => match nth_error mcsites j with
             | Some pcw => if mc_chk img pcw S then Some (mc_post S, M, a) else None
             | None => None
             end
  end.

(* [comment removed for export] *)
#[using="Hwx Himg Hqs Hms HA_agree"] Theorem hnode_ok : forall nk S M a S' M' a', hpost nk S M a = Some (S', M', a') ->
  forall model0 mem0 E ms model T, DEN segs LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' ->
     (forall p, In p (sm_frz M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> mem0' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
     DEN segs LIMIT model0 mem0' E' S' M' ms' model' -> HA E' M' a' mem0' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Himg Hqs Hms HA_agree : LiaFast.U) => LiaFast.u0).
  intros nk S M a S' M' a' Hp model0 mem0 E ms model T Hd Haw HHA Hk.
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf.
  destruct nk as [j|j]; cbn [hpost] in Hp.
  - destruct (nth_error qsites j) as [q|] eqn:Hq; [|discriminate].
    destruct (qc_chk img q S M) eqn:Hc; [|discriminate]. injection Hp as <- <- <-.
    rewrite Forall_forall in Hqs.
    apply (den_qc segs cfg LIMIT model0 mem0 img Hwx Himg q S M E ms model T (Hqs q (nth_error_In _ _ Hq)) Hc Hd).
    intros E' ms' model' Ha' Hd'. apply (Hk E' mem0 ms' model' Ha'); [intros p _ w _; reflexivity | exact Hd' |].
    exact (HA_agree (s_next S) E E' M a mem0 Hwf Haw Ha' HHA).
  - destruct (nth_error mcsites j) as [pcw|] eqn:Hq; [|discriminate].
    destruct (mc_chk img pcw S) eqn:Hc; [|discriminate]. injection Hp as <- <- <-.
    rewrite Forall_forall in Hms.
    apply (den_mc segs cfg LIMIT model0 mem0 img Hwx Himg pcw S M E ms model T (Hms pcw (nth_error_In _ _ Hq)) Hc Hd).
    intros E' ms' model' Ha' Hd'. apply (Hk E' mem0 ms' model' Ha'); [intros p _ w _; reflexivity | exact Hd' |].
    exact (HA_agree (s_next S) E E' M a mem0 Hwf Haw Ha' HHA).
Qed.
End H.
