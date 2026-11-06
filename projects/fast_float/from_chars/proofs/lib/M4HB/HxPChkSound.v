(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEntM FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart FxChain FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChWv FxChMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.FxChLoop OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChSubst FxChBlob.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcFacts.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HxPChk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma frz_same_trans : forall E1 M1 E2 M2 m0 m1 m2, frz_same E1 M1 m0 m1 -> frz_covs E1 M1 E2 M2 -> frz_same E2 M2 m1 m2 -> frz_same E1 M1 m0 m2.
Proof.
  intros E1 M1 E2 M2 m0 m1 m2 H01 Hc H12 p Hp w Hw. destruct (Hc p Hp) as (q & Hq & Hq1 & Hq2).
  rewrite (H12 q Hq w ltac:(rewrite Hq1, Hq2; exact Hw)). exact (H01 p Hp w Hw).
Qed.
Lemma frz_same_refl : forall E M m0, frz_same E M m0 m0.
Proof. intros E M m0 p _ w _. reflexivity. Qed.
Lemma frz_same_msubst : forall E σ MP m0 m1, frz_same (ecomp E σ) MP m0 m1 -> frz_same E (msubst σ MP) m0 m1.
Proof.
  intros E σ MP m0 m1 H p Hp w Hw. unfold msubst in Hp. cbn [sm_frz] in Hp. apply in_map_iff in Hp as (q & <- & Hq).
  unfold ppsubst in Hw. cbn [fst snd] in Hw. rewrite <- !uE_sub in Hw. exact (H q Hq w Hw).
Qed.


Section PSound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable t : tree xi.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Ht : tbl_ok segs t.
Hypothesis Himg : img_ok segs img.
Context {N A : Type}.
Variable apost : N -> sst -> smodel -> A -> option (sst * smodel * A).
Variables (aeqb : A -> A -> bool) (awf : positive -> A -> bool).
Variable HA : valu -> smodel -> A -> (word -> option byte) -> Prop.
Variable asub : tree lin -> A -> A.
Variable agok : smodel -> A -> bool.
Variable alins : A -> list lin.
Variable aset : A -> list lin -> A.
Hypothesis awf_mono : forall n n' a, (n <= n')%positive -> awf n a = true -> awf n' a = true.
Hypothesis aeqb_eq : forall x y, aeqb x y = true -> x = y.
Hypothesis HA_agree : forall n E E' M a m0, sm_wf n M = true -> awf n a = true -> agree n E E' -> HA E M a m0 -> HA E' M a m0.
Hypothesis Hanode : forall nk, anode_ok segs cfg LIMIT apost awf HA nk.
Hypothesis HA_msub : forall E σ M a m0, agok M a = true -> HA E (msubst σ M) (asub σ a) m0 -> HA (ecomp E σ) M a m0.
(* [comment removed for export] *)
Variable subs : list (sst * smodel * A * list (sst * smodel * A)).
Hypothesis HMUse : forall j T MT aT fins, nth_error subs j = Some (T, MT, aT, fins) -> sub_ok segs cfg LIMIT awf HA T MT aT fins.
Hypothesis HA_use : subs <> [] -> forall E σ M a m0, HA (ecomp E σ) M a m0 -> HA E (msubst σ M) (asub σ a) m0.
(* [comment removed for export] *)
Variable amod : smodel -> smodel -> A -> bool.
Hypothesis HA_mod : forall E M M' a m0, amod M M' a = true -> HA E M a m0 -> HA E M' a m0.
Variable LIMW : Z.      (* [comment removed for export] *)
Hypothesis HLW : LIMW = LIMIT \/ (forall M M' a, amod M M' a = false).

(* [comment removed for export] *)
#[using="Type"] Lemma Hpm0 : (length ([] : path) < path_max)%nat.
Proof. LiaFast.lf_pins LiaFast.u0. unfold path_max. cbn. lia. Qed.

Definition PHAX (E : valu) (S : sst) (M : smodel) (a : A) (mem0 : word -> option byte) : Prop := awf (s_next S) a = true /\ HA E M a mem0.

Definition Pp (ch : @mchain N) : Prop :=
  forall S M a finals, pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW ch S M a = Some finals ->
  forall model0 mem0 E ms model T, DEN segs LIMIT model0 mem0 E S M ms model -> PHAX E S M a mem0 ->
  (forall S' M' a' mem0' E' ms' model', In (S', M', a') finals -> DEN segs LIMIT model0 mem0' E' S' M' ms' model' ->
     PHAX E' S' M' a' mem0' -> agree (s_next S) E E' -> frz_covs E M E' M' -> frz_same E M mem0 mem0' ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Definition Qp (ks : @mks N) : Prop :=
  forall L M a finals, pfindu segs t img apost aeqb awf asub agok alins aset subs amod LIMW ks L M a = Some finals ->
  forall model0 mem0 E ms model T, DEN segs LIMIT model0 mem0 E L M ms model -> PHAX E L M a mem0 ->
  (forall S' M' a' mem0' E' ms' model', In (S', M', a') finals -> DEN segs LIMIT model0 mem0' E' S' M' ms' model' ->
     PHAX E' S' M' a' mem0' -> agree (s_next L) E E' -> frz_covs E M E' M' -> frz_same E M mem0 mem0' ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.

#[using="Type"] Lemma frz_covs_self : forall model0 mem0 E S M ms model, DEN segs LIMIT model0 mem0 E S M ms model -> frz_covs E M E M.
Proof. LiaFast.lf_pins LiaFast.u0. intros model0 mem0 E S M ms model Hd. exact (frz_covs_agree (s_next S) E E M M (dn_wf _ _ _ _ _ _ _ _ _ Hd) (agree_refl _ _) eq_refl). Qed.

#[using="Type"] Lemma Qp_nil : Qp KNil.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pfindu] in Hck. injection Hck as <-.
  exact (Hk L M a mem0 E ms model (or_introl eq_refl) Hd HX (agree_refl _ _) (frz_covs_self _ _ _ _ _ _ _ Hd) (frz_same_refl _ _ _)).
Qed.
#[using="Type"] Lemma Qp_cons : forall b sys k r, Pp k -> Qp r -> Qp (KCons b sys k r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b sys k r IHk IHr L M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pfindu] in Hck.
  destruct (Z.eqb b (s_pc L) && (Z.eqb sys 0 || match a7c L with Some c => Z.eqb c sys | None => false end))%bool;
    [exact (IHk L M a finals Hck model0 mem0 E ms model T Hd HX Hk) | exact (IHr L M a finals Hck model0 mem0 E ms model T Hd HX Hk)].
Qed.
#[using="Type"] Lemma Pp_end : Pp MEnd.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck. injection Hck as <-.
  exact (Hk S M a mem0 E ms model (or_introl eq_refl) Hd HX (agree_refl _ _) (frz_covs_self _ _ _ _ _ _ _ Hd) (frz_same_refl _ _ _)).
Qed.
#[using="Type"] Lemma Pp_void : Pp MVoid.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (fx_contra (s_facts S)) eqn:Hc; [|discriminate].
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  exfalso. exact (fx_contra_false [] [] Hpm0 E _ HF0 Hc).
Qed.
#[using="Type"] Lemma Pp_alt : forall k1 k2, Pp k1 -> Pp k2 -> Pp (MAlt k1 k2).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k1 k2 IH1 IH2 S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (is_mvoid k1) eqn:Hv.
  - destruct (fx_contra1 (s_facts S)) eqn:Hc.
    + destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
      exfalso. exact (fx_contra_false [] [] Hpm0 E _ HF0 (fx_contra1_contra _ Hc)).
    + exact (IH2 S M a finals Hck model0 mem0 E ms model T Hd HX Hk).
  - destruct (pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW k1 S M a) as [f1|] eqn:H1.
    + injection Hck as <-. exact (IH1 S M a f1 H1 model0 mem0 E ms model T Hd HX Hk).
    + exact (IH2 S M a finals Hck model0 mem0 E ms model T Hd HX Hk).
Qed.


#[using="awf_mono HA_agree"] Lemma PHAX_step : forall E E' S S' M a mem0, PHAX E S M a mem0 -> sm_wf (s_next S) M = true -> agree (s_next S) E E' ->
  (s_next S <= s_next S')%positive -> PHAX E' S' M a mem0.
Proof. LiaFast.lf_pins (fun (awf_mono HA_agree : LiaFast.U) => LiaFast.u0). intros E E' S S' M a mem0 [Hw Hh] Hwf Ha Hle. split; [exact (awf_mono _ _ a Hle Hw) | exact (HA_agree _ E E' M a mem0 Hwf Hw Ha Hh)]. Qed.
#[using="Type"] Lemma PHAX_same : forall E S S' M a mem0, PHAX E S M a mem0 -> s_next S' = s_next S -> PHAX E S' M a mem0.
Proof. LiaFast.lf_pins LiaFast.u0. intros E S S' M a mem0 [Hw Hh] Hn. split; [rewrite Hn; exact Hw | exact Hh]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cont_same : forall S S' M (finals : list (sst * smodel * A)) (mem0 : word -> option byte) E (T : TSet) model0,
  s_next S' = s_next S -> sm_wf (s_next S) M = true ->
  (forall S'' M'' a'' mem0'' E'' ms'' model'', In (S'', M'', a'') finals -> DEN segs LIMIT model0 mem0'' E'' S'' M'' ms'' model'' ->
     PHAX E'' S'' M'' a'' mem0'' -> agree (s_next S) E E'' -> frz_covs E M E'' M'' -> frz_same E M mem0 mem0'' ->
     realizes_cfg segs cfg (mkCfg ms'' model'') T) ->
  (forall S'' M'' a'' mem0'' E'' ms'' model'', In (S'', M'', a'') finals -> DEN segs LIMIT model0 mem0'' E'' S'' M'' ms'' model'' ->
     PHAX E'' S'' M'' a'' mem0'' -> agree (s_next S') E E'' -> frz_covs E M E'' M'' -> frz_same E M mem0 mem0'' ->
     realizes_cfg segs cfg (mkCfg ms'' model'') T).
Proof. LiaFast.lf_pins LiaFast.u0. intros S S' M finals mem0 E T model0 Hn Hwf Hk. rewrite Hn. exact Hk. Qed.

#[using="Hwx Ht Himg awf_mono HA_agree"] Lemma Pp_segk : forall depth p ks, Qp ks -> Pp (MSegK depth p ks).
Proof. LiaFast.lf_pins (fun (Hwx Ht Himg awf_mono HA_agree : LiaFast.U) => LiaFast.u0).
  intros depth p ks IH S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (pbases_below (s_next S) (s_rgs S)) eqn:Hbi; [|discriminate]. rewrite pbases_below_eq in Hbi.
  rewrite checkB_pos_below in Hck.
  destruct (check t img (pos_below (s_next S)) depth p S) as [Ls|] eqn:Hc; [|discriminate].
  apply (den_seg segs cfg LIMIT model0 mem0 Hwx t img (pos_below (s_next S)) depth p S Ls E M ms model T Ht Himg Hc Hd Hbi
           (pos_below_In (s_next S))).
  intros L E' ms' model' HL Hd' Ha'.
  destruct (all_some_spec _ _ _ Hck L HL) as (o & Ho & Hsub). cbv beta in Ho.
  destruct (sm_wf (s_next L) M && Pos.leb (s_next S) (s_next L))%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hwl Hle]. apply Pos.leb_le in Hle.
  assert (Hwf : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  apply (IH L M a o Ho model0 mem0 E' ms' model' T Hd' (PHAX_step E E' S L M a mem0 HX Hwf Ha' Hle)).
  intros S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' HX'' Ha'' Hc'' Hf''.
  pose proof (frz_covs_agree (s_next S) E E' M M Hwf Ha' eq_refl) as Hc0.
  exact (Hk S'' M'' a'' mem0'' E'' ms'' model'' (Hsub _ Hin'') Hd'' HX'' (agree_trans _ E E' E'' Ha' (agree_mono _ _ E' E'' Hle Ha''))
           (frz_covs_trans E M E' M E'' M'' Hc0 Hc'') (frz_same_trans E M E' M mem0 mem0 mem0'' (frz_same_refl _ _ _) Hc0 Hf'')).
Qed.

#[using="Hanode"] Lemma Pp_call : forall nk k, Pp k -> Pp (MCall nk k).
Proof. LiaFast.lf_pins (fun (Hanode : LiaFast.U) => LiaFast.u0).
  intros nk k IH S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (apost nk S M a) as [[[S' M'] a']|] eqn:Hap; [|discriminate].
  destruct (Pos.leb (s_next S) (s_next S') && frz_eqb (sm_frz M') (sm_frz M) && awf (s_next S') a')%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hwa']. apply andb_prop in Hb as [Hle Hfz]. apply Pos.leb_le in Hle. apply frz_eqb_eq in Hfz.
  assert (Hwf : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  apply (Hanode nk S M a S' M' a' Hap model0 mem0 E ms model T Hd (proj1 HX) (proj2 HX)).
  intros E' mem0' ms' model' Ha' Hfsm Hd' Hha'.
  apply (IH S' M' a' finals Hck model0 mem0' E' ms' model' T Hd' (conj Hwa' Hha')).
  intros S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' HX'' Ha'' Hc'' Hf''.
  pose proof (frz_covs_agree (s_next S) E E' M M' Hwf Ha' Hfz) as Hc0.
  exact (Hk S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' HX'' (agree_trans _ E E' E'' Ha' (agree_mono _ _ E' E'' Hle Ha''))
           (frz_covs_trans E M E' M' E'' M'' Hc0 Hc'') (frz_same_trans E M E' M' mem0 mem0' mem0'' Hfsm Hc0 Hf'')).
Qed.

#[using="HA_mod HLW"] Lemma Pp_alloww : forall j z k, Pp k -> Pp (MAllowW j z k).
Proof. LiaFast.lf_pins (fun (HA_mod HLW : LiaFast.U) => LiaFast.u0).
  intros j z k IH S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (widen_ok LIMW S M j z) eqn:Hok; [|discriminate]. destruct (amod M _ a) eqn:Ham; [|discriminate]. cbn [andb] in Hck.
  destruct HLW as [HL|HL]; [|rewrite HL in Ham; discriminate]. rewrite HL in Hok.
  set (M' := with_allow M (widen_nth j z (sm_allow M))) in *.
  assert (Hwf : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  pose proof (den_allow_widen segs LIMIT model0 mem0 E S M ms model j z Hd Hok) as Hd'.
  apply (IH S M' a finals Hck model0 mem0 E ms model T Hd' (conj (proj1 HX) (HA_mod E M M' a mem0 Ham (proj2 HX)))).
  intros S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' HX'' Ha'' Hc'' Hf''.
  exact (Hk S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' HX'' Ha'' Hc'' Hf'').
Qed.

#[using="Type"] Lemma Pp_sep : forall op k, Pp k -> Pp (MSep op k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros op k IH S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (sep_post segs op S M) as [S'|] eqn:Hs; [|discriminate].
  destruct (sep_post_den segs LIMIT op model0 mem0 E S M ms model S' Hd Hs) as [Hd' Hn].
  assert (Hwf : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  exact (IH S' M a finals Hck model0 mem0 E ms model T Hd' (PHAX_same E S S' M a mem0 HX Hn) (cont_same S S' M finals mem0 E T model0 Hn Hwf Hk)).
Qed.

#[using="Type"] Lemma Pp_concr : forall k, Pp k -> Pp (MConcR k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k IH S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  assert (Hn : s_next (concr S) = s_next S) by reflexivity.
  assert (Hwf : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  exact (IH (concr S) M a finals Hck model0 mem0 E ms model T (den_concr segs LIMIT [] [] Hpm0 model0 mem0 E S M ms model Hd)
           (PHAX_same E S _ M a mem0 HX Hn) (cont_same S (concr S) M finals mem0 E T model0 Hn Hwf Hk)).
Qed.

#[using="Type"] Lemma Pp_gc : forall nk xs k, Pp k -> Pp (MGc nk xs k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros nk xs k IH S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  assert (Hn : s_next (gc_post nk xs S M PFS PSH) = s_next S) by reflexivity.
  assert (Hwf : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  assert (Hdg : DEN segs LIMIT model0 mem0 E (gc_post nk xs S M PFS PSH) M ms model).
  { apply (den_gc segs LIMIT model0 mem0 E S M ms model); [|exact Hd]. intros f Hf. apply fdedup_in in Hf. apply filter_In in Hf. exact (proj1 Hf). }
  exact (IH (gc_post nk xs S M PFS PSH) M a finals Hck model0 mem0 E ms model T Hdg
           (PHAX_same E S _ M a mem0 HX Hn) (cont_same S _ M finals mem0 E T model0 Hn Hwf Hk)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma Pp_fact : forall k S M a finals f model0 mem0 E ms model T, Pp k ->
  pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW k (add_fact S f) M a = Some finals ->
  DEN segs LIMIT model0 mem0 E S M ms model -> PHAX E S M a mem0 -> (forall E', agree (s_next S) E E' -> fact_ok E' f) ->
  (forall S'' M'' a'' mem0'' E'' ms'' model'', In (S'', M'', a'') finals -> DEN segs LIMIT model0 mem0'' E'' S'' M'' ms'' model'' ->
     PHAX E'' S'' M'' a'' mem0'' -> agree (s_next S) E E'' -> frz_covs E M E'' M'' -> frz_same E M mem0 mem0'' ->
     realizes_cfg segs cfg (mkCfg ms'' model'') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k S M a finals f model0 mem0 E ms model T IH Hck Hd HX Hf Hk.
  assert (Hn : s_next (add_fact S f) = s_next S) by reflexivity.
  assert (Hwf : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  exact (IH (add_fact S f) M a finals Hck model0 mem0 E ms model T (den_addfact segs LIMIT model0 mem0 E S M ms model f Hd Hf)
           (PHAX_same E S _ M a mem0 HX Hn) (cont_same S _ M finals mem0 E T model0 Hn Hwf Hk)).
Qed.
#[using="Type"] Lemma in_app_l' : forall {X} (l1 l2 : list X) x, In x l1 -> In x (l1 ++ l2). Proof. LiaFast.lf_pins LiaFast.u0. intros. apply in_or_app. left. assumption. Qed.
#[using="Type"] Lemma in_app_r' : forall {X} (l1 l2 : list X) x, In x l2 -> In x (l1 ++ l2). Proof. LiaFast.lf_pins LiaFast.u0. intros. apply in_or_app. right. assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma Pp_range : forall l c ka kb S M a f1 f2 model0 mem0 E ms model T, Pp ka -> Pp kb -> lwf (s_next S) l = true ->
  (if Z.leb (fst (irange (s_facts S) l)) c then pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW ka (add_fact S (FRange l (fst (irange (s_facts S) l)) (Z.min c (snd (irange (s_facts S) l))))) M a else Some []) = Some f1 ->
  (if Z.ltb c (snd (irange (s_facts S) l)) then pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW kb (add_fact S (FRange l (Z.max (c + 1) (fst (irange (s_facts S) l))) (snd (irange (s_facts S) l)))) M a else Some []) = Some f2 ->
  DEN segs LIMIT model0 mem0 E S M ms model -> PHAX E S M a mem0 ->
  (forall S'' M'' a'' mem0'' E'' ms'' model'', In (S'', M'', a'') (f1 ++ f2) -> DEN segs LIMIT model0 mem0'' E'' S'' M'' ms'' model'' ->
     PHAX E'' S'' M'' a'' mem0'' -> agree (s_next S) E E'' -> frz_covs E M E'' M'' -> frz_same E M mem0 mem0'' ->
     realizes_cfg segs cfg (mkCfg ms'' model'') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l c ka kb S M a f1 f2 model0 mem0 E ms model T IHa IHb Hwl H1 H2 Hd HX Hk.
  pose proof (u_range E l) as Rl.
  assert (HFs : Forall (fact_ok E) (s_facts S)) by (destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  pose proof (irange_sound E (s_facts S) l HFs) as Ir.
  destruct (Z_le_gt_dec (bv_unsigned (lden E l)) c) as [Hle|Hgt].
  - assert (Hc1 : Z.leb (fst (irange (s_facts S) l)) c = true) by (apply Z.leb_le; lia). rewrite Hc1 in H1.
    apply (Pp_fact ka S M a f1 _ model0 mem0 E ms model T IHa H1 Hd HX).
    + intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next S) E E' l Hwl Ha'). lia.
    + intros S'' M'' a'' mem0'' E'' ms'' model'' Hin. exact (Hk S'' M'' a'' mem0'' E'' ms'' model'' (in_app_l' _ _ _ Hin)).
  - assert (Hc2 : Z.ltb c (snd (irange (s_facts S) l)) = true) by (apply Z.ltb_lt; lia). rewrite Hc2 in H2.
    apply (Pp_fact kb S M a f2 _ model0 mem0 E ms model T IHb H2 Hd HX).
    + intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next S) E E' l Hwl Ha'). unfold M64, two64 in *. lia.
    + intros S'' M'' a'' mem0'' E'' ms'' model'' Hin. exact (Hk S'' M'' a'' mem0'' E'' ms'' model'' (in_app_r' _ _ _ Hin)).
Qed.

#[using="Type"] Lemma Pp_split : forall l c ka kb, Pp ka -> Pp kb -> Pp (MSplit l c ka kb).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l c ka kb IHa IHb S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (lwf (s_next S) l) eqn:Hwl; [|discriminate].
  destruct (if Z.leb (fst (irange (s_facts S) l)) c then pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW ka (add_fact S (FRange l (fst (irange (s_facts S) l)) (Z.min c (snd (irange (s_facts S) l))))) M a else Some []) as [f1|] eqn:H1; [|discriminate].
  destruct (if Z.ltb c (snd (irange (s_facts S) l)) then pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW kb (add_fact S (FRange l (Z.max (c + 1) (fst (irange (s_facts S) l))) (snd (irange (s_facts S) l)))) M a else Some []) as [f2|] eqn:H2; [|discriminate].
  injection Hck as <-. exact (Pp_range l c ka kb S M a f1 f2 model0 mem0 E ms model T IHa IHb Hwl H1 H2 Hd HX Hk).
Qed.
#[using="Type"] Lemma Pp_splitG : forall j c ka kb, Pp ka -> Pp kb -> Pp (MSplitG j c ka kb).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros j c ka kb IHa IHb S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (nth_error (sm_maps M) j) as [g|]; [|discriminate].
  destruct (lwf (s_next S) (fst (fst g))) eqn:Hwl; [|discriminate].
  destruct (if Z.leb (fst (irange (s_facts S) (fst (fst g)))) c then pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW ka (add_fact S (FRange (fst (fst g)) (fst (irange (s_facts S) (fst (fst g)))) (Z.min c (snd (irange (s_facts S) (fst (fst g))))))) M a else Some []) as [f1|] eqn:H1; [|discriminate].
  destruct (if Z.ltb c (snd (irange (s_facts S) (fst (fst g)))) then pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW kb (add_fact S (FRange (fst (fst g)) (Z.max (c + 1) (fst (irange (s_facts S) (fst (fst g))))) (snd (irange (s_facts S) (fst (fst g)))))) M a else Some []) as [f2|] eqn:H2; [|discriminate].
  injection Hck as <-. exact (Pp_range _ c ka kb S M a f1 f2 model0 mem0 E ms model T IHa IHb Hwl H1 H2 Hd HX Hk).
Qed.
#[using="Type"] Lemma Pp_splitR : forall r c ka kb, Pp ka -> Pp kb -> Pp (MSplitR r c ka kb).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros r c ka kb IHa IHb S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  set (l := rget (s_regs S) (Z.to_pos (r + 1))) in *.
  destruct (lwf (s_next S) l) eqn:Hwl; [|discriminate].
  destruct (if Z.leb (fst (irange (s_facts S) l)) c then pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW ka (add_fact S (FRange l (fst (irange (s_facts S) l)) (Z.min c (snd (irange (s_facts S) l))))) M a else Some []) as [f1|] eqn:H1; [|discriminate].
  destruct (if Z.ltb c (snd (irange (s_facts S) l)) then pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW kb (add_fact S (FRange l (Z.max (c + 1) (fst (irange (s_facts S) l))) (snd (irange (s_facts S) l)))) M a else Some []) as [f2|] eqn:H2; [|discriminate].
  injection Hck as <-. exact (Pp_range l c ka kb S M a f1 f2 model0 mem0 E ms model T IHa IHb Hwl H1 H2 Hd HX Hk).
Qed.
#[using="Type"] Lemma Pp_splitB : forall l k r0 ka kb, Pp ka -> Pp kb -> Pp (MSplitB l k r0 ka kb).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l k r0 ka kb IHa IHb S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (lwf (s_next S) l && Z.leb 0 k && Z.ltb k 64 && (Z.eqb k 0 && Z.eqb r0 0 || match lowb (s_facts S) l k with Some r => Z.eqb r r0 | None => false end))%bool eqn:Hc;
    [|discriminate].
  destruct (pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW ka (add_fact S (FMod l (k + 1) r0)) M a) as [f1|] eqn:H1; [|discriminate].
  destruct (pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW kb (add_fact S (FMod l (k + 1) (r0 + 2 ^ k))) M a) as [f2|] eqn:H2; [|discriminate].
  injection Hck as <-.
  apply andb_prop in Hc as [Hc Hlow]. apply andb_prop in Hc as [Hc Hk64]. apply andb_prop in Hc as [Hwl Hk0].
  apply Z.leb_le in Hk0. apply Z.ltb_lt in Hk64.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  assert (Hr0 : bv_unsigned (lden E l) mod 2 ^ k = r0).
  { apply orb_prop in Hlow as [Hlow|Hlow].
    - apply andb_prop in Hlow as [Hz Hr]. apply Z.eqb_eq in Hz, Hr. subst k r0. rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
    - destruct (lowb (s_facts S) l k) as [r|] eqn:Hlb; [|discriminate]. apply Z.eqb_eq in Hlow. subst r.
      exact (lowb_sound E _ l k r0 HF0 Hlb). }
  pose proof (u_range E l) as Rl.
  destruct (mod_pow_succ [] [] Hpm0 (bv_unsigned (lden E l)) k r0 ltac:(lia) Hk0 Hr0) as [Hm|Hm].
  - apply (Pp_fact ka S M a f1 _ model0 mem0 E ms model T IHa H1 Hd HX).
    + intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next S) E E' l Hwl Ha'). exact Hm.
    + intros S'' M'' a'' mem0'' E'' ms'' model'' Hin. exact (Hk S'' M'' a'' mem0'' E'' ms'' model'' (in_app_l' _ _ _ Hin)).
  - apply (Pp_fact kb S M a f2 _ model0 mem0 E ms model T IHb H2 Hd HX).
    + intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next S) E E' l Hwl Ha'). exact Hm.
    + intros S'' M'' a'' mem0'' E'' ms'' model'' Hin. exact (Hk S'' M'' a'' mem0'' E'' ms'' model'' (in_app_r' _ _ _ Hin)).
Qed.

#[using="awf_mono aeqb_eq HA_agree"] Lemma Pp_join : forall body jpc k, Pp body -> Pp k -> Pp (MJoin body jpc k).
Proof. LiaFast.lf_pins (fun (awf_mono aeqb_eq HA_agree : LiaFast.U) => LiaFast.u0).
  intros body jpc k IHb IHk S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW body S M a) as [fb|] eqn:Hb; [|discriminate].
  set (J := List.filter (fun '(F, _, _) => Z.eqb (s_pc F) jpc) fb) in *.
  set (O := List.filter (fun '(F, _, _) => negb (Z.eqb (s_pc F) jpc)) fb) in *.
  assert (HinO : forall F MF aF, In (F, MF, aF) fb -> Z.eqb (s_pc F) jpc = false -> In (F, MF, aF) O).
  { intros F MF aF Hin Hpc. unfold O. apply filter_In. split; [exact Hin|]. rewrite Hpc. reflexivity. }
  assert (HinJ : forall F MF aF, In (F, MF, aF) fb -> Z.eqb (s_pc F) jpc = true -> In (F, MF, aF) J).
  { intros F MF aF Hin Hpc. unfold J. apply filter_In. split; [exact Hin|]. exact Hpc. }
  destruct J as [|[[F0 M0] a0] Jr] eqn:HJ.
  - injection Hck as <-.
    apply (IHb S M a fb Hb model0 mem0 E ms model T Hd HX).
    intros F MF aF mem0F EF msF modelF Hin HdF HXF HaF HcF HfF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc; [destruct (HinJ F MF aF Hin Hpc)|].
    exact (Hk F MF aF mem0F EF msF modelF (HinO F MF aF Hin Hpc) HdF HXF HaF HcF HfF).
  - set (n0 := max_next (List.map (fun '(F, _, _) => F) Jr) (s_next F0)) in *.
    set (P := fst (gen2 F0 (List.map (fun '(F, _, _) => F) Jr))) in *.
    destruct (forallb (fun '(F, MF, aF) => ent_ok n0 F P MF && Pos.leb (s_next F) n0 && sm_eqb MF M0 && aeqb aF a0) ((F0, M0, a0) :: Jr) &&
              Pos.leb (s_next S) n0 && awf n0 a0)%bool eqn:Hc; [|discriminate].
    destruct (pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW k P M0 a0) as [fk|] eqn:Hk0; [|discriminate].
    injection Hck as <-.
    apply andb_prop in Hc as [Hc Hwa0]. apply andb_prop in Hc as [Hall Hsn]. apply Pos.leb_le in Hsn.
    rewrite forallb_forall in Hall.
    apply (IHb S M a fb Hb model0 mem0 E ms model T Hd HX).
    intros F MF aF mem0F EF msF modelF Hin HdF HXF HaF HcF HfF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc.
    + pose proof (Hall _ (HinJ F MF aF Hin Hpc)) as Hq. cbv beta in Hq.
      apply andb_prop in Hq as [Hq Hae]. apply andb_prop in Hq as [Hq Hsm]. apply andb_prop in Hq as [Hok HnF].
      apply Pos.leb_le in HnF. apply sm_eqb_eq in Hsm. apply aeqb_eq in Hae. subst MF aF.
      destruct (ent_ok_parts _ _ _ _ Hok) as (Hpf & Hwf0 & Hn1).
      destruct (den_weaken segs LIMIT model0 mem0F EF F P M0 msF modelF n0 HdF Hok) as [HdP HaP].
      assert (HXP : PHAX (ecomp EF (match_st F P)) P M0 a0 mem0F)
        by exact (conj (awf_mono _ _ a0 Hn1 Hwa0) (HA_agree n0 EF _ M0 a0 mem0F Hwf0 Hwa0 HaP (proj2 HXF))).
      apply (IHk P M0 a0 fk Hk0 model0 mem0F _ msF modelF T HdP HXP).
      intros S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' HX'' Ha'' Hc'' Hf''.
      assert (HcP : frz_covs EF M0 (ecomp EF (match_st F P)) M0) by exact (frz_covs_agree n0 EF _ M0 M0 Hwf0 HaP eq_refl).
      apply (Hk S'' M'' a'' mem0'' E'' ms'' model'' (in_app_l' _ _ _ Hin'') Hd'' HX'').
      * apply (agree_trans _ E EF E'' HaF). apply (agree_trans _ EF (ecomp EF (match_st F P)) E'').
        -- exact (agree_mono (s_next S) n0 EF _ Hsn HaP).
        -- exact (agree_mono (s_next S) (s_next P) _ E'' ltac:(lia) Ha'').
      * exact (frz_covs_trans E M EF M0 E'' M'' HcF (frz_covs_trans EF M0 _ M0 E'' M'' HcP Hc'')).
      * exact (frz_same_trans E M EF M0 mem0 mem0F mem0'' HfF HcF
                 (frz_same_trans EF M0 _ M0 mem0F mem0F mem0'' (frz_same_refl _ _ _) HcP Hf'')).
    + exact (Hk F MF aF mem0F EF msF modelF (in_app_r' _ _ _ (HinO F MF aF Hin Hpc)) HdF HXF HaF HcF HfF).
Qed.

#[using="awf_mono aeqb_eq HA_msub"] Lemma Pp_joinL : forall body jpc k, Pp body -> Pp k -> Pp (MJoinL body jpc k).
Proof. LiaFast.lf_pins (fun (awf_mono aeqb_eq HA_msub : LiaFast.U) => LiaFast.u0).
  intros body jpc k IHb IHk S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW body S M a) as [fb|] eqn:Hb; [|discriminate].
  set (J := List.filter (fun '(F, _, _) => Z.eqb (s_pc F) jpc) fb) in *.
  set (O := List.filter (fun '(F, _, _) => negb (Z.eqb (s_pc F) jpc)) fb) in *.
  assert (HinO : forall F MF aF, In (F, MF, aF) fb -> Z.eqb (s_pc F) jpc = false -> In (F, MF, aF) O).
  { intros F MF aF Hin Hpc. unfold O. apply filter_In. split; [exact Hin|]. rewrite Hpc. reflexivity. }
  assert (HinJ : forall F MF aF, In (F, MF, aF) fb -> Z.eqb (s_pc F) jpc = true -> In (F, MF, aF) J).
  { intros F MF aF Hin Hpc. unfold J. apply filter_In. split; [exact Hin|]. exact Hpc. }
  destruct J as [|[[F0 M0] a0] Jr] eqn:HJ.
  - injection Hck as <-.
    apply (IHb S M a fb Hb model0 mem0 E ms model T Hd HX).
    intros F MF aF mem0F EF msF modelF Hin HdF HXF HaF HcF HfF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc; [destruct (HinJ F MF aF Hin Hpc)|].
    exact (Hk F MF aF mem0F EF msF modelF (HinO F MF aF Hin Hpc) HdF HXF HaF HcF HfF).
  - set (n0 := max_next (List.map (fun '(F, _, _) => F) Jr) (s_next F0)) in *.
    destruct (genL (List.map (fun '(F, MF, _) => (F, MF)) ((F0, M0, a0) :: Jr))) as [[P MP]|] eqn:Hg; [|discriminate].
    destruct (forallb (fun '(F, MF, aF) => let σ := matchL F MF P MP in
                 entails F P σ && fixed_below σ n0 && Pos.leb (s_next F) n0 &&
                 sm_eqbm σ MP MF && aeqb (asub σ a0) aF) ((F0, M0, a0) :: Jr) &&
              state_wf P && sm_wf (s_next P) MP && Pos.leb n0 (s_next P) && agok MP a0 &&
              Pos.leb (s_next S) n0 && awf n0 a0)%bool eqn:Hc; [|discriminate].
    destruct (pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW k P MP a0) as [fk|] eqn:Hk0; [|discriminate].
    injection Hck as <-.
    apply andb_prop in Hc as [Hc Hwa0]. apply andb_prop in Hc as [Hc Hsn]. apply andb_prop in Hc as [Hc Hagk].
    apply andb_prop in Hc as [Hc HnP]. apply andb_prop in Hc as [Hc HmwP]. apply andb_prop in Hc as [Hall HswP].
    apply Pos.leb_le in Hsn. apply Pos.leb_le in HnP.
    rewrite forallb_forall in Hall.
    apply (IHb S M a fb Hb model0 mem0 E ms model T Hd HX).
    intros F MF aF mem0F EF msF modelF Hin HdF HXF HaF HcF HfF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc.
    + pose proof (Hall _ (HinJ F MF aF Hin Hpc)) as Hq. cbv beta zeta in Hq.
      set (σ := matchL F MF P MP) in *.
      apply andb_prop in Hq as [Hq Hae]. apply andb_prop in Hq as [Hq Hsm]. apply andb_prop in Hq as [Hq HnF].
      apply andb_prop in Hq as [Hent Hpf]. apply Pos.leb_le in HnF. rewrite fixed_below_eq in Hpf.
      apply sm_eqbm_eq in Hsm as [Hsm Hmk]. apply aeqb_eq in Hae. rewrite <- Hsm in HdF, HXF, HcF. rewrite <- Hae in HXF.
      pose proof (den_ent_M segs LIMIT model0 mem0F EF F P MP msF modelF σ HdF Hent HswP HmwP Hmk) as HdP.
      assert (HaP : agree n0 EF (ecomp EF σ)) by exact (agree_params n0 EF σ Hpf).
      assert (HXP : PHAX (ecomp EF σ) P MP a0 mem0F)
        by exact (conj (awf_mono _ _ a0 HnP Hwa0) (HA_msub EF σ MP a0 mem0F Hagk (proj2 HXF))).
      apply (IHk P MP a0 fk Hk0 model0 mem0F _ msF modelF T HdP HXP).
      intros S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' HX'' Ha'' Hc'' Hf''.
      pose proof (frz_covs_msubst EF σ MP) as HcP.
      apply (Hk S'' M'' a'' mem0'' E'' ms'' model'' (in_app_l' _ _ _ Hin'') Hd'' HX'').
      * apply (agree_trans _ E EF E'' HaF). apply (agree_trans _ EF (ecomp EF σ) E'').
        -- exact (agree_mono (s_next S) n0 EF _ Hsn HaP).
        -- exact (agree_mono (s_next S) (s_next P) _ E'' ltac:(lia) Ha'').
      * exact (frz_covs_trans E M EF (msubst σ MP) E'' M'' HcF (frz_covs_trans EF (msubst σ MP) _ MP E'' M'' HcP Hc'')).
      * exact (frz_same_trans E M EF (msubst σ MP) mem0 mem0F mem0'' HfF HcF
                 (frz_same_msubst EF σ MP mem0F mem0''
                    (frz_same_trans (ecomp EF σ) MP (ecomp EF σ) MP mem0F mem0F mem0'' (frz_same_refl _ _ _)
                       (frz_covs_agree (s_next P) _ _ MP MP HmwP (agree_refl _ _) eq_refl) Hf''))).
    + exact (Hk F MF aF mem0F EF msF modelF (in_app_r' _ _ _ (HinO F MF aF Hin Hpc)) HdF HXF HaF HcF HfF).
Qed.

(* [comment removed for export] *)
#[using="aeqb_eq HA_msub"] Lemma Pp_joinG : forall gen body jpc k, Pp body -> Pp k -> Pp (MJoinG gen body jpc k).
Proof. LiaFast.lf_pins (fun (aeqb_eq HA_msub : LiaFast.U) => LiaFast.u0).
  intros gen body jpc k IHb IHk S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW body S M a) as [fb|] eqn:Hb; [|discriminate].
  set (J := List.filter (fun '(F, _, _) => Z.eqb (s_pc F) jpc) fb) in *.
  set (O := List.filter (fun '(F, _, _) => negb (Z.eqb (s_pc F) jpc)) fb) in *.
  assert (HinO : forall F MF aF, In (F, MF, aF) fb -> Z.eqb (s_pc F) jpc = false -> In (F, MF, aF) O).
  { intros F MF aF Hin Hpc. unfold O. apply filter_In. split; [exact Hin|]. rewrite Hpc. reflexivity. }
  assert (HinJ : forall F MF aF, In (F, MF, aF) fb -> Z.eqb (s_pc F) jpc = true -> In (F, MF, aF) J).
  { intros F MF aF Hin Hpc. unfold J. apply filter_In. split; [exact Hin|]. exact Hpc. }
  destruct J as [|[[F0 M0] a0] Jr] eqn:HJ.
  - injection Hck as <-.
    apply (IHb S M a fb Hb model0 mem0 E ms model T Hd HX).
    intros F MF aF mem0F EF msF modelF Hin HdF HXF HaF HcF HfF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc; [destruct (HinJ F MF aF Hin Hpc)|].
    exact (Hk F MF aF mem0F EF msF modelF (HinO F MF aF Hin Hpc) HdF HXF HaF HcF HfF).
  - set (n0 := max_next (List.map (fun '(F, _, _) => F) Jr) (s_next F0)) in *.
    destruct (gen (List.map (fun '(F, MF, _) => (F, MF)) ((F0, M0, a0) :: Jr)) (List.map (fun '(_, _, aF) => alins aF) ((F0, M0, a0) :: Jr))) as [[[P MP] als]|] eqn:Hg; [|discriminate].
    set (aP := aset a0 als) in *.
    destruct (forallb (fun '(F, MF, aF) => let σ := matchLA F MF (alins aF) P MP (alins aP) in
                 entails F P σ && fixed_below σ n0 && Pos.leb (s_next F) n0 &&
                 sm_eqbm σ MP MF && aeqb (asub σ aP) aF) ((F0, M0, a0) :: Jr) &&
              state_wf P && sm_wf (s_next P) MP && Pos.leb n0 (s_next P) && agok MP aP &&
              Pos.leb (s_next S) n0 && awf (s_next P) aP)%bool eqn:Hc; [|discriminate].
    destruct (pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW k P MP aP) as [fk|] eqn:Hk0; [|discriminate].
    injection Hck as <-.
    apply andb_prop in Hc as [Hc Hwa0]. apply andb_prop in Hc as [Hc Hsn]. apply andb_prop in Hc as [Hc Hagk].
    apply andb_prop in Hc as [Hc HnP]. apply andb_prop in Hc as [Hc HmwP]. apply andb_prop in Hc as [Hall HswP].
    apply Pos.leb_le in Hsn. apply Pos.leb_le in HnP.
    rewrite forallb_forall in Hall.
    apply (IHb S M a fb Hb model0 mem0 E ms model T Hd HX).
    intros F MF aF mem0F EF msF modelF Hin HdF HXF HaF HcF HfF.
    destruct (Z.eqb (s_pc F) jpc) eqn:Hpc.
    + pose proof (Hall _ (HinJ F MF aF Hin Hpc)) as Hq. cbv beta iota zeta in Hq.
      remember (matchLA F MF (alins aF) P MP (alins aP)) as σ eqn:Hσ in *. clear Hσ.
      apply andb_prop in Hq as [Hq Hae]. apply andb_prop in Hq as [Hq Hsm]. apply andb_prop in Hq as [Hq HnF].
      apply andb_prop in Hq as [Hent Hpf]. apply Pos.leb_le in HnF. rewrite fixed_below_eq in Hpf.
      apply sm_eqbm_eq in Hsm as [Hsm Hmk]. apply aeqb_eq in Hae. rewrite <- Hsm in HdF, HXF, HcF. rewrite <- Hae in HXF.
      pose proof (den_ent_M segs LIMIT model0 mem0F EF F P MP msF modelF σ HdF Hent HswP HmwP Hmk) as HdP.
      assert (HaP : agree n0 EF (ecomp EF σ)) by exact (agree_params n0 EF σ Hpf).
      assert (HXP : PHAX (ecomp EF σ) P MP aP mem0F)
        by exact (conj Hwa0 (HA_msub EF σ MP aP mem0F Hagk (proj2 HXF))).
      apply (IHk P MP aP fk Hk0 model0 mem0F _ msF modelF T HdP HXP).
      intros S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' HX'' Ha'' Hc'' Hf''.
      pose proof (frz_covs_msubst EF σ MP) as HcP.
      apply (Hk S'' M'' a'' mem0'' E'' ms'' model'' (in_app_l' _ _ _ Hin'') Hd'' HX'').
      * apply (agree_trans _ E EF E'' HaF). apply (agree_trans _ EF (ecomp EF σ) E'').
        -- exact (agree_mono (s_next S) n0 EF _ Hsn HaP).
        -- exact (agree_mono (s_next S) (s_next P) _ E'' ltac:(lia) Ha'').
      * exact (frz_covs_trans E M EF (msubst σ MP) E'' M'' HcF (frz_covs_trans EF (msubst σ MP) _ MP E'' M'' HcP Hc'')).
      * exact (frz_same_trans E M EF (msubst σ MP) mem0 mem0F mem0'' HfF HcF
                 (frz_same_msubst EF σ MP mem0F mem0''
                    (frz_same_trans (ecomp EF σ) MP (ecomp EF σ) MP mem0F mem0F mem0'' (frz_same_refl _ _ _)
                       (frz_covs_agree (s_next P) _ _ MP MP HmwP (agree_refl _ _) eq_refl) Hf''))).
    + exact (Hk F MF aF mem0F EF msF modelF (in_app_r' _ _ _ (HinO F MF aF Hin Hpc)) HdF HXF HaF HcF HfF).
Qed.

#[using="awf_mono aeqb_eq HA_agree"] Lemma Pp_loopG : forall gen body ks, Pp body -> Qp ks -> Pp (MLoopG gen body ks).
Proof. LiaFast.lf_pins (fun (awf_mono aeqb_eq HA_agree : LiaFast.U) => LiaFast.u0).
  intros gen body ks IHb IHk S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW body S M a) as [fb1|]; [|discriminate].
  destruct (List.find (fun '(F, _, _) => Z.eqb (s_pc F) (s_pc S)) fb1) as [[[F1 M1] a1]|]; [|discriminate].
  destruct (gen S F1 PFS PFS PSH PSH) as [[[[[P n0] FP] shP] meas]|]; [|discriminate].
  destruct (ent_ok n0 S P M && Pos.leb (s_next S) n0 && lwf (s_next P) meas && meas_ok (s_facts P) meas && awf n0 a)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hwa0]. apply andb_prop in Hb as [Hb Hmf]. apply andb_prop in Hb as [Hb Hwm]. apply andb_prop in Hb as [Hok Hn].
  apply Pos.leb_le in Hn.
  destruct (pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW body P M a) as [fb|] eqn:Hbody; [|discriminate].
  destruct (ent_ok_parts _ _ _ _ Hok) as (Hpf & Hwf0 & Hn1).
  assert (HwfS : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  assert (HQ : forall (v : nat) EP msP modelP mem0P, agree n0 E EP -> DEN segs LIMIT model0 mem0P EP P M msP modelP ->
             PHAX EP P M a mem0P -> frz_same E M mem0 mem0P -> (Z.to_nat (bv_unsigned (lden EP meas)) <= v)%nat ->
             realizes_cfg segs cfg (mkCfg msP modelP) T).
  { intros v. induction v as [|v IHv]; intros EP msP modelP mem0P HaP HdP HxP HfP Hv.
    all: apply (IHb P M a fb Hbody model0 mem0P EP msP modelP T HdP HxP).
    all: intros F MF aF mem0F EF msF modelF HinF HdF HxF HaF HcF HfF.
    all: destruct (all_some_spec _ _ _ Hck (F, MF, aF) HinF) as (o & Ho & Hsub); cbv beta in Ho.
    all: assert (HcP : frz_covs E M EP M) by exact (frz_covs_agree (s_next S) E EP M M HwfS (agree_mono _ _ E EP Hn HaP) eq_refl).
    all: destruct (Z.eqb (s_pc F) (s_pc P)) eqn:Hpc.
    all: try (destruct (Pos.leb n0 (s_next F)) eqn:Hnf; [|discriminate]; apply Pos.leb_le in Hnf;
              apply (IHk F MF aF o Ho model0 mem0F EF msF modelF T HdF HxF);
              intros S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' Hx'' Ha'' Hc'' Hf'';
              apply (Hk S'' M'' a'' mem0'' E'' ms'' model'' (Hsub _ Hin'') Hd'' Hx'');
              [ apply (agree_trans _ E EP E''); [exact (agree_mono _ _ E EP Hn HaP)|];
                apply (agree_trans _ EP EF E''); [exact (agree_mono (s_next S) (s_next P) EP EF ltac:(lia) HaF)|];
                exact (agree_mono (s_next S) (s_next F) EF E'' ltac:(lia) Ha'')
              | exact (frz_covs_trans E M EP M E'' M'' HcP (frz_covs_trans EP M EF MF E'' M'' HcF Hc''))
              | exact (frz_same_trans E M EP M mem0 mem0P mem0'' HfP HcP (frz_same_trans EP M EF MF mem0P mem0F mem0'' HfF HcF Hf'')) ]).
    all: destruct (ent_ok n0 F P MF && sm_eqb MF M && aeqb aF a && lmeas_dec F (match_st F P) meas)%bool eqn:Hbe; [|discriminate].
    all: apply andb_prop in Hbe as [Hbe Hmd]; apply andb_prop in Hbe as [Hbe Hae]; apply andb_prop in Hbe as [Hok' Hsm];
         apply sm_eqb_eq in Hsm; subst MF; apply aeqb_eq in Hae; subst aF.
    all: destruct (ent_ok_parts _ _ _ _ Hok') as (Hpf' & _ & Hn1').
    all: destruct (den_weaken segs LIMIT model0 mem0F EF F P M msF modelF n0 HdF Hok') as [HdP' HaP'].
    all: assert (HxP' : PHAX (ecomp EF (match_st F P)) P M a mem0F)
           by exact (conj (awf_mono _ _ a Hn1' Hwa0) (HA_agree n0 EF _ M a mem0F Hwf0 Hwa0 HaP' (proj2 HxF))).
    all: destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HdF)) as (_ & _ & _ & _ & _ & _ & HFF & _).
    all: destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HdP)) as (_ & _ & _ & _ & _ & _ & HFP & _).
    all: destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HdP')) as (_ & _ & _ & _ & _ & _ & HFP' & _).
    all: pose proof (meas_ok_sound [] [] Hpm0 _ _ _ HFP Hmf) as Mv; pose proof (meas_ok_sound [] [] Hpm0 _ _ _ HFP' Hmf) as Mv'.
    all: assert (HmE : lden EF meas = lden EP meas) by exact (lden_agree_wf _ EP EF meas Hwm HaF).
    all: pose proof (lmeas_dec_sound [] [] Hpm0 EF F (match_st F P) meas HFF Hmd ltac:(rewrite HmE; lia) ltac:(lia)) as Hlt; rewrite HmE in Hlt.
    - exfalso. lia.
    - apply (IHv (ecomp EF (match_st F P)) msF modelF mem0F); [| exact HdP' | exact HxP' | | lia].
      + apply (agree_trans _ E EP _ HaP). apply (agree_trans _ EP EF _).
        * exact (agree_mono n0 (s_next P) EP EF Hn1 HaF).
        * exact HaP'.
      + exact (frz_same_trans E M EP M mem0 mem0P mem0F HfP HcP HfF). }
  destruct (den_weaken segs LIMIT model0 mem0 E S P M ms model n0 Hd Hok) as [Hd0 Ha0].
  assert (HX0 : PHAX (ecomp E (match_st S P)) P M a mem0) by exact (conj (awf_mono _ _ a Hn1 Hwa0) (HA_agree n0 E _ M a mem0 Hwf0 Hwa0 Ha0 (proj2 HX))).
  exact (HQ _ _ ms model mem0 Ha0 Hd0 HX0 (frz_same_refl _ _ _) (Nat.le_refl _)).
Qed.

#[using="awf_mono HA_agree"] Lemma Pp_weaken : forall P n0 FP shP k, Pp k -> Pp (MWeaken P n0 FP shP k).
Proof. LiaFast.lf_pins (fun (awf_mono HA_agree : LiaFast.U) => LiaFast.u0).
  intros P n0 FP shP k IH S M a finals Hck model0 mem0 E ms model T Hd HX Hk. cbn [pchecku] in Hck.
  destruct (ent_ok n0 S P M && Pos.leb (s_next S) n0 && awf n0 a)%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hwa0]. apply andb_prop in Hb as [Hok Hn]. apply Pos.leb_le in Hn.
  destruct (ent_ok_parts _ _ _ _ Hok) as (Hpf & Hwf0 & Hn1).
  assert (HwfS : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  destruct (den_weaken segs LIMIT model0 mem0 E S P M ms model n0 Hd Hok) as [Hd0 Ha0].
  assert (HX0 : PHAX (ecomp E (match_st S P)) P M a mem0) by exact (conj (awf_mono _ _ a Hn1 Hwa0) (HA_agree n0 E _ M a mem0 Hwf0 Hwa0 Ha0 (proj2 HX))).
  assert (HaE : agree (s_next S) E (ecomp E (match_st S P))) by exact (agree_mono _ _ E _ Hn Ha0).
  assert (HcE : frz_covs E M (ecomp E (match_st S P)) M) by exact (frz_covs_agree (s_next S) E _ M M HwfS HaE eq_refl).
  apply (IH P M a finals Hck model0 mem0 _ ms model T Hd0 HX0).
  intros S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' Hx'' Ha'' Hc'' Hf''.
  apply (Hk S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' Hx'').
  - apply (agree_trans _ E (ecomp E (match_st S P)) E'' HaE). exact (agree_mono (s_next S) (s_next P) _ E'' ltac:(lia) Ha'').
  - exact (frz_covs_trans E M _ M E'' M'' HcE Hc'').
  - exact (frz_same_trans E M _ M mem0 mem0 mem0'' (frz_same_refl _ _ _) HcE Hf'').
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma keep_fact_wf : forall nb n f, keep_fact nb n f = true -> fwf n f = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros nb n f H. destruct f as [c a b tk|l lo hi|l k r|l m v|x v j|x bs]; try discriminate; cbn [keep_fact] in H;
  apply andb_prop in H as [H _]; exact H.
Qed.

(* [comment removed for export] *)
#[using="aeqb_eq HA_agree HA_msub HMUse HA_use"] Lemma Pp_use : forall j nb k, Pp k -> Pp (MUse j nb k).
Proof. LiaFast.lf_pins (fun (aeqb_eq HA_agree HA_msub HMUse HA_use : LiaFast.U) => LiaFast.u0).
  intros j nb k IH S M a finals Hck model0 mem0 E ms model Tg Hd HX Hk. cbn [pchecku] in Hck.
  destruct (nth_error subs j) as [[[[T MT] aT] fins]|] eqn:Hj; [|discriminate].
  set (σ := psr_ext S T (matchLA S M (alins a) T MT (alins aT))) in *.
  destruct (entails S T σ && state_wf T && sm_wf (s_next T) MT && agok MT aT && sm_eqbm σ MT M && aeqb (asub σ aT) a &&
            Pos.leb nb (s_next T) && Pos.leb nb (s_next S) && fixed_below σ nb && use_bwf σ nb (s_next T) (s_next S) &&
            awf (s_next T) aT)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc HawT]. apply andb_prop in Hc as [Hc Hbw]. apply andb_prop in Hc as [Hc Hpf]. rewrite fixed_below_eq in Hpf. apply andb_prop in Hc as [Hc HnbS].
  apply andb_prop in Hc as [Hc HnbT]. apply andb_prop in Hc as [Hc Hae]. apply andb_prop in Hc as [Hc Hsm]. apply andb_prop in Hc as [Hc Hagk].
  apply andb_prop in Hc as [Hc HmwT]. apply andb_prop in Hc as [Hent HwT].
  apply Pos.leb_le in HnbS, HnbT. apply sm_eqbm_eq in Hsm as [Hsm Hmk]. apply aeqb_eq in Hae.
  pose proof (use_bwf_spec σ nb (s_next T) (s_next S) Hbw) as Hbw'.
  assert (Hsubs : subs <> []) by (intros H; rewrite H in Hj; destruct j; discriminate).
  assert (Hd0 : DEN segs LIMIT model0 mem0 E S (msubst σ MT) ms model) by (rewrite Hsm; exact Hd).
  pose proof (den_ent_M segs LIMIT model0 mem0 E S T MT ms model σ Hd0 Hent HwT HmwT Hmk) as HdT.
  assert (HAT : HA (ecomp E σ) MT aT mem0).
  { apply (HA_msub E σ MT aT mem0 Hagk). rewrite Hsm, Hae. exact (proj2 HX). }
  apply (HMUse j T MT aT fins Hj model0 mem0 (ecomp E σ) ms model _ HdT HawT HAT).
  intros F MF aF mem0' E' ms' model' Hin HdF HawF HAF Ha' Hcov' Hfs'.
  destruct (all_some_spec _ _ _ Hck (F, MF, aF) Hin) as (o & Ho & Hsub'). cbv beta zeta in Ho.
  set (σ' := use_sig σ nb (s_next T) (s_next F) (s_next S)) in *.
  set (nx := use_next nb (s_next F) (s_next S)) in *.
  destruct (Pos.leb (s_next T) (s_next F) && awf nx (asub σ' aF) && marks_ok σ' (sm_maps MF))%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb Hmk']. apply andb_prop in Hb as [HTF Hwa'']. apply Pos.leb_le in HTF.
  set (E2 := use_env E E' nb (s_next S)).
  assert (He2 : forall x, (x < s_next F)%positive -> lden E2 (svar σ' x) = E' x)
    by (intros x Hx; exact (use_sig_ecomp E E' σ nb (s_next T) (s_next F) (s_next S) x HnbT HnbS HTF Hpf Hbw' Ha' Hx)).
  assert (Hag2 : agree (s_next F) E' (ecomp E2 σ')) by (intros x Hx; unfold ecomp; symmetry; exact (He2 x Hx)).
  assert (Hsw : sig_wf σ' (s_next F) nx) by exact (use_sig_wf σ nb (s_next T) (s_next F) (s_next S) HnbS ltac:(lia) Hbw').
  pose proof (den_agree segs LIMIT model0 mem0' E' (ecomp E2 σ') F MF ms' model' HdF Hag2) as HdF2.
  pose proof (den_subst segs LIMIT model0 mem0' E2 σ' F MF nx ms' model' Hsw Hmk' HdF2) as HdS.
  assert (HnS : (s_next S <= nx)%positive) by exact (use_next_ge nb (s_next F) (s_next S) ltac:(lia)).
  assert (HaE2 : agree (s_next S) E E2) by exact (use_env_agree E E' nb (s_next S)).
  assert (HwfF : sm_wf (s_next F) MF = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ HdF).
  assert (Hcov2 : frz_covs E M E2 (msubst σ' MF)).
  { rewrite <- Hsm. apply (frz_covs_trans E (msubst σ MT) (ecomp E σ) MT E2 (msubst σ' MF) (frz_covs_msubst E σ MT)).
    apply (frz_covs_trans (ecomp E σ) MT E' MF E2 (msubst σ' MF) Hcov'). exact (frz_covs_inst E' E2 σ' (s_next F) MF HwfF He2). }
  assert (Hfs2 : frz_same E M mem0 mem0') by (rewrite <- Hsm; exact (frz_same_msubst_m E σ MT mem0 mem0' Hfs')).
  assert (HXS : PHAX E2 (ssubst σ' nx F) (msubst σ' MF) (asub σ' aF) mem0').
  { split; [exact Hwa''|]. apply (HA_use Hsubs E2 σ' MF aF mem0'). exact (HA_agree (s_next F) E' _ MF aF mem0' HwfF HawF Hag2 HAF). }
  assert (HdK : DEN segs LIMIT model0 mem0' E2 (use_keep nb S (ssubst σ' nx F)) (msubst σ' MF) ms' model').
  { change (use_keep nb S (ssubst σ' nx F))
      with (with_facts (ssubst σ' nx F) (s_facts (ssubst σ' nx F) ++
              List.filter (keep_sel nb (s_next S) (s_facts (ssubst σ' nx F)) (svars_tree (ssubst σ' nx F))) (s_facts S))).
    apply (den_add_facts segs LIMIT model0 mem0' E2 (ssubst σ' nx F) (msubst σ' MF) ms' model' _ HdS).
    intros E3 Ha3. rewrite Forall_forall. intros f Hf. apply filter_In in Hf as [Hf1 Hf2].
    assert (Hf2' : keep_fact nb (s_next S) f = true) by (unfold keep_sel in Hf2; destruct (keep_fact nb (s_next S) f); [reflexivity | discriminate Hf2]). clear Hf2. rename Hf2' into Hf2.
    apply (fact_ok_agree (s_next S) E E3 f (keep_fact_wf _ _ _ Hf2)).
    - exact (agree_trans _ E E2 E3 HaE2 (agree_mono (s_next S) nx E2 E3 HnS Ha3)).
    - destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _).
      rewrite Forall_forall in HF. exact (HF f Hf1). }
  assert (HXK : PHAX E2 (use_keep nb S (ssubst σ' nx F)) (msubst σ' MF) (asub σ' aF) mem0') by exact (PHAX_same _ _ _ _ _ _ HXS eq_refl).
  apply (IH (use_keep nb S (ssubst σ' nx F)) (msubst σ' MF) (asub σ' aF) o Ho model0 mem0' E2 ms' model' Tg HdK HXK).
  intros S'' M'' a'' mem0'' E'' ms'' model'' Hin'' Hd'' HX'' Ha'' Hc'' Hf''.
  apply (Hk S'' M'' a'' mem0'' E'' ms'' model'' (Hsub' _ Hin'') Hd'' HX'').
  - exact (agree_trans _ E E2 E'' HaE2 (agree_mono _ _ E2 E'' HnS Ha'')).
  - exact (frz_covs_trans E M E2 (msubst σ' MF) E'' M'' Hcov2 Hc'').
  - exact (frz_same_trans E M E2 (msubst σ' MF) mem0 mem0' mem0'' Hfs2 Hcov2 Hf'').
Qed.

#[using="Hwx Ht Himg awf_mono aeqb_eq HA_agree Hanode HA_msub HMUse HA_use HA_mod HLW"] Theorem pchain_sound_u : forall ch, Pp ch.
Proof. LiaFast.lf_pins (fun (Hwx Ht Himg awf_mono aeqb_eq HA_agree Hanode HA_msub HMUse HA_use HA_mod HLW : LiaFast.U) => LiaFast.u0).
  apply (@mchain_mut N Pp Qp);
    first [ exact Pp_end | exact Pp_void | exact Qp_nil
          | intros; first [ apply Pp_segk | apply Pp_call | apply Pp_join | apply Pp_joinL | apply Pp_joinG | apply Pp_alt | apply Pp_sep
                          | apply Pp_split | apply Pp_splitB | apply Pp_splitG | apply Pp_splitR | apply Pp_concr | apply Pp_gc | apply Pp_loopG | apply Pp_weaken | apply Pp_use | apply Pp_alloww
                          | apply Qp_cons ]; assumption
          | intros; intros S0 M0 a0 finals0 Hck0; cbn [pchecku] in Hck0; discriminate Hck0 ].
Qed.

(* [comment removed for export] *)
#[using="Hwx Ht Himg awf_mono aeqb_eq HA_agree Hanode HA_msub HMUse HA_use HA_mod HLW"] Theorem sub_ok_of_pchecku : forall ch T MT aT fins, pchecku segs t img apost aeqb awf asub agok alins aset subs amod LIMW ch T MT aT = Some fins ->
  sub_ok segs cfg LIMIT awf HA T MT aT fins.
Proof. LiaFast.lf_pins (fun (Hwx Ht Himg awf_mono aeqb_eq HA_agree Hanode HA_msub HMUse HA_use HA_mod HLW : LiaFast.U) => LiaFast.u0).
  intros ch T MT aT fins Hp model0 mem0 E ms model Tg Hd Hw Ha Hk.
  apply (pchain_sound_u ch T MT aT fins Hp model0 mem0 E ms model Tg Hd (conj Hw Ha)).
  intros S' M' a' mem0' E' ms' model' Hin Hd' [Hw' Ha'] Hag Hcov Hsame.
  exact (Hk S' M' a' mem0' E' ms' model' Hin Hd' Hw' Ha' Hag Hcov Hsame).
Qed.
End PSound.

(* [comment removed for export] *)
Section POld.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable t : tree xi.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Ht : tbl_ok segs t.
Hypothesis Himg : img_ok segs img.
Context {N A : Type}.
Variable apost : N -> sst -> smodel -> A -> option (sst * smodel * A).
Variables (aeqb : A -> A -> bool) (awf : positive -> A -> bool).
Variable HA : valu -> smodel -> A -> (word -> option byte) -> Prop.
Variable asub : tree lin -> A -> A.
Variable agok : smodel -> A -> bool.
Variable alins : A -> list lin.
Variable aset : A -> list lin -> A.
Hypothesis awf_mono : forall n n' a, (n <= n')%positive -> awf n a = true -> awf n' a = true.
Hypothesis aeqb_eq : forall x y, aeqb x y = true -> x = y.
Hypothesis HA_agree : forall n E E' M a m0, sm_wf n M = true -> awf n a = true -> agree n E E' -> HA E M a m0 -> HA E' M a m0.
Hypothesis Hanode : forall nk, anode_ok segs cfg LIMIT apost awf HA nk.
Hypothesis HA_msub : forall E σ M a m0, agok M a = true -> HA E (msubst σ M) (asub σ a) m0 -> HA (ecomp E σ) M a m0.

#[using="Type"] Lemma no_subs_use : forall j T MT aT fins, nth_error (@nil (sst * smodel * A * list (sst * smodel * A))) j = Some (T, MT, aT, fins) ->
  sub_ok segs cfg LIMIT awf HA T MT aT fins.
Proof. LiaFast.lf_pins LiaFast.u0. intros j T MT aT fins H. destruct j; discriminate H. Qed.
#[using="Type"] Lemma no_subs_HA : @nil (sst * smodel * A * list (sst * smodel * A)) <> [] ->
  forall E σ M a m0, HA (ecomp E σ) M a m0 -> HA E (msubst σ M) (asub σ a) m0.
Proof. LiaFast.lf_pins LiaFast.u0. intros H. exfalso. apply H. reflexivity. Qed.

#[using="Hwx Ht Himg awf_mono aeqb_eq HA_agree Hanode HA_msub"] Theorem sub_ok_of_pcheck : forall ch T MT aT fins, pcheck segs t img apost aeqb awf asub agok alins aset ch T MT aT = Some fins ->
  sub_ok segs cfg LIMIT awf HA T MT aT fins.
Proof. LiaFast.lf_pins (fun (Hwx Ht Himg awf_mono aeqb_eq HA_agree Hanode HA_msub : LiaFast.U) => LiaFast.u0).
  intros ch T MT aT fins Hp. unfold pcheck in Hp.
  exact (sub_ok_of_pchecku segs cfg LIMIT t img Hwx Ht Himg apost aeqb awf HA asub agok alins aset awf_mono aeqb_eq HA_agree Hanode HA_msub
           [] no_subs_use no_subs_HA (fun _ _ _ => false) (fun E M M' a m0 (H : false = true) => False_ind _ (Bool.diff_false_true H)) 0
           (or_intror (fun _ _ _ => eq_refl)) ch T MT aT fins Hp).
Qed.
End POld.
(* [comment removed for export] *)
