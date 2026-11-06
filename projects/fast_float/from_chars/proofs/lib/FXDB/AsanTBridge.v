(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxSubst FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen FxChain FxWvC FxChMain FxChEntM.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChRecont.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChAllow OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChRecont.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTbl AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanStartAll OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanFinAB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanFinEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcConvG AcSubst AcFam.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition idb17 (σ : tree lin) : bool := forallb (fun k => lin_eqb (svar σ (Pos.of_nat k)) (lvar (Pos.of_nat k))) (List.seq 1 16).
Lemma idb17_sound : forall σ E x, idb17 σ = true -> (x < 17)%positive -> ecomp E σ x = E x.
Proof.
  intros σ E x H Hx. unfold idb17 in H. rewrite forallb_forall in H.
  assert (Hin : In (Pos.to_nat x) (List.seq 1 16)) by (apply in_seq; lia).
  specialize (H _ Hin). rewrite Pos2Nat.id in H. apply lin_eqb_eq in H. unfold ecomp. rewrite H. apply lden_lvar.
Qed.

(* [comment removed for export] *)
Definition bfin (a' : ast) (S3 : sst) (M3 : smodel) : bool :=
  let σ := sig (S3, M3) TMAIN MMAIN in (entails S3 TMAIN σ && sm_eqb M3 (msubst σ MMAIN) && aeqb a' (asubst σ AMAIN) && idb17 σ && marks_ok σ (sm_maps MMAIN))%bool.
Definition bridge_ok (F : sst * smodel) : bool :=
  match apost_convG (fst F) (snd F) ast0 with
  | Some (S', M', a') =>
      let S1 := sep4 S' M' in
      if Nat.eqb (List.length (sm_allow M')) NALW then
        match List.nth_error (sm_maps M') 4, rz_track_post S1 IBSS 134833 with
        | Some g, Some S2 => match recont_post S2 IBSS 134833 0 with
                             | Some S3 => (allow_ins_ok LIM (s_next S3) M' 5 (laddc (fst (fst g)) 4096, 4096) &&
                                           bfin a' S3 (allow_ins M' 5 (laddc (fst (fst g)) 4096, 4096)))%bool
                             | None => false end
        | _, _ => false
        end
      else
        match recont_post S1 IBSS 135705 18446744073709551615 with
        | Some S2 => match recont_post S2 IBSS 134833 1 with Some S3 => bfin a' S3 M' | None => false end
        | None => false
        end
  | None => false
  end.

Lemma bridge_all : forallb bridge_ok (FINC ++ FINA ++ FINB) = true.
Proof. Time vm_compute. reflexivity. Time Qed.
Lemma TMAIN_wf : state_wf TMAIN = true. Proof. vm_compute. reflexivity. Qed.
Lemma MMAIN_wf : sm_wf (s_next TMAIN) MMAIN = true. Proof. vm_compute. reflexivity. Qed.
Lemma AMAIN_ag : ag_ok MMAIN AMAIN = true. Proof. vm_compute. reflexivity. Qed.

Strategy opaque [TMAIN MMAIN AMAIN].

Section B.
Variable cfg : SpuriousCfg.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.

(* [comment removed for export] *)
#[using="Type"] Lemma den_sep4 : forall mem0 E S M ms model, DEN ASEGS LIM model0 mem0 E S M ms model -> DEN ASEGS LIM model0 mem0 E (sep4 S M) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E S M ms model Hd. unfold sep4.
  generalize (List.seq 0 (List.length (sm_maps M))) as l. intros l. revert S Hd.
  induction l as [|j l IH]; intros S Hd; cbn [List.fold_left]; [exact Hd|].
  apply IH. destruct (Nat.eqb j 4); [exact Hd|].
  destruct (sepw_post S M 4 j) as [S'|] eqn:Hs; [|exact Hd].
  exact (den_sepw ASEGS LIM model0 mem0 E S M ms model 4 j S' Hd Hs).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bfin_ok : forall mem0 E S3 M3 a' ms model T, bfin a' S3 M3 = true ->
  DEN ASEGS LIM model0 mem0 E S3 M3 ms model -> HA E M3 a' mem0 ->
  (forall E'', (forall x, (x < 17)%positive -> E'' x = E x) -> DEN ASEGS LIM model0 mem0 E'' TMAIN MMAIN ms model -> HA E'' MMAIN AMAIN mem0 ->
     realizes_cfg ASEGS cfg (mkCfg ms model) T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E S3 M3 a' ms model T Hb Hd HHA Hk. unfold bfin in Hb.
  set (σ := sig (S3, M3) TMAIN MMAIN) in *.
  apply andb_prop in Hb as [Hb Hmk]. apply andb_prop in Hb as [Hb Hid]. apply andb_prop in Hb as [Hb Ha]. apply andb_prop in Hb as [Hent Hm].
  apply sm_eqb_eq in Hm. apply aeqb_eq in Ha.
  rewrite Hm in Hd, HHA. rewrite Ha in HHA.
  apply (Hk (ecomp E σ)).
  - intros x Hx. exact (idb17_sound σ E x Hid Hx).
  - exact (den_ent_M ASEGS LIM model0 mem0 E S3 TMAIN MMAIN ms model σ Hd Hent TMAIN_wf MMAIN_wf Hmk).
  - exact (HA_subst E σ MMAIN AMAIN mem0 AMAIN_ag HHA).
Qed.

#[using="Type"] Theorem tm_handoff : forall F, bridge_ok F = true -> forall mem0 E ms model T,
  DEN ASEGS LIM model0 mem0 E (fst F) (snd F) ms model -> (17 <= s_next (fst F))%positive ->
  (forall E'' mem0' ms' model', agree 17 E E'' -> frz_same E (snd F) mem0 mem0' ->
     DEN ASEGS LIM model0 mem0' E'' TMAIN MMAIN ms' model' -> HA E'' MMAIN AMAIN mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros F Hb mem0 E ms model T Hd H17 Hk. unfold bridge_ok in Hb.
  destruct (apost_convG (fst F) (snd F) ast0) as [[[S' M'] a']|] eqn:Hc; [|discriminate].
  apply (convG_node cfg LIM model0 (fst F) (snd F) ast0 S' M' a' Hc mem0 E ms model T Hd ltac:(vm_compute; reflexivity) (HA_nil E (snd F) ast0 mem0 eq_refl)).
  intros E' mem0' ms' model' Ha Hfs Hd' HHA'.
  pose proof (den_sep4 mem0' E' S' M' ms' model' Hd') as Hd1.
  (* [comment removed for export] *)
  assert (Kont : forall E'', (forall x, (x < 17)%positive -> E'' x = E' x) -> DEN ASEGS LIM model0 mem0' E'' TMAIN MMAIN ms' model' ->
                   HA E'' MMAIN AMAIN mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T).
  { intros E'' Hid Hd'' HHA''. apply (Hk E'' mem0' ms' model'); [| exact Hfs | exact Hd'' | exact HHA''].
    intros x Hx. rewrite (Hid x Hx). apply Ha. lia. }
  destruct (Nat.eqb (List.length (sm_allow M')) NALW).
  - destruct (List.nth_error (sm_maps M') 4) as [g|]; [|discriminate].
    destruct (rz_track_post (sep4 S' M') IBSS 134833) as [S2|] eqn:H2; [|discriminate].
    destruct (recont_post S2 IBSS 134833 0) as [S3|] eqn:H3; [|discriminate].
    apply andb_prop in Hb as [Hal Hb].
    pose proof (den_rz_track ASEGS LIM mem0' model0 E' (sep4 S' M') M' ms' model' IBSS 134833 S2 Hd1 H2) as Hd2.
    pose proof (den_recont ASEGS LIM mem0' model0 E' S2 M' ms' model' IBSS 134833 0 S3 Hd2 H3) as Hd3.
    pose proof (den_allow_ins ASEGS LIM model0 mem0' E' S3 M' ms' model' 5 _ Hd3 Hal) as Hd4.
    apply (bfin_ok mem0' E' S3 _ a' ms' model' T Hb Hd4); [|exact Kont].
    apply (HA_ext E' M' _ a' mem0' mem0'); [apply incl_refl | apply incl_refl | intros x Hx; exact Hx | intros x _ _; reflexivity | intros _ x _; reflexivity | exact HHA'].
  - destruct (recont_post (sep4 S' M') IBSS 135705 18446744073709551615) as [S2|] eqn:H2; [|discriminate].
    destruct (recont_post S2 IBSS 134833 1) as [S3|] eqn:H3; [|discriminate].
    pose proof (den_recont ASEGS LIM mem0' model0 E' (sep4 S' M') M' ms' model' IBSS 135705 18446744073709551615 S2 Hd1 H2) as Hd2.
    pose proof (den_recont ASEGS LIM mem0' model0 E' S2 M' ms' model' IBSS 134833 1 S3 Hd2 H3) as Hd3.
    exact (bfin_ok mem0' E' S3 M' a' ms' model' T Hb Hd3 HHA' Kont).
Qed.
End B.
(* [comment removed for export] *)
