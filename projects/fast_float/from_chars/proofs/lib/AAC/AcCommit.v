(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMALlib AcConv AcDenW AcHA AcOwnSet.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFixXS.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFixNew.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFixXS AcSysK.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcOwnSet OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFixXS.AcFixX OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFixNew.AcFixS OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFixXS OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSysK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma set_kind_same : forall j k gs g, nth_error gs j = Some g -> snd g = k -> set_kind j k gs = gs.
Proof.
  induction j as [|j IH]; intros k [|g0 r] g Hj Hk; cbn in Hj; try discriminate; cbn [set_kind].
  - injection Hj as ->. rewrite <- Hk. destruct g as [p kk]. reflexivity.
  - f_equal. exact (IH k r g Hj Hk).
Qed.
Lemma fix_M_same : forall M j k g, nth_error (sm_maps M) j = Some g -> snd g = k -> fix_M M j k = M.
Proof. intros M j k g Hj Hk. unfold fix_M. rewrite (set_kind_same j k _ g Hj Hk). destruct M; reflexivity. Qed.

(* [comment removed for export] *)
Definition mem0_z (m0 : word -> option byte) (a n : Z) : word -> option byte :=
  fun w => if (Z.leb a (bv_unsigned w) && Z.ltb (bv_unsigned w) (a + n))%bool then Some (Z_to_bv 8 0) else m0 w.

Section Commit.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem den_commit_own : forall mem0 L E M ms model T adl jP gP,
  DEN ASEGS LIMIT model0 mem0 E L M ms model ->
  s_pc L = 0x73c44 -> rget (s_regs L) (rkey a0r) = adl ->
  fixkeep_ok_s LIMIT ASEGSR L M 262144 false jP GE = true ->
  nth_error (sm_maps M) jP = Some gP -> snd gP = GE ->
  (forall fl, arg L 3 = Some fl -> mmap_noreserve_b (Z_to_bv 64 fl) = false) ->
  fx_len E L = 262144 -> uE E adl + 262144 <= 2^47 ->
  (forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E adl <= w < uE E adl + 262144)) ->
  (forall w, own_pt E M w -> ~ (uE E adl <= bv_unsigned (Z_to_bv 64 w) < uE E adl + 262144)) ->
  (forall w, frz_pt E M w -> ~ (uE E adl <= w < uE E adl + 262144)) ->
  (forall ms' model', ms' = advance_past_svc (apply_effect (svc_set ms) (fresh_eff false (lden E adl) (Z_to_bv 64 262144))) ->
      DEN ASEGS LIMIT model0 (mem0_z mem0 (uE E adl) 262144) E (fix_post L adl) (with_own M (sm_own M ++ [(adl, lconst 262144)])) ms' model' ->
      realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros mem0 L E M ms model T adl jP gP Hd Hpc Ha0 Hfk HjP HGE Hnr Hlen H47 Hsep Hnown Hnfrz Hk.
  apply (den_ecall ASEGS cfg LIMIT model0 mem0 Hwx ATBLd E L M ms model T ATBLd_ecall ltac:(rewrite Hpc; exact ecall_73aa8) Hd).
  intros model1 Hd1.
  set (AD := uE E adl) in *.
  assert (Hin_b : forall w : word, (Z.leb AD (bv_unsigned w) && Z.ltb (bv_unsigned w) (AD + 262144))%bool = true <-> AD <= bv_unsigned w < AD + 262144).
  { intros w. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. }
  apply (den_fixkeep_xs ASEGS cfg LIMIT model0 mem0 Hsegb Hoff Hrespos Hreswf E L M ms model1 T 262144 false jP GE (mem0_z mem0 AD 262144) Hd1 Hfk).
  - rewrite Ha0. exact Hsep.
  - intros w Hw. rewrite Ha0, Hlen in Hw. fold AD in Hw. unfold mem0_z.
    destruct (Z.leb AD (bv_unsigned w) && Z.ltb (bv_unsigned w) (AD + 262144))%bool eqn:Eb; [exfalso; apply Hw; apply Hin_b; exact Eb | reflexivity].
  - intros w Ho Hw. rewrite Ha0, Hlen in Hw. fold AD in Hw. exfalso. exact (Hnown w Ho Hw).
  - intros ms' model' Hms' Hvis HD'. rewrite Ha0 in Hms', HD', Hvis. rewrite Hlen in Hms', Hvis. fold AD in Hvis.
    rewrite (fix_M_same M jP GE gP HjP HGE) in HD', Hvis.
    apply (Hk ms' model' Hms').
    apply (den_own_set ASEGS LIMIT model0 (mem0_z mem0 AD 262144) (mem0_z mem0 AD 262144) E (fix_post L adl) M ms' model' (sm_own M ++ [(adl, lconst 262144)]) HD').
    + pose proof (dn_wf _ _ _ _ _ _ _ _ _ HD') as Hwf. unfold sm_wf in Hwf. apply andb_prop in Hwf as [_ Hwo].
      rewrite forallb_app. rewrite Hwo. cbn [forallb fst snd]. rewrite andb_true_r.
      assert (Hwa : lwf (s_next (fix_post L adl)) adl = true).
      { unfold fixkeep_ok_s in Hfk. rewrite Ha0 in Hfk. destruct (a7c L); [|discriminate]. destruct (arg L 2); [|discriminate]. destruct (arg L 3); [|discriminate].
        destruct (arg L 5); [|discriminate]. rewrite HjP in Hfk.
        repeat (apply andb_prop in Hfk as [Hfk ?]). cbn [fix_post s_next].
        match goal with H : lwf (s_next L) adl = true |- _ => exact H end. }
      rewrite Hwa. apply lwf_lconst.
    + intros w _. reflexivity.
    + intros w (q & Hq & Hqw). exists q. split; [cbn [with_own sm_own]; apply in_or_app; left; exact Hq | exact Hqw].
    + intros w (q & Hq & Hqw). cbn [with_own sm_own] in Hq. apply in_app_or in Hq as [Hq|Hq].
      * exact (dn_own _ _ _ _ _ _ _ _ _ HD' q Hq w Hqw).
      * destruct Hq as [<-|[]]. cbn [fst snd] in Hqw. rewrite uE_lc in Hqw by lia. fold AD in Hqw.
        split; [exact (Hvis eq_refl Hnr w Hqw)|]. intros _.
        rewrite Hms', fresh_full_mem. unfold mem0_z.
        assert (Hw64 : 0 <= w < two64) by (pose proof (uE_range E adl); unfold AD, two64 in *; lia).
        rewrite (proj2 (Hin_b (Z_to_bv 64 w))) by (rewrite u_small64 by exact Hw64; exact Hqw).
        apply fresh_mem_in. fold (uE E adl). fold AD. rewrite !u_small64 by (unfold two64 in *; lia). exact Hqw.
Qed.
End Commit.
