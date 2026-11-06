(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChAdd FxChFixNew FxChain FxChMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFixNew OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcSteps.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMALlib.

Module AcSysN.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChSep FxChNull FxChFix FxChAdd FxChFixNew FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFixNew OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcSteps.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMALlib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps.AcP0gen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcFast OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition own_ok_b (M : smodel) (a : ast) : bool := match sm_own M with [] => true | _ => (a_on a && list_eqb pair_eqb (sm_own M) (a_own a))%bool end.
(* [comment removed for export] *)
Definition cmn_ok (fs : list fact) (M : smodel) (a : ast) (ad : lin) (n : Z) (j : nat) : bool :=
  match nth_error (sm_maps M) j with
  | Some g => (match a_pri a with [] => true | _ => false end &&   (* [comment removed for export] *)
               contained_b fs ad n (fst (fst g)) (gsz_lo fs g) && negb (lin_eqb (fst (fst g)) (fst (a_dep a))) &&
               negb (lin_eqb (fst (fst g)) (snd (a_dep a))))%bool
  | None => false
  end.
Definition fix_own_ok (S : sst) (M : smodel) (a : ast) (n : Z) (j : nat) : bool :=
  match sm_own M with [] => true | _ => (a_on a && list_eqb pair_eqb (sm_own M) (a_own a) && cmn_ok (s_facts S) M a (rget (s_regs S) (rk 10)) n j)%bool end.

Definition apost_nullA (LIMIT : Z) (nZ : Z) (k : gkind) (vis piece na : bool) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (Z.eqb (s_pc S) 0x73c44 && null_ok ASEGSR LIMIT S M nZ k vis piece na && own_ok_b M a && Z.ltb 0 nZ && Z.ltb nZ 4294967296)%bool
    (Some (null_post S nZ vis piece, null_M M (s_next S) nZ k vis piece, a)).
Definition apost_sepwA (i j : nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obind (sepw_post S M i j) (fun S' => Some (S', M, a)).
Definition apost_fixA (LIMIT : Z) (n : Z) (j : nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (Z.eqb (s_pc S) 0x73c44 && fixnew_ok_f LIMIT ASEGSR S M n j && fix_own_ok S M a n j && Z.ltb 0 n && Z.ltb n 4294967296)%bool
    (Some (add_post (fix_post S (rget (s_regs S) (rk 10))) (rget (s_regs S) (rk 10)) n (Some (fixnew_piece S)),
           add_M (fix_M M j GE) n (Some (fixnew_piece S)), a)).

Lemma HA_keep_own : forall E E' M M' a m0 n, HA E M a m0 -> sm_wf n M = true -> awf n a = true -> agree n E E' ->
  sm_own M' = sm_own M -> sm_zr M' = sm_zr M -> (forall b z k, In (b, z, k) (sm_maps M) -> exists k', In (b, z, k') (sm_maps M')) -> HA E' M' a m0.
Proof.
  intros E E' M M' a m0 n HA Hwf Haw Ha Ho Hzr Hm Hon. apply (HA_maps E' M M' a m0); [| exact Ho | exact Hzr | exact Hm].
  exact (HA_agree n E E' M a m0 Hwf Haw Ha HA Hon).
Qed.

Section SysNodes.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Hwx Hsegb Hoff"] Theorem nullA_node : forall nZ k vis piece na S M a S' M' a', apost_nullA LIMIT nZ k vis piece na S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff : LiaFast.U) => LiaFast.u0).
  intros nZ k vis piece na S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  unfold apost_nullA in H. apply obool_some in H as (Hb & H). injection H as <- <- <-.
  apply andb_prop in Hb as [Hb Hn2]. apply andb_prop in Hb as [Hb Hn1]. apply andb_prop in Hb as [Hb Hoo]. apply andb_prop in Hb as [Hpc Hnull].
  apply Z.eqb_eq in Hpc. apply Z.ltb_lt in Hn1, Hn2. unfold ASEGSR in Hnull.
  apply (den_ecall ASEGS cfg LIMIT model0 mem0 Hwx ATBLd E S M ms model T ATBLd_ecall ltac:(rewrite Hpc; exact ecall_73aa8) Hd).
  intros model' Hd'.
  apply (den_null ASEGS cfg LIMIT model0 mem0 Hsegb Hoff E S M ms model' T nZ k vis piece na Hd' Hnull).
  - intros ad Hpl. unfold own_ok_b in Hoo.
    destruct (sm_own M) as [|p0 ps] eqn:Hown.
    + split; [exact (own_avoid_nil E M _ _ Hown) | intros _; exact (own_avoid_nil E M _ _ Hown)].
    + apply andb_prop in Hoo as [Hoo Hoe]. apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hoe.
      assert (Hoa : sm_own M = a_own a) by (rewrite Hown; exact Hoe).
      pose proof (HHA Hoo) as HA0. split.
      * apply (dep_avoid_place LIMIT model0 mem0 E S M ms model' a mem0 nZ ad Hd' HA0 Hoa Hpl). unfold two64. lia.
      * intros _. exact (dep_avoid_shadow_place LIMIT model0 mem0 E S M ms model' a mem0 nZ ad Hd' HA0 Hoa Hpl ltac:(unfold two64; lia)).
  - intros E' ms' model'' Hd2 Ha2. apply (Hk E' mem0 ms' model'' Ha2).
    + intros q Hq w Hw. reflexivity.
    + exact Hd2.
    + apply (HA_keep_own E E' M _ a mem0 (s_next S) HHA (dn_wf _ _ _ _ _ _ _ _ _ Hd) Haw Ha2); [reflexivity | reflexivity |].
      intros b z kd Hin. exists kd. unfold null_M. cbn [sm_maps]. right. exact Hin.
Qed.

#[using="Type"] Theorem sepwA_node : forall i j S M a S' M' a', apost_sepwA i j S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i j S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  unfold apost_sepwA in H. apply obind_some in H as (S2 & Hs & H). cbv beta in H. injection H as <- <- <-.
  apply (Hk E mem0 ms model (agree_refl _ _)); [intros q Hq w Hw; reflexivity | | exact HHA].
  exact (den_sepw ASEGS LIMIT model0 mem0 E S M ms model i j S2 Hd Hs).
Qed.

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem fixA_node : forall n j S M a S' M' a', apost_fixA LIMIT n j S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros n j S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  unfold apost_fixA in H. apply obool_some in H as (Hb & H). injection H as <- <- <-.
  apply andb_prop in Hb as [Hb Hn2]. apply andb_prop in Hb as [Hb Hn1]. apply andb_prop in Hb as [Hb Hoo]. apply andb_prop in Hb as [Hpc Hfx].
  apply Z.eqb_eq in Hpc. apply Z.ltb_lt in Hn1, Hn2. rewrite fixnew_ok_f_eq in Hfx. unfold ASEGSR in Hfx.
  apply (den_ecall ASEGS cfg LIMIT model0 mem0 Hwx ATBLd E S M ms model T ATBLd_ecall ltac:(rewrite Hpc; exact ecall_73aa8) Hd).
  intros model' Hd'.
  (* [comment removed for export] *)
  assert (Hav : own_avoid E M (uE E (rget (s_regs S) (rkey a0r))) (uE E (rget (s_regs S) (rkey a0r)) + n) /\
                own_avoid E M (uE E (rget (s_regs S) (rkey a0r)) / 8 + SH_OFF) (uE E (rget (s_regs S) (rkey a0r)) / 8 + SH_OFF + n / 8)).
  { unfold fix_own_ok in Hoo. destruct (sm_own M) as [|p0 ps] eqn:Hown; [split; apply (own_avoid_nil E M _ _ Hown)|].
    apply andb_prop in Hoo as [Hon Hcm]. apply andb_prop in Hon as [Hon Hoe]. apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hoe.
    assert (Hoa : sm_own M = a_own a) by (rewrite Hown; exact Hoe). pose proof (HHA Hon) as HA0.
    unfold cmn_ok in Hcm. destruct (nth_error (sm_maps M) j) as [g|] eqn:Hg; [|discriminate].
    apply andb_prop in Hcm as [Hcm Hnb]. apply andb_prop in Hcm as [Hcn Hna]. apply andb_prop in Hcn as [Hpn Hcn]. apply negb_true_iff in Hna, Hnb. apply lin_eqb_neq in Hna, Hnb.
    assert (Hnil : a_pri a = []) by (destruct (a_pri a); [reflexivity | discriminate]).
    pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd')) as Hd0. destruct Hd0 as (_ & _ & _ & _ & _ & _ & HF & _).
    pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd') as Hgs. rewrite Forall_forall in Hgs. pose proof (Hgs g (nth_error_In _ _ Hg)) as (G1 & G2 & G3 & G4 & G5).
    change (rget (s_regs S) (rk 10)) with (rget (s_regs S) (rkey a0r)) in Hcn.
    pose proof (gsz_bounds E _ g HF) as Gb. pose proof (gsz_lo_nonneg (s_facts S) g) as Gl.
    destruct (contained_sound E _ _ n (fst (fst g)) (gsz_lo (s_facts S) g) HF Hcn ltac:(lia) ltac:(unfold gsz, uE, two64 in *; lia)) as [C1 C2].
    assert (C2' : uE E (rget (s_regs S) (rkey a0r)) + n <= uE E (fst (fst g)) + gsz E g) by lia.
    split.
    - exact (dep_avoid_grant LIMIT model0 mem0 E S M ms model' a mem0 _ g _ _ Hd' HA0 Hoa Hnil Hg (fixnew_ok_nomark _ _ _ _ _ _ g Hfx Hg) C1 C2' Hna Hnb).
    - apply (dep_avoid_shadow2 LIMIT model0 mem0 E S M ms model' a mem0 (uE E (rget (s_regs S) (rkey a0r))) n _ _ Hd' HA0 Hoa); [| | | intros Hne; exfalso; exact (Hne Hnil)].
      + unfold SH_LO, SH_OFF. pose proof (Z.div_pos (uE E (rget (s_regs S) (rkey a0r))) 8 ltac:(unfold uE; pose proof (bv_unsigned_in_range _ (lden E (rget (s_regs S) (rkey a0r)))); lia) ltac:(lia)). lia.
      + unfold SH_HI, SH_OFF. assert (Q : uE E (rget (s_regs S) (rkey a0r)) / 8 + n / 8 <= 17592186044416).
        { assert (Q1 : uE E (rget (s_regs S) (rkey a0r)) / 8 + n / 8 <= (uE E (rget (s_regs S) (rkey a0r)) + n) / 8).
          { pose proof (Z.div_add_l (uE E (rget (s_regs S) (rkey a0r))) 8 (n)) as _X. clear _X.
            pose proof (Z.mul_div_le (uE E (rget (s_regs S) (rkey a0r))) 8 ltac:(lia)) as M1. pose proof (Z.mul_div_le n 8 ltac:(lia)) as M2.
            apply Z.div_le_lower_bound; lia. }
          assert (Q2 : (uE E (rget (s_regs S) (rkey a0r)) + n) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). lia. }
        lia.
      + intros w Hw. pose proof (Z.div_mod (uE E (rget (s_regs S) (rkey a0r))) 8 ltac:(lia)) as E1.
        pose proof (Z.mod_pos_bound (uE E (rget (s_regs S) (rkey a0r))) 8 ltac:(lia)) as B1.
        pose proof (Z.mul_div_le n 8 ltac:(lia)) as M2. lia. }
  destruct Hav as [Hav1 Hav2].
  apply (den_fixnew_g ASEGS cfg LIMIT model0 mem0 Hsegb Hoff Hrespos Hreswf E S M ms model' T n j true mem0 Hd' Hfx).
  - intros w _. reflexivity.
  - intros w Hown Hw. exfalso. exact (Hav1 w Hown Hw).
  - intros _. exact Hav2.
  - intros ms' model'' Hd2. apply (Hk E mem0 ms' model'' (agree_refl _ _)).
    + intros q Hq w Hw. reflexivity.
    + exact Hd2.
    + apply (HA_keep_own E E M _ a mem0 (s_next S) HHA (dn_wf _ _ _ _ _ _ _ _ _ Hd) Haw (agree_refl _ _)); [reflexivity | reflexivity |].
      intros b z kd Hin. unfold add_M, fix_M. cbn [sm_maps]. exact (in_set_kind _ _ _ _ _ _ Hin).
Qed.
End SysNodes.
End AcSysN.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps.AcP0gen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcFast OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSysK.AcSysN.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FixKeepG.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved segs).
Hypothesis Hreswf : ivs_wf (segments_reserved segs).

#[using="Hsegb Hoff Hrespos Hreswf"] Theorem den_fixkeep_g : forall E L M ms model T n na j kd',
  DEN segs LIMIT model0 mem0 E L M ms model ->
  own_avoid E M (uE E (rget (s_regs L) (rkey a0r))) (uE E (rget (s_regs L) (rkey a0r)) + n) ->
  fixkeep_ok LIMIT (segments_reserved segs) L M n na j kd' = true ->
  (forall ms' model', DEN segs LIMIT model0 mem0 E (fix_post L (rget (s_regs L) (rkey a0r))) (fix_M M j kd') ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins (fun (Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros E L M ms model T n na j kd' Hd Hav Hok Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  unfold fixkeep_ok in Hok. set (a := rget (s_regs L) (rkey a0r)) in *. set (ln := rget (s_regs L) (rkey a1r)) in *.
  destruct (a7c L) as [c7|] eqn:H7; [|discriminate].
  destruct (arg L 2) as [prot|] eqn:H2; [|discriminate]. destruct (arg L 3) as [flags|] eqn:H3; [|discriminate].
  destruct (arg L 5) as [off|] eqn:H5; [|discriminate]. destruct (nth_error (sm_maps M) j) as [g|] eqn:Hj; [|discriminate].
  apply andb_prop in Hok as [Hok Hgm]. apply negb_true_iff in Hgm.
  apply andb_prop in Hok as [Hok Hbc]. apply Z.leb_le in Hbc. apply andb_prop in Hok as [Hok Hbud]. apply Z.leb_le in Hbud.
  apply andb_prop in Hok as [Hok Hwa]. apply andb_prop in Hok as [Hok Hzrc]. apply andb_prop in Hok as [Hok Halc].
  apply andb_prop in Hok as [Hok Hnbig]. apply Z.ltb_lt in Hnbig.
  apply andb_prop in Hok as [Hok Hrgc]. apply andb_prop in Hok as [Hok Hkdc]. apply andb_prop in Hok as [Hok Hdal].
  apply andb_prop in Hok as [Hok Hdc]. apply andb_prop in Hok as [Hok Hsel].
  apply andb_prop in Hok as [Hok Hnac]. apply andb_prop in Hok as [Hok Hmod]. apply andb_prop in Hok as [Hok Hlok].
  apply andb_prop in Hok as [Hok Hanon]. apply andb_prop in Hok as [Hc7 Hoffa]. apply Z.eqb_eq in Hc7. subst c7.
  apply negb_true_iff in Hmod, Hnac.
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 222) by exact (a7_const segs E L (restrict H ms) ms 222 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = lden E a) by exact (gpr_lin segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hg1 : ms_gpr ms1 1 = lden E ln) by exact (gpr_lin1 segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 prot) by exact (gpr_const segs E L (restrict H ms) ms 2 prot Hsd eq_refl ltac:(lia) H2).
  assert (Hg3 : ms_gpr ms1 3 = Z_to_bv 64 flags) by exact (gpr_const segs E L (restrict H ms) ms 3 flags Hsd eq_refl ltac:(lia) H3).
  assert (Hg5 : ms_gpr ms1 5 = Z_to_bv 64 off) by exact (gpr_const segs E L (restrict H ms) ms 5 off Hsd eq_refl ltac:(lia) H5).
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & HFl & _).
  unfold len_ok in Hlok. apply andb_prop in Hlok as [Hlok Hl3]. apply andb_prop in Hlok as [Hl1 Hl2].
  apply Z.ltb_lt in Hl1, Hl3. apply Z.leb_le in Hl2. pose proof (irange_sound E _ ln HFl) as Rln.
  set (len := lden E ln) in *.
  assert (Hnz0 : w_is0 len = false) by (unfold w_is0, bv_eqb; apply Z.eqb_neq; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia).
  set (n0 := page_round_up_Z (bv_unsigned len)).
  assert (HnZ : page_round_up_Z (bv_unsigned len) = n0) by reflexivity.
  assert (HnZpos : 0 < n0) by (rewrite <- HnZ; exact (len_nZ_pos _ Hnz0)).
  assert (HnZal : n0 mod 4096 = 0) by (rewrite <- HnZ; exact (page_round_up_Z_aligned' _)).
  assert (Hn0n : n0 <= n) by (pose proof (pru_mono _ _ (proj2 Rln)); unfold n0; lia).
  assert (Hnpos : 0 < n) by lia.
  assert (Hgj : In g (sm_maps M)) by exact (nth_error_In _ _ Hj).
  pose proof Hgsh as Hgsh0. rewrite Forall_forall in Hgsh0. destruct (Hgsh0 g Hgj) as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5).
  pose proof Hgtop as Hgtop0. rewrite Forall_forall in Hgtop0. pose proof (Hgtop0 g Hgj) as Gt.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc0 & _ & _ & _ & HG0 & HD0 & HF0 & _).
  pose proof (gsz_bounds E (s_facts L) g HF0) as Gb. pose proof (gsz_lo_nonneg (s_facts L) g) as Gb0.
  destruct (contained_sound E (s_facts L) a n (fst (fst g)) (gsz_lo (s_facts L) g) HF0 Hdc Hnpos ltac:(unfold uE, two64 in *; lia)) as [Hlo Hhi0].
  assert (Hhi : uE E a + n <= uE E (fst (fst g)) + gsz E g) by lia.
  assert (Hal : uE E a mod 4096 = 0) by (apply (lal_ok_sound E a (fst (fst g)) Hdal Gs3 Hlo); unfold uE, two64 in *; lia).
  assert (Hov : forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> uE E a <= w < uE E a + n ->
      na = false /\ rg_kind R = RZ /\
      (tget (okey (w - uE E (rg_base R))) (rg_cont R) = None \/ tget (okey (w - uE E (rg_base R))) (rg_cont R) = Some (BK 0))).
  { intros R HR w Hw Hin. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (_ & HRw & _).
    apply orb_prop in Hrgc as [Hrgc|Hrgc].
    - (* [comment removed for export] *)
      apply andb_prop in Hrgc as [Hn0 Hex]. apply negb_true_iff in Hn0. rewrite existsb_lz_eq in Hex. apply existsb_exists in Hex as (R0 & HR0 & Hz0).
      destruct (HG0 R0 HR0) as (_ & HR0w & _).
      destruct (zero_ov_inside E (s_facts L) a n R0 HF0 Hz0 Hnpos HR0w) as [I1 I2].
      destruct (In_nth_error _ _ HR) as [i Hi]. destruct (In_nth_error _ _ HR0) as [i0 Hi0].
      destruct (Nat.eq_dec i i0) as [->|Hne].
      + rewrite Hi in Hi0. injection Hi0 as ->. split; [exact Hn0|].
        exact (zero_ov_sound E (s_facts L) a n R0 HF0 Hz0 ltac:(lia) HR0w w Hw Hin).
      + exfalso. pose proof (rgs_disj_nth E (s_rgs L) i i0 R R0 HD0 Hne Hi Hi0) as Hdj. unfold rg_disj in Hdj. unfold uE in *. lia.
    - rewrite forallb_forall in Hrgc. pose proof (Hrgc R HR) as Hc.
      apply orb_prop in Hc as [Hc|Hc]; [apply orb_prop in Hc as [Hc|Hc]|]; [apply orb_prop in Hc as [Hc|Hc]| |];
        [apply orb_prop in Hc as [Hc|Hc]| | |].
      + exfalso. apply (rgs_sep_sound E (s_facts L) a n R HF0 ltac:(lia) ltac:(unfold uE in *; lia) HRw Hc w Hw Hin).
      + exfalso. destruct (HG0 R HR) as (HRs & _ & _).
        exact (sep_app2_sound E (s_facts L) (sm_maps M) model (sm_sp M) _ HF0 Hmaps Hpd Hgsh Hgtop Hsp (proj2 Hspok)
                 j g a n R Hj Hgm Hlo Hhi ltac:(unfold two64; lia) HRs HRw Hc w Hw Hin).
      + exfalso. rewrite <- Hres in Hc.
        exact (sep_res_sound E (sm_maps M) model _ Hmaps Hgsh Hmres j g a n R Hj Hgm Hlo Hhi Hc w Hw Hin).
      + exfalso. destruct (HG0 R HR) as (HRs & _ & _).
        exact (sep_rb_sound E (s_facts L) (sm_maps M) model (sm_sp M) HF0 Hgsh Hgtop Hsp (proj2 Hspok) j a n R HRs HRw Hc w Hw Hin).
      + apply andb_prop in Hc as [Hn0 Hz]. apply negb_true_iff in Hn0. split; [exact Hn0|].
        apply orb_prop in Hz as [Hz|Hz].
        * exact (zero_ov_sound E (s_facts L) a n R HF0 Hz ltac:(lia) HRw w Hw Hin).
        * exact (zero_ov2_sound E (s_facts L) a n R HF0 Hz ltac:(lia) HRw w Hw Hin). }
  assert (Hallow : mmap_noreserve_b (Z_to_bv 64 flags) = true -> forall w, uE E a <= w < uE E a + n ->
                     page_allowedb (allowA E M) (page_base (Z_to_bv 64 w)) = true).
  { intros Hnr w Hw. rewrite Hnr in Halc. cbn in Halc. apply (allow_cov_sound E (s_facts L) a n _ HF0 Halc w Hw).
    pose proof (u_lt (lden E a)). unfold uE, two64 in *. lia. }
  assert (Hnazr : na = true -> forall w, uE E a <= w < uE E a + n -> in_zr (sm_zr M) w = false).
  { intros Hna w Hw. rewrite Hna in Hzrc. cbn in Hzrc. rewrite Hmaps in Hpd.
    exact (zr_sep_g_sound E _ (s_facts L) (sm_maps M) j g a n _ HF0 Hpd Hgsh Hj Hgm (fun w' Hw' => ltac:(lia)) Hzrc w Hw). }
  assert (Hkd : kd' = GE \/ (kd' = snd g /\ (na = true \/ mmap_noreserve_b (Z_to_bv 64 flags) = true))).
  { apply orb_prop in Hkdc as [Hkdc|Hkdc]; [left; destruct kd'; try discriminate; reflexivity|]. right.
    apply andb_prop in Hkdc as [Hk1 Hk2]. apply andb_prop in Hk1 as [Hk1 _]. split; [destruct kd', (snd g); try discriminate; reflexivity|].
    apply orb_prop in Hk2 as [Hk2|Hk2]; [left; exact Hk2 | right; exact Hk2]. }
  assert (Hkdn : kd' <> GN).
  { intros ->. apply orb_prop in Hkdc as [Hkdc|Hkdc]; [discriminate|]. apply andb_prop in Hkdc as [Hk1 _]. apply andb_prop in Hk1 as [_ Hk1].
    discriminate. }
  pose proof (fix_keep_den segs LIMIT model0 mem0 Hsegb E L M ms model a n0 na (Z_to_bv 64 flags) j g kd' mem0 Hd Hwa Hj Hgm
                ltac:(lia) ltac:(lia) HnZpos HnZal Hal Hkd Hkdn
                (fun R HR w Hw Hin => Hov R HR w Hw ltac:(lia))
                (fun Hnr w Hw => Hallow Hnr w ltac:(lia))
                (fun Hna w Hw => Hnazr Hna w ltac:(lia)) Hbud
                (fun w _ => eq_refl) (fun w Hop Hin => False_ind _ (Hav w Hop ltac:(lia)))) as HD'.
  assert (Hsvc : ms_svc_pending ms1 = Some (ms_reg ms 17)) by reflexivity.
  assert (Hno : bv_unsigned (ms_reg ms 17) = 222) by (rewrite Hx8; reflexivity).
  (* [comment removed for export] *)
  assert (HuA : bv_unsigned (lden E a) = uE E a) by reflexivity.
  assert (Htop : uE E a + n0 <= alloc_top (m_vmmaps model)) by lia.
  assert (Hgate : fixed_gate model (lden E a) len).
  { unfold fixed_gate, page_size. rewrite HuA, HnZ. repeat split; lia. }
  assert (HnZw : bv_unsigned (Z_to_bv 64 n0) = n0) by (apply fg64; pose proof (u_lt (lden E a)); unfold uE, two64 in *; lia).
  assert (Hcm : forall x, uE E a <= x < uE E a + n0 -> covered (vm_maps (m_vmmaps model)) x = true).
  { intros x Hx. rewrite Hmaps. apply (covered_In _ (gden E g)); [exact (lden_maps_in E _ _ g Hgj Hgm)|]. unfold gden. rewrite in_iv_word.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold gsz, uE in *; lia. }
  assert (Hctn : (region_free (vm_reserved (m_vmmaps model)) (lden E a) (Z_to_bv 64 n0)
                  && map_contains (vm_maps (m_vmmaps model)) (lden E a) (Z_to_bv 64 n0))%bool = true).
  { apply andb_true_intro. split.
    - rewrite Hres. apply region_free_of_pts; [exact Hreswf | exact Hrespos | | rewrite HnZw; exact HnZpos].
      intros x Hx. rewrite HnZw, HuA in Hx. rewrite <- Hres. exact (Hmres x (Hcm x Hx)).
    - rewrite Hmaps. apply (map_contains_intro _ _ _ (fst (gden E g)) (snd (gden E g))); [rewrite <- surjective_pairing; exact (lden_maps_in E _ _ g Hgj Hgm) | |].
      + unfold gden. cbn [fst]. unfold uE in *. lia.
      + unfold gden. cbn [fst snd]. rewrite HnZw, HuA. unfold gsz, uE in *. lia. }
  rewrite <- HnZ in Hctn.
  destruct na.
  - assert (Hbr := branch_fixed_na_contained segs ms1 (ms_reg ms 17) model Hno).
    rewrite ?Hg0, ?Hg1, ?Hg2, ?Hg3, ?Hg5 in Hbr. rewrite HnZ in Hbr, Hctn.
    specialize (Hbr Hoffa Hanon Hnz0 Hmod Hnac Hsel Hgate Hctn).
    eapply rzc_silent1; [|exact (Hk _ _ HD')].
    exact (node_mmap_fixed_na_contained segs cfg Hoff ms1 model (ms_reg ms 17) (lden E a) (Z_to_bv 64 n0) (Z_to_bv 64 flags) Hh Hsvc Hno
             ltac:(rewrite HuA; lia) Hbr).
  - apply andb_prop in Hsel as [Hsel1 Hsel2]. apply negb_true_iff in Hsel1.
    assert (Hbr := branch_fixed_rw_contained segs ms1 (ms_reg ms 17) model Hno).
    rewrite ?Hg0, ?Hg1, ?Hg2, ?Hg3, ?Hg5 in Hbr. rewrite HnZ in Hbr, Hctn.
    specialize (Hbr Hoffa Hanon Hnz0 Hmod Hnac Hsel1 Hsel2 Hgate Hctn).
    eapply rzc_silent1; [|exact (Hk _ _ HD')].
    apply (node_mmap_fixed_rw_contained segs cfg Hoff ms1 model (ms_reg ms 17) (lden E a) (Z_to_bv 64 n0) (Z_to_bv 64 flags) Hh Hsvc Hno
             ltac:(rewrite HuA; lia) Hbr).
    (* [comment removed for export] *)
    assert (Hmw : model_ivs_wf model).
    { split; [rewrite Hmaps; exact (ivs_wf_lden E model _ _ Hgsh (proj1 Hblob))|]. split; [exact (proj1 Hivwf)|]. split; [exact (proj2 Hivwf) | exact (proj1 Hspok)]. }
    assert (Hvb : vm_backing_used model <= eager_sum (s_facts L) (sm_maps M) + allow_bound (sm_allow M))
      by exact (den_backing_le segs LIMIT model0 mem0 E L M ms model (s_facts L) Hd HF0).
    pose proof (mark_len_nonneg (s_facts L) (sm_maps M)) as Hmn0.
    assert (Hprod : 0 <= (Z.of_nat (length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * n) by (apply Z.mul_nonneg_nonneg; lia).
    destruct (mmap_noreserve_b (Z_to_bv 64 flags)) eqn:Hnr.
    + pose proof (u_lt (lden E a)) as Ra.
      apply mmap_fixed_rw_budget_ok_recommit_intro; [exact Hnr | exact Hmw | | | | |]; unfold page_size; rewrite ?HuA, ?HnZw.
      * exact Hal.
      * exact HnZal.
      * exact HnZpos.
      * unfold uE, two64 in *. change (2 ^ 64) with 18446744073709551616. lia.
      * rewrite Hlim. lia.
    + apply mmap_fixed_rw_budget_ok_commit_intro; [exact Hnr | exact Hmw|]. rewrite Hlim.
      assert (Hov' : overlap_sum (vm_maps (m_vmmaps model)) (bv_unsigned (lden E a)) (bv_unsigned (lden E a) + bv_unsigned (Z_to_bv 64 n0))
                     <= Z.of_nat (length (vm_maps (m_vmmaps model))) * n0).
      { rewrite HnZw. clear -HnZpos. induction (vm_maps (m_vmmaps model)) as [|g0 r IH]; [unfold overlap_sum; cbn; lia|].
        cbn [length]. rewrite overlap_sum_cons. pose proof (iv_count_in_rng_le g0 (bv_unsigned (lden E a)) (bv_unsigned (lden E a) + n0) ltac:(lia)).
        lia. }
      destruct (ledger_lden_bounds E model (s_facts L) _ _ HF0 Hgsh (proj1 Hblob) (proj2 (proj2 Hblob))) as [_ Hln]. rewrite <- Hmaps in Hln.
      pose proof (mark_len_nonneg (s_facts L) (sm_maps M)) as Hmn.
      assert (Z.of_nat (length (vm_maps (m_vmmaps model))) * n0 <= (Z.of_nat (length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * n) by (apply Z.mul_le_mono_nonneg; lia).
      lia.
Qed.
End FixKeepG.

(* [comment removed for export] *)
Definition apost_fixkA (LIMIT : Z) (n : Z) (na : bool) (j : nat) (kd' : gkind) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (Z.eqb (s_pc S) 0x73c44 && fixkeep_ok LIMIT ASEGSR S M n na j kd' && fix_own_ok S M a n j && Z.ltb 0 n && Z.ltb n 4294967296)%bool
    (Some (fix_post S (rget (s_regs S) (rk 10)), fix_M M j kd', a)).

Section FixKNode.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem fixkA_node : forall n na j kd' S M a S' M' a', apost_fixkA LIMIT n na j kd' S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros n na j kd' S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  unfold apost_fixkA in H. apply obool_some in H as (Hb & H). injection H as <- <- <-.
  apply andb_prop in Hb as [Hb Hn2]. apply andb_prop in Hb as [Hb Hn1]. apply andb_prop in Hb as [Hb Hoo]. apply andb_prop in Hb as [Hpc Hfk].
  apply Z.eqb_eq in Hpc. apply Z.ltb_lt in Hn1, Hn2. unfold ASEGSR in Hfk.
  apply (den_ecall ASEGS cfg LIMIT model0 mem0 Hwx ATBLd E S M ms model T ATBLd_ecall ltac:(rewrite Hpc; exact ecall_73aa8) Hd).
  intros model' Hd'.
  (* [comment removed for export] *)
  assert (Hav : own_avoid E M (uE E (rget (s_regs S) (rkey a0r))) (uE E (rget (s_regs S) (rkey a0r)) + n)).
  { unfold fix_own_ok in Hoo. destruct (sm_own M) as [|p0 ps] eqn:Hown; [exact (own_avoid_nil E M _ _ Hown)|].
    apply andb_prop in Hoo as [Hon Hcm]. apply andb_prop in Hon as [Hon Hoe]. apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hoe.
    assert (Hoa : sm_own M = a_own a) by (rewrite Hown; exact Hoe). pose proof (HHA Hon) as HA0.
    unfold cmn_ok in Hcm. destruct (nth_error (sm_maps M) j) as [g|] eqn:Hg; [|discriminate].
    apply andb_prop in Hcm as [Hcm Hnb]. apply andb_prop in Hcm as [Hcn Hna]. apply andb_prop in Hcn as [Hpn Hcn]. apply negb_true_iff in Hna, Hnb. apply lin_eqb_neq in Hna, Hnb.
    assert (Hnil : a_pri a = []) by (destruct (a_pri a); [reflexivity | discriminate]).
    pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd')) as Hd0. destruct Hd0 as (_ & _ & _ & _ & _ & _ & HF & _).
    pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd') as Hgs. rewrite Forall_forall in Hgs. pose proof (Hgs g (nth_error_In _ _ Hg)) as (G1 & G2 & G3 & G4 & G5).
    change (rget (s_regs S) (rk 10)) with (rget (s_regs S) (rkey a0r)) in Hcn.
    pose proof (gsz_bounds E _ g HF) as Gb. pose proof (gsz_lo_nonneg (s_facts S) g) as Gl.
    destruct (contained_sound E _ _ n (fst (fst g)) (gsz_lo (s_facts S) g) HF Hcn ltac:(lia) ltac:(unfold gsz, uE, two64 in *; lia)) as [C1 C2].
    assert (C2' : uE E (rget (s_regs S) (rkey a0r)) + n <= uE E (fst (fst g)) + gsz E g) by lia.
    exact (dep_avoid_grant LIMIT model0 mem0 E S M ms model' a mem0 _ g _ _ Hd' HA0 Hoa Hnil Hg (fixkeep_ok_nomark _ _ _ _ _ _ _ _ g Hfk Hg) C1 C2' Hna Hnb). }
  apply (den_fixkeep_g ASEGS cfg LIMIT model0 mem0 Hsegb Hoff Hrespos Hreswf E S M ms model' T n na j kd' Hd' Hav Hfk).
  intros ms' model'' Hd2. apply (Hk E mem0 ms' model'' (agree_refl _ _)).
  - intros q Hq w Hw. reflexivity.
  - exact Hd2.
  - apply (HA_keep_own E E M _ a mem0 (s_next S) HHA (dn_wf _ _ _ _ _ _ _ _ _ Hd) Haw (agree_refl _ _)); [reflexivity | reflexivity |].
    intros b z kd Hin. unfold fix_M. cbn [sm_maps]. exact (in_set_kind _ _ _ _ _ _ Hin).
Qed.
End FixKNode.
