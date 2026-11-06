(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcSteps AcEntry AcMALp AcHand AcUnwApp AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcHA AcFacts AcCarveP.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcSteps.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcMALlib AcPutN AcUch.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps.AcP0gen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUch.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint find_rg_acc (f : region -> bool) (rgs : list region) (i : nat) : option nat :=
  match rgs with [] => None | R :: r => if f R then Some i else find_rg_acc f r (Datatypes.S i) end.
Definition find_rg (f : region -> bool) (rgs : list region) : option nat := find_rg_acc f rgs O.
Definition got_b (R : region) : bool := got_rg_b (Some R).
Definition psz_rb (R : region) : bool := psz_b (Some R).
Definition shift_ix (k stk np : nat) : nat := if Nat.ltb k stk then k else (k + np)%nat.
Definition top_vars (l : lin) : option (positive * positive) :=
  match l with LIN 4096 [(x1, 32768); (x2, 4096)] => Some (x1, x2) | _ => None end.

(* [comment removed for export] *)
Definition unw_cuts (o osp obuf : Z) : list Z :=
  [o + osp - 1024; o + osp - 64; o + osp; o + obuf + 8; o + obuf + 16; o + obuf + 256; o + obuf + 2056; o - 56; o].
Definition unw_front (L : sst) (rgs : list region) (spl : lin) (lo hi : Z) (x1 x2 : positive) : sst :=
  SST 0x82908 (s_regs L) rgs [FMod spl 4 0; FRange spl lo hi; FRange (lvar x1) 4294901759 4294967295; FRange (lvar x2) 0 7] (s_next L) RNone.

Definition apost_unw0 (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let SPl := rget (s_regs S) (rk 2) in let spl := rget (s_regs S) (rk 12) in let BUFl := rget (s_regs S) (rk 10) in
  obool (Z.eqb (s_pc S) 0x82908 && rsv_none_b (s_resv S))%bool (
  obind (find_stk (s_rgs S) spl) (fun stk =>
  obind (find_ro (s_rgs S)) (fun ro =>
  obind (find_rg got_b (s_rgs S)) (fun got =>
  obind (find_rg psz_rb (s_rgs S)) (fun psz =>
  obind (nth_error (s_rgs S) stk) (fun R =>
  obind (lin_off spl (rg_base R)) (fun o =>
  obind (lin_off SPl spl) (fun osp0 =>
  obind (lin_off BUFl spl) (fun obuf0 =>
  obind (top_vars (rget (s_regs S) (rk 13))) (fun xt =>
  let osp := osp0 - two64 in let obuf := obuf0 - two64 in
  obind (carve_of S stk (unw_cuts o osp obuf)
           [Datatypes.S stk; (stk + 2)%nat; (stk + 4)%nat; (stk + 5)%nat; (stk + 6)%nat; shift_ix ro stk 9; shift_ix got stk 9; shift_ix psz stk 9; (stk + 8)%nat]) (fun cv =>
  let lohi := irange (s_facts S) spl in
  let L := unw_front S (firstn 9 (carve_rgs cv)) spl (fst lohi) (snd lohi) (fst xt) (snd xt) in
  let Sp := put_rest S (skipn 9 (carve_rgs cv)) in
  obool (perm_ix_ok (length (cv_split cv)) (cv_ix cv) && forallb (fact_implied (s_facts S)) (s_facts L) && state_wf L &&
         unw_shape0_b L spl osp obuf (osp - 1024) 960 (obuf + 256) 1800 0 1 2 3 4 5 6 7 (fst xt) (snd xt) (fst lohi) (snd lohi) &&
         (uch1_ok0 L spl (fst lohi) || uchk 31 (s_facts (mrg L Sp)) (s_rgs (mrg L Sp)) spl))%bool (
  let X := mrg (unw_res L [1%nat; 2%nat; 3%nat] 2) Sp in
  let ixb := inv_ix (cv_ix cv) (length (cv_split cv)) in
  obool (perm_ix_ok (length (s_rgs X)) ixb) (
  obind (steps_rgs (s_next X) (s_facts X) (List.map (fun t => nth t (s_rgs X) (RG lc0 lc0 RW TEmpty)) ixb) (List.repeat (RMergeCC stk) 9)) (fun l'' =>
  Some (with_rgs X l'', M, a))))))))))))))).

Lemma apost_unw0_unf : forall S M a,
  (let SPl := rget (s_regs S) (rk 2) in let spl := rget (s_regs S) (rk 12) in let BUFl := rget (s_regs S) (rk 10) in
  obool (Z.eqb (s_pc S) 0x82908 && rsv_none_b (s_resv S))%bool (
  obind (find_stk (s_rgs S) spl) (fun stk =>
  obind (find_ro (s_rgs S)) (fun ro =>
  obind (find_rg got_b (s_rgs S)) (fun got =>
  obind (find_rg psz_rb (s_rgs S)) (fun psz =>
  obind (nth_error (s_rgs S) stk) (fun R =>
  obind (lin_off spl (rg_base R)) (fun o =>
  obind (lin_off SPl spl) (fun osp0 =>
  obind (lin_off BUFl spl) (fun obuf0 =>
  obind (top_vars (rget (s_regs S) (rk 13))) (fun xt =>
  let osp := osp0 - two64 in let obuf := obuf0 - two64 in
  obind (carve_of S stk (unw_cuts o osp obuf)
           [Datatypes.S stk; (stk + 2)%nat; (stk + 4)%nat; (stk + 5)%nat; (stk + 6)%nat; shift_ix ro stk 9; shift_ix got stk 9; shift_ix psz stk 9; (stk + 8)%nat]) (fun cv =>
  let lohi := irange (s_facts S) spl in
  let L := unw_front S (firstn 9 (carve_rgs cv)) spl (fst lohi) (snd lohi) (fst xt) (snd xt) in
  let Sp := put_rest S (skipn 9 (carve_rgs cv)) in
  obool (perm_ix_ok (length (cv_split cv)) (cv_ix cv) && forallb (fact_implied (s_facts S)) (s_facts L) && state_wf L &&
         unw_shape0_b L spl osp obuf (osp - 1024) 960 (obuf + 256) 1800 0 1 2 3 4 5 6 7 (fst xt) (snd xt) (fst lohi) (snd lohi) &&
         (uch1_ok0 L spl (fst lohi) || uchk 31 (s_facts (mrg L Sp)) (s_rgs (mrg L Sp)) spl))%bool (
  let X := mrg (unw_res L [1%nat; 2%nat; 3%nat] 2) Sp in
  let ixb := inv_ix (cv_ix cv) (length (cv_split cv)) in
  obool (perm_ix_ok (length (s_rgs X)) ixb) (
  obind (steps_rgs (s_next X) (s_facts X) (List.map (fun t => nth t (s_rgs X) (RG lc0 lc0 RW TEmpty)) ixb) (List.repeat (RMergeCC stk) 9)) (fun l'' =>
  Some (with_rgs X l'', M, a)))))))))))))))) = apost_unw0 S M a.
Proof. intros. exact eq_refl. Qed.

Section UnwNode.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.

#[using="Hwx"] Theorem unw_node0 : forall S M a S' M' a', apost_unw0 S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  rewrite <- apost_unw0_unf in H. cbv zeta in H.
  apply obool_some in H as (Hon & H). apply andb_prop in Hon as [Hpc Hrs]. apply Z.eqb_eq in Hpc. apply rsv_none_b_sound in Hrs.
  apply obind_some in H as (stk & Hstk & H). cbv beta in H.
  apply obind_some in H as (ro & Hro & H). cbv beta in H.
  apply obind_some in H as (got & Hgot & H). cbv beta in H.
  apply obind_some in H as (psz & Hpsz & H). cbv beta in H.
  apply obind_some in H as (R & HR & H). cbv beta in H.
  apply obind_some in H as (o & Ho & H). cbv beta in H.
  apply obind_some in H as (osp0 & Hosp & H). cbv beta in H.
  apply obind_some in H as (obuf0 & Hobuf & H). cbv beta in H.
  apply obind_some in H as (xt & Hxt & H). cbv beta in H.
  apply obind_some in H as (cv & Hcv & H). cbv beta in H.
  apply obool_some in H as (Hchk & H).
  apply obool_some in H as (Hpb & H).
  apply obind_some in H as (l'' & Hsteps & H). cbv beta in H. injection H as <- <- <-.
  apply andb_prop in Hchk as [Hchk Huch]. apply andb_prop in Hchk as [Hchk Hus]. apply andb_prop in Hchk as [Hchk HwL]. apply andb_prop in Hchk as [Hperm Hfi].
  set (spl := rget (s_regs S) (rk 12)) in *.
  set (lohi := irange (s_facts S) spl) in *.
  set (L := unw_front S (firstn 9 (carve_rgs cv)) spl (fst lohi) (snd lohi) (fst xt) (snd xt)) in *.
  set (Sp := put_rest S (skipn 9 (carve_rgs cv))) in *.
  pose proof (den_carve ASEGS LIMIT model0 mem0 E S M ms model _ _ _ cv Hd Hcv Hperm) as Hd1.
  assert (Hd2 : DEN ASEGS LIMIT model0 mem0 E (mrg L Sp) M ms model).
  { pose proof (den_facts ASEGS LIMIT model0 mem0 E _ M ms model (s_facts L ++ s_facts S) Hd1) as X.
    assert (EQ : with_facts (with_rgs S (carve_rgs cv)) (s_facts L ++ s_facts S) = mrg L Sp).
    { destruct S as [pc0 rg0 rgs0 fs0 nx0 rv0]. cbn [s_pc s_resv] in Hpc, Hrs. subst pc0 rv0.
      unfold with_facts, with_rgs, mrg, L, Sp, unw_front, put_rest. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. rewrite firstn_skipn. reflexivity. }
    rewrite <- EQ. apply X. intros E' _ HF. apply Forall_app. split; [|exact HF].
    rewrite Forall_forall. rewrite forallb_forall in Hfi. intros f Hf. exact (fact_implied_ok E' _ f HF (Hfi f Hf)). }
  set (osp := osp0 - two64) in *. set (obuf := obuf0 - two64) in *.
  pose proof (unw_shape0_b_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hus) as US.
  apply (den_unw_app0 cfg LIMIT model0 Hwx mem0 L Sp E M ms model T spl osp obuf (osp - 1024) 960 (obuf + 256) 1800 0 1 2 3 4 5 6 7
           (fst xt) (snd xt) (fst lohi) (snd lohi) Hd2 HwL US).
  - pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd2)) as Hd0.
    set (msr := restrict (Hof E M model) ms) in *.
    apply orb_prop in Huch as [Huch|Huch].
    2: { (* [comment removed for export] *)
         assert (HV1 : 4294901759 <= bv_unsigned (E (fst xt)) <= 4294967295).
         { pose proof (mrg_fact0 E L Sp msr _ Hd0 (u0_ft1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ US)) as X; cbn [fact_ok] in X; rewrite lden_lvar in X; exact X. }
         assert (HV2 : 0 <= bv_unsigned (E (snd xt)) <= 7).
         { pose proof (mrg_fact0 E L Sp msr _ Hd0 (u0_ft2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ US)) as X; cbn [fact_ok] in X; rewrite lden_lvar in X; exact X. }
         destruct Hd0 as (_ & _ & _ & _ & Hrgs & _ & HF & _).
         apply (uchk_sound E (ms_mem msr) _ _ (4096 + 32768 * bv_unsigned (E (fst xt)) + 4096 * bv_unsigned (E (snd xt))) HF Hrgs ltac:(lia) 31 spl Huch). }
    destruct (uch1_ok0_sound L spl (fst lohi) Huch) as (c & b0 & H8 & H40 & Hb & Hle & Hj).
    pose proof (mrg_rg0 E L Sp msr 8 _ Hd0 H8) as R8.
    assert (Hrg : fst lohi <= bv_unsigned (lden E spl) <= snd lohi) by (pose proof (mrg_fact0 E L Sp msr _ Hd0 (u0_frg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ US)) as X; cbn [fact_ok] in X; exact X).
    assert (HV1 : 4294901759 <= bv_unsigned (E (fst xt)) <= 4294967295).
    { pose proof (mrg_fact0 E L Sp msr _ Hd0 (u0_ft1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ US)) as X; cbn [fact_ok] in X; rewrite lden_lvar in X; exact X. }
    assert (HV2 : 0 <= bv_unsigned (E (snd xt)) <= 7).
    { pose proof (mrg_fact0 E L Sp msr _ Hd0 (u0_ft2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ US)) as X; cbn [fact_ok] in X; rewrite lden_lvar in X; exact X. }
    destruct (u0_num _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ US) as (N1 & N2 & _).
    apply (unw_uch10 (ms_mem msr) E spl (bv_unsigned (lden E spl)) _ c b0 R8 eq_refl); try assumption; lia.
  - intros E' ms' model' Hd' Ha'.
    pose proof (den_uncarve ASEGS LIMIT model0 mem0 E' _ M ms' model' _ _ l'' Hd' Hpb Hsteps) as Hd3.
    apply (Hk E' mem0 ms' model' Ha').
    + intros q Hq w Hw. reflexivity.
    + exact Hd3.
    + apply (HA_agree (s_next S) E E' M a mem0); [exact (dn_wf _ _ _ _ _ _ _ _ _ Hd) | exact Haw | exact Ha' | exact HHA].
Qed.

(* [comment removed for export] *)
Definition apost_unw (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) := apost_unw0 (with_facts S (s_facts S ++ [sp_fact M])) M a.
#[using="Hwx"] Theorem unw_node : forall S M a S' M' a', apost_unw S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_unw in H.
  exact (unw_node0 _ M a S' M' a' H mem0 E ms model T (den_sp_fact ASEGS LIMIT model0 mem0 E S M ms model Hd) Haw HHA Hk).
Qed.
End UnwNode.
(* [comment removed for export] *)
