(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDenW AcCarve AcSteps AcEntry AcMALp AcHand AcHand0 AcUnwApp AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen AcAst AcPri AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarveP AcMALlib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint find_stk_acc (rgs : list region) (x : lin) (i : nat) : option nat :=
  match rgs with
  | [] => None
  | RG b z RW c :: r => match lin_off x b, is_const z with
                        | Some o, Some zz => if (Z.ltb 0 o && Z.leb o zz)%bool then Some i else find_stk_acc r x (Datatypes.S i)
                        | _, _ => find_stk_acc r x (Datatypes.S i)
                        end
  | _ :: r => find_stk_acc r x (Datatypes.S i)
  end.
Definition find_stk (rgs : list region) (x : lin) : option nat := find_stk_acc rgs x O.
Fixpoint find_ro_acc (rgs : list region) (i : nat) : option nat :=
  match rgs with [] => None | R :: r => if ro_b (Some R) then Some i else find_ro_acc r (Datatypes.S i) end.
Definition find_ro (rgs : list region) : option nat := find_ro_acc rgs O.
Definition var_of (l : lin) : option positive := match l with LIN 0 [(x, 1)] => Some x | _ => None end.
Lemma var_of_sound : forall l x, var_of l = Some x -> l = lvar x.
Proof.
  intros [c t] x H. unfold var_of in H. destruct c as [|q|q]; try discriminate. destruct t as [|[y k] t]; try discriminate.
  destruct k as [|p|p]; try discriminate. destruct p; try discriminate. destruct t; try discriminate. injection H as <-. reflexivity.
Qed.

(* [comment removed for export] *)
Definition put_shapeG_b (L : sst) (spl : lin) (otr : Z) (xsz : positive) (lo hi : Z) : bool :=
  let R := s_regs L in let G := s_rgs L in let F := s_facts L in
  (Z.eqb (s_pc L) 0x81f88 && rsv_none_b (s_resv L) &&
   lin_eqb (rget R (rk 2)) spl && lin_eqb (rget R (rk 10)) (laddc spl otr) && lin_eqb (rget R (rk 11)) (lvar xsz) &&
   rg_hdr_b (nth_error G 0) (laddc spl (-2048)) (lconst 2048) RW && rg_hdr_b (nth_error G 1) (laddc spl otr) (lconst 240) RW &&
   ro_b (nth_error G 2) &&
   infact_b (FRange (lvar xsz) 1 30) F && infact_b (FMod spl 4 0) F && infact_b (FRange spl lo hi) F &&
   Z.leb (2^46 + 8192) lo && Z.leb (hi + otr + 240) (2^47) && Z.leb 0 otr && Z.leb otr 8192)%bool.
Lemma put_shapeG_b_sound : forall L spl otr xsz lo hi, put_shapeG_b L spl otr xsz lo hi = true -> put_shapeG L spl otr xsz 0 1 2 lo hi.
Proof.
  intros L spl otr xsz lo hi H. unfold put_shapeG_b in H.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
                      | H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H
                      | H : rsv_none_b _ = true |- _ => apply rsv_none_b_sound in H | H : infact_b _ _ = true |- _ => apply infact_b_sound in H
                      | H : rg_hdr_b _ _ _ _ = true |- _ => apply rg_hdr_b_sound in H
                      | H : ro_b _ = true |- _ => apply ro_b_sound in H end.
  constructor; try assumption. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition ro_split (ro stk : nat) (np : nat) : nat := if Nat.ltb ro stk then ro else (ro + np)%nat.
Definition put_front (L : sst) (spl : lin) (lo hi : Z) (x : positive) (rgs : list region) : sst :=
  SST 0x81f88 (s_regs L) rgs [FMod spl 4 0; FRange spl lo hi; FRange (lvar x) 1 30] (s_next L) RNone.
Definition put_rest (S : sst) (rgs : list region) : sst := SST 0x81f88 (s_regs S) rgs (s_facts S) (s_next S) RNone.

Definition apost_put0 (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let SPl := rget (s_regs S) (rk 2) in let TRl := rget (s_regs S) (rk 10) in
  obool (a_on a && Z.ltb (snd (irange (s_facts S) (a_nl a))) 33000 && Z.eqb (s_pc S) 0x81f88 && rsv_none_b (s_resv S))%bool (
  obind (find_stk (s_rgs S) SPl) (fun stk =>
  obind (find_ro (s_rgs S)) (fun ro =>
  obind (nth_error (s_rgs S) stk) (fun R =>
  obind (lin_off SPl (rg_base R)) (fun o =>
  obind (lin_off TRl SPl) (fun otr =>
  obind (var_of (rget (s_regs S) (rk 11))) (fun x =>
  obind (carve_of S stk [o - 2048; o; o + otr; o + otr + 240] [Datatypes.S stk; Datatypes.S (Datatypes.S (Datatypes.S stk)); ro_split ro stk 4]) (fun cv =>
  let lohi := irange (s_facts S) SPl in
  let L := put_front S SPl (fst lohi) (snd lohi) x (firstn 3 (carve_rgs cv)) in
  let Sp := put_rest S (skipn 3 (carve_rgs cv)) in
  obool (perm_ix_ok (length (cv_split cv)) (cv_ix cv) && forallb (fact_implied (s_facts S)) (s_facts L) && state_wf L &&
         put_shapeG_b L SPl otr x (fst lohi) (snd lohi) && dep_ok M a (mrg L Sp) && band_ok (s_facts S) M SPl)%bool (
  let X := mrg (hand_post L 0x821fc KALLk [0%nat]) Sp in
  let ixb := inv_ix (cv_ix cv) (length (cv_split cv)) in
  obool (perm_ix_ok (length (s_rgs X)) ixb) (
  obind (steps_rgs (s_next X) (s_facts X) (List.map (fun t => nth t (s_rgs X) (RG lc0 lc0 RW TEmpty)) ixb) (List.repeat (RMergeCC stk) 4)) (fun l'' =>
  Some (with_rgs X l'', M, AST (a_on a) (a_rgs a) (a_fcts a) (a_own a) (a_dep a) (laddc (a_nl a) 1) (a_live a) (a_pri a))))))))))))).
Lemma apost_put0_unf : forall S M a,
  (let SPl := rget (s_regs S) (rk 2) in let TRl := rget (s_regs S) (rk 10) in
  obool (a_on a && Z.ltb (snd (irange (s_facts S) (a_nl a))) 33000 && Z.eqb (s_pc S) 0x81f88 && rsv_none_b (s_resv S))%bool (
  obind (find_stk (s_rgs S) SPl) (fun stk =>
  obind (find_ro (s_rgs S)) (fun ro =>
  obind (nth_error (s_rgs S) stk) (fun R =>
  obind (lin_off SPl (rg_base R)) (fun o =>
  obind (lin_off TRl SPl) (fun otr =>
  obind (var_of (rget (s_regs S) (rk 11))) (fun x =>
  obind (carve_of S stk [o - 2048; o; o + otr; o + otr + 240] [Datatypes.S stk; Datatypes.S (Datatypes.S (Datatypes.S stk)); ro_split ro stk 4]) (fun cv =>
  let lohi := irange (s_facts S) SPl in
  let L := put_front S SPl (fst lohi) (snd lohi) x (firstn 3 (carve_rgs cv)) in
  let Sp := put_rest S (skipn 3 (carve_rgs cv)) in
  obool (perm_ix_ok (length (cv_split cv)) (cv_ix cv) && forallb (fact_implied (s_facts S)) (s_facts L) && state_wf L &&
         put_shapeG_b L SPl otr x (fst lohi) (snd lohi) && dep_ok M a (mrg L Sp) && band_ok (s_facts S) M SPl)%bool (
  let X := mrg (hand_post L 0x821fc KALLk [0%nat]) Sp in
  let ixb := inv_ix (cv_ix cv) (length (cv_split cv)) in
  obool (perm_ix_ok (length (s_rgs X)) ixb) (
  obind (steps_rgs (s_next X) (s_facts X) (List.map (fun t => nth t (s_rgs X) (RG lc0 lc0 RW TEmpty)) ixb) (List.repeat (RMergeCC stk) 4)) (fun l'' =>
  Some (with_rgs X l'', M, AST (a_on a) (a_rgs a) (a_fcts a) (a_own a) (a_dep a) (laddc (a_nl a) 1) (a_live a) (a_pri a)))))))))))))) = apost_put0 S M a.
Proof. intros. exact eq_refl. Qed.

Section PutNode.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.

#[using="Hwx"] Theorem put_node0 : forall S M a S' M' a', apost_put0 S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  rewrite <- apost_put0_unf in H. cbv zeta in H.
  apply obool_some in H as (Hon & H).
  apply andb_prop in Hon as [Hon Hrs]. apply andb_prop in Hon as [Hon Hpc]. apply andb_prop in Hon as [Hon Hnl].
  apply Z.ltb_lt in Hnl. apply Z.eqb_eq in Hpc. apply rsv_none_b_sound in Hrs.
  apply obind_some in H as (stk & Hstk & H). cbv beta in H.
  apply obind_some in H as (ro & Hro & H). cbv beta in H.
  apply obind_some in H as (R & HR & H). cbv beta in H.
  apply obind_some in H as (o & Ho & H). cbv beta in H.
  apply obind_some in H as (otr & Hotr & H). cbv beta in H.
  apply obind_some in H as (x & Hx & H). cbv beta in H.
  apply obind_some in H as (cv & Hcv & H). cbv beta in H.
  apply obool_some in H as (Hchk & H).
  apply obool_some in H as (Hpb & H).
  apply obind_some in H as (l'' & Hsteps & H). cbv beta in H. injection H as <- <- <-.
  apply andb_prop in Hchk as [Hchk Hband]. apply andb_prop in Hchk as [Hchk Hdep]. apply andb_prop in Hchk as [Hchk Hps].
  apply andb_prop in Hchk as [Hchk HwL]. apply andb_prop in Hchk as [Hperm Hfi].
  set (SPl := rget (s_regs S) (rk 2)) in *.
  set (lohi := irange (s_facts S) SPl) in *.
  set (L := put_front S SPl (fst lohi) (snd lohi) x (firstn 3 (carve_rgs cv))) in *.
  set (Sp := put_rest S (skipn 3 (carve_rgs cv))) in *.
  pose proof (HHA Hon) as HA0.
  assert (Hnl' : uE E (a_nl a) < 33000).
  { pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
    pose proof (irange_sound E (s_facts S) (a_nl a) HF0) as X. unfold uE. lia. }
  (* [comment removed for export] *)
  pose proof (den_carve ASEGS LIMIT model0 mem0 E S M ms model _ _ _ cv Hd Hcv Hperm) as Hd1.
  assert (Hd2 : DEN ASEGS LIMIT model0 mem0 E (mrg L Sp) M ms model).
  { pose proof (den_facts ASEGS LIMIT model0 mem0 E _ M ms model (s_facts L ++ s_facts S) Hd1) as X.
    assert (EQ : with_facts (with_rgs S (carve_rgs cv)) (s_facts L ++ s_facts S) = mrg L Sp).
    { destruct S as [pc0 rg0 rgs0 fs0 nx0 rv0]. cbn [s_pc s_resv] in Hpc, Hrs. subst pc0 rv0.
      unfold with_facts, with_rgs, mrg, L, Sp, put_front, put_rest. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. rewrite firstn_skipn. reflexivity. }
    rewrite <- EQ. apply X. intros E' _ HF. apply Forall_app. split; [|exact HF].
    rewrite Forall_forall. rewrite forallb_forall in Hfi. intros f Hf. exact (fact_implied_ok E' _ f HF (Hfi f Hf)). }
  pose proof HA0 as HA1. destruct HA1 as [Hdep0 Hown Hownx Hhi HgD HgB Hpri0].
  destruct Hdep0 as (nd & F & st & HI & Hnd & HFr & Hnl0).
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd2) as Hwf. cbn [mrg s_next] in Hwf.
  assert (Hpw : pwf (s_next L) (a_dep a) = true).
  { unfold awf in Haw. apply andb_prop in Haw as [Haw _]. apply andb_prop in Haw as [Haw _]. apply andb_prop in Haw as [_ X]. exact X. }
  apply (den_put_appG cfg LIMIT model0 Hwx mem0 L Sp E M ms model T SPl otr x 0 1 2 (fst lohi) (snd lohi) (dD1 E a) (dB1 E a) nd F st Hd2 HwL
           (put_shapeG_b_sound _ _ _ _ _ _ Hps) HI).
  - lia.
  - lia.
  - intros y Hy Hdw. split; [exact (Hown y Hy Hdw)|]. split.
    + exact (dep_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 Hd2 HA0 Hdep y Hy Hdw).
    + exact (dep_not_frz LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 Hd2 HA0 y Hdw).
  - destruct HgD as (kD & HgD). pose proof (band_hi LIMIT model0 mem0 E _ M ms model SPl _ Hd Hband HgD) as X. unfold gsz in X. cbn [fst snd] in X. rewrite uE_lc in X by (unfold two64; lia). unfold dD1. lia.
  - destruct HgB as (kB & HgB). pose proof (band_hi LIMIT model0 mem0 E _ M ms model SPl _ Hd Hband HgB) as X. unfold gsz in X. cbn [fst snd] in X. rewrite uE_lc in X by (unfold two64; lia). unfold dB1. lia.
  - intros E' ms' model' Hd' Ha' Hfz' (nd' & F' & st' & HI' & Hnd' & HF') Hfr'.
    (* [comment removed for export] *)
    set (hyb := hyb_dep (dD1 E a) (dB1 E a) (ms_mem ms') mem0).
    assert (HwfM : sm_wf (s_next L) M = true) by exact Hwf.
    assert (HbwS : bases_wf (s_next L) (s_rgs (mrg L Sp)) = true) by exact (dn_bases _ _ _ _ _ _ _ _ _ Hd2).
    set (Lh := hand_post L 0x821fc KALLk [0%nat]) in *.
    assert (Hsh : shape (s_rgs (mrg Lh Sp)) = shape (s_rgs (mrg L Sp))).
    { cbn [mrg s_rgs]. unfold Lh, hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
      pose proof (empty_at_shape [0%nat] (s_rgs L) 0) as Hs. unfold shape in Hs. exact Hs. }
    pose proof (dn_own _ _ _ _ _ _ _ _ _ Hd2) as Hown2.
    assert (Hfrzn : forall w, frz_pt E M w -> hyb (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw. unfold hyb, hyb_dep.
      destruct (downed_b (dD1 E a) (dB1 E a) (bv_unsigned (Z_to_bv 64 w))) eqn:Eb; [|reflexivity]. exfalso.
      apply downed_b_spec in Eb. destruct Hw as (q & Hq & Hqw).
      pose proof (dn_frz _ _ _ _ _ _ _ _ _ Hd2 q Hq w Hqw) as (Htop & _ & _).
      pose proof (alloc_top_lo _ (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd2))) as Hlo.
      rewrite u_small64 in Eb by (unfold two64; lia).
      exact (dep_not_frz LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 Hd2 HA0 w Eb (ex_intro _ q (conj Hq Hqw))). }
    assert (HD3 : DEN ASEGS LIMIT model0 hyb E' (mrg Lh Sp) M ms' model').
    { apply (den_snap ASEGS LIMIT model0 (ms_mem ms') hyb E' _ M ms' model' Hd').
      - intros w Hw. pose proof (proj1 (frz_pt_agree (s_next L) E E' M w HwfM Ha') Hw) as Hw0.
        rewrite (Hfrzn w Hw0). symmetry. exact (Hfz' w Hw0).
      - intros w Hw Hout. unfold hyb, hyb_dep.
        destruct (downed_b (dD1 E a) (dB1 E a) (bv_unsigned (Z_to_bv 64 w))) eqn:Eb; [reflexivity|].
        assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next L) E E' M w HwfM Ha') Hw).
        assert (Hout0 : outside E (s_rgs (mrg L Sp)) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E' _ _ _ HbwS Ha' Hsh Hout).
        destruct Hw0 as (q & Hq & Hqw). destruct (Hown2 q Hq w Hqw) as [Hv Hm].
        rewrite <- (Hm Hout0). symmetry. rewrite <- (wa_u (Z_to_bv 64 w)).
        apply Hfr'; [apply bv_unsigned_in_range | rewrite wa_u; exact Hv | | intros Hdw; apply downed_b_spec in Hdw; congruence].
        (* [comment removed for export] *)
        destruct (put_shapeG_b_sound _ _ _ _ _ _ Hps) as [_ _ _ _ _ (c1 & Pa1) _ _ _ _ _ _].
        unfold outside in Hout0. rewrite Forall_forall in Hout0. cbn [mrg s_rgs] in Hout0.
        specialize (Hout0 _ ltac:(apply in_or_app; left; exact (nth_error_In _ _ Pa1))). cbn [rg_base] in Hout0.
        unfold rsz in Hout0. cbn [rg_size] in Hout0. rewrite lden_lconst, (u_small64 2048) in Hout0 by (unfold two64; lia).
        pose proof (bv_unsigned_in_range _ (lden E SPl)) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with two64 in Rsp.
        rewrite lden_laddc in Hout0.
        destruct (put_shapeG_b_sound _ _ _ _ _ _ Hps) as [_ _ _ _ _ _ _ _ _ _ Pfrg Prng].
        pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd2)) as Hd20.
        pose proof (mrg_fact0 E L Sp _ _ Hd20 Pfrg) as Xr. cbn [fact_ok] in Xr.
        clear - Hout0 Rsp Xr Prng. rewrite (u_small64 (bv_unsigned (lden E SPl) + -2048)) in Hout0 by (unfold two64 in *; lia). lia. }
    pose proof (den_uncarve ASEGS LIMIT model0 hyb E' _ M ms' model' _ _ l'' HD3 Hpb Hsteps) as Hd3.
    apply (Hk E' hyb ms' model').
    + exact Ha'.
    + intros q Hq w Hw. apply Hfrzn. exists q. split; [exact Hq | exact Hw].
    + exact Hd3.
    + intros _. apply (HA_put (s_next L) E E' M a mem0 hyb nd' F' st' HA0 Hwf Haw Ha'); [| lia | lia | lia |].
      * apply (INV_D_frame (ms_mem ms')); [exact HI'|]. intros y Hy Hdw. unfold hyb, hyb_dep.
        rewrite u_small64 by (unfold two64; lia). rewrite (proj2 (downed_b_spec _ _ y) Hdw). reflexivity.
      * intros Hne y Hpf. unfold hyb, hyb_dep.
        pose proof (pri_not_downed LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 Hd2 HA0 Hne y Hpf) as Hnd0.
        assert (Hy64 : 0 <= y < two64).
        { pose proof (pri_foot_rng E a mem0 (po_inv _ _ _ _ (Hpri0 Hne)) y Hpf). unfold two64. lia. }
        rewrite u_small64 by exact Hy64.
        destruct (downed_b (dD1 E a) (dB1 E a) y) eqn:Eb; [exfalso; apply Hnd0; apply downed_b_spec; exact Eb | reflexivity].
Qed.


(* [comment removed for export] *)
Definition apost_put (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) := apost_put0 (with_facts S (s_facts S ++ [sp_fact M])) M a.
#[using="Hwx"] Theorem put_node : forall S M a S' M' a', apost_put S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_put in H.
  exact (put_node0 _ M a S' M' a' H mem0 E ms model T (den_sp_fact ASEGS LIMIT model0 mem0 E S M ms model Hd) Haw HHA Hk).
Qed.
End PutNode.
