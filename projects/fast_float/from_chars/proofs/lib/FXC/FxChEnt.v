(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.

Module FxDropOwn.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChSep FxChAdd FxChain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Drop.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_drop_own : forall E S M ms model (f : region -> bool),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall p, In p (sm_own M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) ->
     w < two64 /\ forall R, In R (s_rgs S) -> f R = true -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  (forall R, In R (s_rgs S) -> f R = true -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
     in_zr (sm_zr M) w = true -> ms_mem ms (Z_to_bv 64 w) = Some (Z_to_bv 8 0)) ->
  DEN segs LIMIT model0 mem0 E (drop_post S f) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model f Hd Hno Hf.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; try assumption.
  - intros E'' Ha''. cbn [drop_post s_next] in Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    unfold sden0, drop_post. cbn [s_pc s_regs s_rgs s_facts s_resv]. repeat split; try assumption.
    + apply Forall_forall. intros R HR. apply filter_In in HR as [HR _]. rewrite Forall_forall in H5. exact (H5 R HR).
    + exact (rgs_disj_filter E'' _ _ H6).
  - unfold bases_wf in *. cbn [drop_post s_rgs s_next]. rewrite forallb_forall in *. intros R HR. apply filter_In in HR as [HR _]. exact (Hbw R HR).
  - intros w Hw Hout Hnow Hnb. cbn [drop_post s_rgs] in Hout.
    destruct (Z_lt_le_dec w 0) as [Hneg|Hnn].
    + pose proof (Hzrsh w Hw) as Hs. unfold in_shadow, SH_LO in Hs. apply andb_prop in Hs as [Hs _]. apply Z.leb_le in Hs. lia.
    + (* [comment removed for export] *)
      destruct (existsb (fun R => f R && (Z.leb (uE E (rg_base R)) w && Z.ltb w (uE E (rg_base R) + rsz E R)))%bool (s_rgs S)) eqn:He.
      * apply existsb_exists in He as (R & HR & Hc). apply andb_prop in Hc as [HfR Hc]. apply andb_prop in Hc as [C1 C2].
        apply Z.leb_le in C1. apply Z.ltb_lt in C2. exact (Hf R HR HfR w ltac:(lia) Hw).
      * apply (Hzr w Hw); [|exact Hnow|exact Hnb]. unfold outside in *. apply Forall_forall. intros R HR. rewrite Forall_forall in Hout.
        destruct (f R) eqn:HfR.
        -- assert (Hc : (f R && (Z.leb (uE E (rg_base R)) w && Z.ltb w (uE E (rg_base R) + rsz E R)))%bool = false)
             by (apply not_true_iff_false; intros Hc'; rewrite (proj2 (existsb_exists _ _) (ex_intro _ R (conj HR Hc'))) in He; discriminate).
           rewrite HfR in Hc. cbn [andb] in Hc. pose proof (Hzrsh w Hw) as Hs. unfold in_shadow, SH_HI in Hs.
           apply andb_prop in Hs as [_ Hs]. apply Z.ltb_lt in Hs. rewrite fg64 by (unfold two64; lia).
           apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc; left; unfold uE in Hc; exact Hc | apply Z.ltb_ge in Hc; right; unfold uE in Hc; exact Hc].
        -- apply Hout. apply filter_In. split; [exact HR | rewrite HfR; reflexivity].
  - rewrite Forall_forall in *. intros R HR. apply filter_In in HR as [HR _]. exact (Hrl R HR).
  - apply (frz_keep mem0 E E S (drop_post S f) M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho. unfold outside in *. cbn [drop_post s_rgs]. apply Forall_forall. intros R HR. apply filter_In in HR as [HR _].
      rewrite Forall_forall in Ho. exact (Ho R HR).
    + intros w _ _. reflexivity.
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho. apply Hm.
    destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG & _ & _ & _).
    destruct (Hno p Hp w Hw) as [Hw64 X].
    pose proof (uE_range E (fst p)) as R1.
    unfold outside in *. rewrite Forall_forall in *. intros R HR.
    destruct (f R) eqn:HfR.
    + destruct (HG R HR) as (Hrs & Hrw & _). specialize (X R HR HfR).
      destruct (Z_lt_le_dec w (uE E (rg_base R))) as [Y|Y].
      * left. rewrite fg64' by (unfold two64 in *; lia). unfold uE in Y. exact Y.
      * destruct (Z_lt_le_dec w (uE E (rg_base R) + rsz E R)) as [Y2|Y2]; [exfalso; apply X; split; assumption|].
        right. rewrite fg64' by (unfold two64 in *; lia). unfold uE in Y2. exact Y2.
    + apply Ho. apply filter_In. split; [exact HR | rewrite HfR; reflexivity].
Qed.

(* [comment removed for export] *)
Definition own_below (fs : list fact) (M : smodel) (p : lin * lin) : bool :=
  match is_const (fst p), is_const (snd p) with
  | Some b, Some n => (Z.leb 0 n && Z.leb (b + n) 0x7fff7f800000)%bool
  | _, Some n => existsb (fun g => (lin_eqb (fst (fst g)) (fst p) && Z.leb 0 n && Z.leb n (gsz_lo fs g))%bool) (sm_maps M)
  | _, None => false
  end.
Definition above_sp (fs : list fact) (M : smodel) (R : region) : bool :=
  let '(lo, hi) := irange fs (lsub (rg_base R) (sm_sp M)) in (Z.leb 0 lo && Z.leb hi (2 ^ 40))%bool.
Definition drop_own_ok (S : sst) (M : smodel) (f : region -> bool) : bool :=
  (forallb (own_below (s_facts S) M) (sm_own M) && forallb (fun R => negb (f R) || above_sp (s_facts S) M R) (s_rgs S))%bool.

#[using="Type"] Theorem drop_own_sound : forall E S M ms model f, DEN segs LIMIT model0 mem0 E S M ms model -> drop_own_ok S M f = true ->
  forall p, In p (sm_own M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) ->
     w < two64 /\ forall R, In R (s_rgs S) -> f R = true -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model f Hd Hok p Hp w Hw. unfold drop_own_ok in Hok. apply andb_prop in Hok as [Ho Hr].
  rewrite forallb_forall in Ho, Hr.
  pose proof (dn_spok _ _ _ _ _ _ _ _ _ Hd) as [Hspo Hsph]. pose proof (alloc_top_lo _ Hspo) as Hatl.
  pose proof (dn_sp _ _ _ _ _ _ _ _ _ Hd) as HspE.
  assert (Hat : alloc_top (m_vmmaps model) = uE E (sm_sp M) - 8388608) by (unfold alloc_top, stack_max_size, uE; rewrite HspE; reflexivity).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _).
  (* [comment removed for export] *)
  assert (Hlow : w < alloc_top (m_vmmaps model)).
  { pose proof (Ho p Hp) as Hb. unfold own_below in Hb.
    destruct (is_const (fst p)) as [b|] eqn:Hcb; destruct (is_const (snd p)) as [n|] eqn:Hcn; try discriminate.
    - apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
      destruct (is_const_sound E _ b Hcb) as [Vb Rb]. destruct (is_const_sound E _ n Hcn) as [Vn Rn].
      unfold uE in Hw. rewrite Vb, Vn, !fg64' in Hw by assumption. lia.
    - apply existsb_exists in Hb as (g & Hg & Hc). apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H2].
      apply lin_eqb_eq in Hc. apply Z.leb_le in H2, H3.
      destruct (is_const_sound E _ n Hcn) as [Vn Rn].
      pose proof (dn_gtop _ _ _ _ _ _ _ _ _ Hd) as Hgt. rewrite Forall_forall in Hgt. specialize (Hgt g Hg). rewrite Hc in Hgt.
      pose proof (gsz_bounds E (s_facts S) g HF) as Gb.
      unfold uE in Hw. rewrite Vn, fg64' in Hw by assumption. unfold uE in Hgt. lia. }
  pose proof (uE_range E (sm_sp M)) as Rsp. split; [unfold two64 in *; lia|].
  intros R HR HfR Hin. specialize (Hr R HR). rewrite HfR in Hr. cbn [negb orb] in Hr. unfold above_sp in Hr.
  destruct (irange (s_facts S) (lsub (rg_base R) (sm_sp M))) as [lo hi] eqn:Hir.
  apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1, H2.
  pose proof (irange_sound E (s_facts S) (lsub (rg_base R) (sm_sp M)) HF) as Rd. rewrite Hir in Rd. cbn [fst snd] in Rd.
  fold (uE E (lsub (rg_base R) (sm_sp M))) in Rd.
  pose proof (uE_range E (rg_base R)). pose proof (uE_range E (sm_sp M)).
  unfold sp_window_hi in Hsph. rewrite HspE in Hsph. fold (uE E (sm_sp M)) in Hsph.
  destruct (small_diff E (rg_base R) (sm_sp M) lo hi Rd) as [[Hl He]|[Hl He]]; unfold two64 in *; lia.
Qed.
End Drop.
End FxDropOwn.

Module FxPlaceE.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep FxChain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition P47 : Z := 0x800000000000.
(* [comment removed for export] *)
Definition cst_at (cur : Z) (g : lin * lin * gkind) : bool :=
  if is_mark g then false else
  match is_const (fst (fst g)), is_const (snd (fst g)) with
  | Some b, Some z => (Z.eqb b cur && Z.ltb 0 z)%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Fixpoint sh_chain (gs : list (lin * lin * gkind)) (cur hi : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | Datatypes.S f =>
      if Z.leb hi cur then true else
      match List.find (cst_at cur) gs with
      | Some g => match is_const (snd (fst g)) with Some z => sh_chain gs (cur + z) hi f | None => false end
      | None => false
      end
  end.
(* [comment removed for export] *)
Definition off_ok (n : positive) (fs : list fact) (z o : lin) : bool :=
  let '(dlo, dhi) := irange fs (lsub z o) in
  (lwf n o && Z.leb 0 dlo && Z.ltb dhi P47 && Z.ltb (snd (irange fs o)) P47)%bool.
Definition place_facts (fs : list fact) (b : lin) (low : bool) (os : list lin) : list fact :=
  List.map (fun o => if low then FRange (ladd b o) (fst (irange fs b) + fst (irange fs o)) SH_LO else FRange (ladd b o) SH_HI P47) os.
(* [comment removed for export] *)
Definition sh_fact (fs : list fact) (b o : lin) : list fact :=
  match ldiv8 (ladd b o) with
  | Some l8 => if Z.ltb (snd (irange fs l8)) (2 ^ 60) then [FRange (laddc l8 SH_OFF) SH_OFF SH_HI] else []
  | None => []
  end.
Definition place_facts_sh (fs : list fact) (b : lin) (os : list lin) : list fact := List.flat_map (sh_fact fs b) os.
Definition place_post (S : sst) (M : smodel) (j : nat) (os : list lin) : option sst :=
  match nth_error (sm_maps M) j with
  | Some g =>
      let fs := s_facts S in let b := fst (fst g) in let z := snd (fst g) in
      let '(blo, bhi) := irange fs b in
      if (negb (is_mark g) && match is_const b with None => true | Some _ => false end && lwf (s_next S) b && lwf (s_next S) z &&
          sh_chain (sm_maps M) SH_LO SH_HI 8 && forallb (off_ok (s_next S) fs z) os)%bool
      then if Z.ltb bhi SH_HI then Some (fold_left add_fact (place_facts fs b true os) S)
           else if Z.leb SH_LO blo then Some (fold_left add_fact (place_facts fs b false os ++ place_facts_sh fs b os) S)
           else None
      else None
  | None => None
  end.

(* [comment removed for export] *)
Lemma ldiv8_wf' : forall n l l', ldiv8 l = Some l' -> lwf n l = true -> lwf n l' = true.
Proof.
  intros n [c t] l' H Hw. unfold ldiv8 in H. cbn [l_c l_t] in H.
  destruct (Z.eqb (Z.rem (sgn64 c) 8) 0 && forallb (fun '(_, k) => Z.eqb (Z.rem (sgn64 k) 8) 0) t)%bool; [|discriminate].
  injection H as <-. unfold lwf in *. cbn [l_t] in *. clear - Hw. induction t as [|[x k] t IH]; [reflexivity|].
  cbn [List.map forallb] in *. apply andb_prop in Hw as [H1 H2]. rewrite H1, (IH H2). reflexivity.
Qed.
Lemma uE_ldiv8' : forall E l l', ldiv8 l = Some l' -> 8 * uE E l' < two64 -> uE E l = 8 * uE E l'.
Proof.
  intros E l l' H Hb. pose proof (ldiv8_eqm E l l' H) as Hq. unfold eqm in Hq. unfold uE, lden in *. rewrite !u_Z_to_bv in *.
  unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with two64 in *.
  rewrite Hq. pose proof (Z.mod_pos_bound (lz E l') two64 ltac:(unfold two64; lia)) as B.
  rewrite <- (Z.mod_small (8 * (lz E l' mod two64)) two64) by lia.
  rewrite <- Zmult_mod_idemp_r. reflexivity.
Qed.

Lemma sh_chain_sound : forall gs fuel cur hi, sh_chain gs cur hi fuel = true -> forall x, cur <= x < hi ->
  exists g cb cz, In g gs /\ is_mark g = false /\ is_const (fst (fst g)) = Some cb /\ is_const (snd (fst g)) = Some cz /\ cb <= x < cb + cz.
Proof.
  intros gs fuel. induction fuel as [|f IH]; intros cur hi H x Hx; [discriminate|]. cbn [sh_chain] in H.
  destruct (Z.leb hi cur) eqn:Hle; [apply Z.leb_le in Hle; lia|].
  destruct (List.find (cst_at cur) gs) as [g|] eqn:Hf; [|discriminate].
  destruct (is_const (snd (fst g))) as [z|] eqn:Hz; [|discriminate].
  apply List.find_some in Hf as [Hin Hc]. unfold cst_at in Hc. destruct (is_mark g) eqn:Hm; [discriminate|].
  destruct (is_const (fst (fst g))) as [b|] eqn:Hb; [|discriminate]. rewrite Hz in Hc.
  apply andb_prop in Hc as [Hb1 Hz1]. apply Z.eqb_eq in Hb1. apply Z.ltb_lt in Hz1. subst b.
  destruct (Z_lt_le_dec x (cur + z)) as [Hlt|Hge].
  - exists g, cur, z. repeat split; try assumption; lia.
  - exact (IH (cur + z) hi H x ltac:(lia)).
Qed.

Section PlaceE.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Lemma den_addfacts : forall l E S M ms model, DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall f, In f l -> forall E', agree (s_next S) E E' -> fact_ok E' f) ->
  DEN segs LIMIT model0 mem0 E (fold_left add_fact l S) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction l as [|f l IH]; intros E S M ms model Hd Hl; cbn [fold_left]; [exact Hd|].
  apply IH.
  - apply (den_addfact segs LIMIT model0 mem0); [exact Hd | exact (Hl f (or_introl eq_refl))].
  - intros f' Hf' E' Ha'. exact (Hl f' (or_intror Hf') E' Ha').
Qed.

#[using="Type"] Theorem den_place : forall E S M ms model j os S', DEN segs LIMIT model0 mem0 E S M ms model -> place_post S M j os = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model j os S' Hd Hp. unfold place_post in Hp.
  destruct (nth_error (sm_maps M) j) as [g|] eqn:Hj; [|discriminate]. cbv zeta in Hp.
  set (fs := s_facts S) in *. set (b := fst (fst g)) in *. set (z := snd (fst g)) in *.
  destruct (irange fs b) as [blo bhi] eqn:Hbr.
  match type of Hp with ((if ?c then _ else _) = _) => destruct c eqn:Hc; [|discriminate] end.
  repeat match type of Hc with ((_ && _)%bool = true) => apply andb_prop in Hc as [Hc ?Hx] end.
  rename Hc into Hnm. apply negb_true_iff in Hnm.
  match goal with H : match is_const b with _ => _ end = true |- _ => rename H into Hncb end.
  match goal with H : forallb _ os = true |- _ => rename H into Hos end.
  match goal with H : sh_chain _ _ _ _ = true |- _ => rename H into Hch end.
  assert (Hwb : lwf (s_next S) b = true) by assumption. assert (Hwz : lwf (s_next S) z = true) by assumption.
  destruct (is_const b) as [cb0|] eqn:Hcb0; [discriminate|]. clear Hncb.
  pose proof (dn_sden segs LIMIT model0 mem0 E S M ms model Hd) as Hsd. destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & HF & _). fold fs in HF.
  pose proof (dn_pd segs LIMIT model0 mem0 E S M ms model Hd) as Hpd. rewrite (dn_maps segs LIMIT model0 mem0 E S M ms model Hd) in Hpd.
  pose proof (dn_gsh segs LIMIT model0 mem0 E S M ms model Hd) as Hgsh. rewrite Forall_forall in Hgsh.
  destruct (Hgsh g (nth_error_In _ _ Hj)) as (G1 & _ & _ & G4 & G5). unfold gsz in G1, G4. fold b z in G1, G4, G5.
  set (B0 := uE E b) in *. set (Z0 := uE E z) in *.
  (* [comment removed for export] *)
  assert (Hside : B0 + Z0 <= SH_LO \/ SH_HI <= B0).
  { destruct (Z_le_gt_dec (B0 + Z0) SH_LO) as [|Hgt]; [left; assumption|]. destruct (Z_le_gt_dec SH_HI B0) as [|Hlt]; [right; assumption|]. exfalso.
    set (x := Z.max B0 SH_LO).
    assert (HxA : SH_LO <= x < SH_HI) by (unfold x, SH_LO, SH_HI in *; lia). assert (HxB : B0 <= x < B0 + Z0) by (unfold x, SH_LO, SH_HI in *; lia).
    destruct (sh_chain_sound _ _ _ _ Hch x HxA) as (g' & cb & cz & Hin' & Hm' & Hb' & Hz' & Hxc).
    destruct (In_nth_error _ _ Hin') as (i & Hi).
    assert (Hij : i <> j). { intros ->. rewrite Hj in Hi. injection Hi as <-. fold b in Hb'. rewrite Hcb0 in Hb'. discriminate. }
    pose proof (pdisj_lden_nth E _ _ i j g' g Hpd Hi Hj Hij Hm' Hnm) as Hdj.
    destruct (is_const_sound E _ cb Hb') as [Hbv Hbr']. destruct (is_const_sound E _ cz Hz') as [Hzv Hzr'].
    unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hdj. cbn [fst snd] in Hdj. rewrite Hbv, Hzv in Hdj.
    rewrite (fg64' cb Hbr'), (fg64' cz Hzr') in Hdj. fold b z in Hdj. fold (uE E b) (uE E z) in Hdj. fold B0 Z0 in Hdj. lia. }
  pose proof (irange_sound E fs b HF) as Rb. rewrite Hbr in Rb. cbn [fst snd] in Rb. fold (uE E b) in Rb. fold B0 in Rb.
  (* [comment removed for export] *)
  assert (Hoff : forall o, In o os -> lwf (s_next S) o = true /\ uE E o <= Z0 /\ fst (irange fs o) <= uE E o /\ uE E (ladd b o) = B0 + uE E o).
  { intros o Ho. rewrite forallb_forall in Hos. pose proof (Hos o Ho) as H1. unfold off_ok in H1.
    destruct (irange fs (lsub z o)) as [dlo dhi] eqn:Hdr.
    repeat match type of H1 with ((_ && _)%bool = true) => apply andb_prop in H1 as [H1 ?Hy] end.
    apply Z.leb_le in Hy1. apply Z.ltb_lt in Hy0, Hy.
    pose proof (irange_sound E fs (lsub z o) HF) as Rd. rewrite Hdr in Rd. cbn [fst snd] in Rd. fold (uE E (lsub z o)) in Rd.
    pose proof (irange_sound E fs o HF) as Ro. fold (uE E o) in Ro. pose proof (uE_range E o) as RO. pose proof (uE_range E z) as RZ. fold Z0 in RZ.
    assert (Hle : uE E o <= Z0).
    { destruct (small_diff E z o dlo dhi Rd) as [[Hl He]|[Hl He]]; fold Z0 in Hl, He; [exact Hl|]. exfalso. unfold P47, two64 in *. lia. }
    split; [exact H1|]. split; [exact Hle|]. split; [lia|].
    unfold uE. rewrite lden_ladd, bv_add_unsigned. fold (uE E b) (uE E o). fold B0. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    apply Z.mod_small. unfold two64. lia. }
  assert (Hfacts : forall low, (low = true -> B0 + Z0 <= SH_LO) -> (low = false -> SH_HI <= B0) ->
            forall f, In f (place_facts fs b low os) -> forall E', agree (s_next S) E E' -> fact_ok E' f).
  { intros low Hl1 Hl2 f Hf E' Ha'. unfold place_facts in Hf. apply in_map_iff in Hf as (o & <- & Ho).
    destruct (Hoff o Ho) as (Hwo & Hle & Hlo & Hsum).
    assert (Hag : uE E' (ladd b o) = uE E (ladd b o)).
    { unfold uE. rewrite <- (lden_agree (s_next S) E E' (ladd b o) (lwf_ladd _ _ _ Hwb Hwo) Ha'). reflexivity. }
    pose proof (uE_range E o) as RO. destruct low; cbn [fact_ok]; fold (uE E' (ladd b o)); rewrite Hag, Hsum.
    - specialize (Hl1 eq_refl). rewrite Hbr. cbn [fst]. lia.
    - specialize (Hl2 eq_refl). unfold P47 in *. lia. }
  destruct (Z.ltb bhi SH_HI) eqn:Hlow.
  - injection Hp as <-. apply Z.ltb_lt in Hlow. apply den_addfacts; [exact Hd|].
    apply (Hfacts true); [intros _; destruct Hside as [|Hs]; [assumption | lia] | discriminate].
  - destruct (Z.leb SH_LO blo) eqn:Hhigh; [|discriminate]. injection Hp as <-. apply Z.leb_le in Hhigh. apply den_addfacts; [exact Hd|].
    assert (HhiB : SH_HI <= B0) by (destruct Hside as [Hs|]; [lia | assumption]).
    intros f Hf. apply in_app_or in Hf as [Hf|Hf]; [exact (Hfacts false ltac:(discriminate) (fun _ => HhiB) f Hf)|].
    intros E' Ha'. unfold place_facts_sh in Hf. apply in_flat_map in Hf as (o & Ho & Hf). unfold sh_fact in Hf.
    destruct (ldiv8 (ladd b o)) as [l8|] eqn:H8; [|destruct Hf]. destruct (Z.ltb (snd (irange fs l8)) (2 ^ 60)) eqn:H60; [|destruct Hf].
    destruct Hf as [<-|[]]. apply Z.ltb_lt in H60.
    destruct (Hoff o Ho) as (Hwo & Hle & Hlo & Hsum).
    pose proof (irange_sound E fs l8 HF) as R8. fold (uE E l8) in R8. pose proof (uE_range E l8) as RL8. pose proof (uE_range E o) as RO.
    pose proof (uE_ldiv8' E (ladd b o) l8 H8 ltac:(unfold two64; lia)) as Hq. rewrite Hsum in Hq.
    assert (Hw8 : lwf (s_next S) (laddc l8 SH_OFF) = true) by (apply lwf_laddc; exact (ldiv8_wf' _ _ _ H8 (lwf_ladd _ _ _ Hwb Hwo))).
    cbn [fact_ok]. fold (uE E' (laddc l8 SH_OFF)).
    assert (Hag : uE E' (laddc l8 SH_OFF) = uE E (laddc l8 SH_OFF)) by (unfold uE; rewrite <- (lden_agree (s_next S) E E' _ Hw8 Ha'); reflexivity).
    rewrite Hag. assert (Hv : uE E (laddc l8 SH_OFF) = uE E l8 + SH_OFF).
    { unfold uE. rewrite lden_laddc. fold (uE E l8). apply u_small64. unfold SH_OFF, two64 in *. lia. }
    rewrite Hv. unfold SH_OFF, SH_HI, P47 in *. lia.
Qed.
End PlaceE.
(* [comment removed for export] *)
End FxPlaceE.

Module FxPlaceW.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep FxChain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt.FxPlaceE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition WA_HI : Z := two64 + SH_LO - SH_HI - 1.
Definition WB_HI : Z := two64 + SH_LO - SH_HI.
Definition placew_post (S : sst) (M : smodel) (j : nat) : option sst :=
  match nth_error (sm_maps M) j with
  | Some g =>
      let b := fst (fst g) in let z := snd (fst g) in
      if (negb (is_mark g) && match is_const b with None => true | Some _ => false end && lwf (s_next S) b && lwf (s_next S) z &&
          sh_chain (sm_maps M) SH_LO SH_HI 8)%bool
      then Some (add_fact (add_fact S (FRange (laddc b (- SH_HI)) 0 WA_HI)) (FRange (laddc (ladd b z) (- SH_HI)) 0 WB_HI))
      else None
  | None => None
  end.

Section PlaceW.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_placew : forall E S M ms model j S', DEN segs LIMIT model0 mem0 E S M ms model -> placew_post S M j = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model j S' Hd Hp. unfold placew_post in Hp.
  destruct (nth_error (sm_maps M) j) as [g|] eqn:Hj; [|discriminate]. cbv zeta in Hp.
  set (b := fst (fst g)) in *. set (z := snd (fst g)) in *.
  match type of Hp with ((if ?c then _ else _) = _) => destruct c eqn:Hc; [|discriminate] end.
  repeat match type of Hc with ((_ && _)%bool = true) => apply andb_prop in Hc as [Hc ?Hx] end.
  rename Hc into Hnm. apply negb_true_iff in Hnm.
  match goal with H : match is_const b with _ => _ end = true |- _ => rename H into Hncb end.
  match goal with H : sh_chain _ _ _ _ = true |- _ => rename H into Hch end.
  assert (Hwb : lwf (s_next S) b = true) by assumption. assert (Hwz : lwf (s_next S) z = true) by assumption.
  destruct (is_const b) as [cb0|] eqn:Hcb0; [discriminate|]. clear Hncb. injection Hp as <-.
  pose proof (dn_pd segs LIMIT model0 mem0 E S M ms model Hd) as Hpd. rewrite (dn_maps segs LIMIT model0 mem0 E S M ms model Hd) in Hpd.
  pose proof (dn_gsh segs LIMIT model0 mem0 E S M ms model Hd) as Hgsh. rewrite Forall_forall in Hgsh.
  destruct (Hgsh g (nth_error_In _ _ Hj)) as (G1 & _ & _ & G4 & G5). unfold gsz in G1, G4. fold b z in G1, G4, G5.
  set (B0 := uE E b) in *. set (Z0 := uE E z) in *.
  assert (Hside : B0 + Z0 <= SH_LO \/ SH_HI <= B0).
  { destruct (Z_le_gt_dec (B0 + Z0) SH_LO) as [|Hgt]; [left; assumption|]. destruct (Z_le_gt_dec SH_HI B0) as [|Hlt]; [right; assumption|]. exfalso.
    set (x := Z.max B0 SH_LO).
    assert (HxA : SH_LO <= x < SH_HI) by (unfold x, SH_LO, SH_HI in *; lia). assert (HxB : B0 <= x < B0 + Z0) by (unfold x, SH_LO, SH_HI in *; lia).
    destruct (sh_chain_sound _ _ _ _ Hch x HxA) as (g' & cb & cz & Hin' & Hm' & Hb' & Hz' & Hxc).
    destruct (In_nth_error _ _ Hin') as (i & Hi).
    assert (Hij : i <> j). { intros ->. rewrite Hj in Hi. injection Hi as <-. fold b in Hb'. rewrite Hcb0 in Hb'. discriminate. }
    pose proof (pdisj_lden_nth E _ _ i j g' g Hpd Hi Hj Hij Hm' Hnm) as Hdj.
    destruct (is_const_sound E _ cb Hb') as [Hbv Hbr']. destruct (is_const_sound E _ cz Hz') as [Hzv Hzr'].
    unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hdj. cbn [fst snd] in Hdj. rewrite Hbv, Hzv in Hdj.
    rewrite (fg64' cb Hbr'), (fg64' cz Hzr') in Hdj. fold b z in Hdj. fold (uE E b) (uE E z) in Hdj. fold B0 Z0 in Hdj. lia. }
  assert (HvA : uE E (laddc b (- SH_HI)) = (B0 - SH_HI) mod two64).
  { unfold uE. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. reflexivity. }
  assert (HvE : uE E (ladd b z) = B0 + Z0).
  { unfold uE. rewrite lden_ladd, bv_add_unsigned. fold (uE E b) (uE E z). fold B0 Z0. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    apply Z.mod_small. unfold two64. lia. }
  assert (HvB : uE E (laddc (ladd b z) (- SH_HI)) = (B0 + Z0 - SH_HI) mod two64).
  { unfold uE. rewrite lden_laddc. fold (uE E (ladd b z)). rewrite HvE, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. reflexivity. }
  assert (FA : 0 <= uE E (laddc b (- SH_HI)) <= WA_HI).
  { rewrite HvA. unfold WA_HI. destruct Hside as [Hlo|Hhi].
    - rewrite <- (Z.mod_unique (B0 - SH_HI) two64 (-1) (B0 - SH_HI + two64)); unfold SH_LO, SH_HI, two64 in *; lia.
    - rewrite Z.mod_small; unfold SH_LO, SH_HI, two64 in *; lia. }
  assert (FB : 0 <= uE E (laddc (ladd b z) (- SH_HI)) <= WB_HI).
  { rewrite HvB. unfold WB_HI. destruct Hside as [Hlo|Hhi].
    - rewrite <- (Z.mod_unique (B0 + Z0 - SH_HI) two64 (-1) (B0 + Z0 - SH_HI + two64)); unfold SH_LO, SH_HI, two64 in *; lia.
    - rewrite Z.mod_small; unfold SH_LO, SH_HI, two64 in *; lia. }
  assert (HwA : lwf (s_next S) (laddc b (- SH_HI)) = true) by (apply lwf_laddc; exact Hwb).
  assert (HwB : lwf (s_next S) (laddc (ladd b z) (- SH_HI)) = true) by (apply lwf_laddc; apply lwf_ladd; assumption).
  apply (den_addfact segs LIMIT model0 mem0).
  - apply (den_addfact segs LIMIT model0 mem0); [exact Hd|]. intros E' Ha'. cbn [fact_ok]. fold (uE E' (laddc b (- SH_HI))).
    assert (Hag : uE E' (laddc b (- SH_HI)) = uE E (laddc b (- SH_HI))) by (unfold uE; rewrite <- (lden_agree (s_next S) E E' _ HwA Ha'); reflexivity).
    rewrite Hag. exact FA.
  - intros E' Ha'. cbn [fact_ok]. fold (uE E' (laddc (ladd b z) (- SH_HI))).
    assert (Hag : uE E' (laddc (ladd b z) (- SH_HI)) = uE E (laddc (ladd b z) (- SH_HI))).
    { unfold uE. rewrite <- (lden_agree (s_next S) E E' _ HwB); [reflexivity|]. exact Ha'. }
    rewrite Hag. exact FB.
Qed.
End PlaceW.
(* [comment removed for export] *)
End FxPlaceW.

Module HxLow.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChFix FxChain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition B17 : Z := 0x7fff7000.      Definition S17 : Z := 0x10000000.
Definition B16 : Z := 0x8fff7000.      Definition S16 : Z := 0x20000000000.
Definition B15 : Z := 0x2008fff7000.   Definition S15 : Z := 0xdfff0001000.
Definition KHIZ : Z := 0x10007fff8000.

Fixpoint gidx (gs : list (lin * lin * gkind)) (b : lin) (k : nat) : option nat :=
  match gs with [] => None | g :: r => if lin_eqb (fst (fst g)) b then Some k else gidx r b (Datatypes.S k) end.
Definition is_cg (g : lin * lin * gkind) (b s : Z) : bool := (lin_eqb (fst (fst g)) (lconst b) && lin_eqb (snd (fst g)) (lconst s))%bool.

Definition lowb_chk (S : sst) (M : smodel) (j i17 i16 i15 : nat) : option fact :=
  match nth_error (sm_maps M) j, nth_error (sm_maps M) i17, nth_error (sm_maps M) i16, nth_error (sm_maps M) i15 with
  | Some gj, Some g17, Some g16, Some g15 =>
      if (negb (Nat.eqb j i17) && negb (Nat.eqb j i16) && negb (Nat.eqb j i15) && is_cg g17 B17 S17 && is_cg g16 B16 S16 && is_cg g15 B15 S15 &&
          lwf (s_next S) (fst (fst gj)) && Z.ltb (snd (irange (s_facts S) (fst (fst gj)))) KHIZ && Z.leb 0 (B17 - gsz_lo (s_facts S) gj) && negb (is_mark gj))%bool
      then Some (FRange (fst (fst gj)) 0 (B17 - gsz_lo (s_facts S) gj)) else None
  | _, _, _, _ => None
  end.
(* [comment removed for export] *)
Definition lowb_post (S : sst) (M : smodel) (b : lin) : option sst :=
  match gidx (sm_maps M) b 0, gidx (sm_maps M) (lconst B17) 0, gidx (sm_maps M) (lconst B16) 0, gidx (sm_maps M) (lconst B15) 0 with
  | Some j, Some i17, Some i16, Some i15 =>
      match lowb_chk S M j i17 i16 i15 with Some f => Some (add_fact S f) | None => Some S end
  | _, _, _, _ => Some S
  end.

Section Low.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Lemma uE_lconst : forall E c, 0 <= c < two64 -> uE E (lconst c) = c.
Proof. LiaFast.lf_pins LiaFast.u0. intros E c Hc. unfold uE. rewrite lden_lconst, u_Z_to_bv. apply Z.mod_small. exact Hc. Qed.

#[using="Type"] Lemma den_lowb : forall E S M ms model b S', DEN segs LIMIT model0 mem0 E S M ms model -> lowb_post S M b = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model b S' Hd Hp. unfold lowb_post in Hp.
  destruct (gidx (sm_maps M) b 0) as [j|]; [|injection Hp as <-; exact Hd].
  destruct (gidx (sm_maps M) (lconst B17) 0) as [i17|]; [|injection Hp as <-; exact Hd].
  destruct (gidx (sm_maps M) (lconst B16) 0) as [i16|]; [|injection Hp as <-; exact Hd].
  destruct (gidx (sm_maps M) (lconst B15) 0) as [i15|]; [|injection Hp as <-; exact Hd].
  destruct (lowb_chk S M j i17 i16 i15) as [f|] eqn:Hc; [|injection Hp as <-; exact Hd]. injection Hp as <-.
  unfold lowb_chk in Hc.
  destruct (nth_error (sm_maps M) j) as [gj|] eqn:Hj; [|discriminate]. destruct (nth_error (sm_maps M) i17) as [g17|] eqn:H17; [|discriminate].
  destruct (nth_error (sm_maps M) i16) as [g16|] eqn:H16; [|discriminate]. destruct (nth_error (sm_maps M) i15) as [g15|] eqn:H15; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hb; [|discriminate] end. injection Hc as <-.
  repeat match type of Hb with (_ && _)%bool = true => let X := fresh "X" in apply andb_prop in Hb as [Hb X] end.
  rename X into Hnm, X0 into Hnn, X1 into Hlt, X2 into Hwj, X3 into C15, X4 into C16, X5 into C17, X6 into N15, X7 into N16.
  apply negb_true_iff in Hnm. apply negb_true_iff, Nat.eqb_neq in Hb, N16, N15. apply Z.ltb_lt in Hlt. apply Z.leb_le in Hnn.
  unfold is_cg in C15, C16, C17. apply andb_prop in C15 as [C15b C15s]. apply andb_prop in C16 as [C16b C16s]. apply andb_prop in C17 as [C17b C17s].
  apply lin_eqb_eq in C15b, C15s, C16b, C16s, C17b, C17s.
  pose proof (dn_sden segs LIMIT model0 mem0 E S M ms model Hd) as Hsd. destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & HF & _).
  apply den_addfact; [exact Hd|]. intros E' Ha'. cbn [fact_ok].
  rewrite <- (lden_agree (s_next S) E E' _ Hwj Ha').
  pose proof (dn_pd segs LIMIT model0 mem0 E S M ms model Hd) as Hpd. rewrite (dn_maps segs LIMIT model0 mem0 E S M ms model Hd) in Hpd.
  assert (M17 : is_mark g17 = false) by (destruct g17 as [[b17 s17] k17]; cbn [fst snd] in C17s; rewrite C17s; apply is_mark_csize).
  assert (M16 : is_mark g16 = false) by (destruct g16 as [[b16 s16] k16]; cbn [fst snd] in C16s; rewrite C16s; apply is_mark_csize).
  assert (M15 : is_mark g15 = false) by (destruct g15 as [[b15 s15] k15]; cbn [fst snd] in C15s; rewrite C15s; apply is_mark_csize).
  pose proof (pdisj_lden_nth _ _ _ j i17 _ _ Hpd Hj H17 Hb Hnm M17) as D17. pose proof (pdisj_lden_nth _ _ _ j i16 _ _ Hpd Hj H16 N16 Hnm M16) as D16.
  pose proof (pdisj_lden_nth _ _ _ j i15 _ _ Hpd Hj H15 N15 Hnm M15) as D15.
  pose proof (dn_gsh segs LIMIT model0 mem0 E S M ms model Hd) as Hgsh. rewrite Forall_forall in Hgsh.
  destruct (Hgsh gj (nth_error_In _ _ Hj)) as (S1 & _ & _ & S4 & _).
  unfold iv_disj, FxBacking.B, FxBacking.S, gden in D17, D16, D15. cbn [fst snd] in D17, D16, D15.
  rewrite C17b, C17s in D17. rewrite C16b, C16s in D16. rewrite C15b, C15s in D15.
  change (bv_unsigned (lden E (lconst B17))) with (uE E (lconst B17)) in D17. change (bv_unsigned (lden E (lconst S17))) with (uE E (lconst S17)) in D17.
  change (bv_unsigned (lden E (lconst B16))) with (uE E (lconst B16)) in D16. change (bv_unsigned (lden E (lconst S16))) with (uE E (lconst S16)) in D16.
  change (bv_unsigned (lden E (lconst B15))) with (uE E (lconst B15)) in D15. change (bv_unsigned (lden E (lconst S15))) with (uE E (lconst S15)) in D15.
  rewrite !uE_lconst in D17, D16, D15 by (unfold B17, S17, B16, S16, B15, S15, two64; lia).
  pose proof (irange_sound E (s_facts S) (fst (fst gj)) HF) as Ir.
  pose proof (gsz_bounds E (s_facts S) gj HF) as Bj. pose proof (gsz_lo_nonneg (s_facts S) gj) as Bj0.
  pose proof (u_range E (fst (fst gj))) as Rj.
  unfold gsz, uE in Bj, S1, S4.
  set (bj := bv_unsigned (lden E (fst (fst gj)))) in *. set (sj := bv_unsigned (lden E (snd (fst gj)))) in *.
  unfold B17, S17, B16, S16, B15, S15, KHIZ in *. lia.
Qed.
End Low.
End HxLow.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma agree_params : forall n0 E σ, params_fixed σ (pos_below n0) = true -> agree n0 E (ecomp E σ).
Proof.
  intros n0 E σ H x Hx. unfold params_fixed in H. rewrite forallb_forall in H.
  pose proof (H x (pos_below_In n0 x Hx)) as Hv. apply lin_eqb_eq in Hv.
  unfold ecomp. rewrite Hv. rewrite lden_lvar. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rl_ok_ent : forall E model rs rp σ, rgs_ent rs rp σ = true -> Forall (rl_ok E model) rs -> Forall (rl_ok (ecomp E σ) model) rp.
Proof.
  intros E model rs. induction rs as [|R rs IH]; intros [|R' rp] σ He HF; cbn [rgs_ent] in He; try discriminate; [constructor|].
  apply andb_prop in He as [He1 He2]. inversion HF as [|? ? HR HRs]; subst.
  constructor; [|exact (IH rp σ He2 HRs)].
  destruct (rg_ent_parts R R' σ He1) as (Hb & Hs & _).
  assert (HA : uE (ecomp E σ) (rg_base R') = uE E (rg_base R)) by (unfold uE; rewrite Hb, lden_lsubst; reflexivity).
  assert (HS : rsz (ecomp E σ) R' = rsz E R) by (unfold rsz; rewrite Hs, lden_lsubst; reflexivity).
  unfold rl_ok, app_pt in *. rewrite HA, HS. exact HR.
Qed.

Section Ent.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_ent : forall E S P M ms model σ n0,
  DEN segs LIMIT model0 mem0 E S M ms model ->
  entails S P σ = true -> state_wf P = true -> params_fixed σ (pos_below n0) = true ->
  sm_wf n0 M = true -> (n0 <= s_next P)%positive ->
  DEN segs LIMIT model0 mem0 (ecomp E σ) P M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S P M ms model σ n0 Hd Hent Hwp Hpf Hwf0 Hn.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (E' := ecomp E σ).
  assert (Ha : agree n0 E E') by exact (agree_params n0 E σ Hpf).
  assert (HA : allowA E' M = allowA E M) by exact (allowA_agree n0 E E' M Hwf0 Ha).
  assert (HH : Hof E' M model = Hof E M model) by (unfold Hof; rewrite HA; reflexivity).
  assert (Hrge : rgs_ent (s_rgs S) (s_rgs P) σ = true).
  { unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [_ Hg]. exact Hg. }
  destruct (sm_wf_parts _ M Hwf0) as (Hwg & Hwa & Hwt & Hwb & Hwsb & Hwsp).
  constructor.
  - rewrite HH. apply (entails_sden segs E S P σ _ (sden_0 _ _ _ _ Hsd) Hent Hwp).
  - exact (sm_wf_mono _ _ M Hn Hwf0).
  - exact (state_wf_bases P Hwp).
  - exact Hh.
  - rewrite HA. exact Hawf.
  - exact Hanz.
  - unfold AM. rewrite HA. exact Hminv.
  - rewrite HH. exact Hhoff.
  - exact Hres.
  - exact Hlim.
  - rewrite Hsp. symmetry. exact (lden_agree_wf _ E E' _ Hwsp Ha).
  - exact Hspok.
  - rewrite Hbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwb Ha).
  - rewrite Hsbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwsb Ha).
  - rewrite Htid. destruct (sm_tid M) as [l|]; [cbn; f_equal; symmetry; exact (lden_agree_wf _ E E' l Hwt Ha) | reflexivity].
  - rewrite Hmaps. symmetry. exact (lden_maps_agree _ E E' _ M Hwf0 Ha).
  - apply (Forall_agree_maps n0 E E' M gshape_ok Hwf0 Ha); [|exact Hgsh].
    intros g Hg Hgs. unfold gshape_ok, gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
  - apply (Forall_agree_maps n0 E E' M (fun E g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model)) Hwf0 Ha).
    + intros g Hg Hgs. unfold gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
    + exact Hgtop.
  - exact Hivwf.
  - exact Hpd.
  - exact Hmres.
  - apply (Forall_agree_maps n0 E E' M (fun E g => kind_ok E model g) Hwf0 Ha).
    + intros g Hg Hgs. unfold kind_ok, gden. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
    + exact Hkind.
  - exact Hlzm.
  - exact Hzrsh.
  - exact Hzrm.
  - intros w Hw Hout Hnow Hnb. apply (Hzr w Hw); [|exact (own_pt_keep n0 E E' M M w Hwf0 Ha eq_refl Hnow) | exact Hnb].
    apply (proj2 (rgs_ent_outside E (s_rgs S) (s_rgs P) σ _ Hrge)). exact Hout.
  - exact (rl_ok_ent E model (s_rgs S) (s_rgs P) σ Hrge Hrl).
  - exact Hvmo.
  - exact Hproc.
  - intros q Hq w Hw. pose proof (sm_wf_frz _ M Hwf0) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw q Hq) as [Hf1 Hf2].
    assert (Hw0 : uE E (fst q) <= w < uE E (fst q) + uE E (snd q)) by (unfold uE in *; rewrite <- (lden_agree_wf _ E E' _ Hf1 Ha), <- (lden_agree_wf _ E E' _ Hf2 Ha); exact Hw).
    destruct (Hfrz q Hq w Hw0) as (Htp & Hout & Hm). split; [exact Htp|]. split; [|exact Hm].
    apply (proj1 (rgs_ent_outside E (s_rgs S) (s_rgs P) σ _ Hrge)). exact Hout.
  - rom_tac.
  - intros q Hq w Hw. pose proof (sm_wf_own _ M Hwf0) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw q Hq) as [Hf1 Hf2].
    assert (Hw0 : uE E (fst q) <= w < uE E (fst q) + uE E (snd q)) by (unfold uE in *; rewrite <- (lden_agree_wf _ E E' _ Hf1 Ha), <- (lden_agree_wf _ E E' _ Hf2 Ha); exact Hw).
    destruct (Hown q Hq w Hw0) as [Hv Hm]. split; [rewrite HH; exact Hv|]. intros Hout.
    apply Hm. apply (proj2 (rgs_ent_outside E (s_rgs S) (s_rgs P) σ _ Hrge)). exact Hout.
  - exact (blob_ok_agree n0 E E' M model model _ Hwf0 Ha eq_refl Hblob).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_agree : forall E E' S M ms model,
  DEN segs LIMIT model0 mem0 E S M ms model -> agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' S M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E E' S M ms model Hd Ha.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (HA : allowA E' M = allowA E M) by exact (allowA_agree (s_next S) E E' M Hwf Ha).
  assert (HH : Hof E' M model = Hof E M model) by (unfold Hof; rewrite HA; reflexivity).
  destruct (sm_wf_parts _ M Hwf) as (Hwg & Hwa & Hwt & Hwb & Hwsb & Hwsp).
  constructor.
  - rewrite HH. intros E'' Ha''. apply Hsd. exact (agree_trans _ E E' E'' Ha Ha'').
  - exact Hwf.
  - exact Hbw.
  - exact Hh.
  - rewrite HA. exact Hawf.
  - exact Hanz.
  - unfold AM. rewrite HA. exact Hminv.
  - rewrite HH. exact Hhoff.
  - exact Hres.
  - exact Hlim.
  - rewrite Hsp. symmetry. exact (lden_agree_wf _ E E' _ Hwsp Ha).
  - exact Hspok.
  - rewrite Hbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwb Ha).
  - rewrite Hsbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwsb Ha).
  - rewrite Htid. destruct (sm_tid M) as [l|]; [cbn; f_equal; symmetry; exact (lden_agree_wf _ E E' l Hwt Ha) | reflexivity].
  - rewrite Hmaps. symmetry. exact (lden_maps_agree _ E E' _ M Hwf Ha).
  - apply (Forall_agree_maps (s_next S) E E' M gshape_ok Hwf Ha); [|exact Hgsh].
    intros g Hg Hgs. unfold gshape_ok, gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
  - apply (Forall_agree_maps (s_next S) E E' M (fun E g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model)) Hwf Ha).
    + intros g Hg Hgs. unfold gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
    + exact Hgtop.
  - exact Hivwf.
  - exact Hpd.
  - exact Hmres.
  - apply (Forall_agree_maps (s_next S) E E' M (fun E g => kind_ok E model g) Hwf Ha).
    + intros g Hg Hgs. unfold kind_ok, gden. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
    + exact Hkind.
  - exact Hlzm.
  - exact Hzrsh.
  - exact Hzrm.
  - intros w Hw Hout Hnow Hnb. apply (Hzr w Hw); [exact (proj2 (outside_agree (s_next S) E E' (s_rgs S) _ Hbw Ha) Hout) | | exact Hnb].
    exact (own_pt_keep (s_next S) E E' M M w Hwf Ha eq_refl Hnow).
  - exact (rl_ok_agree_shape (s_next S) E E' model model (s_rgs S) (s_rgs S) Hbw Ha eq_refl eq_refl Hrl).
  - exact Hvmo.
  - exact Hproc.
  - intros q Hq w Hw. pose proof (sm_wf_frz _ M Hwf) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw q Hq) as [Hf1 Hf2].
    assert (Hw0 : uE E (fst q) <= w < uE E (fst q) + uE E (snd q)) by (unfold uE in *; rewrite <- (lden_agree_wf _ E E' _ Hf1 Ha), <- (lden_agree_wf _ E E' _ Hf2 Ha); exact Hw).
    destruct (Hfrz q Hq w Hw0) as (Htp & Hout & Hm). split; [exact Htp|]. split; [|exact Hm].
    exact (proj1 (outside_agree (s_next S) E E' (s_rgs S) _ Hbw Ha) Hout).
  - exact Hrom.
  - intros q Hq w Hw. pose proof (sm_wf_own _ M Hwf) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw q Hq) as [Hf1 Hf2].
    assert (Hw0 : uE E (fst q) <= w < uE E (fst q) + uE E (snd q)) by (unfold uE in *; rewrite <- (lden_agree_wf _ E E' _ Hf1 Ha), <- (lden_agree_wf _ E E' _ Hf2 Ha); exact Hw).
    destruct (Hown q Hq w Hw0) as [Hv Hm]. split; [rewrite HH; exact Hv|]. intros Hout.
    apply Hm. exact (proj2 (outside_agree (s_next S) E E' (s_rgs S) _ Hbw Ha) Hout).
  - exact (blob_ok_agree (s_next S) E E' M model model _ Hwf Ha eq_refl Hblob).
Qed.

(* [comment removed for export] *)
Definition bump (S : sst) (n : positive) : sst := SST (s_pc S) (s_regs S) (s_rgs S) (s_facts S) n (s_resv S).
#[using="Type"] Theorem den_bump : forall E S M ms model n,
  DEN segs LIMIT model0 mem0 E S M ms model -> (s_next S <= n)%positive -> DEN segs LIMIT model0 mem0 E (bump S n) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model n Hd Hn.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; try assumption.
  - intros E' Ha'. cbn [bump s_next] in Ha'. destruct (Hsd E' (agree_mono _ _ E E' Hn Ha')) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    unfold sden0; cbn [bump s_pc s_regs s_rgs s_facts s_resv]. tauto.
  - exact (sm_wf_mono _ _ M Hn Hwf).
  - cbn [bump s_next s_rgs]. exact (bases_wf_shape _ _ _ _ Hn eq_refl Hbw).
Qed.

(* [comment removed for export] *)
Definition ret_gen (S : sst) (lo hi : Z) : sst :=
  add_fact (bump (ret_post S (lvar (s_next S))) (Pos.succ (s_next S))) (FRange (lvar (s_next S)) lo hi).
#[using="Type"] Theorem den_gen_ret : forall E S M ms model (c lo hi : Z),
  DEN segs LIMIT model0 mem0 E (ret_post S (lconst c)) M ms model -> 0 <= c < two64 -> lo <= c <= hi ->
  DEN segs LIMIT model0 mem0 (upd E (s_next S) (Z_to_bv 64 c)) (ret_gen S lo hi) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model c lo hi Hd Hc Hr.
  set (E1 := upd E (s_next S) (Z_to_bv 64 c)).
  assert (Ha : agree (s_next S) E E1) by exact (agree_upd (s_next S) E _).
  assert (HE1 : E1 (s_next S) = Z_to_bv 64 c) by (unfold E1, upd; rewrite Pos.eqb_refl; reflexivity).
  pose proof (den_agree E E1 (ret_post S (lconst c)) M ms model Hd Ha) as Hd1.
  pose proof (den_bump E1 (ret_post S (lconst c)) M ms model (Pos.succ (s_next S)) Hd1 ltac:(cbn [ret_post s_next]; lia)) as Hd2.
  unfold ret_gen. apply den_addfact.
  - destruct Hd2 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
    constructor; try assumption.
    intros E'' Ha''. cbn [bump ret_post s_next] in Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    unfold sden0 in *. cbn [bump ret_post s_pc s_regs s_rgs s_facts s_resv] in *.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|tauto].
    intros r. rewrite (H4 r). destruct (Pos.eq_dec (rkey r) (rkey a0r)) as [Hk|Hk].
    + destruct (Pos.eq_dec (rkey r) xH) as [H0|H0].
      * exfalso. rewrite Hk in H0. discriminate H0.
      * rewrite Hk, !rget_rset_same by exact (fun X => H0 (eq_trans Hk X)).
        rewrite lden_lconst, lden_lvar. rewrite <- (Ha'' (s_next S) ltac:(lia)). rewrite HE1. reflexivity.
    + rewrite !rget_rset_other by exact Hk. reflexivity.
  - intros E' Ha'. cbn [fact_ok]. rewrite lden_lvar. rewrite <- (Ha' (s_next S) ltac:(cbn [bump ret_post s_next]; lia)). rewrite HE1.
    rewrite u_small64 by exact Hc. exact Hr.
Qed.

(* [comment removed for export] *)
Definition ent_ok (n0 : positive) (S P : sst) (M : smodel) : bool :=
  let σ := match_st S P in
  (entails S P σ && state_wf P && fixed_below σ n0 && sm_wf n0 M && Pos.leb n0 (s_next P))%bool.

#[using="Type"] Theorem den_weaken : forall E S P M ms model n0,
  DEN segs LIMIT model0 mem0 E S M ms model -> ent_ok n0 S P M = true ->
  DEN segs LIMIT model0 mem0 (ecomp E (match_st S P)) P M ms model /\ agree n0 E (ecomp E (match_st S P)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S P M ms model n0 Hd Hok. unfold ent_ok in Hok.
  apply andb_prop in Hok as [Hok Hn]. apply andb_prop in Hok as [Hok Hwf0]. apply andb_prop in Hok as [Hok Hpf]. rewrite fixed_below_eq in Hpf.
  apply andb_prop in Hok as [Hent Hwp]. apply Pos.leb_le in Hn.
  split; [exact (den_ent E S P M ms model (match_st S P) n0 Hd Hent Hwp Hpf Hwf0 Hn) | exact (agree_params n0 E _ Hpf)].
Qed.
End Ent.
