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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys.

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
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChRecont.FxPlaceE.
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
End FxPlaceW.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition kadd (k0 : positive) (j : nat) : positive := match j with O => k0 | Datatypes.S _ => (k0 + Pos.of_nat j)%positive end.
Lemma kadd_eq : forall k0 j, kadd k0 j = Pos.of_nat (Pos.to_nat k0 + j).
Proof.
  intros k0 [|j]; cbn [kadd]; [rewrite Nat.add_0_r, Pos2Nat.id; reflexivity|].
  apply Pos2Nat.inj. rewrite Pos2Nat.inj_add, !Nat2Pos.id by (pose proof (Pos2Nat.is_pos k0); lia). reflexivity.
Qed.
(* [comment removed for export] *)
Definition bk_word_ok (t : tree bval) (k0 : positive) (c : Z) : bool :=
  (Z.leb 0 c && Z.ltb c two64 &&
   forallb (fun j => match tget (kadd k0 j) t with
                     | Some (BK b) => Z.eqb b (Z.land (Z.shiftr c (8 * Z.of_nat j)) 255)
                     | _ => false end) (List.seq 0 8))%bool.
Fixpoint put_bv (t : tree bval) (k0 : positive) (c : Z) (j : nat) : tree bval :=
  match j with
  | O => t
  | Datatypes.S j' => put_bv (tset (kadd k0 j') (BV (lconst c) (Z.of_nat j')) t) k0 c j'
  end.
Definition recont_rg (R : region) (k0 : positive) (c : Z) : option region :=
  if bk_word_ok (rg_cont R) k0 c then Some (RG (rg_base R) (rg_size R) (rg_kind R) (put_bv (rg_cont R) k0 c 8)) else None.
Definition recont_post (S : sst) (i : nat) (k0 : positive) (c : Z) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match recont_rg R k0 c with
              | Some R' => Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (s_next S) (s_resv S))
              | None => None
              end
  | None => None
  end.

Lemma tget_put_bv : forall j t k0 c p, tget p (put_bv t k0 c j) =
  if existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 j)
  then Some (BV (lconst c) (Z.of_nat (Pos.to_nat p - Pos.to_nat k0))) else tget p t.
Proof.
  induction j as [|j IH]; intros t k0 c p; cbn [put_bv]; [reflexivity|].
  rewrite kadd_eq, IH. rewrite seq_S, existsb_app. cbn [existsb]. rewrite orb_false_r, Nat.add_0_l.
  destruct (existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 j)) eqn:He; [reflexivity|].
  cbn [orb]. destruct (Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + j))) eqn:Hp.
  - apply Pos.eqb_eq in Hp. subst p. rewrite tget_tset_same. rewrite Nat2Pos.id by (pose proof (Pos2Nat.is_pos k0); lia).
    replace (Pos.to_nat k0 + j - Pos.to_nat k0)%nat with j by lia. reflexivity.
  - rewrite tget_tset_other; [reflexivity|]. intros X. subst. rewrite Pos.eqb_refl in Hp. discriminate.
Qed.

Lemma bden_bv_const : forall E c j, 0 <= c < two64 -> 0 <= j ->
  bden E (BV (lconst c) j) = Z_to_bv 8 (Z.land (Z.shiftr c (8 * j)) 255).
Proof.
  intros E c j Hc Hj. cbn [bden]. rewrite lden_lconst, u_small64 by exact Hc.
  apply Z_to_bv8_bits. intros k Hk. change 255 with (Z.ones 8). rewrite Z.land_spec, Z.ones_spec_low by lia. rewrite andb_true_r. reflexivity.
Qed.

Lemma recont_rg_ok : forall segs E m R k0 c R', recont_rg R k0 c = Some R' -> rg_ok segs E m R -> rg_ok segs E m R'.
Proof.
  intros segs E m R k0 c R' Hr Hok. unfold recont_rg in Hr. destruct (bk_word_ok (rg_cont R) k0 c) eqn:Hb; [|discriminate].
  injection Hr as <-. unfold bk_word_ok in Hb. apply andb_prop in Hb as [Hb Hall]. apply andb_prop in Hb as [Hc0 Hc1].
  apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc1. rewrite forallb_forall in Hall.
  (* [comment removed for export] *)
  assert (Hkey : forall p, existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 8) = true ->
            exists b, tget p (rg_cont R) = Some (BK b) /\ b = Z.land (Z.shiftr c (8 * Z.of_nat (Pos.to_nat p - Pos.to_nat k0))) 255).
  { intros p Hp. apply existsb_exists in Hp as (i & Hi & Hpi). apply Pos.eqb_eq in Hpi. subst p. specialize (Hall i Hi). rewrite kadd_eq in Hall.
    destruct (tget (Pos.of_nat (Pos.to_nat k0 + i)) (rg_cont R)) as [[b|l j]|] eqn:Ht; try discriminate.
    apply Z.eqb_eq in Hall. exists b. split; [reflexivity|]. rewrite Nat2Pos.id by (pose proof (Pos2Nat.is_pos k0); lia). apply in_seq in Hi.
    replace (Pos.to_nat k0 + i - Pos.to_nat k0)%nat with i by lia. exact Hall. }
  assert (HT : forall p, tget p (put_bv (rg_cont R) k0 c 8) = None -> tget p (rg_cont R) = None).
  { intros p Hn. rewrite tget_put_bv in Hn. destruct (existsb _ _) eqn:He; [discriminate | exact Hn]. }
  assert (HS : forall p v, tget p (put_bv (rg_cont R) k0 c 8) = Some v ->
             (existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 8) = true /\ v = BV (lconst c) (Z.of_nat (Pos.to_nat p - Pos.to_nat k0))) \/
             tget p (rg_cont R) = Some v).
  { intros p v Hp. rewrite tget_put_bv in Hp. destruct (existsb _ _) eqn:He; [left; split; [reflexivity | injection Hp as <-; reflexivity] | right; exact Hp]. }
  destruct Hok as (Hs & Hw & Hbytes & Hc). cbn [rg_base rg_size rg_kind rg_cont] in *. unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont].
  unfold rsz in *. cbn [rg_size] in *.
  split; [exact Hs|]. split; [exact Hw|]. split.
  - intros i Hi. specialize (Hbytes i Hi). destruct (rg_kind R); try exact Hbytes.
    + destruct Hbytes as [H1 H2]. split; [exact H1|]. intros Hn. apply H2. exact (HT _ Hn).
    + destruct Hbytes as [H1 H2]. split; [exact H1|]. intros Hn. apply H2. exact (HT _ Hn).
  - intros p v Hp. destruct (HS p v Hp) as [[He ->]|Hp'].
    + destruct (Hkey p He) as (b & Hb & Heq). destruct (Hc p (BK b) Hb) as [Hp1 Hp2]. split; [exact Hp1|].
      rewrite Hp2. rewrite bden_bv_const by lia. cbn [bden]. rewrite Heq. reflexivity.
    + exact (Hc p v Hp').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rz_trackn_ok (R : region) (k0 : positive) (n : nat) : bool :=
  (rkind_eqb (rg_kind R) RZ &&
   match is_const (rg_size R) with Some sz => Z.leb (Zpos k0 + Z.of_nat n - 1) sz | None => false end &&
   forallb (fun j => match tget (kadd k0 j) (rg_cont R) with None => true | Some _ => false end) (List.seq 0 n))%bool.
Definition rz_track_ok (R : region) (k0 : positive) : bool := rz_trackn_ok R k0 8.
Fixpoint put_bk0 (t : tree bval) (k0 : positive) (j : nat) : tree bval :=
  match j with
  | O => t
  | Datatypes.S j' => put_bk0 (tset (kadd k0 j') (BK 0) t) k0 j'
  end.
Definition rz_trackn_rg (R : region) (k0 : positive) (n : nat) : option region :=
  if rz_trackn_ok R k0 n then Some (RG (rg_base R) (rg_size R) (rg_kind R) (put_bk0 (rg_cont R) k0 n)) else None.
Definition rz_trackn_post (S : sst) (i : nat) (k0 : positive) (n : nat) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match rz_trackn_rg R k0 n with
              | Some R' => Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (s_next S) (s_resv S))
              | None => None
              end
  | None => None
  end.
Definition rz_track_rg (R : region) (k0 : positive) : option region := rz_trackn_rg R k0 8.
Definition rz_track_post (S : sst) (i : nat) (k0 : positive) : option sst := rz_trackn_post S i k0 8.
Lemma tget_put_bk0 : forall j t k0 p, tget p (put_bk0 t k0 j) =
  if existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 j) then Some (BK 0) else tget p t.
Proof.
  induction j as [|j IH]; intros t k0 p; cbn [put_bk0]; [reflexivity|].
  rewrite kadd_eq, IH. rewrite seq_S, existsb_app. cbn [existsb]. rewrite orb_false_r, Nat.add_0_l.
  destruct (existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 j)) eqn:He; [reflexivity|].
  cbn [orb]. destruct (Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + j))) eqn:Hp.
  - apply Pos.eqb_eq in Hp. subst p. rewrite tget_tset_same. reflexivity.
  - rewrite tget_tset_other; [reflexivity|]. intros X. subst. rewrite Pos.eqb_refl in Hp. discriminate.
Qed.
Lemma rz_trackn_rg_ok : forall segs E m R k0 n R', rz_trackn_rg R k0 n = Some R' -> rg_ok segs E m R -> rg_ok segs E m R'.
Proof.
  intros segs E m R k0 n R' Hr Hok. unfold rz_trackn_rg in Hr. destruct (rz_trackn_ok R k0 n) eqn:Hb; [|discriminate].
  injection Hr as <-. unfold rz_trackn_ok in Hb. apply andb_prop in Hb as [Hb Hall]. apply andb_prop in Hb as [Hk Hsz].
  destruct (is_const (rg_size R)) as [sz|] eqn:Hs; [|discriminate]. apply Z.leb_le in Hsz. rewrite forallb_forall in Hall.
  assert (HK : rg_kind R = RZ) by (destruct (rg_kind R); try discriminate; reflexivity).
  assert (Hrs : bv_unsigned (lden E (rg_size R)) = sz) by (destruct (is_const_sound E _ sz Hs) as [H1 H2]; rewrite H1; apply u_small64; exact H2).
  assert (Hkey : forall p, existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 n) = true ->
            tget p (rg_cont R) = None /\ 0 <= Zpos p - 1 < sz).
  { intros p Hp. apply existsb_exists in Hp as (i & Hi & Hpi). apply Pos.eqb_eq in Hpi. subst p. specialize (Hall i Hi). rewrite kadd_eq in Hall.
    destruct (tget (Pos.of_nat (Pos.to_nat k0 + i)) (rg_cont R)); [discriminate|]. split; [reflexivity|].
    apply in_seq in Hi. pose proof (Pos2Nat.is_pos k0).
    assert (Hz : Zpos (Pos.of_nat (Pos.to_nat k0 + i)) = Zpos k0 + Z.of_nat i).
    { rewrite <- positive_nat_Z. rewrite Nat2Pos.id by lia. rewrite Nat2Z.inj_add, positive_nat_Z. reflexivity. }
    rewrite Hz. lia. }
  assert (HT : forall p, tget p (put_bk0 (rg_cont R) k0 n) = None -> tget p (rg_cont R) = None).
  { intros p Hn. rewrite tget_put_bk0 in Hn. destruct (existsb _ _) eqn:He; [discriminate | exact Hn]. }
  assert (HS : forall p v, tget p (put_bk0 (rg_cont R) k0 n) = Some v ->
             (existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 n) = true /\ v = BK 0) \/ tget p (rg_cont R) = Some v).
  { intros p v Hp. rewrite tget_put_bk0 in Hp. destruct (existsb _ _) eqn:He; [left; split; [reflexivity | injection Hp as <-; reflexivity] | right; exact Hp]. }
  destruct Hok as (Hs0 & Hw & Hbytes & Hc). unfold rg_ok, rsz in *. cbn [rg_base rg_size rg_kind rg_cont] in *.
  split; [exact Hs0|]. split; [exact Hw|]. split.
  - intros i Hi. specialize (Hbytes i Hi). rewrite HK in Hbytes |- *. destruct Hbytes as [H1 H2]. split; [exact H1|].
    intros Hn. apply H2. exact (HT _ Hn).
  - intros p v Hp. destruct (HS p v Hp) as [[He ->]|Hp'].
    + destruct (Hkey p He) as [Hn Hlt]. rewrite Hrs. split; [lia|].
      specialize (Hbytes (Zpos p - 1) ltac:(rewrite Hrs; lia)). rewrite HK in Hbytes. destruct Hbytes as [_ H2].
      replace (okey (Zpos p - 1)) with p in H2 by (unfold okey; replace (Zpos p - 1 + 1) with (Zpos p) by lia; reflexivity).
      exact (H2 Hn).
    + exact (Hc p v Hp').
Qed.
Section Recont.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_recont : forall model0 E S M ms model i k0 c S', DEN segs LIMIT model0 mem0 E S M ms model -> recont_post S i k0 c = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model i k0 c S' Hd Hp. unfold recont_post in Hp.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. destruct (recont_rg R k0 c) as [R'|] eqn:Hr; [|discriminate].
  injection Hp as <-.
  assert (HR' : rg_base R' = rg_base R /\ rg_size R' = rg_size R /\ rg_kind R' = rg_kind R).
  { unfold recont_rg in Hr. destruct (bk_word_ok (rg_cont R) k0 c); [|discriminate]. injection Hr as <-. cbn. tauto. }
  destruct HR' as (Hb' & Hs' & Hk').
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (S2 := SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (s_next S) (s_resv S)).
  assert (Hshape : shape (s_rgs S2) = shape (s_rgs S)) by (cbn [S2 s_rgs]; exact (shape_upd (s_rgs S) i R' R Hi Hb' Hs')).
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply Forall_forall. intros R0 HR0. destruct (In_nth_error _ _ HR0) as (j & Hj).
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-.
        exact (recont_rg_ok segs E'' _ R k0 c R' Hr (proj1 (Forall_nth' _ _) HG i R Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. rewrite Forall_forall in HG. exact (HG R0 (nth_error_In _ _ Hj)).
    + eapply rgs_disj_upd; [exact Hi | exact Hb' | exact Hs' | exact HD].
  - eapply bases_wf_shape; [|exact Hshape|exact Hbw]. cbn [S2 s_next]. lia.
  - intros w Hw Hout' Hnow. apply (Hzr w Hw); [|exact Hnow].
    exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Hout').
  - exact (rl_ok_agree_shape (s_next S) E E model model (s_rgs S) _ Hbw (agree_refl _ _) Hshape eq_refl Hrl).
  - apply (frz_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho'. unfold outside in *. rewrite Forall_forall in *. intros R0 HR0.
      destruct (In_nth_error _ _ HR0) as (j & Hj). cbn [S2 s_rgs] in Hj.
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-. unfold rsz in *. rewrite Hb', Hs'. exact (Ho' R (nth_error_In _ _ Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. exact (Ho' R0 (nth_error_In _ _ Hj)).
    + intros w _ _. reflexivity.
  - apply (own_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho'. exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Ho').
    + intros w _. reflexivity.
    + intros x Hx. exact Hx.
Qed.

#[using="Type"] Theorem den_rz_trackn : forall model0 E S M ms model i k0 n S', DEN segs LIMIT model0 mem0 E S M ms model -> rz_trackn_post S i k0 n = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model i k0 n S' Hd Hp. unfold rz_trackn_post in Hp.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. destruct (rz_trackn_rg R k0 n) as [R'|] eqn:Hr; [|discriminate].
  injection Hp as <-.
  assert (HR' : rg_base R' = rg_base R /\ rg_size R' = rg_size R /\ rg_kind R' = rg_kind R).
  { unfold rz_trackn_rg in Hr. destruct (rz_trackn_ok R k0 n); [|discriminate]. injection Hr as <-. cbn. tauto. }
  destruct HR' as (Hb' & Hs' & Hk').
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (S2 := SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (s_next S) (s_resv S)).
  assert (Hshape : shape (s_rgs S2) = shape (s_rgs S)) by (cbn [S2 s_rgs]; exact (shape_upd (s_rgs S) i R' R Hi Hb' Hs')).
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply Forall_forall. intros R0 HR0. destruct (In_nth_error _ _ HR0) as (j & Hj).
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-.
        exact (rz_trackn_rg_ok segs E'' _ R k0 n R' Hr (proj1 (Forall_nth' _ _) HG i R Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. rewrite Forall_forall in HG. exact (HG R0 (nth_error_In _ _ Hj)).
    + eapply rgs_disj_upd; [exact Hi | exact Hb' | exact Hs' | exact HD].
  - eapply bases_wf_shape; [|exact Hshape|exact Hbw]. cbn [S2 s_next]. lia.
  - intros w Hw Hout' Hnow. apply (Hzr w Hw); [|exact Hnow].
    exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Hout').
  - exact (rl_ok_agree_shape (s_next S) E E model model (s_rgs S) _ Hbw (agree_refl _ _) Hshape eq_refl Hrl).
  - apply (frz_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho'. unfold outside in *. rewrite Forall_forall in *. intros R0 HR0.
      destruct (In_nth_error _ _ HR0) as (j & Hj). cbn [S2 s_rgs] in Hj.
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-. unfold rsz in *. rewrite Hb', Hs'. exact (Ho' R (nth_error_In _ _ Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. exact (Ho' R0 (nth_error_In _ _ Hj)).
    + intros w _ _. reflexivity.
  - apply (own_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho'. exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Ho').
    + intros w _. reflexivity.
    + intros x Hx. exact Hx.
Qed.
#[using="Type"] Theorem den_rz_track : forall model0 E S M ms model i k0 S', DEN segs LIMIT model0 mem0 E S M ms model -> rz_track_post S i k0 = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0. intros model0 E S M ms model i k0 S' Hd Hp. exact (den_rz_trackn model0 E S M ms model i k0 8 S' Hd Hp). Qed.
End Recont.
