(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition NP_okA (NP : positive) : Prop := (V_TOP < NP)%positive.
Lemma NP_okA_intro : forall NP, (V_TOP <? NP)%positive = true -> NP_okA NP.
Proof. intros NP H. apply Pos.ltb_lt. exact H. Qed.

Ltac cm_stack H := first [exact H | match goal with E : aa_geom _ = aa_geom _ |- _ => first [rewrite E; exact H | rewrite <- E; exact H] end].
Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Section WithSegs.
Variable segs : list Segment.

Hypothesis HTOP : InitState.segs_top segs <= IMG_HI.

Lemma find_segment_none_high : forall a : word, IMG_HI <= bv_unsigned a -> find_segment segs (bv_unsigned a) 1 = None.
Proof using HTOP.
  intros a Ha. destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:E0; [|reflexivity].
  exfalso. pose proof (InitState.find_segment_top segs (bv_unsigned a) 1 seg ltac:(lia) E0). lia.
Qed.
Lemma image_byte_none_high : forall a : word, IMG_HI <= bv_unsigned a -> image_byte segs a = None.
Proof using HTOP. intros a Ha. unfold image_byte, memory_read. rewrite find_segment_none_high by exact Ha. reflexivity. Qed.
Lemma rd_of_high : forall m (a : word), IMG_HI <= bv_unsigned a -> rd_of segs m a = m a.
Proof using HTOP. intros m a Ha. unfold rd_of. destruct (m a); [reflexivity|]. apply image_byte_none_high. exact Ha. Qed.
Lemma wview_high : forall m (a : word), IMG_HI <= bv_unsigned a -> wview segs m a = m a.
Proof using HTOP. intros m a Ha. unfold wview. destruct (m a); [reflexivity|]. rewrite find_segment_none_high by exact Ha. reflexivity. Qed.
Lemma rd_high : forall ms (a : word), rom_ok segs ms -> IMG_HI <= bv_unsigned a -> rd ms a = ms_mem ms a.
Proof using HTOP.
  intros ms a Hrom Ha. unfold rd, ms_read_byte. destruct (ms_mem ms a) eqn:E0; [reflexivity|].
  rewrite (Hrom a). apply image_byte_none_high. exact Ha.
Qed.

Lemma smatchA_unobj : forall rho A objs R tp tr ms md,
  ss_objs (ax_S A) = objs ++ R -> smatchA segs rho tp A (tr, mkCfg ms md) ->
  smatchA segs (rho_absorb rho R (vms md tp ms)) tp (ax_setS A (set_objs (ax_S A) objs)) (tr, mkCfg ms md).
Proof using .
  intros rho A objs R tp tr ms md Ho Hsm.
  exact (proj1 (SPA_unobj segs (fun _ _ _ _ => True) rho A objs R tp tr ms md Ho (conj Hsm I) (fun _ => I))).
Qed.

Lemma released_bytesA : forall rho A objs R o tp tr ms md,
  ss_objs (ax_S A) = objs ++ R -> In o R -> smatchA segs rho tp A (tr, mkCfg ms md) ->
  dflt_writable (ob_dflt o) = true -> IMG_HI <= fst (obj_range rho o) -> snd (obj_range rho o) <= 2 ^ 63 ->
  let rho' := rho_absorb rho R (vms md tp ms) in
  (forall z, fst (obj_range rho o) <= z < snd (obj_range rho o) -> rm rho' (Z_to_bv 64 z) <> None)
  /\ (forall off v, In (mkCell (SLit off) 8 v) (ob_cells o) -> - 2 ^ 62 <= off < 2 ^ 62 ->
        rd64 (rm rho') (bv_unsigned (eval rho (ob_base o)) + off) = Some (bv_unsigned (eval rho v))).
Proof using HTOP.
  intros rho A objs R o tp tr ms md Ho HoR (Hsm & _) Hdw Hlo Hhi rho'.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [virt fst snd cfg_ms cfg_model] in *.
  assert (Hin_o : In o (ss_objs (ax_S A))) by (rewrite Ho; apply in_or_app; right; exact HoR).
  pose proof (proj1 (Forall_forall _ _) Hall o Hin_o) as Hoh.
  unfold obj_range in *. cbn [fst snd] in *.
  set (bb := bv_unsigned (eval rho (ob_base o))) in *.
  destruct Hoh as (Hrng & Hwv & Hcells & _ & _).
  assert (INR : forall z, bb + obj_lo_of rho o <= z < bb + obj_hi_of rho o -> in_ranges rho R (Z_to_bv 64 z)).
  { intros z Hz. exists o. split; [exact HoR|]. unfold obj_range. cbn [fst snd]. fold bb. rewrite u64_of_sum by lia. exact Hz. }
  assert (BY : forall z, bb + obj_lo_of rho o <= z < bb + obj_hi_of rho o -> exists x, rm rho' (Z_to_bv 64 z) = Some x /\ ms_mem (vms md tp ms) (Z_to_bv 64 z) = Some x).
  { intros z Hz. unfold rho'. rewrite (rm_absorb_in rho R _ _ (INR z Hz)).
    pose proof (Hwv (z - bb) ltac:(lia) Hdw) as W. fold bb in W. replace (bb + (z - bb)) with z in W by lia.
    rewrite wview_high in W by (rewrite u64_of_sum by lia; lia). cbn [w_cfg w_tr cfg_model cfg_ms fst snd] in W.
    destruct (ms_mem (vms md tp ms) (Z_to_bv 64 z)) as [x|]; [exists x; auto | exfalso; exact (W eq_refl)]. }
  split.
  - intros z Hz. destruct (BY z Hz) as (x & Hx & _). rewrite Hx. discriminate.
  - intros off v Hcell Hoff. pose proof (proj1 (Forall_forall _ _) Hcells _ Hcell) as CH.
    unfold cell_holds in CH. cbn [c_off c_width c_val] in CH. rewrite soff_lit_small in CH by lia.
    destruct CH as (C1 & C2 & C3). change (Z.to_nat 8) with 8%nat in C3.
    apply rd64_of_bytes. intros j Hj.
    assert (Hz : bb + obj_lo_of rho o <= bb + off + Z.of_nat j < bb + obj_hi_of rho o) by lia.
    destruct (BY _ Hz) as (x & Hx1 & Hx2). rewrite Hx1.
    pose proof (rd_bytes_nth (vms md tp ms) 8 (oaddr rho (ob_base o) off) _ j C3 Hj) as RB.
    rewrite oaddr_unsigned in RB by lia. fold bb in RB. cbn [c_val] in RB. specialize (RB ltac:(lia)).
    rewrite rd_high in RB; [| exact Hrom | rewrite u64_of_sum by lia; lia]. rewrite Hx2 in RB. exact RB.
Qed.

Definition plain_obj (base hi : sv) : sobj := mkObj base (SLit 0) hi [] DUnknown.

Lemma SPA_carve_plain : forall (J : jpredA) rho A tp w base hi nx,
  SPA segs J A rho tp w ->
  let S := ax_S A in
  let S' := mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [plain_obj base hi]) (ss_facts S) nx (ss_lenient S) in
  swf S' = true -> (ss_next S <= nx)%positive ->
  let b := bv_unsigned (eval rho base) in let h := bv_unsigned (eval rho hi) in
  h < 2 ^ 63 -> b + h <= 2 ^ 64 ->
  Forall (fun o' => ranges_disjoint (obj_range rho o') (b, b + h)) (ss_objs S) ->
  (forall z, b <= z < b + h -> exists x, rm rho (Z_to_bv 64 z) = Some x) ->
  xwords_clear rho A b (b + h) ->
  SPA segs J (ax_setS A S') rho tp w.
Proof using .
  intros J rho A tp w base hi nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S S' Hwf' Hnx b h Hh Hbh Hdisj Hdef Hxs.
  subst S. split; [|exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    exact (TobjJVA.smatch_carve_plain segs rho (ax_S A) _ base hi nx Hsm Hwf' Hh Hbh Hdisj Hdef).
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta.
    unfold obj_range, obj_lo_of, obj_hi_of, plain_obj. cbn [ob_base ob_lo ob_hi fst snd]. fold b.
    rewrite soff_lit_small by lia.
    assert (Hsoff : soff rho hi = h).
    { unfold soff. rewrite bv_signed_U. fold h. pose proof (bv_urange (eval rho hi)) as Rh. fold h in Rh. destruct (Zsigned_spec h) as [[_ X]|[X _]]; [exact X | lia]. }
    rewrite Hsoff. destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2.
    pose proof (Hxs rr y j Hr Hy Hj). lia.
Qed.

Lemma rw_set3 : forall rho n (x y z : word),
  let rho' := rho_set_rw (rho_set_rw (rho_set_rw rho n x) (n + 1) y) (n + 2) z in
  rw rho' n = x /\ rw rho' (n + 1)%positive = y /\ rw rho' (n + 2)%positive = z /\ agree_below n rho rho'.
Proof using .
  intros rho n x y z. unfold rho_set_rw. cbn [rw].
  assert (E1 : Pos.eqb n (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (E2 : Pos.eqb n (n + 1) = false) by (apply Pos.eqb_neq; lia).
  assert (E3 : Pos.eqb (n + 1) (n + 2) = false) by (apply Pos.eqb_neq; lia).
  rewrite E1, E2, E3, !Pos.eqb_refl. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|split; [intros; reflexivity | intros; reflexivity]].
  intros i Hi. cbn [rw].
  assert (F1 : Pos.eqb i (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (F2 : Pos.eqb i (n + 1) = false) by (apply Pos.eqb_neq; lia).
  assert (F3 : Pos.eqb i n = false) by (apply Pos.eqb_neq; lia).
  rewrite F1, F2, F3. reflexivity.
Qed.

Lemma swf_facts_suffix : forall pc regs fregs fcsr resv objs F G nx lm,
  swf (mkSS pc regs fregs fcsr resv objs (F ++ G) nx lm) = true ->
  swf (mkSS pc regs fregs fcsr resv objs G nx lm) = true.
Proof using .
  intros pc regs fregs fcsr resv objs F G nx lm H. unfold swf in *.
  cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts] in *.
  apply andb_prop in H as [H HF]. rewrite H. cbn [andb]. rewrite forallb_app in HF. apply andb_prop in HF as [_ HG]. exact HG.
Qed.

Definition POT (u : sv) : list bitem := [BI 1 0 [(1, AMin u 2 66 AV0)] 0; BI 0 1 [(1, AMin u 4 4 AK0)] 0].

Lemma POT_vals : forall rho u, bsumV (POT u) rho = potV (uval rho u) /\ bsumK (POT u) rho = potK (uval rho u)
  /\ bd_nn (POT u) rho /\ bd_wpos (POT u) = true.
Proof.
  intros rho u. pose proof (uval_range rho u) as R. unfold POT, potV, potK, AV0, AK0, KU. cbn [bsumV bsumK bi_v bi_k].
  unfold bival. cbn [lfval aval bi_f bi_c]. unfold AV0, AK0, KU.
  split; [lia|]. split; [lia|]. split; [|reflexivity].
  repeat constructor; unfold bival; cbn [lfval aval bi_f bi_c]; unfold AV0, AK0, KU; lia.
Qed.

Lemma BUD_pot_items : forall b BX pv pk kc V Km Kf rho u,
  BUD b (fst (bx2 BX) + pv, snd (bx2 BX) + pk + kc) V Km Kf rho ->
  0 <= fst (bx2 BX) -> 0 <= snd (bx2 BX) -> 0 <= kc ->
  potV (uval rho u) = pv -> potK (uval rho u) = pk ->
  BUD (b ++ POT u) (fst (bx2 BX) + 0, snd (bx2 BX) + 0 + kc) V Km Kf rho.
Proof.
  intros b BX pv pk kc V Km Kf rho u H HX1 HX2 Hkc Ev Ek.
  destruct (POT_vals rho u) as (P1 & P2 & P3 & P4). rewrite Ev in P1. rewrite Ek in P2.
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). cbn [fst snd] in *.
  unfold BUD. cbn [fst snd]. rewrite bsumV_app, bsumK_app, bd_wpos_app, P1, P2, Hw, P4.
  split; [lia|]. split; [lia|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [reflexivity|].
  split; [apply bd_nn_app; split; [exact Hn | exact P3]|]. lia.
Qed.

Lemma BUD_const_items : forall b BX pv pk kc V Km Kf rho,
  BUD b (fst (bx2 BX) + pv, snd (bx2 BX) + pk + kc) V Km Kf rho ->
  0 <= fst (bx2 BX) -> 0 <= snd (bx2 BX) -> 0 <= kc -> 0 <= pv -> 0 <= pk ->
  BUD (b ++ [BIc 1 0 pv; BIc 0 1 pk]) (fst (bx2 BX) + 0, snd (bx2 BX) + 0 + kc) V Km Kf rho.
Proof.
  intros b BX pv pk kc V Km Kf rho H HX1 HX2 Hkc Hpv Hpk.
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). cbn [fst snd] in *.
  unfold BUD. cbn [fst snd]. rewrite bsumV_app, bsumK_app, bd_wpos_app, Hw. unfold BIc. cbn [bsumV bsumK bi_v bi_k bd_wpos forallb andb Z.leb].
  unfold bival. cbn [lfval bi_f bi_c].
  split; [lia|]. split; [lia|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [reflexivity|].
  split; [apply bd_nn_app; split; [exact Hn | repeat constructor; unfold bival; cbn [lfval bi_f bi_c]; lia]|]. lia.
Qed.

Lemma BUD_bx_drop : forall b x1 x2 pv pk V Km Kf rho,
  BUD b (x1 + pv, x2 + pk) V Km Kf rho -> 0 <= x1 -> 0 <= x2 -> 0 <= pv -> 0 <= pk -> BUD b (x1, x2) V Km Kf rho.
Proof.
  intros b x1 x2 pv pk V Km Kf rho H H1 H2 H3 H4. pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). cbn [fst snd] in *.
  unfold BUD. cbn [fst snd]. repeat (split; [first [assumption | lia]|]). lia.
Qed.

Variable E : aentry.
Variable AInv : AA -> valuation -> list word -> Model -> Prop.
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : forall a, in_rangesZ CST a -> 0 <= a < IMG_HI.
Ltac hcst H := match type of H with _ /\ _ => let H' := fresh in destruct H as [H H']; apply HCST in H | _ => apply HCST in H end.
Hypothesis HXGL : forall a, in_rangesZ XGL a -> 0 <= a < IMG_HI.

Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : list (Z * Z * Z).
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.
Hypothesis HNP : NP_okA NP.

Let JAi := JAi AInv CST XGL NP Kc rho0 P0f FB FF BX PA.
Let JA := JA AInv CST XGL NP Kc rho0 P0f FB FF BX PA.

Lemma T_ok_of_TPA : forall rho Ai, agree_vals NP rho0 rho -> TPA rho0 Ai -> T_ok rho (topG (aa_geom Ai)).
Proof using HNP. intros rho Ai Hav HT. exact (T_of_TPA NP rho0 rho Ai Hav HNP HT). Qed.

Definition robjs_okF (rho : valuation) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (R : list sobj) : Prop :=
  forall o a, In o R -> fst (obj_range rho o) <= a < snd (obj_range rho o) ->
    pclMA CST rho0 (FBx FB rho tv) (FFx FF rho fr) a \/ 0 <= a < IMG_HI.

Definition xrs_ok47 (rho : valuation) (X : list (sv * sv)) : Prop :=
  forall r a, In r X -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) -> 0 <= a < 2 ^ 47.

Lemma chain_block_free : forall Ai rho tp md tv fr R b n a,
  AInv Ai rho tp md -> fbinA FB Ai -> ffinA FF Ai -> TPA rho0 Ai -> tvinA FB Ai rho tv -> frinA FF Ai rho fr ->
  robjs_okF rho tv fr R ->
  In (b, n) (aa_live Ai) -> ~ In (b, n) FB -> untracked rho tv (b, n) -> b <= a < b + n ->
  forall o, In o R -> ~ (fst (obj_range rho o) <= a < snd (obj_range rho o)).
Proof using ALA HCST.
  intros Ai rho tp md tv fr R b n a HM HB HFF HT HN HFR HR Hin Hnfb Hut Ha o Ho Hr.
  assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (fbinA_FBx FB Ai rho tv [] HB HNx) as FBX. pose proof (ffinA_FFx FF Ai rho fr HFF HFR) as FFX.
  assert (Hut' : untracked rho (tv ++ []) (b, n)) by (rewrite app_nil_r; exact Hut).
  destruct (untracked_kept_FBx FB rho tv [] b n Hut' Hnfb) as [HnF _].
  destruct (HR o a Ho Hr) as [Hc|Himg].
  - exact (live_not_pclMA segs AInv CST ALA HCST rho0 Ai rho tp md (FBx FB rho tv) (FFx FF rho fr) b n a HM FBX FFX HT Hin HnF Ha Hc).
  - destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (_ & HBl & _). destruct (HBl b n Hin) as (_ & _ & _ & _ & G5).
    unfold IMG_HI, HIGH_SHADOW_END in *. lia.
Qed.

Definition hdr_cells (n : positive) : list (Z * nat * sv) :=
  [(0, 8%nat, SVar n); (8, 8%nat, SVar (n + 1)); (16, 8%nat, SVar (n + 2))].
Definition e32 (cap : sv) : sv := SAlu ALU_ADD cap (SLit 32).
Definition open_factsA (hd : sv) (n : positive) : list sprop :=
  [SPUle (SVar (n + 2)) (SVar (n + 1));
   SPUle (SLit 65536) (SVar (n + 1));
   SPUle (SVar (n + 1)) (SLit (2 ^ 40 - 33));
   SPUle (SAlu ALU_ADD hd (e32 (SVar (n + 1)))) (SLit 140737479966720);
   SPUle hd (SLit 140737479966720); SPUle (SLit 4096) hd;
   SPUle (SAlu ALU_ADD hd (e32 (SVar (n + 1)))) (SVar V_TOP)]
  ++ match hd with SVar v => [SPAlign v 4] | _ => [] end.
Definition open_stateA (A : axst) (hd : sv) : axst :=
  let S := ax_S A in let n := ss_next S in
  let S' := mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                 (ss_objs S ++ [carved hd 0 24 (hdr_cells n)]) (ss_facts S) (n + 3) (ss_lenient S) in
  ax_with_facts (ax_setX (ax_setS A S') ((hd, e32 (SVar (n + 1))) :: ax_X A)) (open_factsA hd n ++ ss_facts S).

Lemma JA_open : forall tv fr bd hd pot (A : axst) rho tp w,
  swf (ax_S (open_stateA A hd)) = true ->
  ax_base A = SLit SHADOW_OFF ->
  (NP <=? ss_next (ax_S A))%positive = true -> nd_below (ss_next (ax_S A)) (NDA tv fr bd (AHead hd pot)) = true ->
  existsb (sprop_eqb (SPNot (SPBranch BC_EQ hd (SLit 0)))) (ss_facts (ax_S A)) = true ->
  (forall Ai rho1 tp1 md1, Forall (holds rho) (ss_facts (ax_S A)) -> P0f rho0 -> agree_vals NP rho0 rho -> AInv Ai rho1 tp1 md1 -> TPA rho0 Ai -> T_ok rho (topG (aa_geom Ai)) ->
      robjs_okF rho tv fr (ss_objs (ax_S A)) /\ xrs_ok47 rho (ax_X A)) ->
  SPA segs (JA (NDA tv fr bd (AHead hd pot))) A rho tp w ->
  exists rho', agree_below (ss_next (ax_S A)) rho rho'
    /\ SPA segs (JA (NDA tv fr (bd ++ (if pot then POT (SVar (ss_next (ax_S A) + 2)) else [])) (AOpen hd (SVar (ss_next (ax_S A))) (SVar (ss_next (ax_S A) + 1)) [])))
           (open_stateA A hd) rho' tp w.
Proof using ALA HCST HXGL HBX HKc HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd pot A rho tp w Hwf Hbase Hnp Hnb Hnz HSITE [Hsm (Ai & kc & HJ)].
  destruct w as [tr [ms md]]. apply Pos.leb_le in Hnp.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  destruct (HSITE Ai rho tp md HF HP0 Hav HM HT (T_ok_of_TPA rho Ai Hav HT)) as [HROK HX47].
  destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba). cbn [nd_tv nd_fr nd_bd nd_am am_below] in Hbt, Hbf, Hbb, Hba.

  unfold XA in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU uval] in HXA. destruct HXA as (ns & HC & Hkc).
  assert (Hh : uval rho hd <> 0).
  { exact (tnz_of_fact rho hd (SLit 0) (holds_mem _ _ _ HF Hnz)). }
  destruct HC as (HA & HNS & HND).
  destruct (achain_cons (rm rho) _ ns HA Hh) as (cap & r & ->). pose proof HA as HA0.
  cbn [achain] in HA. destruct HA as (_ & _ & Hcap0 & Hrd8 & (u & Hrd16 & Hu) & Hdef & (nx & Hrd0 & HAr)).
  set (h := uval rho hd) in *.
  pose proof (Forall_inv HNS) as HNh. pose proof (Forall_inv_tail HNS) as HNr.
  destruct HNh as (Hlive & Hnfb & Hut & Hcap & Hcap32 & Hxm). cbn [fst snd] in Hlive, Hnfb, Hut, Hcap, Hcap32, Hxm.
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr).
  destruct (HBl h (HDR + cap) Hlive) as (G1 & G2 & G3 & G4 & G5). unfold HDR in G4, G5. unfold HDR in Hcap32.
  pose proof (rd64_range _ _ _ Hrd0) as Rnx. pose proof (rd64_range _ _ _ Hrd8) as Rcap. pose proof (rd64_range _ _ _ Hrd16) as Ru.
  set (n := ss_next (ax_S A)) in *.
  destruct (rw_set3 rho n (Z_to_bv 64 nx) (Z_to_bv 64 cap) (Z_to_bv 64 u)) as (R0 & R1 & R2 & Hag).
  set (rho' := rho_set_rw (rho_set_rw (rho_set_rw rho n (Z_to_bv 64 nx)) (n + 1) (Z_to_bv 64 cap)) (n + 2) (Z_to_bv 64 u)) in *.
  exists rho'. split; [exact Hag|].
  assert (Hrm : rm rho' = rm rho) by reflexivity.
  assert (Ehd : eval rho' hd = eval rho hd) by (symmetry; apply (eval_agree n); [exact Hag | exact Hba]).
  clearbody rho'.
  pose proof (agree_below_vals _ _ _ Hag) as Hagv.
  assert (Ucap : bv_unsigned (rw rho' (n + 1)%positive) = cap) by (rewrite R1, Z_to_bv_unsigned; apply bv_wrap_small; rewrite two64; lia).
  assert (Uu : bv_unsigned (rw rho' (n + 2)%positive) = u) by (rewrite R2, Z_to_bv_unsigned; apply bv_wrap_small; rewrite two64; lia).
  assert (Unx : bv_unsigned (rw rho' n) = nx) by (rewrite R0, Z_to_bv_unsigned; apply bv_wrap_small; rewrite two64; lia).
  assert (Uhd : bv_unsigned (eval rho' hd) = h) by (rewrite Ehd; reflexivity).

  assert (DISJ : forall a, h <= a < h + (HDR + cap) -> forall o, In o (ss_objs (ax_S A)) -> ~ (fst (obj_range rho o) <= a < snd (obj_range rho o))).
  { intros a Ha. eapply (chain_block_free Ai rho tp md tv fr); eauto. }
  assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (fbinA_FBx FB Ai rho tv [] HB HNx) as FBX. pose proof (ffinA_FFx FF Ai rho fr HFF HFR) as FFX.

  pose proof (smatchA_agree segs rho rho' tp A _ Hag Hsm) as Hsm'.
  assert (Hwf1 : swf (mkSS (ss_pc (ax_S A)) (ss_regs (ax_S A)) (ss_fregs (ax_S A)) (ss_fcsr (ax_S A)) (ss_resv (ax_S A))
                           (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n)]) (ss_facts (ax_S A)) (n + 3) (ss_lenient (ax_S A))) = true).
  { unfold open_stateA, ax_with_facts, with_facts in Hwf.
    cbn [ax_S ax_setX ax_setS ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf. fold n in Hwf.
    eapply swf_facts_suffix. exact Hwf. }
  assert (SP1 : SPA segs (JAi (NDA tv fr bd (AHead hd pot)) Ai kc)
                    (ax_setS A (mkSS (ss_pc (ax_S A)) (ss_regs (ax_S A)) (ss_fregs (ax_S A)) (ss_fcsr (ax_S A)) (ss_resv (ax_S A))
                           (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n)]) (ss_facts (ax_S A)) (n + 3) (ss_lenient (ax_S A))))
                    rho' tp (tr, mkCfg ms md)).
  { apply (SPA_carve_obj segs (JAi (NDA tv fr bd (AHead hd pot)) Ai kc) rho' A tp (tr, mkCfg ms md) hd 0 24 (hdr_cells n) (n + 3)).
    - split; [exact Hsm'|]. eapply (JAi_stable segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA n); [lia | exact Hnb | exact Hag | apply mat_equiv_refl | exact HJ].
    - exact Hwf1.
    - lia.
    - lia. - lia. - lia. - lia.
    - rewrite Uhd. lia.
    - rewrite Uhd. lia.
    - unfold hdr_cells, cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - apply Forall_forall. intros o Ho. rewrite Uhd.
      rewrite (obj_range_agree_vals n rho rho' o Hagv (proj1 (forallb_forall _ _) (swf_objs _ (smatch_swf segs _ _ _ (proj1 Hsm))) o Ho)).
      destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
      apply (DISJ a ltac:(unfold HDR; lia) o Ho). rewrite Eo. cbn [fst snd]. exact Ha1.
    - intros off Hoff. rewrite Hrm, Uhd. unfold wok_of, rd_of.
      destruct (rm rho (Z_to_bv 64 (h + off))) as [x|] eqn:Ex; [split; [reflexivity | exists x; reflexivity]|].
      exfalso. apply (Hdef (h + off)); [unfold HDR; lia | exact Ex].
    - unfold hdr_cells, cells_in_view. rewrite Hrm, Uhd.
      repeat constructor; intros j Hj; cbn [eval]; rewrite ?R0, ?R1, ?R2; unfold rd_of.
      + rewrite Z.add_0_r. rewrite (rd64_enc_bytes (rm rho) h nx Hrd0 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 8) cap Hrd8 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 16) u Hrd16 j Hj). reflexivity.
    -
      intros rr y j Hr Hy Hj Hin. rewrite Hbase in Hin. cbn [eval] in Hin. rewrite lit_unsigned in Hin. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hin.
      rewrite Uhd in Hin.
      pose proof Hsm' as (_ & _ & HwfA & _). unfold axwf in HwfA. apply andb_prop in HwfA as [HXb _].
      pose proof (proj1 (forallb_forall _ _) HXb rr Hr) as Yb. unfold xr_below in Yb. apply andb_prop in Yb as [Yb1 Yb2].
      rewrite <- (eval_agree n rho rho' _ Hag Yb1), <- (eval_agree n rho rho' _ Hag Yb2) in Hy.
      pose proof (HX47 rr y Hr ltac:(unfold uval; exact Hy)) as Hy47.
      pose proof (word_byte_of_shadow (Sh y) j (Sh_is_shadow y Hy47) Hj) as WS.
      destruct (word_byte_range (Sh y) j ltac:(pose proof (Sh_is_shadow y Hy47) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia) Hj) as (_ & EWB & _).
      rewrite EWB in WS. unfold Sh in WS. replace (y / 8 + SHADOW_OFF) with (SHADOW_OFF + y / 8) in WS by lia.
      unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold HDR in Hin. lia. }

  set (A1 := ax_setS A (mkSS (ss_pc (ax_S A)) (ss_regs (ax_S A)) (ss_fregs (ax_S A)) (ss_fcsr (ax_S A)) (ss_resv (ax_S A))
                           (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n)]) (ss_facts (ax_S A)) (n + 3) (ss_lenient (ax_S A)))) in SP1.
  assert (XB : xr_below (ss_next (ax_S A1)) (hd, e32 (SVar (n + 1))) = true).
  { subst A1. unfold xr_below. cbn [fst snd ax_S ax_setS ss_next e32 sv_below]. rewrite (sv_below_mono n (n + 3) hd ltac:(lia) Hba). cbn [andb]. rewrite andb_true_r. apply Pos.ltb_lt. lia. }
  assert (XOK : xr_ok rho' (ss_objs (ax_S A1)) (bv_unsigned (eval rho' (ax_base A1))) (hd, e32 (SVar (n + 1)))).
  { subst A1. cbn [ax_base ax_setS ax_S ss_objs fst snd]. rewrite Hbase. cbn [eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
      unfold xr_ok. cbn zeta. cbn [fst snd]. rewrite Uhd. unfold e32. rewrite U_add, U_lit. cbn [eval]. rewrite Ucap. unfold M64v. rewrite (Z.mod_small 32) by lia. rewrite (Z.mod_small (cap + 32)) by lia.
      destruct Hxm as [Xal Xm]. split; [exact Xal|]. split; [lia|].
      intros a Ha. assert (Ha47 : 0 <= a < 2 ^ 47) by (unfold HDR in Ha; lia). pose proof (Sh_is_shadow a Ha47) as HSa.
      destruct (Xm a ltac:(unfold HDR; lia)) as [XW (v & Xv1 & Xv2)].
      assert (OUTW : forall j, 0 <= j < 8 -> outside_all rho' (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n)]) (word_byte (SHADOW_OFF + a / 8) j)).
      { intros j Hj. pose proof (word_byte_of_shadow (Sh a) j HSa Hj) as WS.
        replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
        apply outside_all_app_iff. split.
        - eapply (outside_all_exts n rho rho'); [reflexivity | exact (swf_objs _ (smatch_swf segs _ _ _ (proj1 Hsm))) | exact Hag |].
          unfold outside_all. apply Forall_forall. intros o Ho Hr.
          destruct (HROK o _ Ho Hr) as [Hc|Himg]; [|unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in WS; unfold IMG_HI in Himg; lia].
          pose proof (law_client_app _ _ _ ALA Ai rho tp md _ HM (pclFA_client CST _ _ _ Ai _ FBX FFX HT (pclMA_pclFA _ _ _ _ _ Hc))) as APP.
          unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in APP. top_rng APP. unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in WS. lia.
        - unfold outside_all. repeat constructor. unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi fst snd].
          rewrite !soff_lit_small by lia. rewrite Uhd. unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in WS. unfold HIGH_SHADOW_END in G5. unfold HDR in *. lia. }
      split; [pose proof HSa as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END, Sh in SS; lia|].
      split; [rewrite shadow_addr_word_byte; apply OUTW; apply Z.mod_pos_bound; lia|].
      split; [intros j Hj; split; [apply OUTW; exact Hj | rewrite Hrm; exact (XW j Hj)]|].
      exists v. rewrite Hrm. split; [exact Xv1 |]. unfold HDR in Xv2. replace (h + (cap + 32)) with (h + (32 + cap)) by lia. exact Xv2. }
  pose proof (SPA_x_publish segs _ rho' A1 _ tp _ XB XOK SP1) as SP2.

  assert (FB' : forallb (sprop_below (ss_next (ax_S (ax_setX A1 ((hd, e32 (SVar (n + 1))) :: ax_X A1))))) (open_factsA hd n ++ ss_facts (ax_S A)) = true).
  { subst A1. cbn [ax_S ax_setX ax_setS ss_next]. rewrite forallb_app. apply andb_true_intro. split.
      * unfold open_stateA, ax_with_facts, with_facts in Hwf.
        cbn [ax_S ax_setX ax_setS ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf. fold n in Hwf.
        pose proof (swf_facts _ Hwf) as WFF. cbn [ss_facts ss_next] in WFF. rewrite forallb_app in WFF. apply andb_prop in WFF as [W1 _]. exact W1.
      * apply forallb_forall. intros q Hq. eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) (swf_facts _ (smatch_swf segs _ _ _ (proj1 Hsm))) q Hq)]. lia. }
  assert (FH : Forall (holds rho') (ss_facts (ax_S (ax_setX A1 ((hd, e32 (SVar (n + 1))) :: ax_X A1)))) -> Forall (holds rho') (open_factsA hd n ++ ss_facts (ax_S A))).
  { subst A1. cbn [ax_S ax_setX ax_setS ss_facts]. intros HF'. apply Forall_app. split; [|exact HF'].
      unfold open_factsA. apply Forall_app. split.
      * unfold e32.
        assert (E1 : bv_unsigned (eval rho' (SAlu ALU_ADD (SVar (n + 1)) (SLit 32))) = cap + 32).
        { rewrite U_add, U_lit. cbn [eval]. rewrite Ucap. unfold M64v. rewrite (Z.mod_small 32) by lia. apply Z.mod_small. lia. }
        assert (E2 : bv_unsigned (eval rho' (SAlu ALU_ADD hd (SAlu ALU_ADD (SVar (n + 1)) (SLit 32)))) = h + (cap + 32)).
        { rewrite U_add, E1, Uhd. unfold M64v. apply Z.mod_small. lia. }
        assert (ET : bv_unsigned (rw rho' V_TOP) = topG (aa_geom Ai)).
        { rewrite <- (proj1 Hag V_TOP ltac:(unfold NP_okA in HNP; lia)). exact (proj1 (T_ok_of_TPA rho Ai Hav HT)). }
        repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?E2, ?E1, ?U_lit, ?Uhd; cbn [eval]; rewrite ?Ucap, ?Uu, ?ET; unfold M64v;
          rewrite ?Z.mod_small by lia; lia.
      * destruct hd as [v| | | | | | |]; try apply Forall_nil. apply Forall_cons; [|apply Forall_nil]. cbn [holds]. cbn [eval] in Uhd. rewrite Uhd.
        change (2 ^ 4) with 16. split; [lia | exact G2]. }
  pose proof (SPA_refacts segs _ rho' _ (open_factsA hd n ++ ss_facts (ax_S A)) tp (tr, mkCfg ms md) SP2 FB' FH) as SP3.
  subst A1. unfold open_stateA. fold n. split; [exact (proj1 SP3)|].

  { exists Ai, kc.
    assert (HJ' : JAi (NDA tv fr bd (AHead hd pot)) Ai kc rho' tp tr md).
    { eapply (JAi_stable segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA n); [lia | exact Hnb | exact Hag | apply mat_equiv_refl | exact HJ]. }
    pose proof HJ' as (Hav' & _ & HM' & HT' & _ & _ & (HN' & HD' & HZ') & HFR' & HK0' & _ & HXA' & HBU' & HPA').
    cbn [nd_tv nd_fr nd_bd nd_am] in HN', HD', HZ', HFR', HXA', HBU'.
    split; [exact Hav'|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HT'|]. split; [exact HB|]. split; [exact HFF|].
    split; [split; [exact HN'|split; [exact HD'|exact HZ']]|]. split; [exact HFR'|]. split; [exact HK0'|]. split; [exact HP0|].
    cbn [nd_tv nd_fr nd_bd nd_am]. refine (conj _ (conj _ HPA')).
    +
      unfold XA. split.
      { cbn -[chainZ KU uval HDR untrackedZ tvals]. unfold uval. cbn [eval]. rewrite Uhd, Unx, Ucap.
      split; [exact Hh|]. split; [exact Hlive|]. split; [exact Hnfb|].
      split; [unfold untracked in Hut; rewrite (tvals_agree n rho rho' tv Hagv Hbt); exact Hut|].
      split; [exact Hcap|]. split; [unfold HDR; lia|].
      split; [intros z Hz; rewrite Hrm; apply Hdef; unfold HDR in *; lia|]. split; [constructor|].
      exists r. split.
      * split; [rewrite Hrm; exact HAr|]. split; [|inversion HND; assumption].
        apply Forall_forall. intros bc Hbc. destruct (proj1 (Forall_forall _ _) HNr bc Hbc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
        split; [exact Y1|]. split; [exact Y2|]. split; [rewrite (tvals_agree n rho rho' tv Hagv Hbt); exact Y3|].
        split; [exact Y4|]. split; [exact Y5|]. rewrite Hrm. exact Y6.
      * split; [|rewrite Hkc; cbn [length]; rewrite Nat2Z.inj_succ; lia].
        inversion HND; subst. intros Hin'. apply H1. apply list_elem_of_In. exact Hin'. }
      {
        cbn [am_eval map]. unfold uval. cbn [eval]. rewrite Uhd, Unx, Ucap. rewrite Hrm, (tvals_agree n rho rho' tv Hagv Hbt).
        apply (lcenZ_mode FB (AHz h pot) _ Ai (rm rho) (tvals rho tv)); [|exact HCEN].
        intros bn. exact (proj1 (amblkZ_open_iff (rm rho) h pot nx cap [] r HA0 HAr bn)). }
    +
      pose proof (XAz_kc_nonneg _ _ _ _ _ _ HXA') as Hkc0.
      unfold apot in HBU'. cbn [am_eval apotz] in HBU'. unfold bxa in HBU' |- *. cbn [apot am_eval apotz fst snd].
      destruct pot.
      * unfold areq in HBU'. fold h in HBU'. unfold uval in HBU'. rewrite Uhd in HBU'.
        destruct (Z.eqb_spec h 0) as [E0|_]; [exfalso; exact (Hh E0)|]. rewrite Hrm, Hrd16 in HBU'. cbn [fst snd] in HBU'.
        eapply BUD_pot_items; [exact HBU' | exact (proj1 (BXok_d_pair _ BX HBX)) | exact (proj2 (BXok_d_pair _ BX HBX)) | exact Hkc0 | |]; unfold uval; cbn [eval]; rewrite Uu; reflexivity.
      * cbn [fst snd] in HBU'. rewrite app_nil_r. exact HBU'. }
Qed.

Lemma JA_pot_out0 : forall tv fr bd hd (A : axst) rho tp w,
  existsb (sprop_eqb (SPBranch BC_EQ hd (SLit 0))) (ss_facts (ax_S A)) = true ->
  SPA segs (JA (NDA tv fr bd (AHead hd true))) A rho tp w ->
  SPA segs (JA (NDA tv fr (bd ++ [BIc 1 0 AV0; BIc 0 1 AK0]) (AHead hd false))) A rho tp w.
Proof using HBX.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd A rho tp w Hz [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  assert (Hh : uval rho hd = 0).
  { pose proof (holds_mem _ _ _ HF Hz) as F0. zf F0. rewrite uval_lit in F0 by lia. exact F0. }
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [exact HXA|]. split; [|exact HPA].
  unfold apot in HBU |- *. cbn [am_eval apotz] in HBU |- *. unfold areq in HBU. rewrite Hh in HBU. cbn [Z.eqb fst snd] in HBU.
  unfold bxa in HBU |- *. cbn [fst snd] in HBU |- *.
  eapply BUD_const_items; [exact HBU | exact (proj1 (BXok_d_pair _ BX HBX)) | exact (proj2 (BXok_d_pair _ BX HBX)) | exact (XA_kc_nonneg _ _ _ _ _ _ HXA) | unfold AV0; lia | unfold AK0, KU; lia].
Qed.

Lemma JA_pot_drop : forall tv fr bd hd (A : axst) rho tp w,
  SPA segs (JA (NDA tv fr bd (AHead hd true))) A rho tp w -> SPA segs (JA (NDA tv fr bd (AHead hd false))) A rho tp w.
Proof using HBX.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd A rho tp w [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [exact HXA|]. split; [|exact HPA].
  unfold bxa in HBU |- *. unfold apot in HBU |- *. cbn [am_eval apotz fst snd] in HBU |- *.
  set (P := areq (rm rho) (uval rho hd)) in *. pose proof (areq_range (rm rho) (uval rho hd)) as [R1 R2]. fold P in R1, R2.
  pose proof (XA_kc_nonneg _ _ _ _ _ _ HXA) as Hkc0.
  replace (snd (bx2 BX) + snd P + kc) with ((snd (bx2 BX) + kc) + snd P) in HBU by lia.
  pose proof (BUD_bx_drop bd (fst (bx2 BX)) (snd (bx2 BX) + kc) (fst P) (snd P) _ _ _ _ HBU (proj1 (BXok_d_pair _ BX HBX)) ltac:(lia) ltac:(lia) ltac:(lia)) as B.
  cbn [nd_bd nd_am am_eval apotz fst snd]. replace (snd (bx2 BX) + 0 + kc) with (snd (bx2 BX) + kc) by lia. replace (fst (bx2 BX) + 0) with (fst (bx2 BX)) by lia. exact B.
Qed.

Definition carve_stateA (A : axst) (p sz : sv) : axst :=
  let S := ax_S A in
  ax_setS A (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [plain_obj p sz]) (ss_facts S) (ss_next S) (ss_lenient S)).

Lemma JA_carve : forall tv fr bd hd nx cap p sz (A : axst) rho tp w,
  swf (ax_S (carve_stateA A p sz)) = true ->
  ax_base A = SLit SHADOW_OFF ->
  sv_below (ss_next (ax_S A)) p = true -> sv_below (ss_next (ax_S A)) sz = true ->

  (forall r, Forall (holds r) (ss_facts (ax_S A)) ->
      uval r hd + 24 <= uval r p /\ uval r p + uval r sz <= uval r hd + 32 + uval r cap) ->
  (forall Ai rho1 tp1 md1, Forall (holds rho) (ss_facts (ax_S A)) -> P0f rho0 -> agree_vals NP rho0 rho -> AInv Ai rho1 tp1 md1 -> TPA rho0 Ai -> T_ok rho (topG (aa_geom Ai)) ->
      (forall o a, In o (ss_objs (ax_S A)) -> fst (obj_range rho o) <= a < snd (obj_range rho o) ->
          pclMA CST rho0 (FBx FB rho tv) (FFx FF rho fr) a \/ 0 <= a < IMG_HI \/ (uval rho hd <= a < uval rho hd + 24))
      /\ xrs_ok47 rho (ax_X A)) ->
  SPA segs (JA (NDA tv fr bd (AOpen hd nx cap []))) A rho tp w ->
  SPA segs (JA (NDA tv fr bd (AOpen hd nx cap [(p, sz)]))) (carve_stateA A p sz) rho tp w.
Proof using ALA HCST HXGL HNP.
  intros tv fr bd hd nx cap p sz A rho tp w Hwf Hbase Hbp Hbsz HIN HSITE [Hsm (Ai & kc & HJ)].
  destruct w as [tr [ms md]].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  destruct (HIN rho HF) as [S1 S2]. destruct (HSITE Ai rho tp md HF HP0 Hav HM HT (T_ok_of_TPA rho Ai Hav HT)) as [HROK HX47].
  unfold XA in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU uval HDR untrackedZ tvals] in HXA.
  destruct HXA as (X1 & X2 & X3 & X4 & X5 & X5b & X6 & X7 & ns & HC & Hnin & Hkc).
  set (h := uval rho hd) in *. set (c := uval rho cap) in *.
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr).
  destruct (HBl h (HDR + c) X2) as (G1 & G2 & G3 & G4 & G5). unfold HDR in G4, G5. unfold HDR in X5b, S2.
  assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (fbinA_FBx FB Ai rho tv [] HB HNx) as FBX. pose proof (ffinA_FFx FF Ai rho fr HFF HFR) as FFX.
  split.
  - apply (SPA_carve_plain (JAi (NDA tv fr bd (AOpen hd nx cap [])) Ai kc) rho A tp (tr, mkCfg ms md) p sz (ss_next (ax_S A))).
    + split; [exact Hsm|]. exact HJ.
    + exact Hwf.
    + lia.
    + unfold uval in *. lia.
    + unfold uval in *. lia.
    + apply Forall_forall. intros o Ho. destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
      destruct (HROK o a Ho ltac:(rewrite Eo; exact Ha1)) as [Hc|[Himg|Hhdr]]; [|unfold uval in S1; unfold IMG_HI, HIGH_SHADOW_END in Himg, G5; lia|unfold uval in *; lia].
      assert (Hut' : untracked rho (tv ++ []) (h, HDR + c)) by (rewrite app_nil_r; exact X4).
      destruct (untracked_kept_FBx FB rho tv [] h (HDR + c) Hut' X3) as [HnF _].
      exact (live_not_pclMA segs AInv CST ALA HCST rho0 Ai rho tp md _ _ h (HDR + c) a HM FBX FFX HT X2 HnF ltac:(unfold uval, HDR in *; lia) Hc).
    + intros z Hz. destruct (rm rho (Z_to_bv 64 z)) as [x|] eqn:Ex; [exists x; reflexivity|]. exfalso. apply (X6 z); [unfold uval, HDR in *; lia | exact Ex].
    +
      intros rr y j Hr Hy Hj Hin. rewrite Hbase in Hin. cbn [eval] in Hin. rewrite lit_unsigned in Hin. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hin.
      pose proof (HX47 rr y Hr ltac:(unfold uval; exact Hy)) as Hy47.
      pose proof (word_byte_of_shadow (Sh y) j (Sh_is_shadow y Hy47) Hj) as WS.
      destruct (word_byte_range (Sh y) j ltac:(pose proof (Sh_is_shadow y Hy47) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia) Hj) as (_ & EWB & _).
      rewrite EWB in WS. unfold Sh in WS. replace (y / 8 + SHADOW_OFF) with (SHADOW_OFF + y / 8) in WS by lia.
      unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold uval in *. lia.
  - exists Ai, kc.
    split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
    split; [exact (conj HN (conj HD HZ))|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. cbn [nd_tv nd_fr nd_bd nd_am]. split.
    + unfold XA. split; [|exact HCEN].
      cbn -[chainZ KU uval HDR untrackedZ tvals]. fold h c.
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [unfold HDR; lia|].
      split; [exact X6|]. split; [constructor; [cbn [fst snd]; unfold uval, HDR in *; lia | constructor]|].
      exists ns. auto.
    + exact (conj HBU HPA).
Qed.

Lemma live_not_pclFA : forall Ai rho tp md b n a,
  AInv Ai rho tp md -> fbinA FB Ai -> ffinA FF Ai -> TPA rho0 Ai -> In (b, n) (aa_live Ai) -> ~ In (b, n) FB -> b <= a < b + n ->
  ~ pclFA CST rho0 FB FF a.
Proof using ALA HCST.
  clear HBX. intros Ai rho tp md b n a HM HB HFF HT Hin Hnfb Ha Hp.
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr). destruct (HBl b n Hin) as (G1 & G2 & G3 & G4 & G5).
  destruct Hp as [Hc|[Hc|[(b2 & m & Hb2 & Hr)|(f & sz & fl & Hf & Hr)]]].
  - rewrite (TPA_top rho0 Ai HT) in G4. lia.
  - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
  - eapply (live_not_pclMA segs AInv CST ALA HCST rho0 Ai rho tp md FB (FFx FF rho []) b n a HM HB); [| exact HT | exact Hin | exact Hnfb | exact Ha |].
    + intros f sz fl Hf. unfold FFx in Hf. cbn [map] in Hf. rewrite app_nil_r in Hf. exact (HFF f sz fl Hf).
    + right; right; left. exists b2, m. auto.
  - destruct (HFF _ _ _ Hf) as [HfA Hfl]. destruct Hr as [Hr| ->].
    + eapply (live_not_pclMA segs AInv CST ALA HCST rho0 Ai rho tp md FB (FFx FF rho []) b n a HM HB); [| exact HT | exact Hin | exact Hnfb | exact Ha |].
      * intros f' sz' fl' Hf'. unfold FFx in Hf'. cbn [map] in Hf'. rewrite app_nil_r in Hf'. exact (HFF f' sz' fl' Hf').
      * right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hf | exact Hr].
    + destruct (HFr f sz HfA) as (_ & _ & _ & _ & _ & _ & _ & HD8 & _). destruct (HD8 b n Hin); rewrite <- Hfl in *; lia.
Qed.

Lemma core_block_write : forall Ai rho rho' tp md tv fr b n,
  AInv Ai rho tp md -> fbinA FB Ai -> ffinA FF Ai -> TPA rho0 Ai ->
  tvinA FB Ai rho tv -> tvd rho tv -> tvz rho tv -> frinA FF Ai rho fr -> keptFA CST XGL rho0 FB FF (rm rho0) (rm rho) ->
  In (b, n) (aa_live Ai) -> ~ In (b, n) FB ->
  (forall e, eval rho' e = eval rho e) ->
  (forall a, ~ (b <= bv_unsigned a < b + n) -> rm rho' a = rm rho a) ->
  AInv Ai rho' tp md /\ (tvinA FB Ai rho' tv /\ tvd rho' tv /\ tvz rho' tv) /\ frinA FF Ai rho' fr /\ keptFA CST XGL rho0 FB FF (rm rho0) (rm rho').
Proof using ALA HCST HXGL.
  clear HBX. intros Ai rho rho' tp md tv fr b n HM HB HFF HT HN HD HZ HFR HK Hin Hnfb EV OUT.
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr). destruct (HBl b n Hin) as (G1 & G2 & G3 & G4 & G5).

  assert (SHOUT : forall a, is_shadowZ (bv_unsigned a) -> rm rho' a = rm rho a).
  { intros a Hs. apply OUT. unfold is_shadowZ, HIGH_SHADOW_END in *. lia. }
  split; [|split; [|split]].
  - eapply (law_frame _ _ _ ALA); [exact HM| |].
    + intros a Hnm _. apply OUT. intros Hr. apply Hnm. right; left. exists b, n. auto.
    + intros a (f & sz & Hf & Hr) Hd. rewrite OUT; [exact Hd|]. intros Hr'.
      destruct (HFr f sz Hf) as (_ & _ & F64 & Fhs & Fce & _).
      pose proof (Sh_is_shadow f ltac:(unfold HIGH_SHADOW_END in Fhs; lia)) as S1.
      pose proof (Sh_is_shadow (f + sz - 1) ltac:(unfold HIGH_SHADOW_END in Fhs; lia)) as S2.
      unfold is_shadowZ, HIGH_SHADOW_END in *. lia.
  - split; [|split]; [eapply tvinA_map; [| | exact HN] | eapply tvd_map; [| | exact HD] | eapply tvz_map; [| | exact HZ]];
      try (apply map_ext; intros t; unfold tvv; rewrite !EV; reflexivity);
      intros k t t' Ht Ht'; rewrite Ht in Ht'; injection Ht' as <-; unfold tnz; rewrite EV; tauto.
  - destruct HFR as [HFR HCEN]. split.
    + unfold frinA0 in HFR |- *. apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) HFR x Hx) as Y.
      unfold frv, uval in Y |- *. rewrite !EV. exact Y.
    + eapply frinA_rest_map; [reflexivity | | exact HCEN]. apply map_ext. intros x. unfold frv, uval. rewrite !EV. reflexivity.
  - destruct HK as [K1 K2]. split.
    + intros a Ha Hp. rewrite OUT; [exact (K1 a Ha Hp)|]. rewrite u64_of_sum by exact Ha. intros Hr.
      destruct Hp as [Hp|[(x & Hx & Hpx & ->) _]].
      * exact (live_not_pclFA Ai rho tp md b n a HM HB HFF HT Hin Hnfb Hr Hp).
      * assert (Hx47 : 0 <= x < 2 ^ 47).
        { destruct Hpx as [Hpx|Hg]; [exact (pclFA_range segs AInv CST ALA HCST _ FB FF Ai rho tp md x HM HB HFF HT Hpx) | apply HXGL in Hg; unfold IMG_HI, LOW_SHADOW_BEG in Hg; lia]. }
        pose proof (Sh_is_shadow x Hx47) as SS. unfold is_shadowZ, HIGH_SHADOW_END in SS, G5. unfold HDR in *. lia.
    + intros a j Ha Hp Hj Hd. rewrite SHOUT; [exact (K2 a j Ha Hp Hj Hd)|].
      destruct Hp as (x & Hx & Hpx & ->).
      assert (Hx47 : 0 <= x < 2 ^ 47).
      { destruct Hpx as [Hpx|Hg]; [exact (pclFA_range segs AInv CST ALA HCST _ FB FF Ai rho tp md x HM HB HFF HT Hpx) | apply HXGL in Hg; unfold IMG_HI, LOW_SHADOW_BEG in Hg; lia]. }
      apply word_byte_of_shadow; [apply Sh_is_shadow; exact Hx47 | exact Hj].
Qed.

Lemma chainZ_frame_nodes : forall F Ai m1 m2 tvs1 tvs2 h ns,
  chainZ F Ai m1 tvs1 h ns ->
  (forall b c, In (b, c) ns -> untrackedZ tvs1 (b, HDR + c) -> untrackedZ tvs2 (b, HDR + c)) ->
  (forall b c z, In (b, c) ns -> b <= z < b + (HDR + c) -> m2 (Z_to_bv 64 z) = m1 (Z_to_bv 64 z)) ->
  (forall b c a, In (b, c) ns -> b <= a < b + (HDR + c) ->
       m2 (shadow_addr SHADOW_OFF a) = m1 (shadow_addr SHADOW_OFF a)
       /\ (forall j, 0 <= j < 8 -> m1 (word_byte (SHADOW_OFF + a / 8) j) <> None -> m2 (word_byte (SHADOW_OFF + a / 8) j) <> None)) ->
  chainZ F Ai m2 tvs2 h ns.
Proof using .
  clear HBX HKc. intros F Ai m1 m2 tvs1 tvs2 h ns [HA [HF HD]] HU HM HS. pose proof (achain_caps _ _ _ HA) as CAPS.
  split; [|split; [|exact HD]].
  - eapply achain_frame; [exact HA| |].
    + intros z (b & c & Hin & Hz). pose proof (proj1 (Forall_forall _ _) CAPS _ Hin) as [Hc _]. cbn [snd] in Hc. apply (HM b c z Hin). unfold HDR. lia.
    + intros z (b & c & Hin & Hz) Hdef. rewrite (HM b c z Hin ltac:(lia)). exact Hdef.
  - apply Forall_forall. intros [b c] Hin. destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & H2 & H3 & H4 & H5 & H6). cbn [fst snd] in *.
    split; [exact H1|]. split; [exact H2|]. split; [exact (HU b c Hin H3)|]. split; [exact H4|]. split; [exact H5|].
    eapply xmemA_frame; [exact H6| |].
    + intros a Ha _. exact (proj1 (HS b c a Hin Ha)).
    + intros a j Ha Hj. exact (proj2 (HS b c a Hin Ha) j Hj).
Qed.

Definition drop_lastA (A : axst) (objs : list sobj) : axst := ax_setS A (set_objs (ax_S A) objs).

Lemma JA_unslot : forall tv fr bd hd nx cap p sz (A : axst) objs o rho tp tr ms md,
  ss_objs (ax_S A) = objs ++ [o] ->
  sv_eqb (ob_base o) p &&& (sv_eqb (ob_lo o) (SLit 0) &&& (sv_eqb (ob_hi o) sz &&& dflt_writable (ob_dflt o))) = true ->
  SPA segs (JA (NDA tv fr bd (AOpen hd nx cap [(p, sz)]))) A rho tp (tr, mkCfg ms md) ->
  SPA segs (JA (NDA tv fr bd (AOpen hd nx cap []))) (drop_lastA A objs) (rho_absorb rho [o] (vms md tp ms)) tp (tr, mkCfg ms md).
Proof using ALA HCST HXGL HKc HTOP HNP.
  intros tv fr bd hd nx cap p sz A objs o rho tp tr ms md Hobjs Hsh [Hsm (Ai & kc & HJ)].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  apply lazy_andb_prop in Hsh as [Hb Hsh]. apply lazy_andb_prop in Hsh as [Hl Hsh]. apply lazy_andb_prop in Hsh as [Hh Hdw].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  unfold XA in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU uval HDR untrackedZ tvals] in HXA.
  destruct HXA as (X1 & X2 & X3 & X4 & X5 & X5b & X6 & X7 & ns & HC & Hnin & Hkc).
  pose proof (Forall_inv X7) as [S1 S2]. cbn [fst snd] in S1, S2.
  set (h := uval rho hd) in *. set (c := uval rho cap) in *. unfold uval in S1, S2.
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr).
  destruct (HBl h (HDR + c) X2) as (G1 & G2 & G3 & G4 & G5). unfold HDR in G4, G5. unfold HDR in X5b, S2.
  pose proof (bv_urange (eval rho sz)) as Rsz. pose proof (bv_urange (eval rho p)) as Rp.
  assert (Hrng : obj_range rho o = (bv_unsigned (eval rho p), bv_unsigned (eval rho p) + bv_unsigned (eval rho sz))).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. rewrite soff_lit_small by lia. unfold soff. rewrite bv_signed_U.
    destruct (Zsigned_spec (bv_unsigned (eval rho sz))) as [[_ X]|[X _]]; [rewrite X; f_equal; lia | exfalso; lia]. }
  set (rho' := rho_absorb rho [o] (vms md tp ms)).
  assert (OUT : forall a, ~ (bv_unsigned (eval rho p) <= bv_unsigned a < bv_unsigned (eval rho p) + bv_unsigned (eval rho sz)) -> rm rho' a = rm rho a).
  { intros a Ha. unfold rho'. apply rm_absorb_out. intros (o2 & [<-|[]] & Hr). rewrite Hrng in Hr. exact (Ha Hr). }
  destruct (released_bytesA rho A objs [o] o tp tr ms md Hobjs ltac:(left; reflexivity) Hsm Hdw
              ltac:(rewrite Hrng; cbn [fst]; unfold IMG_HI, HIGH_SHADOW_END in *; lia) ltac:(rewrite Hrng; cbn [snd]; lia)) as [BY _].
  rewrite Hrng in BY. cbn [fst snd] in BY. fold rho' in BY.
  assert (OUTB : forall a, ~ (h <= bv_unsigned a < h + (HDR + c)) -> rm rho' a = rm rho a).
  { intros a Ha. apply OUT. unfold HDR in *. lia. }
  assert (EV : forall e, eval rho' e = eval rho e) by (intros e; unfold rho'; apply eval_absorb).
  destruct (core_block_write Ai rho rho' tp md tv fr h (HDR + c) HM HB HFF HT HN HD HZ HFR HK0 X2 X3 EV OUTB) as (HM' & HTV' & HFR' & HK').
  split; [exact (smatchA_unobj rho A objs [o] tp tr ms md Hobjs Hsm)|].
  assert (Hav' : agree_vals NP rho0 rho') by (unfold rho'; cbn; exact Hav).
  clearbody rho'. exists Ai, kc.
  assert (HC' : chainZ FB Ai (rm rho') (tvals rho tv) (uval rho nx) ns).
  {
      pose proof HC as (HA & HFn & HND).
      assert (OTHER : forall b2 c2 z, In (b2, c2) ns -> b2 <= z < b2 + (HDR + c2) -> ~ (h <= z < h + (HDR + c))).
      { intros b2 c2 z Hb2 Hz Hz'. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
        apply In_nth_error in B1 as [i2 Hi2]. pose proof X2 as X2'. apply In_nth_error in X2' as [i1 Hi1].
        destruct (Nat.eq_dec i1 i2) as [->|Hne].
        - rewrite Hi1 in Hi2. injection Hi2 as E1 E2. apply Hnin. apply in_map_iff. exists (b2, c2). split; [cbn; lia | exact Hb2].
        - assert (Hi1' : nth_error (aa_live Ai ++ aa_frames Ai) i1 = Some (h, HDR + c)) by (rewrite nth_error_app1; [exact Hi1 | apply nth_error_Some; congruence]).
          assert (Hi2' : nth_error (aa_live Ai ++ aa_frames Ai) i2 = Some (b2, HDR + c2)) by (rewrite nth_error_app1; [exact Hi2 | apply nth_error_Some; congruence]).
          pose proof (pd_elems _ _ _ _ _ HPD Hi1' Hi2' Hne) as D. cbn [fst snd] in D. lia. }
      eapply (chainZ_frame_nodes FB Ai (rm rho) (rm rho')); [exact HC | intros; assumption | |].
      * intros b2 c2 z Hb2 Hz. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
        destruct (HBl b2 (HDR + c2) B1) as (_ & _ & B3 & B4 & B5).
        apply OUTB. rewrite u64_of_sum by lia. exact (OTHER b2 c2 z Hb2 Hz).
      * intros b2 c2 a Hb2 Ha. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
        destruct (HBl b2 (HDR + c2) B1) as (_ & _ & B3 & B4 & B5).
        assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as SS.
        split.
        -- rewrite shadow_addr_Sh. apply OUTB. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia).
           unfold is_shadowZ, HIGH_SHADOW_END in SS, G5. unfold HDR in *. lia.
        -- intros j Hj Hd. rewrite OUTB; [exact Hd|]. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
           pose proof (word_byte_of_shadow (Sh a) j SS Hj) as WS. unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold HDR in *. lia. }
  split; [exact Hav'|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HTV'|]. split; [exact HFR'|]. split; [exact HK'|]. split; [exact HP0|]. cbn [nd_tv nd_fr nd_bd nd_am]. refine (conj _ (conj _ (JA_tail_ext _ _ _ rho rho' _ EV HPA))).
  -
    unfold XA. rewrite (am_eval_exteq (AOpen hd nx cap []) rho rho' ltac:(intros e _; apply EV)).
    unfold tvals. rewrite (map_ext (tvv rho') (tvv rho)) by (intros t; unfold tvv; rewrite !EV; reflexivity).
    cbn -[chainZ KU uval HDR untrackedZ lcenZ]. fold h c. change (map (tvv rho) tv) with (tvals rho tv).
    split.
    2: {
         intros bn H1 H2 H3 H4. pose proof (HCEN bn H1 H2 H3 H4) as HB0. cbn [amblkZ am_eval] in HB0 |- *.
         destruct HB0 as [E0|(ns' & HA' & Hin')]; [left; exact E0 | right].
         rewrite (achain_det _ _ _ _ (proj1 HC) HA') in Hin'. exists ns. split; [exact (proj1 HC') | exact Hin']. }
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [unfold HDR; lia|]. split.
    + intros z Hz. destruct (Z_lt_dec z (bv_unsigned (eval rho p))) as [L|L]; [rewrite OUT by (rewrite u64_of_sum by lia; lia); apply X6; exact Hz|].
      destruct (Z_lt_dec z (bv_unsigned (eval rho p) + bv_unsigned (eval rho sz))) as [L2|L2]; [apply BY; lia|].
      rewrite OUT by (rewrite u64_of_sum by (unfold HDR in Hz; lia); lia). apply X6. exact Hz.
    + split; [constructor|]. exists ns. split; [|split; [exact Hnin | exact Hkc]].
      exact HC'.
  -
    unfold bxa in HBU |- *. unfold apot in HBU |- *. cbn [am_eval apotz fst snd] in HBU |- *.
    destruct (bsum_eval_ext bd rho' rho EV) as [E1 E2]. unfold BUD in HBU |- *. rewrite E1, E2.
    destruct HBU as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). repeat (split; [assumption|]). split; [|split; assumption].
    eapply bd_nn_eval_ext; [| exact Q7]. intros e. symmetry. apply EV.
Qed.

Lemma BUD_pot_absorb : forall b x1 x2 kc V Km Kf rho u pv pk,
  BUD (POT u ++ b) (x1 + 0, x2 + 0 + kc) V Km Kf rho ->
  potV (uval rho u) = pv -> potK (uval rho u) = pk ->
  BUD b (x1 + pv, x2 + pk + kc) V Km Kf rho.
Proof.
  clear. intros b x1 x2 kc V Km Kf rho u pv pk H Ev Ek.
  destruct (POT_vals rho u) as (P1 & P2 & P3 & P4). rewrite Ev in P1. rewrite Ek in P2.
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). cbn [fst snd] in *.
  rewrite bsumV_app, P1 in B1. rewrite bsumK_app, P2 in B2. rewrite bd_wpos_app, P4 in Hw. cbn [andb] in Hw.
  apply bd_nn_app in Hn as [_ Hn]. pose proof (potV_range (uval rho u) (proj1 (uval_range rho u))). pose proof (potK_range (uval rho u) (proj1 (uval_range rho u))).
  unfold BUD. cbn [fst snd]. repeat (split; [first [assumption | lia]|]). lia.
Qed.

Lemma JA_close : forall tv fr bd bd' hd nx cap u (A : axst) objs o rho tp tr ms md,
  ss_objs (ax_S A) = objs ++ [o] ->
  TobjJVA.hdr_shape o hd nx cap u = true ->
  uleq (ss_facts (ax_S A)) u 0 cap = true ->
  In (hd, e32 cap) (ax_X A) -> ax_base A = SLit SHADOW_OFF ->
  bud_pay (ss_facts (ax_S A)) (SLit 0) 0 bd (POT u ++ bd') = true ->
  SPA segs (JA (NDA tv fr bd (AOpen hd nx cap []))) A rho tp (tr, mkCfg ms md) ->
  SPA segs (JA (NDA tv fr bd' (AHead hd true))) (drop_lastA A objs) (rho_absorb rho [o] (vms md tp ms)) tp (tr, mkCfg ms md).
Proof using ALA HCST HXGL HKc HTOP HBX HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd bd' hd nx cap u A objs o rho tp tr ms md Hobjs Hsh Hule HXin Hbase HPAY [Hsm (Ai & kc & HJ)].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  unfold TobjJVA.hdr_shape in Hsh.
  apply lazy_andb_prop in Hsh as [Hb Hsh]. apply lazy_andb_prop in Hsh as [Hl Hsh]. apply lazy_andb_prop in Hsh as [Hh Hsh].
  apply lazy_andb_prop in Hsh as [Hdw Hsh]. apply lazy_andb_prop in Hsh as [Hc0 Hsh]. apply lazy_andb_prop in Hsh as [Hc8 Hc16].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  apply TobjJVA.has_cell8_In in Hc0. apply TobjJVA.has_cell8_In in Hc8. apply TobjJVA.has_cell8_In in Hc16.
  unfold XA in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU uval HDR untrackedZ tvals] in HXA.
  destruct HXA as (X1 & X2 & X3 & X4 & X5 & X5b & X6 & X7 & ns & HC & Hnin & Hkc).
  set (h := uval rho hd) in *. set (c := uval rho cap) in *.
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr).
  destruct (HBl h (HDR + c) X2) as (G1 & G2 & G3 & G4 & G5). unfold HDR in G4, G5. unfold HDR in X5b.
  assert (Hrng : obj_range rho o = (h, h + 24)).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. rewrite !soff_lit_small by lia. change (bv_unsigned (eval rho hd)) with h. f_equal; lia. }
  set (rho' := rho_absorb rho [o] (vms md tp ms)).
  assert (OUT : forall a, ~ (h <= bv_unsigned a < h + 24) -> rm rho' a = rm rho a).
  { intros a Ha. unfold rho'. apply rm_absorb_out. intros (o2 & [<-|[]] & Hr). rewrite Hrng in Hr. cbn [fst snd] in Hr. exact (Ha Hr). }
  destruct (released_bytesA rho A objs [o] o tp tr ms md Hobjs ltac:(left; reflexivity) Hsm Hdw
              ltac:(rewrite Hrng; cbn [fst]; unfold IMG_HI, HIGH_SHADOW_END in *; lia) ltac:(rewrite Hrng; cbn [snd]; lia)) as [BY CELLS].
  rewrite Hrng in BY. cbn [fst snd] in BY. fold rho' in BY. fold rho' in CELLS. rewrite Hb in CELLS. change (bv_unsigned (eval rho hd)) with h in CELLS.
  assert (OUTB : forall a, ~ (h <= bv_unsigned a < h + (HDR + c)) -> rm rho' a = rm rho a).
  { intros a Ha. apply OUT. unfold HDR in *. lia. }
  assert (EV : forall e, eval rho' e = eval rho e) by (intros e; unfold rho'; apply eval_absorb).
  destruct (core_block_write Ai rho rho' tp md tv fr h (HDR + c) HM HB HFF HT HN HD HZ HFR HK0 X2 X3 EV OUTB) as (HM' & HTV' & HFR' & HK').
  pose proof (uleq_sound rho (ss_facts (ax_S A)) u 0 cap HF Hule) as U1. unfold U in U1. fold c in U1. change (bv_unsigned (eval rho cap)) with c in U1.

  pose proof HC as (HA & HFn & HND).
  assert (OTHER : forall b2 c2 z, In (b2, c2) ns -> b2 <= z < b2 + (HDR + c2) -> ~ (h <= z < h + (HDR + c))).
  { intros b2 c2 z Hb2 Hz Hz'. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
    apply In_nth_error in B1 as [i2 Hi2]. pose proof X2 as X2'. apply In_nth_error in X2' as [i1 Hi1].
    destruct (Nat.eq_dec i1 i2) as [->|Hne].
    - rewrite Hi1 in Hi2. injection Hi2 as E1 E2. apply Hnin. apply in_map_iff. exists (b2, c2). split; [cbn; lia | exact Hb2].
    - assert (Hi1' : nth_error (aa_live Ai ++ aa_frames Ai) i1 = Some (h, HDR + c)) by (rewrite nth_error_app1; [exact Hi1 | apply nth_error_Some; congruence]).
      assert (Hi2' : nth_error (aa_live Ai ++ aa_frames Ai) i2 = Some (b2, HDR + c2)) by (rewrite nth_error_app1; [exact Hi2 | apply nth_error_Some; congruence]).
      pose proof (pd_elems _ _ _ _ _ HPD Hi1' Hi2' Hne) as D. cbn [fst snd] in D. lia. }
  assert (HC' : chainZ FB Ai (rm rho') (tvals rho tv) (uval rho nx) ns).
  { eapply (chainZ_frame_nodes FB Ai (rm rho) (rm rho')); [exact HC | intros; assumption | |].
    - intros b2 c2 z Hb2 Hz. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
      destruct (HBl b2 (HDR + c2) B1) as (_ & _ & B3 & B4 & B5).
      apply OUTB. rewrite u64_of_sum by lia. exact (OTHER b2 c2 z Hb2 Hz).
    - intros b2 c2 a Hb2 Ha. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
      destruct (HBl b2 (HDR + c2) B1) as (_ & _ & B3 & B4 & B5).
      assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as SS.
      split.
      + rewrite shadow_addr_Sh. apply OUTB. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia).
        unfold is_shadowZ, HIGH_SHADOW_END in SS, G5. unfold HDR in *. lia.
      + intros j Hj Hd. rewrite OUTB; [exact Hd|]. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
        pose proof (word_byte_of_shadow (Sh a) j SS Hj) as WS. unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold HDR in *. lia. }

  assert (XM : xmemA (rm rho') h (HDR + c)).
  { pose proof Hsm as (_ & _ & _ & Hsh0 & _). unfold shadow_ok in Hsh0. pose proof (proj1 (Forall_forall _ _) Hsh0 _ HXin) as XR.
    rewrite Hbase in XR. cbn [eval fst snd] in XR. rewrite lit_unsigned in XR. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in XR.
    unfold xr_ok in XR. cbn zeta in XR. cbn [fst snd] in XR. fold h in XR. change (bv_unsigned (eval rho hd)) with h in XR.
    unfold e32 in XR. rewrite U_add, U_lit in XR. change (bv_unsigned (eval rho cap)) with c in XR. unfold M64v in XR.
    rewrite (Z.mod_small 32) in XR by lia. rewrite (Z.mod_small (c + 32)) in XR by lia.
    destruct XR as (XR1 & XR2 & XR3). split; [exact XR1|]. intros a Ha.
    assert (Ha47 : 0 <= a < 2 ^ 47) by (unfold HDR in Ha; lia). pose proof (Sh_is_shadow a Ha47) as SS.
    destruct (XR3 a ltac:(unfold HDR in Ha; lia)) as (_ & _ & XW & v & Xv1 & Xv2). split.
    - intros j Hj. rewrite OUTB; [exact (proj2 (XW j Hj))|]. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
      pose proof (word_byte_of_shadow (Sh a) j SS Hj) as WS. unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold HDR in *. lia.
    - exists v. split; [|unfold HDR; replace (h + (32 + c)) with (h + (c + 32)) by lia; exact Xv2].
      rewrite shadow_addr_Sh. rewrite OUTB; [rewrite <- shadow_addr_Sh; exact Xv1|].
      rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia).
      unfold is_shadowZ, HIGH_SHADOW_END in SS, G5. unfold HDR in *. lia. }
  split; [exact (smatchA_unobj rho A objs [o] tp tr ms md Hobjs Hsm)|].
  assert (Hav' : agree_vals NP rho0 rho') by (unfold rho'; cbn; exact Hav).

  pose proof HBU as HBU0. unfold bxa in HBU0. unfold apot in HBU0. cbn [am_eval apotz fst snd] in HBU0.
  pose proof (BUD_pay (ss_facts (ax_S A)) (SLit 0) 0 bd (POT u ++ bd') _ (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho HF HPAY HBU0) as HB1.
  destruct (law_budget _ _ _ ALA Ai rho tp md HM) as (_ & _ & HV0 & HKm0 & HKf0).
  specialize (HB1 HV0 HKm0 HKf0 ltac:(pose proof (uval_range rho (SLit 0)); lia) ltac:(lia)).
  clearbody rho'. exists Ai, kc.
  split; [exact Hav'|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HTV'|]. split; [exact HFR'|]. split; [exact HK'|]. split; [exact HP0|]. cbn [nd_tv nd_fr nd_bd nd_am]. refine (conj _ (conj _ (JA_tail_ext _ _ _ rho rho' _ EV HPA))).
  - unfold XA. rewrite (am_eval_exteq (AHead hd true) rho rho' ltac:(intros e _; apply EV)).
    unfold tvals. rewrite (map_ext (tvv rho') (tvv rho)) by (intros t; unfold tvv; rewrite !EV; reflexivity).
    cbn -[chainZ KU uval HDR untrackedZ lcenZ]. fold h. change (map (tvv rho) tv) with (tvals rho tv).
    assert (HAH : achain (rm rho') h ((h, c) :: ns)).
    { destruct HC' as (HA' & _ & _). cbn [achain]. split; [reflexivity|]. split; [exact X1|]. split; [lia|]. split.
      { apply (CELLS 8 cap Hc8). lia. }
      split.
      { exists (uval rho u). split; [apply (CELLS 16 u Hc16); lia | unfold uval; lia]. }
      split.
      { intros z Hz. destruct (Z_lt_dec z (h + 24)) as [L|L]; [apply BY; lia|].
        rewrite OUT by (rewrite u64_of_sum by (unfold HDR in Hz; lia); lia). apply X6. unfold HDR in *. lia. }
      exists (uval rho nx). split; [rewrite <- (Z.add_0_r h); apply (CELLS 0 nx Hc0); lia | exact HA']. }
    split.
    2: {
         intros bn H1 H2 H3 H4. pose proof (HCEN bn H1 H2 H3 H4) as HB0. cbn [amblkZ am_eval] in HB0 |- *.
         exists ((h, c) :: ns). split; [exact HAH|]. cbn [map In cblk fst snd].
         destruct HB0 as [E0|(ns' & HA0' & Hin')]; [left; symmetry; exact E0 | right].
         rewrite (achain_det _ _ _ _ (proj1 HC) HA0') in Hin'. exact Hin'. }
    exists ((h, c) :: ns). split; [|rewrite Hkc; cbn [length]; rewrite Nat2Z.inj_succ; lia].
    destruct HC' as (HA' & HFn' & HND').
    split; [|split].
    + exact HAH.
    + constructor; [|exact HFn']. unfold node_okZ. cbn [fst snd]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [unfold HDR; lia|]. exact XM.
    + cbn [map fst]. constructor; [intros Hin; apply Hnin; apply list_elem_of_In; exact Hin | exact HND'].
  -
    unfold bxa. unfold apot. cbn [am_eval apotz fst snd]. unfold areq.
    rewrite (am_eval_exteq (AHead hd true) rho rho' ltac:(intros e _; apply EV)) || idtac.
    change (uval rho' hd) with (bv_unsigned (eval rho' hd)). rewrite EV. change (bv_unsigned (eval rho hd)) with h.
    destruct (Z.eqb_spec h 0) as [E0|_]; [exfalso; exact (X1 E0)|].
    rewrite (CELLS 16 u Hc16) by lia. cbn [fst snd].
    destruct (bsum_eval_ext (POT u ++ bd') rho' rho EV) as [E1 E2].
    assert (HB2 : BUD (POT u ++ bd') (fst (bx2 BX) + 0, snd (bx2 BX) + 0 + kc) (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho').
    { unfold BUD in HB1 |- *. rewrite E1, E2. destruct HB1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). repeat (split; [assumption|]). split; [|split; assumption].
      eapply bd_nn_eval_ext; [| exact Q7]. intros e. symmetry. apply EV. }
    eapply BUD_pot_absorb; [exact HB2 | |]; unfold uval; rewrite EV; reflexivity.
Qed.

Lemma JA_close_np : forall tv fr bd hd nx cap u (A : axst) objs o rho tp tr ms md,
  ss_objs (ax_S A) = objs ++ [o] ->
  TobjJVA.hdr_shape o hd nx cap u = true ->
  uleq (ss_facts (ax_S A)) u 0 cap = true ->
  In (hd, e32 cap) (ax_X A) -> ax_base A = SLit SHADOW_OFF ->
  SPA segs (JA (NDA tv fr bd (AOpen hd nx cap []))) A rho tp (tr, mkCfg ms md) ->
  SPA segs (JA (NDA tv fr bd (AHead hd false))) (drop_lastA A objs) (rho_absorb rho [o] (vms md tp ms)) tp (tr, mkCfg ms md).
Proof using ALA HCST HXGL HKc HTOP HBX HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd nx cap u A objs o rho tp tr ms md Hobjs Hsh Hule HXin Hbase [Hsm (Ai & kc & HJ)].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  unfold TobjJVA.hdr_shape in Hsh.
  apply lazy_andb_prop in Hsh as [Hb Hsh]. apply lazy_andb_prop in Hsh as [Hl Hsh]. apply lazy_andb_prop in Hsh as [Hh Hsh].
  apply lazy_andb_prop in Hsh as [Hdw Hsh]. apply lazy_andb_prop in Hsh as [Hc0 Hsh]. apply lazy_andb_prop in Hsh as [Hc8 Hc16].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  apply TobjJVA.has_cell8_In in Hc0. apply TobjJVA.has_cell8_In in Hc8. apply TobjJVA.has_cell8_In in Hc16.
  unfold XA in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU uval HDR untrackedZ tvals] in HXA.
  destruct HXA as (X1 & X2 & X3 & X4 & X5 & X5b & X6 & X7 & ns & HC & Hnin & Hkc).
  set (h := uval rho hd) in *. set (c := uval rho cap) in *.
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr).
  destruct (HBl h (HDR + c) X2) as (G1 & G2 & G3 & G4 & G5). unfold HDR in G4, G5. unfold HDR in X5b.
  assert (Hrng : obj_range rho o = (h, h + 24)).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. rewrite !soff_lit_small by lia. change (bv_unsigned (eval rho hd)) with h. f_equal; lia. }
  set (rho' := rho_absorb rho [o] (vms md tp ms)).
  assert (OUT : forall a, ~ (h <= bv_unsigned a < h + 24) -> rm rho' a = rm rho a).
  { intros a Ha. unfold rho'. apply rm_absorb_out. intros (o2 & [<-|[]] & Hr). rewrite Hrng in Hr. cbn [fst snd] in Hr. exact (Ha Hr). }
  destruct (released_bytesA rho A objs [o] o tp tr ms md Hobjs ltac:(left; reflexivity) Hsm Hdw
              ltac:(rewrite Hrng; cbn [fst]; unfold IMG_HI, HIGH_SHADOW_END in *; lia) ltac:(rewrite Hrng; cbn [snd]; lia)) as [BY CELLS].
  rewrite Hrng in BY. cbn [fst snd] in BY. fold rho' in BY. fold rho' in CELLS. rewrite Hb in CELLS. change (bv_unsigned (eval rho hd)) with h in CELLS.
  assert (OUTB : forall a, ~ (h <= bv_unsigned a < h + (HDR + c)) -> rm rho' a = rm rho a).
  { intros a Ha. apply OUT. unfold HDR in *. lia. }
  assert (EV : forall e, eval rho' e = eval rho e) by (intros e; unfold rho'; apply eval_absorb).
  destruct (core_block_write Ai rho rho' tp md tv fr h (HDR + c) HM HB HFF HT HN HD HZ HFR HK0 X2 X3 EV OUTB) as (HM' & HTV' & HFR' & HK').
  pose proof (uleq_sound rho (ss_facts (ax_S A)) u 0 cap HF Hule) as U1. unfold U in U1. fold c in U1. change (bv_unsigned (eval rho cap)) with c in U1.

  pose proof HC as (HA & HFn & HND).
  assert (OTHER : forall b2 c2 z, In (b2, c2) ns -> b2 <= z < b2 + (HDR + c2) -> ~ (h <= z < h + (HDR + c))).
  { intros b2 c2 z Hb2 Hz Hz'. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
    apply In_nth_error in B1 as [i2 Hi2]. pose proof X2 as X2'. apply In_nth_error in X2' as [i1 Hi1].
    destruct (Nat.eq_dec i1 i2) as [->|Hne].
    - rewrite Hi1 in Hi2. injection Hi2 as E1 E2. apply Hnin. apply in_map_iff. exists (b2, c2). split; [cbn; lia | exact Hb2].
    - assert (Hi1' : nth_error (aa_live Ai ++ aa_frames Ai) i1 = Some (h, HDR + c)) by (rewrite nth_error_app1; [exact Hi1 | apply nth_error_Some; congruence]).
      assert (Hi2' : nth_error (aa_live Ai ++ aa_frames Ai) i2 = Some (b2, HDR + c2)) by (rewrite nth_error_app1; [exact Hi2 | apply nth_error_Some; congruence]).
      pose proof (pd_elems _ _ _ _ _ HPD Hi1' Hi2' Hne) as D. cbn [fst snd] in D. lia. }
  assert (HC' : chainZ FB Ai (rm rho') (tvals rho tv) (uval rho nx) ns).
  { eapply (chainZ_frame_nodes FB Ai (rm rho) (rm rho')); [exact HC | intros; assumption | |].
    - intros b2 c2 z Hb2 Hz. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
      destruct (HBl b2 (HDR + c2) B1) as (_ & _ & B3 & B4 & B5).
      apply OUTB. rewrite u64_of_sum by lia. exact (OTHER b2 c2 z Hb2 Hz).
    - intros b2 c2 a Hb2 Ha. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
      destruct (HBl b2 (HDR + c2) B1) as (_ & _ & B3 & B4 & B5).
      assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as SS.
      split.
      + rewrite shadow_addr_Sh. apply OUTB. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia).
        unfold is_shadowZ, HIGH_SHADOW_END in SS, G5. unfold HDR in *. lia.
      + intros j Hj Hd. rewrite OUTB; [exact Hd|]. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
        pose proof (word_byte_of_shadow (Sh a) j SS Hj) as WS. unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold HDR in *. lia. }

  assert (XM : xmemA (rm rho') h (HDR + c)).
  { pose proof Hsm as (_ & _ & _ & Hsh0 & _). unfold shadow_ok in Hsh0. pose proof (proj1 (Forall_forall _ _) Hsh0 _ HXin) as XR.
    rewrite Hbase in XR. cbn [eval fst snd] in XR. rewrite lit_unsigned in XR. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in XR.
    unfold xr_ok in XR. cbn zeta in XR. cbn [fst snd] in XR. fold h in XR. change (bv_unsigned (eval rho hd)) with h in XR.
    unfold e32 in XR. rewrite U_add, U_lit in XR. change (bv_unsigned (eval rho cap)) with c in XR. unfold M64v in XR.
    rewrite (Z.mod_small 32) in XR by lia. rewrite (Z.mod_small (c + 32)) in XR by lia.
    destruct XR as (XR1 & XR2 & XR3). split; [exact XR1|]. intros a Ha.
    assert (Ha47 : 0 <= a < 2 ^ 47) by (unfold HDR in Ha; lia). pose proof (Sh_is_shadow a Ha47) as SS.
    destruct (XR3 a ltac:(unfold HDR in Ha; lia)) as (_ & _ & XW & v & Xv1 & Xv2). split.
    - intros j Hj. rewrite OUTB; [exact (proj2 (XW j Hj))|]. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
      pose proof (word_byte_of_shadow (Sh a) j SS Hj) as WS. unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold HDR in *. lia.
    - exists v. split; [|unfold HDR; replace (h + (32 + c)) with (h + (c + 32)) by lia; exact Xv2].
      rewrite shadow_addr_Sh. rewrite OUTB; [rewrite <- shadow_addr_Sh; exact Xv1|].
      rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia).
      unfold is_shadowZ, HIGH_SHADOW_END in SS, G5. unfold HDR in *. lia. }
  split; [exact (smatchA_unobj rho A objs [o] tp tr ms md Hobjs Hsm)|].
  assert (Hav' : agree_vals NP rho0 rho') by (unfold rho'; cbn; exact Hav).
  pose proof HBU as HB1. unfold bxa in HB1. unfold apot in HB1. cbn [am_eval apotz fst snd] in HB1.
  clearbody rho'. exists Ai, kc.
  split; [exact Hav'|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HTV'|]. split; [exact HFR'|]. split; [exact HK'|]. split; [exact HP0|]. cbn [nd_tv nd_fr nd_bd nd_am]. refine (conj _ (conj _ (JA_tail_ext _ _ _ rho rho' _ EV HPA))).
  - unfold XA. rewrite (am_eval_exteq (AHead hd false) rho rho' ltac:(intros e _; apply EV)).
    unfold tvals. rewrite (map_ext (tvv rho') (tvv rho)) by (intros t; unfold tvv; rewrite !EV; reflexivity).
    cbn -[chainZ KU uval HDR untrackedZ lcenZ]. fold h. change (map (tvv rho) tv) with (tvals rho tv).
    assert (HAH : achain (rm rho') h ((h, c) :: ns)).
    { destruct HC' as (HA' & _ & _). cbn [achain]. split; [reflexivity|]. split; [exact X1|]. split; [lia|]. split.
      { apply (CELLS 8 cap Hc8). lia. }
      split.
      { exists (uval rho u). split; [apply (CELLS 16 u Hc16); lia | unfold uval; lia]. }
      split.
      { intros z Hz. destruct (Z_lt_dec z (h + 24)) as [L|L]; [apply BY; lia|].
        rewrite OUT by (rewrite u64_of_sum by (unfold HDR in Hz; lia); lia). apply X6. unfold HDR in *. lia. }
      exists (uval rho nx). split; [rewrite <- (Z.add_0_r h); apply (CELLS 0 nx Hc0); lia | exact HA']. }
    split.
    2: {
         intros bn H1 H2 H3 H4. pose proof (HCEN bn H1 H2 H3 H4) as HB0. cbn [amblkZ am_eval] in HB0 |- *.
         exists ((h, c) :: ns). split; [exact HAH|]. cbn [map In cblk fst snd].
         destruct HB0 as [E0|(ns' & HA0' & Hin')]; [left; symmetry; exact E0 | right].
         rewrite (achain_det _ _ _ _ (proj1 HC) HA0') in Hin'. exact Hin'. }
    exists ((h, c) :: ns). split; [|rewrite Hkc; cbn [length]; rewrite Nat2Z.inj_succ; lia].
    destruct HC' as (HA' & HFn' & HND').
    split; [|split].
    + exact HAH.
    + constructor; [|exact HFn']. unfold node_okZ. cbn [fst snd]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [unfold HDR; lia|]. exact XM.
    + cbn [map fst]. constructor; [intros Hin; apply Hnin; apply list_elem_of_In; exact Hin | exact HND'].
  -
    unfold bxa. unfold apot. cbn [am_eval apotz fst snd].
    destruct (bsum_eval_ext bd rho' rho EV) as [E1 E2].
    unfold BUD in HB1 |- *. rewrite E1, E2. destruct HB1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). repeat (split; [assumption|]). split; [|split; assumption].
    eapply bd_nn_eval_ext; [| exact Q7]. intros e. symmetry. apply EV.
Qed.

Lemma BUD_deposit : forall facts bfrom bto x1 x2 kc V Km Kf rho,
  Forall (holds rho) facts -> bud_pay facts (SLit 0) KU bfrom bto = true ->
  BUD bfrom (x1, x2 + kc) V Km Kf rho -> BUD bto (x1, x2 + (kc + KU)) V Km Kf rho.
Proof.
  clear. intros facts bfrom bto x1 x2 kc V Km Kf rho HF HP H.
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). cbn [fst snd] in *.
  destruct (bud_pay_sound facts _ _ _ _ rho HF Hn HP) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof (uval_range rho (SLit 0)).
  unfold BUD. cbn [fst snd]. unfold KU in *. repeat (split; [first [assumption | lia]|]). lia.
Qed.

Lemma JA_push_open : forall tv fr bd bd' i t hd capE uE (A : axst) objs oh ot rho tp tr ms md,
  ss_objs (ax_S A) = (objs ++ [oh]) ++ [ot] ->
  nth_error tv i = Some t ->
  TobjJVA.hdr_shape oh (fst t) hd capE uE = true ->
  sv_eqb (ob_base ot) (fst t) &&& (sv_eqb (ob_lo ot) (SLit 24) &&& (sv_eqb (ob_hi ot) (snd t) &&& dflt_writable (ob_dflt ot))) = true ->
  uleq (ss_facts (ax_S A)) (snd t) 0 (e32 capE) = true -> uleq (ss_facts (ax_S A)) (e32 capE) 0 (snd t) = true ->
  uleq (ss_facts (ax_S A)) (SLit 65536) 0 capE = true -> uleq (ss_facts (ax_S A)) capE 0 (SLit (2 ^ 40 - 33)) = true ->
  existsb (sprop_eqb (SPNot (SPBranch BC_EQ (fst t) (SLit 0)))) (ss_facts (ax_S A)) = true ->
  bud_pay (ss_facts (ax_S A)) (SLit 0) KU bd bd' = true ->
  SPA segs (JA (NDA tv fr bd (AHead hd false))) A rho tp (tr, mkCfg ms md) ->
  SPA segs (JA (NDA (remove_nth i tv) fr bd' (AOpen (fst t) hd capE []))) (drop_lastA A (objs ++ [oh]))
      (rho_absorb rho [ot] (vms md tp ms)) tp (tr, mkCfg ms md).
Proof using ALA HCST HXGL HKc HTOP HBX HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd bd' i t hd capE uE A objs oh ot rho tp tr ms md Hobjs Hnth Hsh Hot Hu1 Hu2 Hu3 Hu4 Hnz HPAY [Hsm (Ai & kc & HJ)].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  apply lazy_andb_prop in Hot as [Hb Hot]. apply lazy_andb_prop in Hot as [Hl Hot]. apply lazy_andb_prop in Hot as [Hh Hdw].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  unfold XA in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU uval HDR untrackedZ tvals] in HXA. destruct HXA as (ns & HC & Hkc).
  set (h := uval rho hd) in *.
  destruct t as [pe ne]. cbn [fst snd] in *.
  set (p := uval rho pe) in *. set (n := uval rho ne) in *.
  pose proof (uleq_sound rho _ _ _ _ HF Hu1) as U1. pose proof (uleq_sound rho _ _ _ _ HF Hu2) as U2.
  pose proof (uleq_sound rho _ _ _ _ HF Hu3) as U3. pose proof (uleq_sound rho _ _ _ _ HF Hu4) as U4.
  unfold U in U1, U2, U3, U4. unfold e32 in U1, U2. rewrite U_add, U_lit in U1, U2. rewrite U_lit in U3, U4. unfold M64v in U1, U2, U3, U4.
  set (cE := uval rho capE) in *. change (bv_unsigned (eval rho capE)) with cE in U1, U2, U3, U4. change (bv_unsigned (eval rho ne)) with n in U1, U2.
  pose proof (uval_range rho capE) as RcE. fold cE in RcE. pose proof (uval_range rho ne) as Rn. fold n in Rn. pose proof (uval_range rho pe) as Rp. fold p in Rp.
  rewrite (Z.mod_small 32) in U1, U2 by lia. rewrite (Z.mod_small 65536) in U3 by lia. rewrite (Z.mod_small (2 ^ 40 - 33)) in U4 by lia.
  assert (HcE : cE + 32 < 2 ^ 40) by lia.
  rewrite (Z.mod_small (cE + 32)) in U1, U2 by lia.
  assert (En : n = HDR + cE) by (unfold HDR; lia).
  assert (Hnzt : tnz rho (pe, ne)) by (apply tnz_of_fact; exact (holds_mem _ _ _ HF Hnz)).
  pose proof (nth_error_In _ _ Hnth) as Hint.
  destruct (proj1 (Forall_forall _ _) HN _ Hint Hnzt) as (Tpos & Tin & TFB). unfold tvv in Tpos, Tin, TFB. cbn [fst snd] in Tpos, Tin, TFB.
  fold p n in Tin. fold p n in TFB. fold n in Tpos. change (bv_unsigned (eval rho pe)) with p in Tin, TFB. change (bv_unsigned (eval rho ne)) with n in Tin, TFB, Tpos.
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr).
  destruct (HBl p n Tin) as (G1 & G2 & G3 & G4 & G5).
  assert (Hp0 : p <> 0) by lia.
  assert (Hrng : obj_range rho ot = (p + 24, p + n)).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. rewrite soff_lit_small by lia. unfold soff. rewrite bv_signed_U.
    change (bv_unsigned (eval rho pe)) with p. change (bv_unsigned (eval rho ne)) with n.
    destruct (Zsigned_spec n) as [[_ X]|[X _]]; [rewrite X; reflexivity | exfalso; lia]. }
  set (rho' := rho_absorb rho [ot] (vms md tp ms)).
  assert (OUT : forall a, ~ (p + 24 <= bv_unsigned a < p + n) -> rm rho' a = rm rho a).
  { intros a Ha. unfold rho'. apply rm_absorb_out. intros (o2 & [<-|[]] & Hr). rewrite Hrng in Hr. cbn [fst snd] in Hr. exact (Ha Hr). }
  destruct (released_bytesA rho A (objs ++ [oh]) [ot] ot tp tr ms md Hobjs ltac:(left; reflexivity) Hsm Hdw
              ltac:(rewrite Hrng; cbn [fst]; unfold IMG_HI, HIGH_SHADOW_END in *; lia) ltac:(rewrite Hrng; cbn [snd]; lia)) as [BY _].
  rewrite Hrng in BY. cbn [fst snd] in BY. fold rho' in BY.
  assert (OUTB : forall a, ~ (p <= bv_unsigned a < p + n) -> rm rho' a = rm rho a) by (intros a Ha; apply OUT; lia).
  assert (EV : forall e, eval rho' e = eval rho e) by (intros e; unfold rho'; apply eval_absorb).
  destruct (core_block_write Ai rho rho' tp md tv fr p n HM HB HFF HT HN HD HZ HFR HK0 Tin TFB EV OUTB) as (HM' & (HN' & HD' & HZ') & HFR' & HK').

  pose proof HC as (HA & HFn & HND).
  assert (NODE_NE : forall b2 c2, In (b2, c2) ns -> (b2, HDR + c2) <> (p, n)).
  { intros b2 c2 Hb2 Heq. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (_ & _ & B3 & _). cbn [fst snd] in B3.
    apply (B3 (tvv rho (pe, ne))); [unfold tvals; apply in_map; exact Hint | exact Hnzt | unfold tvv; cbn [fst snd]; rewrite Heq; reflexivity]. }
  assert (OTHER : forall b2 c2 z, In (b2, c2) ns -> b2 <= z < b2 + (HDR + c2) -> ~ (p <= z < p + n)).
  { intros b2 c2 z Hb2 Hz Hz'. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
    apply In_nth_error in B1 as [i2 Hi2]. pose proof Tin as Tin'. apply In_nth_error in Tin' as [i1 Hi1].
    destruct (Nat.eq_dec i1 i2) as [->|Hne]; [rewrite Hi1 in Hi2; injection Hi2 as E1 E2; apply (NODE_NE b2 c2 Hb2); rewrite E1, E2; reflexivity|].
    assert (Hi1' : nth_error (aa_live Ai ++ aa_frames Ai) i1 = Some (p, n)) by (rewrite nth_error_app1; [exact Hi1 | apply nth_error_Some; congruence]).
    assert (Hi2' : nth_error (aa_live Ai ++ aa_frames Ai) i2 = Some (b2, HDR + c2)) by (rewrite nth_error_app1; [exact Hi2 | apply nth_error_Some; congruence]).
    pose proof (pd_elems _ _ _ _ _ HPD Hi1' Hi2' Hne) as D. cbn [fst snd] in D. lia. }
  assert (HC' : chainZ FB Ai (rm rho') (tvals rho (remove_nth i tv)) h ns).
  { eapply (chainZ_frame_nodes FB Ai (rm rho) (rm rho')); [exact HC | | |].
    - intros b2 c2 Hb2 Hut v Hv. unfold tvals in Hv. apply in_map_iff in Hv as (t2 & <- & Ht2). apply Hut. unfold tvals. apply in_map. eapply remove_nth_In. exact Ht2.
    - intros b2 c2 z Hb2 Hz. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
      destruct (HBl b2 (HDR + c2) B1) as (_ & _ & B3 & B4 & B5).
      apply OUTB. rewrite u64_of_sum by lia. exact (OTHER b2 c2 z Hb2 Hz).
    - intros b2 c2 a Hb2 Ha. destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
      destruct (HBl b2 (HDR + c2) B1) as (_ & _ & B3 & B4 & B5).
      assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as SS.
      split.
      + rewrite shadow_addr_Sh. apply OUTB. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia).
        unfold is_shadowZ, HIGH_SHADOW_END in SS, G5. unfold HDR in *. lia.
      + intros j Hj Hd. rewrite OUTB; [exact Hd|]. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
        pose proof (word_byte_of_shadow (Sh a) j SS Hj) as WS. unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold HDR in *. lia. }
  assert (PNIN : ~ In p (map fst ns)).
  { intros Hin. apply in_map_iff in Hin as ([b2 c2] & Eb & Hb2). cbn [fst] in Eb. subst b2.
    destruct (proj1 (Forall_forall _ _) HFn _ Hb2) as (B1 & _). cbn [fst snd] in B1.
    pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hb2) as [Bc _]. cbn [snd] in Bc.
    exact (OTHER p c2 p Hb2 ltac:(unfold HDR; lia) ltac:(lia)). }
  split; [exact (smatchA_unobj rho A (objs ++ [oh]) [ot] tp tr ms md Hobjs Hsm)|].
  assert (Hav' : agree_vals NP rho0 rho') by (unfold rho'; cbn; exact Hav).
  pose proof HBU as HBU0. unfold bxa in HBU0. unfold apot in HBU0. cbn [am_eval apotz fst snd] in HBU0.
  pose proof (BUD_deposit (ss_facts (ax_S A)) bd bd' (fst (bx2 BX) + 0) (snd (bx2 BX) + 0) kc (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho HF HPAY HBU0) as HB1.
  clearbody rho'. exists Ai, (kc + KU).
  split; [exact Hav'|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split.
  { split; [|split].
    - unfold tvinA in HN' |- *. apply Forall_forall. intros t2 Ht2. apply (proj1 (Forall_forall _ _) HN'). eapply remove_nth_In. exact Ht2.
    - apply tvd_remove. exact HD'.
    - unfold tvz in HZ' |- *. apply Forall_forall. intros t2 Ht2. apply (proj1 (Forall_forall _ _) HZ'). eapply remove_nth_In. exact Ht2. }
  split; [exact HFR'|]. split; [exact HK'|]. split; [exact HP0|]. cbn [nd_tv nd_fr nd_bd nd_am].

  assert (HCNT : cntS rho tv <= cntS rho' (remove_nth i tv)).
  { rewrite (cntS_ext rho rho' _ EV), (cntS_remove_nth rho tv i (pe, ne) Hnth).
    rewrite (is_smallZ_big (tvv rho (pe, ne))); [lia|]. unfold tvv, LARGE_MIN. cbn [fst snd]. change (bv_unsigned (eval rho ne)) with n. unfold HDR in En. lia. }
  refine (conj _ (conj _ (JA_tail_le _ _ _ rho rho' tv _ HCNT HPA))).
  - unfold XA. rewrite (am_eval_exteq (AOpen pe hd capE []) rho rho' ltac:(intros e _; apply EV)).
    unfold tvals. rewrite (map_ext (tvv rho') (tvv rho)) by (intros t2; unfold tvv; rewrite !EV; reflexivity).
    cbn -[chainZ KU uval HDR untrackedZ lcenZ]. fold h p cE. change (map (tvv rho) (remove_nth i tv)) with (tvals rho (remove_nth i tv)).
    split.
    2: {
         intros [b0 n0] H1 H2 H3 H4. cbn [amblkZ am_eval].
         destruct (Z.eq_dec b0 p) as [E1|N1]; [destruct (Z.eq_dec n0 (HDR + cE)) as [E2|N2]; [left; subst b0 n0; reflexivity|]|].
         all: right; assert (HU : untrackedZ (tvals rho tv) (b0, n0)) by (
                intros v Hv Hvz; unfold tvals in Hv; apply in_map_iff in Hv as (t2 & <- & Ht2);
                destruct (In_remove_nth_or tv i t2 Ht2) as [Ei|Ei];
                [ rewrite Hnth in Ei; injection Ei as <-; unfold tvv; cbn [fst snd]; change (bv_unsigned (eval rho pe)) with p; change (bv_unsigned (eval rho ne)) with n; intros Heq; injection Heq as Q1 Q2; lia
                | apply H4; [unfold tvals; apply in_map; exact Ei | exact Hvz] ]);
              pose proof (HCEN (b0, n0) H1 H2 H3 HU) as HB0; cbn [amblkZ am_eval] in HB0; destruct HB0 as (ns' & HA0' & Hin');
              rewrite (achain_det _ _ _ _ (proj1 HC) HA0') in Hin'; exists ns; split; [exact (proj1 HC') | exact Hin']. }
    unfold XAz0. cbn -[chainZ KU uval HDR untrackedZ]. rewrite <- En.
    split; [exact Hp0|]. split; [exact Tin|]. split; [exact TFB|]. split.
    { intros v Hv Hvz. unfold tvals in Hv. apply in_map_iff in Hv as (t2 & <- & Ht2). intros Heq.
      apply (tvd_nth_distinct rho tv i (pe, ne) t2 HD Hnth Ht2 Hnzt); [exact Hvz|]. rewrite Heq. unfold tvv. cbn [fst snd]. reflexivity. }
    split; [lia|]. split; [rewrite En; unfold HDR; lia|]. split.
    { intros z Hz. apply BY. rewrite En. lia. }
    split; [constructor|]. exists ns. split; [exact HC'|]. split; [exact PNIN|]. rewrite Hkc. unfold KU. lia.
  - unfold bxa. unfold apot. cbn [am_eval apotz fst snd].
    destruct (bsum_eval_ext bd' rho' rho EV) as [E1 E2]. unfold BUD in HB1 |- *. cbn [fst snd] in HB1 |- *. rewrite E1, E2.
    destruct HB1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). split; [lia|]. split; [lia|]. repeat (split; [assumption|]). split; [|split; lia].
    eapply bd_nn_eval_ext; [| exact Q7]. intros e. symmetry. apply EV.
Qed.

Lemma JA_repay : forall tv fr bd bd' am (A : axst) rho tp w,
  payA NP rho0 P0f (ss_facts (ax_S A)) (SLit 0) 0 bd bd' ->
  SPA segs (JA (NDA tv fr bd am)) A rho tp w -> SPA segs (JA (NDA tv fr bd' am)) A rho tp w.
Proof using .
  clear HTOP ALA HCST HXGL HKc HBX.
  intros tv fr bd bd' am A rho tp w HPAY [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HN3 & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN3, HFR, HXA, HBU |- *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HN3|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [exact HXA|]. split; [|exact HPA].
  pose proof HBU as (A1 & A2 & A3 & A4 & A5 & _).
  eapply (BUD_payF (TobjJAM.preA NP rho0 P0f) (ss_facts (ax_S A)) (SLit 0) 0 bd bd' _ _ _ _ _ _ _ rho (smatchA_facts segs _ _ _ _ Hsm) (conj HP0 Hav) HPAY HBU);
    [exact A3 | exact A4 | exact A5 | pose proof (uval_range rho (SLit 0)); unfold uval in *; lia | lia].
Qed.

Lemma SPA_entails_JA : forall (L T : axst) s ndi ndj rho tp w,
  entailsA L T s = true -> wsub_id_below s NP = true -> (NP <=? ss_next (ax_S L))%positive = true ->
  nd_below (ss_next (ax_S L)) ndi = true ->
  tv_sub_eqb s (nd_tv ndi) (nd_tv ndj) = true -> fr_sub_eqb s (nd_fr ndi) (nd_fr ndj) = true ->
  bud_le (ss_facts (ax_S L)) (bd_subst s (nd_bd ndj)) (nd_bd ndi) = true ->
  am_eqb (am_subst s (nd_am ndj)) (nd_am ndi) = true ->
  SPA segs (JA ndi) L rho tp w -> SPA segs (JA ndj) T (rho_sub rho s) tp w.
Proof using ALA HKc.
  intros L T s ndi ndj rho tp w He Hid Hnp Hnb Htv Hfr Hbd Ham [Hsm HJ]. apply Pos.leb_le in Hnp. apply am_eqb_sound in Ham.
  split; [eapply smatchA_entails; [exact He | exact Hsm]|].
  destruct w as [tr [ms md]]. cbn [w_tr w_cfg cfg_model] in HJ |- *.
  eapply (JA_transfer segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA ALA s (ss_next (ax_S L)) (ss_facts (ax_S L)));
    [exact Hid | exact Hnp | exact Hnb | exact Htv | exact Hfr | exact Hbd | exact Ham | apply agree_below_refl | | exact HJ].
  exact (smatchA_facts segs _ _ _ _ Hsm).
Qed.
End Sum.
End WithSegs.
