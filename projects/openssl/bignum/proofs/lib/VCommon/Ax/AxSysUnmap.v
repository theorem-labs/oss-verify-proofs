(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWAcc AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxSys AxMeasure AxSysNode AxSysMmap AxGrant AxSysFix AxSysUnmap0 AxPostFix.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxFd AxModelRel AxMRFix AxSys2B AxSysFixS AxSysFixS3.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section Regions.
Variable segs : list Segment.
Variable ρ : valuation.
Variable A : list region.
Variables m m' : word -> option byte.
Variable model : Model.
Variables a n : Z.
Hypothesis HRM : RMem segs ρ A m.
Hypothesis Hhs : hs_ok ρ A m.
Hypothesis Hcomp : comp_inv segs ρ A model.
Hypothesis Hm_out : forall x : word, ~ (a <= bv_unsigned x < a + n) -> m' x = m x.

Lemma RMem_cut_filter (g : region -> bool) :
  (forall X, In X A -> g X = true -> forall z, in_rg ρ X z -> ~ (a <= z < a + n)) -> RMem segs ρ (List.filter g A) m'.
Proof.
  intros Hmiss. destruct HRM as [Hok HRR]. split; [exact (regions_ok_filter ρ g A Hok)|].
  apply Forall_forall. intros X HX. apply filter_In in HX as [HX Hg]. pose proof (regions_ok_in ρ A X Hok HX) as WX.
  apply (RRegion_mframe segs ρ m m' X WX); [|exact (proj1 (Forall_forall _ _) HRR X HX)].
  intros z Hz. apply Hm_out. destruct WX as (W1 & _). pose proof (smod_range ρ (rg_ts X) (rg_bo X)) as Hb. fold (rbase ρ X) in Hb.
  rewrite u_wz by (unfold FastWord.two64 in *; lia). exact (Hmiss X HX Hg z Hz).
Qed.

Lemma filter_true (l : list region) : List.filter (fun _ => true) l = l.
Proof. induction l as [|x r IH]; [reflexivity|]. cbn [List.filter]. rewrite IH. reflexivity. Qed.

Section Drop.
Variables isR isC : region -> bool.
Variables R C : region.
Hypothesis HRin : In R A.
Hypothesis HCin : In C A.
Hypothesis HisR : forall X, isR X = true -> is_shadow X = false /\ rbase ρ X = a /\ to_Z (rg_n X) = n.
Hypothesis HisC : forall X, isC X = true -> rg_kind X = KShadow /\ rg_cells X = IEmpty /\ rbase ρ X = a / 8 + sh_off /\ to_Z (rg_n X) = n / 8.
Hypothesis HR : isR R = true.
Hypothesis HC : isC C = true.
Hypothesis Ha8 : a mod 8 = 0.
Hypothesis Hn8 : n mod 8 = 0.
Hypothesis Hn0 : 0 < n.

Let g := fun X => negb (isR X) &&& negb (isC X).

Lemma drop_g (X : region) : g X = true -> isR X = false /\ isC X = false.
Proof. unfold g. intros H. apply andb_prop in H as [H1 H2]. apply negb_true_iff in H1. apply negb_true_iff in H2. split; assumption. Qed.

Lemma drop_disj (X Y : region) : In X A -> In Y A -> X <> Y -> rdisj ρ X Y.
Proof.
  intros HX HY Hne. destruct HRM as [Hok _]. apply In_nth_error in HX as [k Hk]. apply In_nth_error in HY as [k' Hk'].
  apply (regions_ok_disj ρ A k k' X Y Hok Hk Hk'). intros ->. rewrite Hk in Hk'. injection Hk' as E. exact (Hne E).
Qed.

Lemma drop_miss : forall X, In X A -> g X = true -> forall z, in_rg ρ X z -> ~ (a <= z < a + n).
Proof.
  intros X HX Hg z Hz Hr. destruct (drop_g X Hg) as [G1 _]. destruct (HisR R HR) as (_ & Rb & Rn).
  assert (Hne : X <> R) by (intros ->; rewrite HR in G1; discriminate G1).
  pose proof (drop_disj X R HX HRin Hne) as D. unfold rdisj in D. unfold in_rg in Hz. rewrite Rb, Rn in D. lia.
Qed.

Lemma drop_old : hs_old ρ A m.
Proof. apply (hs_old_of_sh ρ A m C HCin); [destruct (HisC C HC) as (Ck & _); unfold is_shadow; rewrite Ck; reflexivity | exact Hhs]. Qed.

Lemma drop_cut_ss (z : Z) : a <= z < a + n -> ~ in_ss z.
Proof.
  intros Hz. destruct drop_old as [P1 _]. destruct (HisR R HR) as (Rs & Rb & Rn). apply (P1 R HRin Rs). unfold in_rg. rewrite Rb, Rn. exact Hz.
Qed.

Lemma drop_sub : forall X, In X (List.filter g A) -> exists Y, In Y A /\ is_shadow X = is_shadow Y /\ forall z, in_rg ρ X z -> in_rg ρ Y z.
Proof. intros X HX. apply filter_In in HX as [HX _]. exists X. split; [exact HX|]. split; [reflexivity | intros z Hz; exact Hz]. Qed.

Lemma drop_bg : forall z, in_ss z -> (forall S', In S' (List.filter g A) -> is_shadow S' = true -> ~ in_rg ρ S' z) ->
  (forall S, In S A -> is_shadow S = true -> ~ in_rg ρ S z) \/ m (wz z) = None \/ m (wz z) = Some (Z_to_bv 8 0).
Proof.
  intros z Hss Hout. destruct HRM as [Hok HRR]. destruct (HisC C HC) as (Ck & Cc & Cb & Cn).
  pose proof (regions_ok_in ρ A C Hok HCin) as WC.
  destruct (Z_le_gt_dec (rbase ρ C) z) as [L1|L1]; [destruct (Z_lt_le_dec z (rbase ρ C + to_Z (rg_n C))) as [L2|L2]|].
  - right. pose proof (zz_region_bytes segs ρ m C (proj1 (Forall_forall _ _) HRR C HCin) (or_intror Ck) Cc WC (z - rbase ρ C) ltac:(lia)) as [Z1 _].
    replace (rbase ρ C + (z - rbase ρ C)) with z in Z1 by lia. unfold rv in Z1. destruct (m (wz z)) as [b|]; [right; exact Z1 | left; reflexivity].
  - left. intros S HS Hs Hz. destruct (isC S) eqn:E.
    + destruct (HisC S E) as (_ & _ & Sb & Sn). unfold in_rg in Hz. rewrite Sb, Sn in Hz. rewrite Cb, Cn in L2. lia.
    + apply (Hout S); [|exact Hs | exact Hz]. apply filter_In. split; [exact HS|]. unfold g. rewrite E.
      destruct (isR S) eqn:E2; [|reflexivity]. destruct (HisR S E2) as (Ss & _). rewrite Ss in Hs. discriminate Hs.
  - left. intros S HS Hs Hz. destruct (isC S) eqn:E.
    + destruct (HisC S E) as (_ & _ & Sb & Sn). unfold in_rg in Hz. rewrite Sb, Sn in Hz. rewrite Cb in L1. lia.
    + apply (Hout S); [|exact Hs | exact Hz]. apply filter_In. split; [exact HS|]. unfold g. rewrite E.
      destruct (isR S) eqn:E2; [|reflexivity]. destruct (HisR S E2) as (Ss & _). rewrite Ss in Hs. discriminate Hs.
Qed.

Lemma drop_pre : forall S', In S' (List.filter g A) -> is_shadow S' = true -> forall z, in_rg ρ S' z -> forall q, preimage z q -> ~ (a <= q < a + n).
Proof.
  intros S' HS' Hs z Hz q Hq Hr. apply filter_In in HS' as [HS' Hg]. destruct (drop_g S' Hg) as [_ G2].
  destruct (HisC C HC) as (_ & _ & Cb & Cn).
  assert (Hne : S' <> C) by (intros ->; rewrite HC in G2; discriminate G2).
  pose proof (drop_disj S' C HS' HCin Hne) as D. unfold rdisj in D. unfold in_rg in Hz. rewrite Cb, Cn in D. unfold preimage in Hq.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. rewrite Ha8 in Da. rewrite Hn8 in Dn. lia.
Qed.

End Drop.

End Regions.

Section Main.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).

Lemma rg_is_spec (ρ : valuation) (f : lin) (n : Z) (X : region) :
  0 <= fst f < 9223372036854775808 -> 0 <= leval ρ f < AxAcct.two64 -> rg_is (snd f) (wofZ (fst f)) n X = true ->
  is_shadow X = false /\ rbase ρ X = leval ρ f /\ to_Z (rg_n X) = n.
Proof.
  intros Hc Hv H. unfold rg_is in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply teqb_eq in H1. rewrite w_eqb_spec in H2. apply Z.eqb_eq in H2. apply wZ_inj in H2. apply Z.eqb_eq in H3.
  split; [unfold is_shadow; destruct (rg_kind X); first [reflexivity | discriminate H4]|].
  split; [unfold rbase; rewrite H1, H2; exact (smod_form ρ f Hc Hv) | exact H3].
Qed.

Lemma cp_is_spec (ρ : valuation) (f : lin) (n a : Z) (X : region) :
  0 <= fst f < 9223372036854775808 -> lin_al 4096 f = true -> leval ρ f = a -> 0 <= a -> a <= 2 ^ 47 ->
  cp_is (tdiv8 (snd f)) (wofZ (wS (wofZ (fst f)) / 8 + sh_off)) n X = true ->
  rg_kind X = KShadow /\ rg_cells X = IEmpty /\ rbase ρ X = a / 8 + sh_off /\ to_Z (rg_n X) = n.
Proof.
  intros Hc Hal Ea Ha0 Ha47 H. unfold cp_is in H. apply andb_prop in H as [H H5]. apply Z.eqb_eq in H5.
  unfold rg_at in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply teqb_eq in H1. rewrite w_eqb_spec in H2. apply Z.eqb_eq in H2. apply wZ_inj in H2.
  assert (Hk : rg_kind X = KShadow) by (destruct (rg_kind X); first [reflexivity | discriminate H4]).
  assert (Hce : rg_cells X = IEmpty) by (unfold is_empty in H3; destruct (rg_cells X); [reflexivity | discriminate..]).
  split; [exact Hk|]. split; [exact Hce|]. split; [|exact H5].
  assert (Hw8 : wS (wofZ (fst f)) mod 8 = 0).
  { rewrite (wS_wofZ_small (fst f) Hc). apply mod4096_8. unfold lin_al in Hal. apply andb_prop in Hal as [Q _]. apply Z.eqb_eq in Q. exact Q. }
  assert (Hsum : teval ρ (snd f) + wS (wofZ (fst f)) = a) by (rewrite (wS_wofZ_small (fst f) Hc), <- Ea; unfold leval; lia).
  destruct (comp_rg_wf ρ (snd f) (wofZ (fst f)) 0 a (lin_al_tdiv8 f Hal) Hw8 Hsum Ha0 ltac:(lia) (Z.le_refl 0)) as (Cb0 & _ & _).
  rewrite <- Cb0. unfold rbase, comp_rg. cbn [rg_ts rg_bo]. rewrite H1, H2. reflexivity.
Qed.

Theorem sys_munmap2_sound (A : AST) (l : list AST) :
  pc_ok (npc A) = true -> xlit (aget (a_regs A) 17%uint63) = Some 215 -> sys_munmap2 A = Some l ->
  (forall B, In B l -> forall ρ c, RR ρ B c -> forall o, out_val ρ B o -> realizes_cfg segs cfg c (KT ρ o)) ->
  forall ρ c, RR ρ A c -> (exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true) ->
  forall o, out_val ρ A o -> realizes_cfg segs cfg c (KT ρ o).
Proof.
  intros Hpc H17 Hsys HS ρ [ms model] HR [w [Hf He]] o Ho. cbn [cfg_ms] in Hf.
  unfold sys_munmap2 in Hsys.
  destruct (len_shape A) as [nZ|] eqn:Esh; [|discriminate Hsys].
  destruct (xform (a_facts A) (aget (a_regs A) 10%uint63)) as [f|] eqn:Ef; [|discriminate Hsys].
  destruct (find_exact f nZ (am_maps (a_model A))) as [e0|] eqn:Ee; [|discriminate Hsys].
  destruct (var_ent e0 &&& am_shadow (a_model A) &&& lin_al 4096 f &&& eb_above (a_facts A) (am_atop (a_model A)) (a_mem A)) eqn:Eg; [|discriminate Hsys].
  apply andb_prop in Eg as [Eg Q4]. apply andb_prop in Eg as [Eg Q3]. apply andb_prop in Eg as [Q1 Q2].
  destruct (len_shape_spec A nZ Esh) as (len & L11 & Hlen & EnZ).
  subst nZ. set (nZ := page_round_up_Z len) in *.
  pose proof HR as [H1 H2 H3 H4 H5 H6 H7 H8 H9 [H10 H10'] H11 H12 H13 H14 H15]. cbn [cfg_ms cfg_model] in *.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 17) 17%uint63 215 H4 eq_refl H17) as R17.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 11) 11%uint63 len H4 eq_refl L11) as R11.
  pose proof (xform_sound ρ _ _ (rg ms (Z_to_bv 5 10)) f H11 (H4 (Z_to_bv 5 10)) Ef) as R10.
  destruct (find_exact_spec f nZ _ e0 Ee) as (He0 & Eb & Es).
  destruct (page_round_up_bounds len ltac:(flia)) as [Hb1 Hb2]. fold nZ in Hb1, Hb2.
  pose proof (lin_al_sound ρ 4096 f ltac:(flia) Q3) as Hal.
  pose proof (MR_ent segs fs0 ρ _ model e0 H8 He0) as Hent. pose proof Hent as (K1 & K2 & K3). rewrite Eb in K1, K3. rewrite Es in K3.
  pose proof (mr_top segs fs0 ρ _ model H8 _ (MR_ent_in segs fs0 ρ _ model e0 H8 He0)) as Htop.
  rewrite (ent_val_bas ρ e0 Hent), (ent_val_bsz ρ e0 Hent), Eb, Es in Htop.
  destruct (eb_above_sound ρ _ _ _ H11 Q4) as [Hat Heb]. rewrite <- (mr_atop segs fs0 ρ _ model H8) in Hat, Heb.
  set (a := leval ρ f) in *.
  assert (HnZ0 : 0 < nZ) by flia.
  assert (Ev : ent_val ρ e0 = (Z_to_bv 64 a, Z_to_bv 64 nZ)) by (unfold ent_val; rewrite Eb, Es; reflexivity).
  pose proof (gate_addr ρ f (rg ms (Z_to_bv 5 10)) R10) as Eaddr. fold a in Eaddr.
  pose proof (gate_fix_n len (rg ms (Z_to_bv 5 11)) R11) as En. fold nZ in En.
  assert (Wa : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_Z_to_bv; unfold AxAcct.two64 in *; flia).
  assert (Wn : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u_Z_to_bv; unfold AxAcct.two64 in *; flia).

  assert (G : unmap_gate model (rg ms (Z_to_bv 5 10)) (rg ms (Z_to_bv 5 11))).
  { constructor.
    - rewrite R11. flia.
    - rewrite R10. exact Hal.
    - rewrite (gate_fix_nZ len _ R11), R10. fold nZ a. unfold TASK_SIZE. flia.
    - rewrite En, Eaddr. unfold map_has. apply existsb_exists. exists (ent_val ρ e0). split; [exact (MR_ent_in segs fs0 ρ _ model e0 H8 He0)|].
      rewrite Ev. cbn [fst snd]. apply andb_true_intro. split; apply bv_eqb_eq; reflexivity. }
  set (m' := munmap_model (Z_to_bv 64 a) (Z_to_bv 64 nZ) model).
  assert (Hothers : forall q, In q (vm_maps (m_vmmaps model)) -> fst q <> Z_to_bv 64 a ->
                      iv_disj (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 nZ)) q).
  { intros q Hq Hne. destruct (MR_maps_ent segs fs0 ρ _ model q H8 Hq) as [e [Hein [-> _]]].
    assert (Hd : e <> e0) by (intros ->; apply Hne; rewrite Ev; reflexivity).
    pose proof (um_other segs fs0 ρ _ model H8 e0 He0 e Hein Hd) as D. rewrite Ev in D. cbn [fst snd] in D. unfold iv_disj. flia. }
  assert (Hused : vm_backing_used m' <= a_budget A).
  { pose proof (used_munmap model (Z_to_bv 64 a) (Z_to_bv 64 nZ) (MR_maps_nowrap segs fs0 ρ _ model H8) (mr_na segs fs0 ρ _ model H8)
                  (MR_lazy_nowrap segs fs0 ρ _ model H8) Hothers) as X. fold m' in X. flia. }
  assert (Evm : m_vmmaps m' = mkVmMapsFull (vm_reserved (m_vmmaps model)) (map_remove (vm_maps (m_vmmaps model)) (Z_to_bv 64 a))
                  (maps_subtract (vm_noaccess (m_vmmaps model)) a (a + nZ))
                  (vm_start_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)) (vm_limit (m_vmmaps model))
                  (vm_mmap_base (m_vmmaps model)) (vm_init_sp (m_vmmaps model)))
    by (unfold m', munmap_model; rewrite destroyed_vmmaps_eq, Wa, Wn; reflexivity).
  assert (Hlim : vm_limit (m_vmmaps m') = LIM) by (rewrite Evm; exact H10').
  assert (HMR' : MRm ρ (del_ent (a_model A) e0) m').
  { assert (Hual : leval ρ (ae_base e0) mod 4096 = 0 /\ ae_size e0 mod 4096 = 0).
    { rewrite Eb, Es. split; [exact Hal | unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult]. }
    pose proof (MR_unmap segs fs0 ρ _ model H8 e0 He0 (fun _ => Q1) (AxLz.lzfull_var e0 Q1) Hual) as X. rewrite Ev in X. exact X. }
  set (mem' := apply_unmaps (ms_mem ms) [(Z_to_bv 64 a, Z_to_bv 64 nZ)]).
  assert (Hin : forall x : word, a <= bv_unsigned x < a + nZ -> mem' x = None) by (intros x Hx; unfold mem'; apply unmaps_in; rewrite Wa, Wn; exact Hx).
  assert (Hout : forall x : word, ~ (a <= bv_unsigned x < a + nZ) -> mem' x = ms_mem ms x) by (intros x Hx; unfold mem'; apply unmaps_out; rewrite Wa, Wn; exact Hx).

  assert (Hlo : leval ρ (ae_base e0) <= leval ρ f) by (rewrite Eb; flia).
  assert (Hhi : leval ρ f + nZ <= leval ρ (ae_base e0) + ae_size e0) by (rewrite Eb, Es; flia).
  assert (Hsegs : forall z, in_segs segs z -> ~ (a <= z < a + nZ)).
  { intros z Hz Hr. destruct (in_segs_reserved segs Hlow z Hz) as [q [Hq Hzq]]. rewrite <- (mr_res segs fs0 ρ _ model H8) in Hq.
    pose proof (rng_res segs fs0 ρ _ model H8 e0 He0 f nZ Hlo Hhi q Hq) as D. unfold iv_disj in D. fold a in D. flia. }
  assert (Hled : forall q, ~ (a <= q < a + nZ) -> in_ledger_w segs (m_vmmaps model) q -> in_ledger_w segs (m_vmmaps m') q).
  { intros q Hq [X|[X|X]]; [left; exact X | right; left; rewrite Evm; exact X|]. right. right.
    destruct (MR_inl_ent segs fs0 ρ _ model q H8 X) as [e [Hein Hze]].
    assert (Hd : e <> e0) by (intros ->; unfold in_ent in Hze; rewrite Eb, Es in Hze; fold a in Hze; flia).
    pose proof (MR_ent segs fs0 ρ _ model e H8 Hein) as Hok.
    exists (ent_val ρ e). split.
    - rewrite (mr_maps segs fs0 ρ _ m' HMR'). cbn [del_ent am_maps]. apply in_map. apply filter_In. split; [exact Hein|].
      destruct (aent_eqb e e0) eqn:E; [apply aent_eqb_eq in E; contradiction | reflexivity].
    - rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok). exact Hze. }
  assert (Hna' : forall q, inl (vm_noaccess (m_vmmaps m')) q -> inl (vm_noaccess (m_vmmaps model)) q \/ a <= q < a + nZ).
  { intros q Hq. rewrite Evm in Hq. cbn [vm_noaccess] in Hq. left. apply (inl_subtract1 _ _ _ q (mr_na segs fs0 ρ _ model H8)) in Hq as [Hq _]. exact Hq. }

  apply (rzc_latch segs cfg ms model w (KT ρ o) H9 H3 Hf He).
  apply (rzc_sys_silent segs cfg (latch ms) model (rg ms (Z_to_bv 5 17)) (KT ρ o) H9 eq_refl).
  - rewrite (check_syscall_215 segs (latch ms) _ _ model R17). exact (chk_munmap_modeled model _ _ G _).
  - intros eff m1 evs Hc0. rewrite (check_syscall_215 segs (latch ms) _ _ model R17) in Hc0.
    destruct (chk_munmap model _ _ G eff m1 evs Hc0) as (_ & -> & ->). split; [reflexivity | exact H9].
  - exists (mkEffectU (Z_to_bv 64 0) [] [] [(rg ms (Z_to_bv 5 10), fix_n (rg ms (Z_to_bv 5 11)))] [] []), (munmap_model (rg ms (Z_to_bv 5 10)) (fix_n (rg ms (Z_to_bv 5 11))) model). split.
    + rewrite (check_syscall_215 segs (latch ms) _ _ model R17). exact (chk_munmap_ok model _ _ G).
    + apply refusal_b_uninjected; rewrite R17; [discriminate | reflexivity].
  - intros eff m1 Hc0 _. rewrite (check_syscall_215 segs (latch ms) _ _ model R17) in Hc0.
    destruct (chk_munmap model _ _ G eff m1 [] Hc0) as (-> & -> & _).
    rewrite En, Eaddr. fold m'. exists m'. split; [exact (materialize_nil m')|]. rewrite adv_unmaps. fold mem'.
    assert (Hrv : xv_val ρ (XL w_zero) (Z_to_bv 64 0)) by reflexivity.
    assert (Hh' : m_halted m' = None) by exact H9.

    destruct (ae_na e0) eqn:Ena.
    +
      destruct (no_exp e0 (am_exp (a_model A))) eqn:Enx; [|discriminate Hsys]. injection Hsys as <-.
      pose proof (no_exp_sound e0 _ Enx) as Hnx.
      assert (Hexp : forall z, a <= z < a + nZ -> ~ in_exp ρ (am_exp (a_model A)) e0 z) by (intros z _ [x [Hx [Hxe _]]]; exact (Hnx x Hx Hxe)).
      assert (Hcut_ss : forall z, a <= z < a + nZ -> ~ in_ss z).
      { intros z Hz. destruct (mr_span segs fs0 ρ _ model H8 Q2 e0 He0 Q1) as [X|X]; rewrite Eb in X; fold a in X; try rewrite Es in X;
          unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, sh_lo, sh_hi in *; flia. }
      assert (Heb' : forall X, In X (a_mem A) -> is_entry X = true -> a + nZ <= rbase ρ X) by (intros X HX HeX; specialize (Heb X HX HeX); flia).
      assert (Hfresh := na_fresh segs fs0 ρ _ model (a_mem A) (ms_mem ms) H8 H7 H15 e0 He0 Ena a nZ ltac:(rewrite Eb; fold a; flia)
                          ltac:(rewrite Eb, Es; fold a; flia) Hexp Heb').
      assert (Hmiss : forall X, In X (a_mem A) -> forall z, in_rg ρ X z -> ~ (a <= z < a + nZ)).
      { intros X HX z Hz Hr. destruct (is_shadow X) eqn:Esx; [|exact (Hfresh X HX Esx z Hz Hr)].
        exact (Hcut_ss z Hr (proj1 (H14 X HX Esx z Hz))). }
      set (B := with_model A (npc A) (aset (a_regs A) reg_a0 (XL w_zero)) (a_mem A) (a_facts A) (del_ent (a_model A) e0) (a_budget A)).
      apply (HS B (or_introl eq_refl) ρ); [|exact Ho].
      assert (HRM' : RMem segs ρ (a_mem A) mem').
      { rewrite <- (filter_true (a_mem A)). eapply RMem_cut_filter with (m := ms_mem ms) (a := a) (n := nZ); try eassumption.
        intros X HX _. exact (Hmiss X HX). }
      assert (Hsub : forall X, In X (a_mem A) -> exists Y, In Y (a_mem A) /\ is_shadow X = is_shadow Y /\ forall z, in_rg ρ X z -> in_rg ρ Y z)
        by (intros X HX; exists X; split; [exact HX | split; [reflexivity | intros z Hz; exact Hz]]).
      assert (Hbg : forall z, in_ss z -> (forall S', In S' (a_mem A) -> is_shadow S' = true -> ~ in_rg ρ S' z) ->
                (forall S, In S (a_mem A) -> is_shadow S = true -> ~ in_rg ρ S z) \/ ms_mem ms (wz z) = None \/ ms_mem ms (wz z) = Some (Z_to_bv 8 0))
        by (intros z _ X; left; exact X).
      assert (Hpre : forall S', In S' (a_mem A) -> is_shadow S' = true -> forall z, in_rg ρ S' z -> forall q, preimage z q -> ~ (a <= q < a + nZ)).
      { intros S' HS' Hs z Hz q Hq Hr. destruct H15 as [_ [_ N3]]. apply (N3 S' HS' Hs z Hz q Hq).
        exact (na_point segs fs0 ρ _ model H8 e0 He0 Ena a nZ ltac:(rewrite Eb; fold a; flia) ltac:(rewrite Eb, Es; fold a; flia) Hexp q Hr). }
      assert (Hmode : plain_mode (a_mem A) -> plain_mode (a_mem A)) by (intros X; exact X).
      apply (R_sys_post_B segs fs0 LIM ρ A B ms model m' _ (XL w_zero) _ HR); try reflexivity; try assumption.
      * eapply hs_ok_cut with (m := ms_mem ms) (A := a_mem A) (a := a) (n := nZ); eassumption.
      * eapply mem_cov_cut with (m := ms_mem ms) (model := model) (a := a) (n := nZ); eassumption.
      * eapply comp_inv_cut with (A := a_mem A) (model := model) (a := a) (n := nZ); eassumption.
      * eapply na_ok_cut with (A := a_mem A) (m := ms_mem ms) (model := model) (a := a) (n := nZ); eassumption.
    +
      match type of Hsys with (if ?c then _ else _) = _ => destruct c eqn:Ec; [|discriminate Hsys] end. injection Hsys as <-.
      apply andb_prop in Ec as [Ec W2]. apply andb_prop in Ec as [Ec W1]. apply andb_prop in Ec as [C1 C2].
      apply Z.leb_le in C1. apply Z.ltb_lt in C2.
      apply lexists_exists in W1 as [Rg [HRin HRis]]. apply lexists_exists in W2 as [Cg [HCin HCis]].
      assert (Hc : 0 <= fst f < 9223372036854775808) by flia.
      assert (Hv : 0 <= leval ρ f < AxAcct.two64) by (fold a; unfold AxAcct.two64 in *; flia).
      assert (Ha0 : 0 <= a) by flia. assert (Ha47 : a <= 2 ^ 47) by flia.
      assert (Ha8 : a mod 8 = 0) by (apply mod4096_8; exact Hal). assert (Hn8 : nZ mod 8 = 0) by (apply mod4096_8; exact Hb2).
      set (isR := rg_is (snd f) (wofZ (fst f)) nZ) in *. set (isC := cp_is (tdiv8 (snd f)) (wofZ (wS (wofZ (fst f)) / 8 + sh_off)) (nZ / 8)) in *.
      assert (HisR : forall X, isR X = true -> is_shadow X = false /\ rbase ρ X = a /\ to_Z (rg_n X) = nZ)
        by (intros X HX; exact (rg_is_spec ρ f nZ X Hc Hv HX)).
      assert (HisC : forall X, isC X = true -> rg_kind X = KShadow /\ rg_cells X = IEmpty /\ rbase ρ X = a / 8 + sh_off /\ to_Z (rg_n X) = nZ / 8)
        by (intros X HX; exact (cp_is_spec ρ f (nZ / 8) a X Hc Q3 eq_refl Ha0 Ha47 HX)).
      set (g := fun X => negb (isR X) &&& negb (isC X)).
      set (B := with_model A (npc A) (aset (a_regs A) reg_a0 (XL w_zero)) (List.filter g (a_mem A)) (a_facts A) (del_ent (a_model A) e0) (a_budget A)).
      apply (HS B (or_introl eq_refl) ρ); [|exact Ho].
      assert (Hmiss : forall X, In X (a_mem A) -> g X = true -> forall z, in_rg ρ X z -> ~ (a <= z < a + nZ)).
      { eapply drop_miss with (R := Rg) (isR := isR) (isC := isC); eassumption. }
      assert (HRM' : RMem segs ρ (List.filter g (a_mem A)) mem').
      { eapply RMem_cut_filter with (m := ms_mem ms) (a := a) (n := nZ); eassumption. }
      assert (Hcut_ss : forall z, a <= z < a + nZ -> ~ in_ss z).
      { eapply drop_cut_ss with (R := Rg) (isR := isR); eassumption. }
      assert (Hsub : forall X, In X (List.filter g (a_mem A)) -> exists Y, In Y (a_mem A) /\ is_shadow X = is_shadow Y /\ forall z, in_rg ρ X z -> in_rg ρ Y z)
        by (apply drop_sub).
      assert (Hbg : forall z, in_ss z -> (forall S', In S' (List.filter g (a_mem A)) -> is_shadow S' = true -> ~ in_rg ρ S' z) ->
                (forall S, In S (a_mem A) -> is_shadow S = true -> ~ in_rg ρ S z) \/ ms_mem ms (wz z) = None \/ ms_mem ms (wz z) = Some (Z_to_bv 8 0)).
      { eapply drop_bg with (a := a) (n := nZ) (C := Cg); eassumption. }
      assert (Hpre : forall S', In S' (List.filter g (a_mem A)) -> is_shadow S' = true -> forall z, in_rg ρ S' z -> forall q, preimage z q -> ~ (a <= q < a + nZ)).
      { eapply drop_pre with (C := Cg); eassumption. }
      assert (Hmode : plain_mode (a_mem A) -> plain_mode (List.filter g (a_mem A))).
      { intros [_ Hno]. exfalso. pose proof (Hno Cg HCin) as X. destruct (HisC Cg HCis) as (Ck & _). unfold is_shadow in X. rewrite Ck in X. discriminate X. }
      apply (R_sys_post_B segs fs0 LIM ρ A B ms model m' _ (XL w_zero) _ HR); try reflexivity; try assumption.
      * eapply hs_ok_cut with (m := ms_mem ms) (A := a_mem A) (a := a) (n := nZ); eassumption.
      * eapply mem_cov_cut with (m := ms_mem ms) (model := model) (a := a) (n := nZ); eassumption.
      * eapply comp_inv_cut with (A := a_mem A) (model := model) (a := a) (n := nZ); eassumption.
      * eapply na_ok_cut with (A := a_mem A) (m := ms_mem ms) (model := model) (a := a) (n := nZ); eassumption.
Qed.

End Main.
