(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxLearn.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXS Require Import HxsStep HxsStepSound HxsHook HxsHookSound.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaInit HxaImage HxaInv HxaHooks HxaHk HxaHkMalloc HxaHkRelease.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section HkRealloc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
(* [comment removed for export] *)
Hypothesis LIVE_POS : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> 0 < n.
Variable PMc : Model -> Prop.
Hypothesis PMc_fdfs : fdfs_only PMc.
Hypothesis PMc_mat : mat_stable PMc.
Variable T : TSet.
Variables (CL : list (Z * Z)) (lo sp0 r : Z) (m0 : word -> option byte) (cr0 anc : Z) (xp : xpar).
Hypothesis H_r : r = 0 \/ r = 16.
Hypothesis XP_stk : stk_okx (xp_stk xp).
Hypothesis XP_ro : rg_wr (xp_rgsh xp) = false.
(* [comment removed for export] *)
Hypothesis H_nb : 1600 <= xp_nbmax xp.
Hypothesis IMGSH_OK : forall Σ m rho t, ART RT Σ m -> region_ok bsegs rho t (xp_rgsh xp) m.
Variable TR : list (list int).
Hypothesis TRACES_OK : traces_ok TR.

Notation FMemA := (FMem RT CL lo sp0 r m0 cr0 anc xp).
Notation FInvA := (FInv RT CL lo sp0 r m0 cr0 anc xp).
Notation JA := (J RT PMc T).
Notation B0A := (B0 sp0 r xp).
Notation XInvA := (XInv bsegs SHBW (ghost RT) FInvA).
Notation xhook_okA := (xhook_ok bsegs SHBW (ghost RT) JA FInvA).

(* [comment removed for export] *)
Lemma blk_base_unique (g : ghost RT) (rho : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m : word -> option byte) (t : int) :
  FMemA g rho cd M nx m -> In t (x_blocks cd) ->
  (forall b, In b (x_blocks cd) -> b <> t -> rho b <> rho t) /\ (forall p' n', In (p', n') CL -> p' <> rho t).
Proof.
  intros (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrho & HART & _) Hin.
  destruct (proj1 Hlink t Hin) as (rg & Eg & _ & _ & Hs0 & _).
  destruct (in_split t (x_blocks cd) Hin) as (l1 & l2 & El).
  assert (Hnd' : List.NoDup (x_blocks cd)) by (exact (proj1 (List.NoDup_app_remove_r _ _ Hnd) ) || (apply (NoDup_app_remove_r _ _ Hnd))).
  assert (Esp : rt_live RT (g_S RT g) = map (fun t0 => (rho t0, rsize M t0)) l1 ++ (rho t, to_Z (rg_size rg)) :: (map (fun t0 => (rho t0, rsize M t0)) l2 ++ CL)).
  { rewrite Hlive. unfold blk_list. rewrite El, map_app. cbn [map]. rewrite (rsize_get M t rg Eg), <- app_assoc. reflexivity. }
  assert (HinL : forall e, In e (rt_live RT (g_S RT g)) -> 0 < snd e).
  { intros [p n] He. exact (LIVE_POS _ _ p n HART He). }
  split.
  - intros b Hb Hne E.
    assert (Hb' : In b (l1 ++ l2)).
    { rewrite El in Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|[Hb|Hb]]; [left; exact Hb | exfalso; apply Hne; symmetry; exact Hb | right; exact Hb]. }
    assert (Hin2 : In (rho b, rsize M b) (map (fun t0 => (rho t0, rsize M t0)) l1 ++ (map (fun t0 => (rho t0, rsize M t0)) l2 ++ CL))).
    { apply in_app_or in Hb'. destruct Hb' as [Hb'|Hb']; [apply in_or_app; left | apply in_or_app; right; apply in_or_app; left]; apply in_map_iff; exists b; auto. }
    destruct (proj1 Hlink b Hb) as (rgb & Egb & _ & _ & Hsb0 & _). rewrite (rsize_get M b rgb Egb) in Hin2.
    destruct (af_live_disj RT AF _ _ _ _ _ _ _ _ HART Esp Hin2) as [D|D]; lia.
  - intros p' n' Hc E. subst p'.
    assert (Hin2 : In (rho t, n') (map (fun t0 => (rho t0, rsize M t0)) l1 ++ (map (fun t0 => (rho t0, rsize M t0)) l2 ++ CL))).
    { apply in_or_app; right; apply in_or_app; right; exact Hc. }
    assert (Hn' : 0 < n') by (apply (LIVE_POS _ _ (rho t) n' HART); rewrite Hlive; apply in_or_app; right; exact Hc).
    destruct (af_live_disj RT AF _ _ _ _ _ _ _ _ HART Esp Hin2) as [D|D]; lia.
Qed.

Lemma nodup_app_disj {A : Type} (l1 l2 : list A) (x : A) : List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|a l1 IH]; intros Hnd H1 H2; [destruct H1|]. cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hni Hnd].
  destruct H1 as [->|H1]; [apply Hni; apply in_or_app; right; exact H2 | exact (IH Hnd H1 H2)].
Qed.

Definition hkA_realloc : @hook xcd := hk_at PC_REALLOC (hkx_realloc bsegs TPV T_STK RT_STACK TR T_S0 IMG_TOP).

Lemma PC_REALLOC_Z : wbv PC_REALLOC = Z_to_bv 64 e_realloc. Proof. reflexivity. Qed.

Lemma region_ok_dead (rho : valuation) (t : int) (m : word -> option byte) : region_ok bsegs rho t dead_rg m.
Proof.
  apply (region_ok_fresh_gen bsegs rho t (Some 0%uint63) 0%uint63 0%uint63 false 0%nat m); unfold rbase; cbn [rg_abs];
    change (to_Z 0%uint63) with 0; try (unfold two63); try lia; try reflexivity; try (intros i Hi; lia).
Qed.

Lemma hkA_realloc_ok : xhook_okA hkA_realloc.
Proof.
  intros g rho cd S cd' S' ms [[HRn Hlaw] [HF (Hro & Hnf)]] Hh K.
  unfold hkA_realloc, hk_at in Hh. destruct (w_eqb (s_pc S) PC_REALLOC) eqn:Epc; [|discriminate]. apply w_eqb_true_iff in Epc.
  unfold hkx_realloc in Hh.
  destruct (xtp_ok TPV S && xsp_ok T_STK S && unwind_okb bsegs T_STK TR T_S0 IMG_TOP S) eqn:Eg0; [|discriminate].
  apply andb_prop in Eg0 as [Eg0 Eun]. apply andb_prop in Eg0 as [Etp Esp].
  destruct (rget S X10) as [|t o| |] eqn:Ea10; try discriminate. destruct (rget S X11) as [n| | |] eqn:Ea11; try discriminate.
  destruct (mget (s_mem S) t) as [rg|] eqn:Eg; [|discriminate]. destruct (mget (s_mem S) (sh_tag t)) as [rgs0|] eqn:Egs0; [|discriminate].
  destruct (is_zero o && existsb (fun x => (x =? t)%uint63) (x_blocks cd) && negb (wh n) && (0 <? wl n)%uint63 && (wl n <=? 64512)%uint63
            && (wl n land 7 =? 0)%uint63 && negb (rg_size rg =? 0)%uint63 && (rg_size rg <=? wl n)%uint63 && (x_nb cd <? 1600) && (x_calls cd <? 2000)) eqn:Eck; [|discriminate].
  apply andb_prop in Eck as [Eck Ec10]. apply andb_prop in Eck as [Eck Ec9]. apply andb_prop in Eck as [Eck Ec8]. apply andb_prop in Eck as [Eck Ec7].
  apply andb_prop in Eck as [Eck Ec6]. apply andb_prop in Eck as [Eck Ec5]. apply andb_prop in Eck as [Eck Ec4]. apply andb_prop in Eck as [Eck Ec3].
  apply andb_prop in Eck as [Ec1 Ec2].
  apply is_zero_spec in Ec1. subst o. apply existsb_exists in Ec2 as (t' & Hint & Et'). apply Uint63.eqb_spec in Et'. subst t'.
  apply negb_true_iff in Ec3. apply ltb_spec in Ec4. apply leb_spec in Ec5, Ec8. apply Uint63.eqb_spec in Ec6. apply Z.ltb_lt in Ec9, Ec10.
  change (to_Z 0%uint63) with 0 in Ec4. change (to_Z 64512%uint63) with 64512 in Ec5.
  assert (Ec7' : to_Z (rg_size rg) <> 0).
  { intros E. apply negb_true_iff in Ec7. destruct (eqbP (rg_size rg) 0%uint63) as [X|X]; [discriminate|]. apply X. exact E. }
  cbv zeta in Hh. set (t2 := even_up (s_next S)) in *.
  destruct (xclobber_stack RT_STACK S (s_mem S)) as [Mc|] eqn:Ecl; [|discriminate].
  destruct (t2 <? 999990)%uint63 eqn:Et; [|discriminate]. apply ltb_spec in Et. change (to_Z 999990%uint63) with 999990 in Et.
  match type of Hh with match xret S ?res ?MM ?nn with _ => _ end = _ => destruct (xret S res MM nn) as [S1|] eqn:Ert; [|discriminate] end.
  injection Hh as <- <-.
  destruct (xclobber_inv T_STK RT_STACK S _ _ Ecl Esp) as (o & rgs & Esp2 & Eho & Egs & Eabs & Edf & Ho16 & Hrt & Hosz & Ewr & ->).
  destruct (xret_inv _ _ _ _ _ Ert) as (ra & Era & Erv & ->).
  destruct (ms_nf rho S ms (Rn_R bsegs rho S ms HRn) Erv Hro Hnf)
    as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
        & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Ems & HRg).
  set (m := ms_mem ms) in *. set (F := ms_fregs ms) in *. set (fc := ms_fcsr ms) in *. clearbody m F fc. subst ms.
  cbn [ms_mem ms_regs ms_rom MS] in HF, Hro, Hnf.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & D2 & D4 & D8 & D10 & D11 & _).
  pose proof D1 as D1'. pose proof D2 as D2'. rewrite Era in D1'. rewrite Esp2 in D2'. rewrite Ea10 in D10. rewrite Ea11 in D11. cbn [den] in D1', D2', D10, D11.
  unfold xtp_ok in Etp. destruct (rget S X4) as [tpw| | |]; try discriminate. apply w_eqb_true_iff in Etp. subst tpw. cbn [den] in D4.
  assert (HRall : forall rho2, agree_below (s_next S) rho rho2 ->
            Rregs rho2 (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wbv (s_pc S)) fc None)
            /\ Rmem bsegs rho2 (s_mem S) m).
  { intros rho2 Hag. destruct (HRn rho2 Hag) as (_ & _ & HRg2 & _ & HRm2). exact (conj HRg2 HRm2). }
  destruct (stk_class RT CL lo sp0 r m0 cr0 anc xp g rho cd _ _ m rgs HF Egs Eabs) as [Esz _].
  destruct (call_geometry RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd _ _ m o x2 HF Eho Ho16 Hrt ltac:(lia) D2') as (Espv & Hcall & Hspc).
  pose proof (unwind_premise RT AF CL lo sp0 r m0 cr0 anc xp XP_stk TR TRACES_OK g rho cd S m x1 x2 x8 HF (proj2 (HRall rho (agree_below_refl _ _))) Eun D1 D2 D8) as Hunw.
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hr0 & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & (Hc1 & Hc2 & Hc3 & Hc4) & Hagr).
  change (to_Z NEXT0) with 32 in *.
  (* [comment removed for export] *)
  pose proof (to_Z_bounded (wl n)) as Bn. pose proof (to_Z_bounded (rg_size rg)) as Bs.
  assert (EwZn : wZ n = to_Z (wl n)) by (unfold wZ; rewrite Ec3; lia).
  assert (En8 : to_Z (wl n) mod 8 = 0) by (rewrite <- phi_land7, Ec6; reflexivity).
  set (nz := to_Z (wl n)) in *. set (n0 := to_Z (rg_size rg)) in *.
  (* [comment removed for export] *)
  destruct (proj1 Hlink t Hint) as (rg' & Eg' & Eabst & Ewrt & Hs0 & Hs8). rewrite Eg in Eg'. injection Eg' as <-. fold n0 in Hs0, Hs8.
  destruct (Htl t (in_or_app _ _ _ (or_introl Hint))) as (Ttev & Tt1 & Tt2).
  set (p := rho t) in *.
  assert (HinL : In (p, n0) (rt_live RT (g_S RT g))).
  { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists t. rewrite (rsize_get _ t rg Eg). auto. }
  destruct (blk_base_unique g rho cd _ _ m t HF Hint) as [Huniq HuniqCL]. fold p in Huniq, HuniqCL.
  (* [comment removed for export] *)
  destruct (even_up_spec (s_next S) Hnx) as [Tev Tr]. fold t2 in Tev, Tr.
  assert (Et1 : to_Z (sh_tag t2) = to_Z t2 + 1) by (apply sh_tag_Z; lia).
  assert (Et2 : to_Z (t2 + 2)%uint63 = to_Z t2 + 2) by (apply add2_Z; lia).
  assert (Est : to_Z (sh_tag t) = to_Z t + 1) by (apply sh_tag_Z; lia).
  (* [comment removed for export] *)
  intros c Hc. rewrite Epc, PC_REALLOC_Z in Hc.
  assert (Hlen : Z.of_nat (length (rt_live RT (g_S RT g))) < LIVE_MAX).
  { rewrite Hlive, length_app. unfold blk_list. rewrite length_map. lia. }
  assert (Hmc0 : mcost nz = 0) by (unfold mcost; destruct (Z.leb_spec nz 64512); [reflexivity | lia]).
  assert (Hcost : mcost nz <= rt_credit RT (g_S RT g)) by (rewrite Hmc0; exact (af_credit_nonneg RT AF _ _ HART)).
  apply (rc_realloc RT RTC (g_S RT g) PMc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           F fc m p n0 nz lo PMc_fdfs PMc_mat HinL ltac:(lia) ltac:(lia)
           ltac:(rewrite D10; unfold pword; change (wZ w_zero) with 0; rewrite Z.add_0_r; reflexivity)
           ltac:(rewrite D11; unfold wbv; rewrite EwZn; reflexivity) ltac:(rewrite D4; exact TPV_Z) Hlen Hcost HART Hmi Hcall Hunw T c Hc).
  intros c' (Σ' & q & Hc' & El' & Ef' & Es' & Ecr' & Hq0 & Hq16 & Hqtop).
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & (m' & Hret & (HART' & MI' & Hstk') & Hpres & Hwr' & Hacc' & Hcopy) & Hc'').
  destruct Hret as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & Ems').
  rewrite Espv in Hstk', Hpres.
  (* [comment removed for export] *)
  set (rho' := fun t' : int => if (t' =? t2)%uint63 then q else if (t' =? sh_tag t2)%uint63 then shad q else rho t').
  assert (Hag' : agree_below (s_next S) rho rho').
  { intros t' Ht'. unfold rho'. destruct (eqbP t' t2) as [E|E]; [rewrite E in Ht'; lia|]. destruct (eqbP t' (sh_tag t2)) as [E'|E']; [rewrite E' in Ht'; lia | reflexivity]. }
  assert (Erho't : rho' t2 = q) by (unfold rho'; rewrite Uint63.eqb_refl; reflexivity).
  assert (Erho's : rho' (sh_tag t2) = shad q).
  { unfold rho'. destruct (eqbP (sh_tag t2) t2) as [E|E]; [lia|]. rewrite Uint63.eqb_refl. reflexivity. }
  (* [comment removed for export] *)
  assert (Ht20 : to_Z t2 < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  assert (Hst20 : to_Z (sh_tag t2) < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  assert (Hto20 : to_Z t < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  assert (Hsto20 : to_Z (sh_tag t) < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  assert (Nt_stk : t <> T_STK) by (intros E; rewrite E in Tt1; change (to_Z T_STK) with 2 in Tt1; lia).
  assert (Nst_stk : sh_tag t <> T_STK) by (intros E; rewrite E in Est; change (to_Z T_STK) with 2 in Est; lia).
  remember (mset (s_mem S) T_STK (drop_below rgs (wl o))) as Mc eqn:EMc.
  assert (GetMc : forall x, x <> T_STK -> mget Mc x = mget (s_mem S) x).
  { rewrite EMc. intros x Nx. rewrite (mget_mset _ T_STK x _ (mget_lt _ _ _ Egs)). destruct (Z.eqb_spec (to_Z T_STK) (to_Z x)) as [E|E]; [apply to_Z_inj in E; exfalso; apply Nx; symmetry; exact E | reflexivity]. }
  assert (CasesMc : forall x rgx, mget Mc x = Some rgx -> (x = T_STK /\ rgx = drop_below rgs (wl o)) \/ (x <> T_STK /\ mget (s_mem S) x = Some rgx)).
  { rewrite EMc. intros x rgx G. exact (mget_mset_cases _ T_STK x _ rgx (mget_lt _ _ _ Egs) G). }
  assert (EgMc : mget Mc t = Some rg) by (rewrite (GetMc t Nt_stk); exact Eg).
  remember (kill_region (kill_region Mc t rg) (sh_tag t) rgs0) as Mk eqn:EMk.
  assert (CasesMk : forall x rgx, mget Mk x = Some rgx ->
            (x = sh_tag t /\ rgx = dead_rg) \/ (x = t /\ rgx = dead_rg) \/ (x <> sh_tag t /\ x <> t /\ mget Mc x = Some rgx)).
  { rewrite EMk. intros x rgx G. destruct (mget_kill_cases _ (sh_tag t) x _ rgx Hsto20 G) as [[-> ->]|[N1 G']]; [left; auto|].
    destruct (mget_kill_cases _ t x _ rgx Hto20 G') as [[-> ->]|[N2 G'']]; [right; left; auto | right; right; auto]. }
  assert (GetMk : forall x, x <> t -> x <> sh_tag t -> mget Mk x = mget Mc x).
  { rewrite EMk. intros x N1 N2. rewrite (mget_kill_region _ (sh_tag t) x rgs0 Hsto20).
    destruct (Z.eqb_spec (to_Z (sh_tag t)) (to_Z x)) as [E|E]; [apply to_Z_inj in E; exfalso; apply N2; symmetry; exact E|].
    rewrite (mget_kill_region _ t x rg Hto20). destruct (Z.eqb_spec (to_Z t) (to_Z x)) as [E'|E']; [apply to_Z_inj in E'; exfalso; apply N1; symmetry; exact E' | reflexivity]. }
  assert (HoldK : forall x rgx, mget Mk x = Some rgx -> to_Z x < to_Z (s_next S)).
  { intros x rgx G. destruct (CasesMk x rgx G) as [[-> _]|[[-> _]|(_ & _ & G')]]; [lia | lia |].
    destruct (CasesMc x rgx G') as [[-> _]|[_ G'']]; [exact (Htags _ _ Egs) | exact (Htags _ _ G'')]. }
  set (newrg := RG None (wl n) 4 true DUnk (depth_for 60 (wl n) 0) (copy_cells rg (rg_size rg) (depth_for 60 (wl n) 0))) in *.
  set (shrg := shadow_region (wl n >> 3)%uint63 false DZero) in *.
  assert (Hcases : forall t3 rg3, mget (mset (mset Mk t2 newrg) (sh_tag t2) shrg) t3 = Some rg3 ->
            (t3 = sh_tag t2 /\ rg3 = shrg) \/ (t3 = t2 /\ rg3 = newrg) \/ (t3 <> sh_tag t2 /\ t3 <> t2 /\ mget Mk t3 = Some rg3)).
  { intros t3 rg3 G3. destruct (mget_mset_cases _ (sh_tag t2) t3 _ rg3 Hst20 G3) as [[-> ->]|[N1 G3']]; [left; auto|].
    destruct (mget_mset_cases Mk t2 t3 _ rg3 Ht20 G3') as [[-> ->]|[N2 G3'']]; [right; left; auto | right; right; auto]. }
  assert (HfreshT : mget Mk t2 = None).
  { destruct (mget Mk t2) as [rgx|] eqn:Ex; [|reflexivity]. pose proof (HoldK t2 rgx Ex). lia. }
  assert (HfreshS : mget (mset Mk t2 newrg) (sh_tag t2) = None).
  { rewrite (mget_mset Mk t2 (sh_tag t2) newrg Ht20). destruct (Z.eqb_spec (to_Z t2) (to_Z (sh_tag t2))) as [E|E]; [lia|].
    destruct (mget Mk (sh_tag t2)) as [rgx|] eqn:Ex; [|reflexivity]. pose proof (HoldK _ rgx Ex). lia. }
  assert (GetT : mget (mset (mset Mk t2 newrg) (sh_tag t2) shrg) t2 = Some newrg).
  { rewrite (mget_mset _ (sh_tag t2) t2 shrg Hst20). destruct (Z.eqb_spec (to_Z (sh_tag t2)) (to_Z t2)) as [E|E]; [lia|].
    rewrite (mget_mset Mk t2 t2 newrg Ht20), Z.eqb_refl. reflexivity. }
  assert (GetOld : forall t3, to_Z t3 < to_Z (s_next S) -> t3 <> T_STK -> t3 <> t -> t3 <> sh_tag t ->
            mget (mset (mset Mk t2 newrg) (sh_tag t2) shrg) t3 = mget (s_mem S) t3).
  { intros t3 H3 N3 N4 N5. rewrite (mget_mset _ (sh_tag t2) t3 shrg Hst20). destruct (Z.eqb_spec (to_Z (sh_tag t2)) (to_Z t3)) as [E|E]; [lia|].
    rewrite (mget_mset Mk t2 t3 newrg Ht20). destruct (Z.eqb_spec (to_Z t2) (to_Z t3)) as [E'|E']; [lia|].
    rewrite (GetMk t3 N4 N5). exact (GetMc t3 N3). }
  (* [comment removed for export] *)
  assert (HinQ : In (q, nz) (rt_live RT Σ')) by (rewrite El'; left; reflexivity).
  destruct (af_live_range RT AF _ _ _ _ HART' HinQ) as (P1 & P2 & P3).
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof (to_Z_bounded (wl o)) as Bo.
  assert (Esz8 : to_Z (wl n >> 3)%uint63 = nz / 8) by (rewrite phi_shr3; reflexivity).
  assert (Ers : rsize (mset (mset Mk t2 newrg) (sh_tag t2) shrg) t2 = nz) by (unfold rsize; rewrite GetT; reflexivity).
  assert (Hnd_bl : List.NoDup (x_blocks cd)) by (apply (NoDup_app_remove_r _ _ Hnd)).
  assert (Elr : live_remove p (rt_live RT (g_S RT g)) = blk_list rho (s_mem S) (remove_tag t (x_blocks cd)) ++ CL).
  { rewrite Hlive. unfold blk_list. apply (live_remove_blk (fun t0 => (rho t0, rsize (s_mem S) t0)) t p CL (x_blocks cd) Hnd_bl Hint eq_refl).
    - intros b Hb Nb. cbn [fst]. exact (Huniq b Hb Nb).
    - exact HuniqCL. }
  assert (Hrem : forall b, In b (remove_tag t (x_blocks cd)) -> In b (x_blocks cd) /\ b <> t /\ b <> sh_tag t /\ b <> T_STK).
  { intros b Hb. pose proof (remove_tag_In t b _ Hb) as Hb'. destruct (Htl b (in_or_app _ _ _ (or_introl Hb'))) as (Tbe & Tb1 & Tb2).
    split; [exact Hb'|]. split; [intros ->; exact (proj2 (remove_tag_NoDup t _ Hnd_bl) Hb)|].
    split; [intros ->; destruct (sh_tag_odd t Ttev Hto20) as [Y _]; rewrite Y in Tbe; discriminate Tbe|].
    intros ->. change (to_Z T_STK) with 2 in Tb1. lia. }
  apply (K (GH RT Σ') rho' ms' Hag'); [|exact Hc'']. subst ms'.
  assert (HF' : FMemA (GH RT Σ') rho' (XCD (t2 :: remove_tag t (x_blocks cd)) (x_frames cd) (x_calls cd + 1) (x_nb cd)) (mset (mset Mk t2 newrg) (sh_tag t2) shrg) (t2 + 2)%uint63 m').
  { apply (FMem_update RT CL lo sp0 r m0 cr0 anc xp g rho rho' cd (s_mem S) _ (s_next S) _ m m' Σ' (B0A + to_Z (wl o)) _ _ _ _ HF Hag'); try assumption; try lia.
    - apply (kept_stack sp0 _ _ _ 0 0 m m' (pres_ex_of_pres _ _ _ m m' Hpres)); [unfold B0, SEGTOP_A, STACK_WIN in *; lia | tauto | intros; lia].
    - pose proof Hpres as Hpres2. rewrite Elr in Hpres2. apply (kept_caller CL sp0 xp _ _ _ 0 0 m m' (pres_ex_of_pres _ _ _ m m' Hpres2)); [lia | intros; lia].
    - rewrite El', Elr. unfold blk_list. cbn [map app]. rewrite Erho't, Ers. f_equal. f_equal. apply map_ext_in. intros b Hb.
      destruct (Hrem b Hb) as (Hb' & Nb1 & Nb2 & Nb3). destruct (Htl b (in_or_app _ _ _ (or_introl Hb'))) as (_ & Tb1 & Tb2). rewrite (Hag' b) by lia. f_equal.
      unfold rsize. rewrite GetOld; [reflexivity | lia | exact Nb3 | exact Nb1 | exact Nb2].
    - rewrite Ef', Hfr. unfold frm_list. apply map_ext_in. intros f Hf. destruct (Htl f (in_or_app _ _ _ (or_intror Hf))) as (_ & Tb1 & Tb2).
      rewrite (Hag' f) by lia. reflexivity.
    - cbn [app]. constructor.
      + intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        * destruct (Htl t2 (in_or_app _ _ _ (or_introl (remove_tag_In t _ _ Hin)))) as (_ & _ & X). lia.
        * destruct (Htl t2 (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & X). lia.
      + apply NoDup_app; [exact (proj1 (remove_tag_NoDup t _ Hnd_bl)) | exact (NoDup_app_remove_l _ _ Hnd) |].
        intros x Hx Hx'. exact (nodup_app_disj _ _ x Hnd (remove_tag_In t _ _ Hx) Hx').
    - intros t0 [<-|Hin]; [split; [exact Tev|]; change (to_Z NEXT0) with 32; lia|].
      assert (Hin0 : In t0 (x_blocks cd ++ x_frames cd)) by (apply in_app_or in Hin; apply in_or_app; destruct Hin as [H|H]; [left; exact (remove_tag_In t _ _ H) | right; exact H]).
      destruct (Htl t0 Hin0) as (X1 & X2 & X3). split; [exact X1|]. change (to_Z NEXT0) with 32. lia.
    - intros t0 rg0 G0. destruct (Hcases t0 rg0 G0) as [[-> _]|[[-> _]|(_ & _ & G)]]; [lia | lia | pose proof (HoldK _ _ G); lia].
    - intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> ->]|[[-> ->]|(N1 & N2 & G)]].
      + cbn [shrg shadow_region rg_abs rg_size rg_wr]. right; right; right; left. exists t2. split; [left; reflexivity|]. split; [reflexivity|].
        split; [|reflexivity]. rewrite Ers. exact Esz8.
      + cbn [newrg rg_abs rg_wr]. right; right; left. split; [left; reflexivity | reflexivity].
      + destruct (CasesMk t3 rg3 G) as [[-> ->]|[[-> ->]|(N3 & N4 & G')]].
        * cbn [rg_abs rg_size rg_wr]. left. repeat split; reflexivity.
        * cbn [rg_abs rg_size rg_wr]. left. repeat split; reflexivity.
        * destruct (CasesMc t3 rg3 G') as [[-> ->]|[N5 G'']].
          -- cbn [drop_below rg_abs rg_size rg_wr]. rewrite Eabs. left. auto.
          -- pose proof (Hcls t3 rg3 G'') as C. destruct (rg_abs rg3); [exact C|].
             destruct C as [C|[C|[(Hin & Ew3)|[(b & Hin & Eb & Es3 & Ew3)|[C|C]]]]].
             ++ left. exact C.
             ++ right; left. exact C.
             ++ right; right; left. split; [right; exact (remove_tag_other t t3 _ Hin N4) | exact Ew3].
             ++ assert (Nb : b <> t) by (intros ->; apply N3; exact Eb).
                pose proof (remove_tag_other t b _ Hin Nb) as Hb2. destruct (Hrem b Hb2) as (_ & Nb1 & Nb2 & Nb3).
                destruct (Htl b (in_or_app _ _ _ (or_introl Hin))) as (_ & Tb1 & Tb2).
                right; right; right; left. exists b. split; [right; exact Hb2|]. split; [exact Eb|]. split; [|exact Ew3]. rewrite Es3. f_equal.
                unfold rsize. rewrite GetOld; [reflexivity | lia | exact Nb3 | exact Nb1 | exact Nb2].
             ++ right; right; right; right; left. exact C.
             ++ right; right; right; right; right. exact C.
    - destruct Hlink as [LL1 LL2]. split.
      + intros b [<-|Hb].
        * exists newrg. split; [exact GetT|]. cbn [newrg rg_abs rg_wr rg_size]. fold nz. repeat split; try reflexivity; lia.
        * destruct (Hrem b Hb) as (Hb' & Nb1 & Nb2 & Nb3). destruct (LL1 b Hb') as (rgb & Gb & X). exists rgb. split; [|exact X].
          destruct (Htl b (in_or_app _ _ _ (or_introl Hb'))) as (_ & Tb1 & Tb2). rewrite GetOld; [exact Gb | lia | exact Nb3 | exact Nb1 | exact Nb2].
      + intros f Hf. destruct (LL2 f Hf) as (rgf & Gf & X). exists rgf. split; [|exact X]. destruct (Htl f (in_or_app _ _ _ (or_intror Hf))) as (Tfe & Tb1 & Tb2).
        rewrite GetOld; [exact Gf | lia | intros ->; change (to_Z T_STK) with 2 in Tb1; lia | | ].
        * intros ->. exact (nodup_app_disj _ _ t Hnd Hint Hf).
        * intros ->. destruct (sh_tag_odd t Ttev Hto20) as [Y _]. rewrite Y in Tfe. discriminate Tfe.
    - intros t0 [<-|Hin]; [rewrite Erho's, Erho't; reflexivity|].
      assert (Hin0 : In t0 (x_blocks cd ++ x_frames cd)) by (apply in_app_or in Hin; apply in_or_app; destruct Hin as [H|H]; [left; exact (remove_tag_In t _ _ H) | right; exact H]).
      destruct (Htl t0 Hin0) as (_ & X2 & X3).
      rewrite (Hag' (sh_tag t0)) by (rewrite sh_tag_Z by lia; lia). rewrite (Hag' t0) by lia. exact (Hrsh t0 Hin0).
    - cbn [length]. pose proof (remove_tag_length t _ Hint). lia. }
  pose proof (shad_range q ltac:(unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as Rp1.
  pose proof (shad_range (q + nz) ltac:(unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as Rp2.
  pose proof (shad_end q nz En8) as Rp3. unfold SH_LO, SH_HI in Rp1, Rp2.
  destruct (FMem_loc_bounds RT CL lo sp0 r m0 cr0 anc xp g rho cd _ _ m HF) as [HB _].
  destruct (depth_for_ok (wl n) ltac:(fold nz; lia)) as [Hd1 Hd2]. fold nz in Hd1.
  split; [split|split; [exact HF' | split; [reflexivity | cbn [ms_regs MS]; do 31 eexists; reflexivity]]].
  - (* [comment removed for export] *)
    intros rho2 Hag2. cbn [s_next] in Hag2.
    assert (Hag02 : agree_below (s_next S) rho rho2).
    { intros t' Ht'. rewrite (Hag2 t') by lia. apply Hag'. exact Ht'. }
    assert (Erho2t : rho2 t2 = q) by (rewrite (Hag2 t2) by lia; exact Erho't).
    assert (Erho2s : rho2 (sh_tag t2) = shad q) by (rewrite (Hag2 (sh_tag t2)) by lia; exact Erho's).
    assert (Erho2o : rho2 t = p) by (apply Hag02; lia).
    destruct (HRall rho2 Hag02) as [HRg2 HRm2].
    apply (R_return rho2 S (VP t2 w_zero) _ (s_abs S) (t2 + 2)%uint63 ra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
             t0' t1' t2' (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F F' (wbv (s_pc S)) fc fc' None m' (seg_rom bsegs) HRg2 D1').
    { cbn [den]. unfold pword. rewrite Erho2t. change (wZ w_zero) with 0. rewrite Z.add_0_r. reflexivity. }
    assert (EBt : rbase rho2 t2 newrg = q) by (unfold rbase; cbn [newrg rg_abs]; exact Erho2t).
    assert (EBs : rbase rho2 (sh_tag t2) shrg = shad q) by (unfold rbase; cbn [shrg shadow_region rg_abs]; exact Erho2s).
    assert (EBo : rbase rho2 t rg = p) by (unfold rbase; rewrite Eabst; exact Erho2o).
    (* [comment removed for export] *)
    assert (Kd : forall t3 rg3, mget Mc t3 = Some rg3 -> rkind RT sp0 r xp (g_S RT g) (rbase rho2 t3 rg3) (to_Z (rg_size rg3)) (rg_wr rg3)).
    { intros t3 rg3 G3. rewrite EMc in G3. exact (region_loc_clobbered RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho rho2 cd (s_mem S) (s_next S) m rgs (wl o) t3 rg3 HF Hag02 Egs G3). }
    assert (Hnp : forall t3 rg3, mget Mc t3 = Some rg3 -> t3 <> t -> In (rbase rho2 t3 rg3, to_Z (rg_size rg3)) (rt_live RT (g_S RT g)) -> 0 < to_Z (rg_size rg3) -> rbase rho2 t3 rg3 <> p).
    { intros t3 rg3 G3 N3 _ Hpos E.
      assert (X : exists rg3', mget (s_mem S) t3 = Some rg3' /\ rbase rho2 t3 rg3' = rbase rho2 t3 rg3 /\ rg_size rg3' = rg_size rg3).
      { destruct (CasesMc t3 rg3 G3) as [[-> ->]|[_ G3']]; [exists rgs; split; [exact Egs | split; reflexivity] | exists rg3; auto]. }
      destruct X as (rg3' & G3' & EB3 & ES3).
      destruct (proj2 HRm2 t3 t rg3' rg G3' Eg N3 (or_intror Ewrt)) as [D|D]; rewrite ?EB3, ?ES3, ?EBo in D; fold n0 in D; lia. }
    split.
    + intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> ->]|[[-> ->]|(N1 & N2 & G)]].
      * (* [comment removed for export] *)
        apply (zero_region_ok rho2 (sh_tag t2) (wl n >> 3)%uint63 m' (shad q) Erho2s); [lia | unfold two63; lia | lia |].
        pose proof (af_sh_live RT AF _ _ _ _ HART' HinQ) as Q. rewrite (ushadow_whole nz En8) in Q. rewrite Esz8. exact Q.
      * (* [comment removed for export] *)
        pose proof (proj1 HRm2 t rg Eg) as Hokt.
        destruct (af_live_range RT AF _ _ _ _ HART HinL) as (Pp1 & Pp2 & _).
        destruct (bytes_rw_CB bsegs m p (Z.to_nat n0)) as (old & Hold).
        { lia. } { rewrite Z2Nat.id by lia. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *. lia. }
        { intros i Hi. rewrite Z2Nat.id in Hi by lia. destruct (region_mapped bsegs rho2 t rg m Hokt i Hi) as [Hb Hw]. rewrite EBo in Hb, Hw. split; [exact Hb | exact (Hw Ewrt)]. }
        assert (Holdb : bytes_at bsegs m p old).
        { destruct Hold as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
        assert (Hlo : length old = Z.to_nat n0) by (destruct Hold as [[[Hl _] _] _]; exact Hl).
        pose proof (Hcopy old Holdb ltac:(rewrite Hlo, Z2Nat.id by lia; lia)) as Hnewb.
        unfold region_ok. rewrite EBt. cbn [newrg rg_abs rg_size rg_al rg_wr rg_d]. fold nz. change (to_Z 4%uint63) with 4.
        split; [split; [lia | left; exact Hq0]|]. split; [unfold two63, USTACK_TOP in *; lia|]. split; [lia|]. split; [exact Hd1|]. split; [exact Hd2|]. split; [lia|].
        split; [exact Hq16|].
        intros i Hi. destruct Hwr' as (_ & _ & Hw'). pose proof (Hw' i Hi) as Hwi.
        destruct (wview_mrd bsegs m' _ asegs_wr_rd Hwi) as [b Eb].
        exists b. split; [exact Eb|]. split; [|intros _; exact Hwi].
        unfold newrg. destruct (rg_kb_copy bsegs rg (rg_size rg) None (wl n) 4 true (depth_for 60 (wl n) 0) i Hi Hd1 Hd2 Ec8) as [->|[Hi8 ->]]; [exact I|].
        fold n0 in Hi8. assert (Hi0 : i < n0) by (pose proof (Z.div_mod n0 8 ltac:(lia)); pose proof (Z.mod_pos_bound n0 8 ltac:(lia)); lia).
        destruct Hokt as (_ & _ & _ & _ & _ & _ & _ & Hby). destruct (Hby i ltac:(fold n0; lia)) as (b0 & Eb0 & Kb0 & _). rewrite EBo in Eb0.
        pose proof (bytes_at_mrd m p old i Holdb ltac:(rewrite Hlo, Z2Nat.id by lia; lia)) as X1.
        pose proof (bytes_at_mrd m' q old i Hnewb ltac:(rewrite Hlo, Z2Nat.id by lia; lia)) as X2.
        rewrite Eb in X2. rewrite Eb0 in X1. rewrite <- X1 in X2. injection X2 as ->. exact Kb0.
      * destruct (CasesMk t3 rg3 G) as [[-> ->]|[[-> ->]|(N3 & N4 & G')]]; [apply region_ok_dead | apply region_ok_dead |].
        (* [comment removed for export] *)
        rewrite EMc in G'.
        apply (regions_after_call RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk IMGSH_OK g rho rho2 cd (s_mem S) (s_next S) m m' Σ' (live_remove p (rt_live RT (g_S RT g))) o rgs t (s_next S) 0 0
                 HF HRm2 Hag02 Egs Eabs Edf Ewr Ho16 Hosz HART' MI' Hstk' (pres_ex_of_pres _ _ _ m m' Hpres) Es'); try assumption; try lia.
        -- intros b Hb Nb. assert (Hin : In (rho b, rsize (s_mem S) b) (live_remove p (rt_live RT (g_S RT g)))).
           { rewrite Elr. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists b. split; [reflexivity | exact (remove_tag_other t b _ Hb Nb)]. }
           split; [exact Hin | rewrite El'; right; exact Hin].
        -- intros e He. assert (Hin : In e (live_remove p (rt_live RT (g_S RT g)))) by (rewrite Elr; apply in_or_app; right; exact He).
           split; [exact Hin | rewrite El'; right; exact Hin].
        -- intros E. pose proof (Htags _ _ Egs) as X. rewrite <- E in X. lia.
        -- intros E. rewrite <- EMc in G'. pose proof (HoldK t3 rg3 G) as X. rewrite E in X. lia.
    + (* [comment removed for export] *)
      assert (HRmc : Rmem bsegs rho2 Mc m).
      { rewrite EMc. apply (Rmem_clobber bsegs rho2 (s_mem S) T_STK rgs (wl o) m HRm2 Egs Edf).
        replace (to_Z (wl o)) with (0 + (2 * (to_Z (wl o) / 16)) * 8) by (pose proof (Z.div_mod (to_Z (wl o)) 16 ltac:(lia)); lia). rewrite Z.mod_add by lia. reflexivity. }
      assert (EgsK : mget (kill_region Mc t rg) (sh_tag t) = Some rgs0).
      { rewrite (mget_kill_region _ t (sh_tag t) rg Hto20). destruct (Z.eqb_spec (to_Z t) (to_Z (sh_tag t))) as [E|E]; [lia|]. rewrite (GetMc _ Nst_stk). exact Egs0. }
      assert (SepK : regions_sep rho2 Mk).
      { rewrite EMk. exact (proj2 (Rmem_kill_region bsegs rho2 _ (sh_tag t) rgs0 m (Rmem_kill_region bsegs rho2 Mc t rg m HRmc EgMc) EgsK)). }
      apply (regions_sep_new_wr rho2 _ (sh_tag t2) shrg); [| exact HfreshS | exact Hst20 |].
      * apply (regions_sep_new rho2 Mk t2 newrg SepK HfreshT Ht20).
        intros t3 rg3 G3. rewrite EBt. cbn [newrg rg_size]. fold nz.
        destruct (CasesMk t3 rg3 G3) as [[-> ->]|[[-> ->]|(N3 & N4 & G')]]; [right; unfold rbase; cbn [rg_abs rg_size]; change (to_Z 0%uint63) with 0; lia | right; unfold rbase; cbn [rg_abs rg_size]; change (to_Z 0%uint63) with 0; lia |].
        apply (kind_apart_block RT AF lo sp0 r xp H_r XP_stk (g_S RT g) Σ' m m' _ _ _ q nz p (live_remove p (rt_live RT (g_S RT g))) (Kd t3 rg3 G') HART HB HART' El'); try assumption; try lia.
        -- intros b0 s0 Hin Hne. rewrite Elr. rewrite Hlive in Hin. apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left | right; exact Hin].
           unfold blk_list in *. apply in_map_iff in Hin as (b & Eb & Hb). apply in_map_iff. exists b. split; [exact Eb|].
           apply (remove_tag_other t b _ Hb). intros ->. apply Hne. injection Eb as <- _. reflexivity.
        -- intros Hin Hpos. exact (Hnp t3 rg3 G' N4 Hin Hpos).
      * intros t3 rg3 G3 [Hw|Hw]; [discriminate Hw|]. rewrite EBs. cbn [shrg shadow_region rg_size]. rewrite Esz8.
        destruct (mget_mset_cases Mk t2 t3 _ rg3 Ht20 G3) as [[-> ->]|[N2 G3']].
        -- rewrite EBt. cbn [newrg rg_size]. fold nz. destruct (af_live_offshadow RT AF _ _ _ _ HART' HinQ) as [D|D]; [right; lia | left; lia].
        -- destruct (CasesMk t3 rg3 G3') as [[-> ->]|[[-> ->]|(N3 & N4 & G')]]; [discriminate Hw | discriminate Hw |].
           pose proof (Kd t3 rg3 G') as Kd2. rewrite Hw in Kd2.
           exact (kind_apart_bshadow RT AF lo sp0 r xp H_r XP_stk (g_S RT g) Σ' m m' _ _ q nz Kd2 HART HB HART' HinQ Ef' Es' ltac:(lia) En8).
  - intros rho2 Hag2. exact (FMem_law RT CL lo sp0 r m0 cr0 anc xp (GH RT Σ') rho' rho2 _ _ _ m' HF' Hag2).
Time Qed.

End HkRealloc.
