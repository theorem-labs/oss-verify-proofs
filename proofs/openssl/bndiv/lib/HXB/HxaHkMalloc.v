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
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXS Require Import HxsStep HxsStepSound HxsHook HxsHookSound.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaInit HxaImage HxaInv HxaHooks HxaHk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section HkMalloc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
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

Definition hkA_malloc : @hook xcd := hk_at PC_MALLOC (hkx_malloc bsegs TPV T_STK RT_STACK TR T_S0 IMG_TOP).

Lemma PC_MALLOC_Z : wbv PC_MALLOC = Z_to_bv 64 e_malloc. Proof. reflexivity. Qed.

Lemma ushadow_whole (n : Z) : n mod 8 = 0 -> ushadow n = repeat z8 (Z.to_nat (n / 8)).
Proof. intros H. unfold ushadow. rewrite H. cbn [Z.eqb]. apply app_nil_r. Qed.

Lemma hkA_malloc_ok : xhook_okA hkA_malloc.
Proof.
  intros g rho cd S cd' S' ms [[HRn Hlaw] [HF (Hro & Hnf)]] Hh K.
  unfold hkA_malloc, hk_at in Hh. destruct (w_eqb (s_pc S) PC_MALLOC) eqn:Epc; [|discriminate]. apply w_eqb_true_iff in Epc.
  unfold hkx_malloc in Hh.
  destruct (xtp_ok TPV S && xsp_ok T_STK S && unwind_okb bsegs T_STK TR T_S0 IMG_TOP S) eqn:Eg; [|discriminate].
  apply andb_prop in Eg as [Eg Eun]. apply andb_prop in Eg as [Etp Esp].
  destruct (rget S X10) as [n| | |] eqn:Ea10; try discriminate.
  destruct (negb (wh n) && (0 <? wl n)%uint63 && (wl n <=? 64512)%uint63 && (wl n land 7 =? 0)%uint63 && (x_nb cd <? 1600) && (x_calls cd <? 2000)) eqn:Eck; [|discriminate].
  apply andb_prop in Eck as [Eck Ec6]. apply andb_prop in Eck as [Eck Ec5]. apply andb_prop in Eck as [Eck Ec4].
  apply andb_prop in Eck as [Eck Ec3]. apply andb_prop in Eck as [Ec1 Ec2].
  apply negb_true_iff in Ec1. apply ltb_spec in Ec2. apply leb_spec in Ec3. apply Uint63.eqb_spec in Ec4. apply Z.ltb_lt in Ec5, Ec6.
  change (to_Z 0%uint63) with 0 in Ec2. change (to_Z 64512%uint63) with 64512 in Ec3.
  cbv zeta in Hh. set (t := even_up (s_next S)) in *.
  destruct (xclobber_stack RT_STACK S (s_mem S)) as [Mc|] eqn:Ecl; [|discriminate].
  destruct (t <? 999990)%uint63 eqn:Et; [|discriminate]. apply ltb_spec in Et. change (to_Z 999990%uint63) with 999990 in Et.
  match type of Hh with match xret S ?res ?MM ?nn with _ => _ end = _ => destruct (xret S res MM nn) as [S1|] eqn:Ert; [|discriminate] end.
  injection Hh as <- <-.
  destruct (xclobber_inv T_STK RT_STACK S _ _ Ecl Esp) as (o & rgs & Esp2 & Eho & Egs & Eabs & Edf & Ho16 & Hrt & Hosz & Ewr & ->).
  destruct (xret_inv _ _ _ _ _ Ert) as (ra & Era & Erv & ->).
  destruct (ms_nf rho S ms (Rn_R bsegs rho S ms HRn) Erv Hro Hnf)
    as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
        & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Ems & HRg).
  set (m := ms_mem ms) in *. set (F := ms_fregs ms) in *. set (fc := ms_fcsr ms) in *. clearbody m F fc. subst ms.
  cbn [ms_mem ms_regs ms_rom MS] in HF, Hro, Hnf.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & D2 & D4 & D8 & D10 & _ & _).
  pose proof D1 as D1'. pose proof D2 as D2'. rewrite Era in D1'. rewrite Esp2 in D2'. rewrite Ea10 in D10. cbn [den] in D1', D2', D10.
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
  pose proof (to_Z_bounded (wl n)) as Bn.
  assert (EwZn : wZ n = to_Z (wl n)) by (unfold wZ; rewrite Ec1; lia).
  assert (En8 : to_Z (wl n) mod 8 = 0) by (rewrite <- phi_land7, Ec4; reflexivity).
  set (nz := to_Z (wl n)) in *.
  (* [comment removed for export] *)
  destruct (even_up_spec (s_next S) Hnx) as [Tev Tr]. fold t in Tev, Tr.
  assert (Et1 : to_Z (sh_tag t) = to_Z t + 1) by (apply sh_tag_Z; lia).
  assert (Et2 : to_Z (t + 2)%uint63 = to_Z t + 2) by (apply add2_Z; lia).
  (* [comment removed for export] *)
  intros c Hc. rewrite Epc, PC_MALLOC_Z in Hc.
  assert (Hlen : Z.of_nat (length (rt_live RT (g_S RT g))) < LIVE_MAX).
  { rewrite Hlive, length_app. unfold blk_list. rewrite length_map. lia. }
  assert (Hcost : mcost nz <= rt_credit RT (g_S RT g)).
  { unfold mcost. destruct (Z.leb_spec nz 64512) as [_|X]; [exact (af_credit_nonneg RT AF _ _ HART) | lia]. }
  apply (rc_malloc RT RTC (g_S RT g) PMc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           F fc m nz lo PMc_fdfs PMc_mat ltac:(lia) ltac:(rewrite D10; unfold wbv; rewrite EwZn; reflexivity) ltac:(rewrite D4; exact TPV_Z) Hlen Hcost HART Hmi Hcall Hunw T c Hc).
  intros c' (Σ' & p & Hc' & El' & Ef' & Es' & Ecr' & Hp0 & Hp16 & Hptop).
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & (m' & Hret & (HART' & MI' & WM & Hstk') & Hpres & Hwr' & Hacc') & Hc'').
  destruct Hret as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & Ems').
  rewrite Espv in Hstk', Hpres.
  (* [comment removed for export] *)
  set (rho' := fun t' : int => if (t' =? t)%uint63 then p else if (t' =? sh_tag t)%uint63 then shad p else rho t').
  assert (Hag' : agree_below (s_next S) rho rho').
  { intros t' Ht'. unfold rho'. destruct (eqbP t' t) as [E|E]; [rewrite E in Ht'; lia|]. destruct (eqbP t' (sh_tag t)) as [E'|E']; [rewrite E' in Ht'; lia | reflexivity]. }
  assert (Erho't : rho' t = p) by (unfold rho'; rewrite Uint63.eqb_refl; reflexivity).
  assert (Erho's : rho' (sh_tag t) = shad p).
  { unfold rho'. destruct (eqbP (sh_tag t) t) as [E|E]; [lia|]. rewrite Uint63.eqb_refl. reflexivity. }
  (* [comment removed for export] *)
  assert (Ht20 : to_Z t < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  assert (Hst20 : to_Z (sh_tag t) < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  remember (mset (s_mem S) T_STK (drop_below rgs (wl o))) as Mc eqn:EMc.
  set (newrg := RG None (wl n) 4 true DUnk (depth_for 60 (wl n) 0) IEmpty).
  set (shrg := shadow_region (wl n >> 3)%uint63 false DZero).
  assert (Hcases : forall t3 rg3, mget (mset (mset Mc t newrg) (sh_tag t) shrg) t3 = Some rg3 ->
            (t3 = sh_tag t /\ rg3 = shrg) \/ (t3 = t /\ rg3 = newrg) \/ (t3 <> sh_tag t /\ t3 <> t /\ mget Mc t3 = Some rg3)).
  { intros t3 rg3 G3. destruct (mget_mset_cases _ (sh_tag t) t3 _ rg3 Hst20 G3) as [[-> ->]|[N1 G3']]; [left; auto|].
    destruct (mget_mset_cases Mc t t3 _ rg3 Ht20 G3') as [[-> ->]|[N2 G3'']]; [right; left; auto | right; right; auto]. }
  assert (Hold : forall t3 rg3, mget Mc t3 = Some rg3 -> to_Z t3 < to_Z (s_next S)).
  { intros t3 rg3 G3. rewrite EMc in G3. destruct (mget_mset_cases _ T_STK t3 _ rg3 (mget_lt _ _ _ Egs) G3) as [[-> _]|[_ G3']]; [exact (Htags _ _ Egs) | exact (Htags _ _ G3')]. }
  assert (HfreshT : mget Mc t = None).
  { destruct (mget Mc t) as [rgx|] eqn:Ex; [|reflexivity]. pose proof (Hold t rgx Ex). lia. }
  assert (HfreshS : mget (mset Mc t newrg) (sh_tag t) = None).
  { rewrite (mget_mset Mc t (sh_tag t) newrg Ht20). destruct (Z.eqb_spec (to_Z t) (to_Z (sh_tag t))) as [E|E]; [lia|].
    destruct (mget Mc (sh_tag t)) as [rgx|] eqn:Ex; [|reflexivity]. pose proof (Hold _ rgx Ex). lia. }
  assert (GetT : mget (mset (mset Mc t newrg) (sh_tag t) shrg) t = Some newrg).
  { rewrite (mget_mset _ (sh_tag t) t shrg Hst20). destruct (Z.eqb_spec (to_Z (sh_tag t)) (to_Z t)) as [E|E]; [lia|].
    rewrite (mget_mset Mc t t newrg Ht20), Z.eqb_refl. reflexivity. }
  assert (GetS : mget (mset (mset Mc t newrg) (sh_tag t) shrg) (sh_tag t) = Some shrg).
  { rewrite (mget_mset _ (sh_tag t) (sh_tag t) shrg Hst20), Z.eqb_refl. reflexivity. }
  assert (GetOld : forall t3, to_Z t3 < to_Z (s_next S) -> t3 <> T_STK -> mget (mset (mset Mc t newrg) (sh_tag t) shrg) t3 = mget (s_mem S) t3).
  { intros t3 H3 N3. rewrite (mget_mset _ (sh_tag t) t3 shrg Hst20). destruct (Z.eqb_spec (to_Z (sh_tag t)) (to_Z t3)) as [E|E]; [lia|].
    rewrite (mget_mset Mc t t3 newrg Ht20). destruct (Z.eqb_spec (to_Z t) (to_Z t3)) as [E'|E']; [lia|].
    rewrite EMc, (mget_mset _ T_STK t3 _ (mget_lt _ _ _ Egs)). destruct (Z.eqb_spec (to_Z T_STK) (to_Z t3)) as [E''|E'']; [apply to_Z_inj in E''; congruence | reflexivity]. }
  assert (GetStk : mget (mset (mset Mc t newrg) (sh_tag t) shrg) T_STK = Some (drop_below rgs (wl o))).
  { rewrite (mget_mset _ (sh_tag t) T_STK shrg Hst20). destruct (Z.eqb_spec (to_Z (sh_tag t)) (to_Z T_STK)) as [E|E]; [change (to_Z T_STK) with 2 in E; lia|].
    rewrite (mget_mset Mc t T_STK newrg Ht20). destruct (Z.eqb_spec (to_Z t) (to_Z T_STK)) as [E'|E']; [change (to_Z T_STK) with 2 in E'; lia|].
    rewrite EMc, (mget_mset _ T_STK T_STK _ (mget_lt _ _ _ Egs)), Z.eqb_refl. reflexivity. }
  (* [comment removed for export] *)
  assert (HinP : In (p, nz) (rt_live RT Σ')) by (rewrite El'; left; reflexivity).
  destruct (af_live_range RT AF _ _ _ _ HART' HinP) as (P1 & P2 & P3).
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof (to_Z_bounded (wl o)) as Bo.
  assert (Esz8 : to_Z (wl n >> 3)%uint63 = nz / 8) by (rewrite phi_shr3; reflexivity).
  assert (Hmc0 : mcost nz = 0) by (unfold mcost; destruct (Z.leb_spec nz 64512); [reflexivity | lia]).
  assert (Ers : rsize (mset (mset Mc t newrg) (sh_tag t) shrg) t = nz) by (unfold rsize; rewrite GetT; reflexivity).
  apply (K (GH RT Σ') rho' ms' Hag'); [|exact Hc'']. subst ms'. rewrite new_region_eq. fold newrg. fold shrg.
  assert (HF' : FMemA (GH RT Σ') rho' (XCD (t :: x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd + 1)) (mset (mset Mc t newrg) (sh_tag t) shrg) (t + 2)%uint63 m').
  { apply (FMem_update RT CL lo sp0 r m0 cr0 anc xp g rho rho' cd (s_mem S) _ (s_next S) _ m m' Σ' (B0A + to_Z (wl o)) _ _ _ _ HF Hag'); try assumption; try lia.
    - apply (kept_stack sp0 _ _ _ 0 0 m m' (pres_ex_of_pres _ _ _ m m' Hpres)); [unfold B0, SEGTOP_A, STACK_WIN in *; lia | tauto | intros; lia].
    - pose proof Hpres as Hpres2. rewrite Hlive in Hpres2. apply (kept_caller CL sp0 xp _ _ _ 0 0 m m' (pres_ex_of_pres _ _ _ m m' Hpres2)); [lia | intros; lia].
    - rewrite El', Hlive. unfold blk_list. cbn [map app]. rewrite Erho't, Ers. f_equal. f_equal. apply map_ext_in. intros b Hb.
      destruct (Htl b (in_or_app _ _ _ (or_introl Hb))) as (_ & Tb1 & Tb2). rewrite (Hag' b) by lia. f_equal.
      unfold rsize. rewrite GetOld; [reflexivity | lia | intros ->; change (to_Z T_STK) with 2 in Tb1; lia].
    - rewrite Ef', Hfr. unfold frm_list. apply map_ext_in. intros f Hf. destruct (Htl f (in_or_app _ _ _ (or_intror Hf))) as (_ & Tb1 & Tb2).
      rewrite (Hag' f) by lia. reflexivity.
    - cbn [app]. constructor; [|exact Hnd]. intros Hin. destruct (Htl t Hin) as (_ & _ & X). lia.
    - intros t0 [<-|Hin]; [split; [exact Tev|]; change (to_Z NEXT0) with 32; lia|]. destruct (Htl t0 Hin) as (X1 & X2 & X3).
      split; [exact X1|]. change (to_Z NEXT0) with 32. lia.
    - intros t0 rg0 G0. destruct (Hcases t0 rg0 G0) as [[-> _]|[[-> _]|(_ & _ & G)]]; [lia | lia | pose proof (Hold _ _ G); lia].
    - intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> ->]|[[-> ->]|(N1 & N2 & G)]].
      + cbn [shrg shadow_region rg_abs rg_size rg_wr]. right; right; right; left. exists t. split; [left; reflexivity|]. split; [reflexivity|].
        split; [|reflexivity]. rewrite Ers. exact Esz8.
      + cbn [newrg rg_abs rg_wr]. right; right; left. split; [left; reflexivity | reflexivity].
      + rewrite EMc in G. destruct (mget_mset_cases _ T_STK t3 _ rg3 (mget_lt _ _ _ Egs) G) as [[-> ->]|[N3 G']].
        * cbn [drop_below rg_abs rg_size rg_wr]. rewrite Eabs. left. auto.
        * pose proof (Hcls t3 rg3 G') as C. destruct (rg_abs rg3); [exact C|].
          destruct C as [C|[C|[(Hin & Ew3)|[(b & Hin & Eb & Es3 & Ew3)|[C|C]]]]].
          -- left. exact C.
          -- right; left. exact C.
          -- right; right; left. split; [right; exact Hin | exact Ew3].
          -- right; right; right; left. exists b. split; [right; exact Hin|]. split; [exact Eb|]. split; [|exact Ew3]. rewrite Es3. f_equal.
             destruct (Htl b (in_or_app _ _ _ (or_introl Hin))) as (_ & Tb1 & Tb2).
             unfold rsize. rewrite GetOld; [reflexivity | lia | intros ->; change (to_Z T_STK) with 2 in Tb1; lia].
          -- right; right; right; right; left. exact C.
          -- right; right; right; right; right. exact C.
    - destruct Hlink as [LL1 LL2]. split.
      + intros b [<-|Hb].
        * exists newrg. split; [exact GetT|]. cbn [newrg rg_abs rg_wr rg_size]. fold nz. repeat split; try reflexivity; lia.
        * destruct (LL1 b Hb) as (rgb & Gb & X). exists rgb. split; [|exact X]. destruct (Htl b (in_or_app _ _ _ (or_introl Hb))) as (_ & Tb1 & Tb2).
          rewrite GetOld; [exact Gb | lia | intros ->; change (to_Z T_STK) with 2 in Tb1; lia].
      + intros f Hf. destruct (LL2 f Hf) as (rgf & Gf & X). exists rgf. split; [|exact X]. destruct (Htl f (in_or_app _ _ _ (or_intror Hf))) as (_ & Tb1 & Tb2).
        rewrite GetOld; [exact Gf | lia | intros ->; change (to_Z T_STK) with 2 in Tb1; lia].
    - intros t0 [<-|Hin]; [rewrite Erho's, Erho't; reflexivity|]. destruct (Htl t0 Hin) as (_ & X2 & X3).
      rewrite (Hag' (sh_tag t0)) by (rewrite sh_tag_Z by lia; lia). rewrite (Hag' t0) by lia. exact (Hrsh t0 Hin).
    - cbn [length]. lia. }
  pose proof (shad_range p ltac:(unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as Rp1.
  pose proof (shad_range (p + nz) ltac:(unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as Rp2.
  pose proof (shad_end p nz En8) as Rp3. unfold SH_LO, SH_HI in Rp1, Rp2.
  destruct (FMem_loc_bounds RT CL lo sp0 r m0 cr0 anc xp g rho cd _ _ m HF) as [HB _].
  split; [split|split; [exact HF' | split; [reflexivity | cbn [ms_regs MS]; do 31 eexists; reflexivity]]].
  - (* [comment removed for export] *)
    intros rho2 Hag2. cbn [s_next] in Hag2.
    assert (Hag02 : agree_below (s_next S) rho rho2).
    { intros t' Ht'. rewrite (Hag2 t') by lia. apply Hag'. exact Ht'. }
    assert (Erho2t : rho2 t = p) by (rewrite (Hag2 t) by lia; exact Erho't).
    assert (Erho2s : rho2 (sh_tag t) = shad p) by (rewrite (Hag2 (sh_tag t)) by lia; exact Erho's).
    destruct (HRall rho2 Hag02) as [HRg2 HRm2].
    apply (R_return rho2 S (VP t w_zero) _ (s_abs S) (t + 2)%uint63 ra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
             t0' t1' t2' (Z_to_bv 64 p) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F F' (wbv (s_pc S)) fc fc' None m' (seg_rom bsegs) HRg2 D1').
    { cbn [den]. unfold pword. rewrite Erho2t. change (wZ w_zero) with 0. rewrite Z.add_0_r. reflexivity. }
    assert (EBt : rbase rho2 t newrg = p) by (unfold rbase; cbn [newrg rg_abs]; exact Erho2t).
    assert (EBs : rbase rho2 (sh_tag t) shrg = shad p) by (unfold rbase; cbn [shrg shadow_region rg_abs]; exact Erho2s).
    assert (Kd : forall t2 rg2, mget Mc t2 = Some rg2 -> rkind RT sp0 r xp (g_S RT g) (rbase rho2 t2 rg2) (to_Z (rg_size rg2)) (rg_wr rg2)).
    { intros t2 rg2 G2. rewrite EMc in G2. exact (region_loc_clobbered RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho rho2 cd (s_mem S) (s_next S) m rgs (wl o) t2 rg2 HF Hag02 Egs G2). }
    split.
    + intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> ->]|[[-> ->]|(N1 & N2 & G)]].
      * (* [comment removed for export] *)
        apply (zero_region_ok rho2 (sh_tag t) (wl n >> 3)%uint63 m' (shad p) Erho2s); [lia | unfold two63; lia | lia |].
        pose proof (af_sh_live RT AF _ _ _ _ HART' HinP) as Q. rewrite (ushadow_whole nz En8) in Q. rewrite Esz8. exact Q.
      * (* [comment removed for export] *)
        apply (fresh_region_ok rho2 t (wl n) 4 true m' p Erho2t); fold nz; try lia; [unfold two63, USTACK_TOP in *; lia | change (to_Z 4%uint63) with 4; lia | exact Hp16 | exact Hwr'].
      * (* [comment removed for export] *)
        rewrite EMc in G.
        apply (regions_after_call RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk IMGSH_OK g rho rho2 cd (s_mem S) (s_next S) m m' Σ' (rt_live RT (g_S RT g)) o rgs (s_next S) (s_next S) 0 0
                 HF HRm2 Hag02 Egs Eabs Edf Ewr Ho16 Hosz HART' MI' Hstk' (pres_ex_of_pres _ _ _ m m' Hpres) Es'); try assumption; try lia.
        -- intros b Hb _. assert (Hin : In (rho b, rsize (s_mem S) b) (rt_live RT (g_S RT g))).
           { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists b. auto. }
           split; [exact Hin | rewrite El'; right; exact Hin].
        -- intros e He. assert (Hin : In e (rt_live RT (g_S RT g))) by (rewrite Hlive; apply in_or_app; right; exact He).
           split; [exact Hin | rewrite El'; right; exact Hin].
        -- intros E. pose proof (Htags _ _ Egs) as X. rewrite <- E in X. lia.
        -- intros E. rewrite <- EMc in G. pose proof (Hold _ _ G) as X. rewrite E in X. lia.
        -- intros E. rewrite <- EMc in G. pose proof (Hold _ _ G) as X. rewrite E in X. rewrite sh_tag_Z in X by lia. lia.
        -- intros E. rewrite <- EMc in G. pose proof (Hold _ _ G) as X. rewrite E in X. lia.
    + (* [comment removed for export] *)
      apply (regions_sep_new_wr rho2 _ (sh_tag t) shrg); [| exact HfreshS | exact Hst20 |].
      * apply (regions_sep_new rho2 Mc t newrg); [| exact HfreshT | exact Ht20 |].
        -- rewrite EMc. exact (regions_sep_mset_same rho2 _ T_STK rgs _ Egs (same_dir_drop_below rgs (wl o)) (proj2 HRm2)).
        -- intros t2 rg2 G2. rewrite EBt. cbn [newrg rg_size]. fold nz.
           apply (kind_apart_block RT AF lo sp0 r xp H_r XP_stk (g_S RT g) Σ' m m' _ _ _ p nz 0 (rt_live RT (g_S RT g)) (Kd t2 rg2 G2) HART HB HART' El'); try assumption; try lia.
           ++ intros b0 s0 Hin _. exact Hin.
           ++ intros Hin _. destruct (af_live_range RT AF _ _ _ _ HART Hin) as (X & _). lia.
      * intros t2 rg2 G2 [Hw|Hw]; [discriminate Hw|]. rewrite EBs. cbn [shrg shadow_region rg_size]. rewrite Esz8.
        destruct (mget_mset_cases Mc t t2 _ rg2 Ht20 G2) as [[-> ->]|[N2 G2']].
        -- rewrite EBt. cbn [newrg rg_size]. fold nz. destruct (af_live_offshadow RT AF _ _ _ _ HART' HinP) as [D|D]; [right; lia | left; lia].
        -- pose proof (Kd t2 rg2 G2') as Kd2. rewrite Hw in Kd2.
           exact (kind_apart_bshadow RT AF lo sp0 r xp H_r XP_stk (g_S RT g) Σ' m m' _ _ p nz Kd2 HART HB HART' HinP Ef' Es' ltac:(lia) En8).
  - intros rho2 Hag2. exact (FMem_law RT CL lo sp0 r m0 cr0 anc xp (GH RT Σ') rho' rho2 _ _ _ m' HF' Hag2).
Qed.

End HkMalloc.
