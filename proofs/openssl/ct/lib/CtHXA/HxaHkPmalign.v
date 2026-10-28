(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_unwind_chain RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsStep HxsStepSound HxsHookSound.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXS Require Import HxsHookCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaInit HxaImage HxaInv HxaHooks HxaHk HxaHkDefs HxaHkMalloc HxaHkRelease HxaHkRealloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section HkPmalign.
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
Hypothesis H_nb : NB_MAX <= xp_nbmax xp.
Hypothesis IMGSH_OK : forall Σ m rho t, ART RT Σ m -> region_ok ctasegs rho t (xp_rgsh xp) m.
Hypothesis PMA : posix_memalign_init_contract RT.

Notation FMemA := (FMem RT CL lo sp0 r m0 cr0 anc xp).
Notation FInvA := (FInv RT CL lo sp0 r m0 cr0 anc xp).
Notation JA := (J RT PMc T).
Notation B0A := (B0 sp0 r xp).
Notation XInvA := (XInv ctasegs SHBW (ghost RT) FInvA).
Notation xhook_okA := (xhook_ok ctasegs SHBW (ghost RT) JA FInvA).

Lemma PC_POSIX_MEMALIGN_Z : wbv PC_POSIX_MEMALIGN = Z_to_bv 64 e_posix_memalign. Proof. reflexivity. Qed.

Lemma hkA_posix_memalign_ok : xhook_okA hkA_posix_memalign.
Proof.
  intros g rho cd S cd' S' ms [[HRn Hlaw] [HF (Hro & Hnf)]] Hh K.
  unfold hkA_posix_memalign, hk_at in Hh. destruct (w_eqb (s_pc S) PC_POSIX_MEMALIGN) eqn:Epc; [|discriminate]. apply w_eqb_true_iff in Epc.
  unfold hkx_posix_memalign in Hh.
  destruct (xtp_ok TPV S && xsp_ok T_STK S && unwind_okb ctasegs T_STK TRACES T_S0 IMG_TOP S) eqn:Eg; [|discriminate].
  apply andb_prop in Eg as [Eg Eun]. apply andb_prop in Eg as [Etp Esp].
  destruct (rget S X10) as [|tm om| |] eqn:Ea10; try discriminate. destruct (rget S X11) as [al| | |] eqn:Ea11; try discriminate.
  destruct (rget S X12) as [n| | |] eqn:Ea12; try discriminate.
  destruct (negb (wh om) && negb (wh al) && negb (wh n) && (wl al =? 64)%uint63 && (wl n =? 32768)%uint63
           && (wl om land 7 =? 0)%uint63 && (x_nb cd <? NB_MAX) && (x_calls cd <? CALLS_MAX)
           && (tag_even tm) && existsb (fun x => (x =? tm)%uint63) (x_frames cd)) eqn:Eck; [|discriminate].
  apply andb_prop in Eck as [Eck Ec10]. apply andb_prop in Eck as [Eck Ec9]. apply andb_prop in Eck as [Eck Ec6]. apply andb_prop in Eck as [Eck Ec5].
  apply andb_prop in Eck as [Eck Ec4]. apply andb_prop in Eck as [Eck Ec3]. apply andb_prop in Eck as [Eck Ec2]. apply andb_prop in Eck as [Eck Ec1b]. apply andb_prop in Eck as [Ec1 Ec1a].
  apply negb_true_iff in Ec1. apply negb_true_iff in Ec1a. apply negb_true_iff in Ec1b. apply Uint63.eqb_spec in Ec2. apply Uint63.eqb_spec in Ec3. apply Uint63.eqb_spec in Ec4.
  apply Z.ltb_lt in Ec5, Ec6. unfold NB_MAX, CALLS_MAX in Ec5, Ec6, H_nb.
  apply existsb_exists in Ec10 as (tm' & Hintm & Etm'). apply Uint63.eqb_spec in Etm'. subst tm'.
  cbv zeta in Hh. set (t := even_up (s_next S)) in *.
  destruct (xclobber_stack RT_STACK S (s_mem S)) as [Mc|] eqn:Ecl; [|discriminate].
  destruct (mget Mc tm) as [rgm|] eqn:Egm0; [|discriminate].
  destruct (rg_wr rgm && (wl om <=? rg_size rgm)%uint63 && (wl om + 8 <=? rg_size rgm)%uint63 && match rg_abs rgm with None => true | Some _ => false end) eqn:Eckm; [|discriminate].
  apply andb_prop in Eckm as [Eckm Eabsm0]. apply andb_prop in Eckm as [Eckm Eszm]. apply andb_prop in Eckm as [Ewrm Eszm0]. apply leb_spec in Eszm. apply leb_spec in Eszm0.
  destruct (rg_abs rgm) eqn:Eabsm; [discriminate|]. clear Eabsm0.
  set (rgm' := RG None (rg_size rgm) (rg_al rgm) (rg_wr rgm) (rg_dflt rgm) (rg_d rgm) (iset (rg_d rgm) (rg_cells rgm) (wl om >> 3)%uint63 (CP t w_zero))) in *.
  destruct (t <? 999990)%uint63 eqn:Et; [|discriminate]. apply ltb_spec in Et. change (to_Z 999990%uint63) with 999990 in Et.
  match type of Hh with match xret S ?res ?MM ?nn with _ => _ end = _ => destruct (xret S res MM nn) as [S1|] eqn:Ert; [|discriminate] end.
  injection Hh as <- <-.
  destruct (xclobber_inv T_STK RT_STACK S _ _ Ecl Esp) as (o & rgs & Esp2 & Eho & Egs & Eabs & Edf & Ho16 & Hrt & Hosz & Ewr & EMc0).
  destruct (xret_inv _ _ _ _ _ Ert) as (ra & Era & Erv & ->).
  destruct (ms_nf rho S ms (Rn_R ctasegs rho S ms HRn) Erv Hro Hnf)
    as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
        & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Ems & HRg).
  set (m := ms_mem ms) in *. set (F := ms_fregs ms) in *. set (fc := ms_fcsr ms) in *. clearbody m F fc. subst ms.
  cbn [ms_mem ms_regs ms_rom MS] in HF, Hro, Hnf.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & D2 & D4 & D8 & D10 & D11 & D12).
  pose proof D1 as D1'. pose proof D2 as D2'. rewrite Era in D1'. rewrite Esp2 in D2'. rewrite Ea10 in D10. rewrite Ea11 in D11. rewrite Ea12 in D12. cbn [den] in D1', D2', D10, D11, D12.
  unfold xtp_ok in Etp. destruct (rget S X4) as [tpw| | |]; try discriminate. apply w_eqb_true_iff in Etp. subst tpw. cbn [den] in D4.
  assert (HRall : forall rho2, agree_below (s_next S) rho rho2 ->
            Rregs rho2 (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wbv (s_pc S)) fc None)
            /\ Rmem ctasegs rho2 (s_mem S) m).
  { intros rho2 Hag. destruct (HRn rho2 Hag) as (_ & _ & HRg2 & _ & HRm2). exact (conj HRg2 HRm2). }
  subst Mc.
  destruct (stk_class RT CL lo sp0 r m0 cr0 anc xp g rho cd _ _ m rgs HF Egs Eabs) as [Esz _].
  destruct (call_geometry RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd _ _ m o x2 HF Eho Ho16 Hrt ltac:(lia) D2') as (Espv & Hcall & Hspc).
  pose proof (unwind_premise RT AF CL lo sp0 r m0 cr0 anc xp XP_stk g rho cd S m x1 x2 x8 HF (proj2 (HRall rho (agree_below_refl _ _))) Eun D1 D2 D8) as Hunw.      (* [comment removed for export] *)
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hr0 & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & (Hc1 & Hc2 & Hc3 & Hc4) & Hagr).
  change (to_Z NEXT0) with 32 in *.
  (* [comment removed for export] *)
  pose proof (to_Z_bounded (wl n)) as Bn. pose proof (to_Z_bounded (wl om)) as Bom.
  assert (EwZn : wZ n = to_Z (wl n)) by (unfold wZ; rewrite Ec1b; lia).
  assert (Enz : to_Z (wl n) = 32768) by (rewrite Ec3; reflexivity).
  assert (EwZal : wZ al = 64) by (unfold wZ; rewrite Ec1a, Ec2; reflexivity).
  assert (EwZom : wZ om = to_Z (wl om)) by (unfold wZ; rewrite Ec1; lia).
  assert (Eom8 : to_Z (wl om) mod 8 = 0) by (rewrite <- phi_land7, Ec4; reflexivity).
  set (nz := to_Z (wl n)) in *.
  destruct (ushadow_region_shape (wl n) ltac:(lia)) as (USa & USw & USal & USsz & USd & USdf).
  (* [comment removed for export] *)
  assert (Hintm' : In tm (x_blocks cd ++ x_frames cd)) by (apply in_or_app; right; exact Hintm).
  destruct (Htl tm Hintm') as (Ttmev & Ttm1 & Ttm2).
  assert (Ntm : tm <> T_STK) by (intros ->; change (to_Z T_STK) with 2 in Ttm1; lia).
  assert (Egm : mget (s_mem S) tm = Some rgm).
  { rewrite (mget_mset _ T_STK tm _ (mget_lt _ _ _ Egs)) in Egm0. destruct (Z.eqb_spec (to_Z T_STK) (to_Z tm)) as [E|E]; [apply to_Z_inj in E; congruence | exact Egm0]. }
  destruct (proj2 Hlink tm Hintm) as (rgm_ & Egm_ & _ & _ & Hfszm). rewrite Egm in Egm_. injection Egm_ as <-.
  pose proof (fsz_facts _ Hfszm) as (FZ1 & FZ2 & FZ3 & FZ4). pose proof (to_Z_bounded (rg_size rgm)) as Bszm.
  set (km := fcls (to_Z (rg_size rgm))).
  assert (Efkm : fs_size km = to_Z (rg_size rgm) + 8) by (unfold km; apply fcls_size; exact Hfszm).
  assert (HinFm : In (rho tm, km) (rt_frames RT (g_S RT g))).
  { rewrite Hfr. unfold frm_list. apply in_map_iff. exists tm. unfold km. rewrite (rsize_get _ tm rgm Egm). auto. }
  destruct (af_frames_range RT AF _ _ _ _ HART HinFm) as (Fm1 & Fm2 & Fm3 & Fm4). rewrite Efkm in Fm2, Fm3, Fm4.
  destruct (af_frames_align RT AF _ _ _ _ HART HinFm) as [Fm64 _].
  set (mp := rho tm + to_Z (wl om)) in *.
  assert (Hmp8 : mp mod 8 = 0) by (unfold mp; Z.div_mod_to_equations; lia).
  pose proof (proj2 (HRall rho (agree_below_refl _ _))) as HRm0.
  pose proof (proj1 HRm0 tm rgm Egm) as Hokm. pose proof Hokm as (Bm0 & Bm1 & Bm2 & Bm3 & Bm4 & _ & _ & Hbym). unfold rbase in Bm0, Bm1, Hbym. rewrite Eabsm in Bm0, Bm1, Hbym. unfold two63 in Bm1.
  assert (Eom8s : to_Z (wl om + 8)%uint63 = to_Z (wl om) + 8).
  { rewrite add_spec. change (to_Z 8%uint63) with 8. apply Z.mod_small. rewrite wB_eq. unfold two63. lia. }
  rewrite Eom8s in Eszm.
  assert (Hwrmp : wr_at ctasegs m mp 8).
  { split; [unfold mp; lia|]. split; [unfold mp; lia|]. intros i Hi. destruct (Hbym (to_Z (wl om) + i) ltac:(lia)) as (b & _ & _ & W).
    unfold mp. rewrite <- Z.add_assoc. exact (W Ewrm). }
  (* [comment removed for export] *)
  destruct (even_up_spec (s_next S) Hnx) as [Tev Tr]. fold t in Tev, Tr.
  assert (Et1 : to_Z (sh_tag t) = to_Z t + 1) by (apply sh_tag_Z; lia).
  assert (Et2 : to_Z (t + 2)%uint63 = to_Z t + 2) by (apply add2_Z; lia).
  (* [comment removed for export] *)
  intros c Hc. rewrite Epc, PC_POSIX_MEMALIGN_Z in Hc.
  assert (Hlen : live_room (rt_live RT (g_S RT g)) PMA_SIZE).      (* [comment removed for export] *)
  { rewrite Hlive. apply (lroom3_live_room _ 1 LW_MAX 1); [| lia | lia | lia]. apply lroom3_app_intro.
    pose proof (psum_le_len (blk_list rho (s_mem S) (x_blocks cd))) as WBL. pose proof (nbig_le_len (blk_list rho (s_mem S) (x_blocks cd))) as NBL.
    unfold blk_list in *. rewrite length_map in *.
    eapply lroom3_mono; [exact Hc1| | |]; unfold LW_MAX in *; lia. }
  assert (Hcost : mcost PMA_SIZE <= rt_credit RT (g_S RT g)) by (unfold mcost, PMA_SIZE; cbn; exact (af_credit_nonneg RT AF _ _ HART)).
  apply (PMA (g_S RT g) PMc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           F fc m mp lo PMc_fdfs PMc_mat ltac:(rewrite D10; unfold pword, mp; rewrite EwZom; reflexivity)
           ltac:(rewrite D11; unfold wbv; rewrite EwZal; reflexivity) ltac:(rewrite D12; unfold wbv; rewrite EwZn, Enz; reflexivity)
           ltac:(rewrite D4; exact TPV_Z) Hlen Hcost HART Hmi Hcall Hunw Hmp8
           ltac:(intros i Hi; rewrite Espv; right; right; right; left; exists (rho tm), km; split; [exact HinFm | rewrite Efkm; unfold mp; lia])
           Hwrmp ltac:(left; lia) T c Hc).
  intros c' (Σ' & p & Hc' & El' & Ef' & Es' & Ecr' & Hp0 & Hp16 & Hptop). unfold PMA_SIZE, PMA_ALIGN in El', Ecr', Hp16, Hptop.
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & (m' & Hret & (HART' & MI' & WM & Hstk') & Hpres & Hmpc & Hwr' & Hacc') & Hc''). unfold PMA_SIZE in Hwr', Hacc'.
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
  assert (Htm20 : to_Z tm < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  remember (mset (mset (s_mem S) T_STK (drop_below rgs (wl o))) tm rgm') as Mc eqn:EMc.
  set (newrg := RG None (wl n) 6 true DUnk (depth_for 60 (wl n) 0) IEmpty).
  set (shrg := ushadow_region (wl n)). fold shrg in USa, USw, USal, USsz, USd, USdf.
  assert (Ergm' : rgm' = wr_cell rgm (wl om >> 3)%uint63 (CP t w_zero)) by (unfold rgm', wr_cell; rewrite Eabsm; reflexivity).
  assert (Hsdm : same_dir rgm rgm') by (rewrite Ergm'; apply same_dir_wr_cell).
  assert (Hcases : forall t3 rg3, mget (mset (mset Mc t newrg) (sh_tag t) shrg) t3 = Some rg3 ->
            (t3 = sh_tag t /\ rg3 = shrg) \/ (t3 = t /\ rg3 = newrg) \/ (t3 <> sh_tag t /\ t3 <> t /\ mget Mc t3 = Some rg3)).
  { intros t3 rg3 G3. destruct (mget_mset_cases _ (sh_tag t) t3 _ rg3 Hst20 G3) as [[-> ->]|[N1 G3']]; [left; auto|].
    destruct (mget_mset_cases Mc t t3 _ rg3 Ht20 G3') as [[-> ->]|[N2 G3'']]; [right; left; auto | right; right; auto]. }
  assert (CasesMc : forall t3 rg3, mget Mc t3 = Some rg3 -> (t3 = tm /\ rg3 = rgm') \/ (t3 <> tm /\ mget (mset (s_mem S) T_STK (drop_below rgs (wl o))) t3 = Some rg3)).
  { intros t3 rg3 G3. rewrite EMc in G3. exact (mget_mset_cases _ tm t3 _ rg3 Htm20 G3). }
  assert (Hold : forall t3 rg3, mget Mc t3 = Some rg3 -> to_Z t3 < to_Z (s_next S)).
  { intros t3 rg3 G3. destruct (CasesMc t3 rg3 G3) as [[-> _]|[_ G3x]]; [lia|].
    destruct (mget_mset_cases _ T_STK t3 _ rg3 (mget_lt _ _ _ Egs) G3x) as [[-> _]|[_ G3']]; [exact (Htags _ _ Egs) | exact (Htags _ _ G3')]. }
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
  assert (GetOld : forall t3, to_Z t3 < to_Z (s_next S) -> t3 <> T_STK -> t3 <> tm -> mget (mset (mset Mc t newrg) (sh_tag t) shrg) t3 = mget (s_mem S) t3).
  { intros t3 H3 N3 N4. rewrite (mget_mset _ (sh_tag t) t3 shrg Hst20). destruct (Z.eqb_spec (to_Z (sh_tag t)) (to_Z t3)) as [E|E]; [lia|].
    rewrite (mget_mset Mc t t3 newrg Ht20). destruct (Z.eqb_spec (to_Z t) (to_Z t3)) as [E'|E']; [lia|].
    rewrite EMc, (mget_mset _ tm t3 _ Htm20). destruct (Z.eqb_spec (to_Z tm) (to_Z t3)) as [E3|E3]; [apply to_Z_inj in E3; congruence|].
    rewrite (mget_mset _ T_STK t3 _ (mget_lt _ _ _ Egs)). destruct (Z.eqb_spec (to_Z T_STK) (to_Z t3)) as [E''|E'']; [apply to_Z_inj in E''; congruence | reflexivity]. }
  assert (GetTm : mget (mset (mset Mc t newrg) (sh_tag t) shrg) tm = Some rgm').
  { rewrite (mget_mset _ (sh_tag t) tm shrg Hst20). destruct (Z.eqb_spec (to_Z (sh_tag t)) (to_Z tm)) as [E|E]; [lia|].
    rewrite (mget_mset Mc t tm newrg Ht20). destruct (Z.eqb_spec (to_Z t) (to_Z tm)) as [E'|E']; [lia|].
    rewrite EMc, (mget_mset _ tm tm _ Htm20), Z.eqb_refl. reflexivity. }
  assert (Erszq : forall q, In q (x_blocks cd ++ x_frames cd) -> rsize (mset (mset Mc t newrg) (sh_tag t) shrg) q = rsize (s_mem S) q).
  { intros q Hq. destruct (Htl q Hq) as (_ & Tq1 & Tq2). unfold rsize. destruct (eqbP q tm) as [E|E].
    - apply to_Z_inj in E. subst q. rewrite GetTm, Egm. reflexivity.
    - rewrite GetOld; [reflexivity | lia | intros ->; change (to_Z T_STK) with 2 in Tq1; lia | intros X4; apply E; rewrite X4; reflexivity]. }
  assert (GetStk : mget (mset (mset Mc t newrg) (sh_tag t) shrg) T_STK = Some (drop_below rgs (wl o))).
  { rewrite (mget_mset _ (sh_tag t) T_STK shrg Hst20). destruct (Z.eqb_spec (to_Z (sh_tag t)) (to_Z T_STK)) as [E|E]; [change (to_Z T_STK) with 2 in E; lia|].
    rewrite (mget_mset Mc t T_STK newrg Ht20). destruct (Z.eqb_spec (to_Z t) (to_Z T_STK)) as [E'|E']; [change (to_Z T_STK) with 2 in E'; lia|].
    rewrite EMc, (mget_mset _ tm T_STK _ Htm20). destruct (Z.eqb_spec (to_Z tm) (to_Z T_STK)) as [E3|E3]; [change (to_Z T_STK) with 2 in E3; lia|].
    rewrite (mget_mset _ T_STK T_STK _ (mget_lt _ _ _ Egs)), Z.eqb_refl. reflexivity. }
  (* [comment removed for export] *)
  assert (HinP : In (p, nz) (rt_live RT Σ')) by (rewrite El', Enz; left; reflexivity).
  destruct (af_live_range RT AF _ _ _ _ HART' HinP) as (P1 & P2 & P3).
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof (to_Z_bounded (wl o)) as Bo.
  assert (Hmc0 : mcost 32768 = 0) by reflexivity.
  assert (Ers : rsize (mset (mset Mc t newrg) (sh_tag t) shrg) t = nz) by (unfold rsize; rewrite GetT; reflexivity).
  apply (K (GH RT Σ') rho' ms' Hag'); [|exact Hc'']. subst ms'. fold newrg. fold shrg.
  assert (HF' : FMemA (GH RT Σ') rho' (XCD (t :: x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd + 1)) (mset (mset Mc t newrg) (sh_tag t) shrg) (t + 2)%uint63 m').
  { apply (FMem_update RT CL lo sp0 r m0 cr0 anc xp g rho rho' cd (s_mem S) _ (s_next S) _ m m' Σ' (B0A + to_Z (wl o)) _ _ _ _ HF Hag'); try assumption; try lia.
    - apply (kept_stack sp0 _ _ _ mp 8 m m' Hpres); [unfold B0, SEGTOP_A, STACK_WIN in *; lia | tauto | intros; unfold B0, mp, SEGTOP_A, STACK_WIN in *; lia].
    - pose proof Hpres as Hpres2. rewrite Hlive in Hpres2. apply (kept_caller CL sp0 xp _ _ _ mp 8 m m' Hpres2); [lia |].
      intros a Hca Hin. destruct (wr_facts RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd _ _ m tm rgm a HF Egm Ewrm) as (_ & X & _); [unfold rbase; rewrite Eabsm; unfold mp in Hin; lia | exact (X Hca)].
    - rewrite El', Hlive. unfold blk_list. cbn [map app]. rewrite Erho't, Ers. f_equal; [fold nz; rewrite Enz; reflexivity|]. f_equal. apply map_ext_in. intros b Hb.
      destruct (Htl b (in_or_app _ _ _ (or_introl Hb))) as (_ & Tb1 & Tb2). rewrite (Hag' b) by lia. f_equal. symmetry. exact (Erszq b (in_or_app _ _ _ (or_introl Hb))).
    - rewrite Ef', Hfr. unfold frm_list. apply map_ext_in. intros f Hf. destruct (Htl f (in_or_app _ _ _ (or_intror Hf))) as (_ & Tb1 & Tb2).
      rewrite (Hag' f) by lia. f_equal. f_equal. symmetry. exact (Erszq f (in_or_app _ _ _ (or_intror Hf))).
    - cbn [app]. constructor; [|exact Hnd]. intros Hin. destruct (Htl t Hin) as (_ & _ & X). lia.
    - intros t0 [<-|Hin]; [split; [exact Tev|]; change (to_Z NEXT0) with 32; lia|]. destruct (Htl t0 Hin) as (X1 & X2 & X3).
      split; [exact X1|]. change (to_Z NEXT0) with 32. lia.
    - intros t0 rg0 G0. destruct (Hcases t0 rg0 G0) as [[-> _]|[[-> _]|(_ & _ & G)]]; [lia | lia | pose proof (Hold _ _ G); lia].
    - intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> ->]|[[-> ->]|(N1 & N2 & G)]].
      + rewrite USa. right; right; right; left. exists t. split; [left; reflexivity|]. split; [reflexivity|].
        split; [|exact USw]. rewrite Ers. exact USsz.
      + cbn [newrg rg_abs rg_wr]. right; right; left. split; [left; reflexivity | reflexivity].
      + destruct (CasesMc t3 rg3 G) as [[-> ->]|[N3t Gx]].
        * (* [comment removed for export] *)
          cbn [rgm' rg_abs rg_size rg_wr]. right; right; right; right; left. split; [exact Hintm | split; [exact Hfszm | exact Ewrm]].
        * destruct (mget_mset_cases _ T_STK t3 _ rg3 (mget_lt _ _ _ Egs) Gx) as [[-> ->]|[N3 G']].
          -- cbn [drop_below rg_abs rg_size rg_wr]. rewrite Eabs. left. auto.
          -- pose proof (Hcls t3 rg3 G') as C. destruct (rg_abs rg3); [exact C|].
             destruct C as [C|[C|[(Hin & Ew3)|[(b & Hin & Eb & Es3 & Ew3)|[C|[(f & Hin & Ef & Es3 & Ew3)|C]]]]]].
             ++ left. exact C.
             ++ right; left. exact C.
             ++ right; right; left. split; [right; exact Hin | exact Ew3].
             ++ right; right; right; left. exists b. split; [right; exact Hin|]. split; [exact Eb|]. split; [|exact Ew3]. rewrite Es3. f_equal.
                rewrite (Erszq b (in_or_app _ _ _ (or_introl Hin))). reflexivity.
             ++ right; right; right; right; left. exact C.
             ++ right; right; right; right; right; left. exists f. split; [exact Hin|]. split; [exact Ef|]. split; [|exact Ew3]. rewrite Es3. f_equal. f_equal.
                symmetry. exact (Erszq f (in_or_app _ _ _ (or_intror Hin))).
             ++ right; right; right; right; right; right. exact C.
    - destruct Hlink as [LL1 LL2]. split.
      + intros b [<-|Hb].
        * exists newrg. split; [exact GetT|]. cbn [newrg rg_abs rg_wr rg_size]. fold nz. repeat split; try reflexivity. lia.
        * destruct (LL1 b Hb) as (rgb & Gb & X). exists rgb. split; [|exact X]. destruct (Htl b (in_or_app _ _ _ (or_introl Hb))) as (Tbe & Tb1 & Tb2).
          rewrite GetOld; [exact Gb | lia | intros ->; change (to_Z T_STK) with 2 in Tb1; lia | intros ->; exact (nodup_app_disj _ _ tm Hnd Hb Hintm)].
      + intros f Hf. destruct (eqbP f tm) as [E|E].
        * apply to_Z_inj in E. subst f. exists rgm'. split; [exact GetTm|]. cbn [rgm' rg_abs rg_wr rg_size]. split; [reflexivity|]. split; [exact Ewrm | exact Hfszm].
        * destruct (LL2 f Hf) as (rgf & Gf & X). exists rgf. split; [|exact X]. destruct (Htl f (in_or_app _ _ _ (or_intror Hf))) as (_ & Tb1 & Tb2).
          rewrite GetOld; [exact Gf | lia | intros ->; change (to_Z T_STK) with 2 in Tb1; lia | intros X4; apply E; rewrite X4; reflexivity].
    - intros t0 [<-|Hin]; [rewrite Erho's, Erho't; split; [reflexivity | Z.div_mod_to_equations; lia]|]. destruct (Htl t0 Hin) as (_ & X2 & X3).
      rewrite (Hag' (sh_tag t0)) by (rewrite sh_tag_Z by lia; lia). rewrite (Hag' t0) by lia. exact (Hrsh t0 Hin).
    - cbn [length]. lia. }
  pose proof (shad_range p ltac:(unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as Rp1.
  pose proof (shsz_bounds nz ltac:(lia)) as Rp2. unfold SH_LO, SH_HI in Rp1.
  assert (Hp8 : p mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (shad_range (p + 8 * shsz nz) ltac:(rewrite Es' in P2; unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as Rp3.
  rewrite <- (shad_shsz p nz Hp8 ltac:(lia)) in Rp3. unfold SH_LO, SH_HI in Rp3.
  destruct (FMem_loc_bounds RT CL lo sp0 r m0 cr0 anc xp g rho cd _ _ m HF) as [HB _].
  split; [split|split; [exact HF' | split; [reflexivity | cbn [ms_regs MS]; do 31 eexists; reflexivity]]].
  - (* [comment removed for export] *)
    intros rho2 Hag2. cbn [s_next] in Hag2.
    assert (Hag02 : agree_below (s_next S) rho rho2).
    { intros t' Ht'. rewrite (Hag2 t') by lia. apply Hag'. exact Ht'. }
    assert (Erho2t : rho2 t = p) by (rewrite (Hag2 t) by lia; exact Erho't).
    assert (Erho2s : rho2 (sh_tag t) = shad p) by (rewrite (Hag2 (sh_tag t)) by lia; exact Erho's).
    destruct (HRall rho2 Hag02) as [HRg2 HRm2].
    apply (R_return rho2 S (VC w_zero) _ (s_abs S) (t + 2)%uint63 ra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
             t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F F' (wbv (s_pc S)) fc fc' None m' (seg_rom ctasegs) HRg2 D1').
    { cbn [den]. reflexivity. }
    assert (EBt : rbase rho2 t newrg = p) by (unfold rbase; cbn [newrg rg_abs]; exact Erho2t).
    assert (EBs : rbase rho2 (sh_tag t) shrg = shad p) by (unfold rbase; rewrite USa; exact Erho2s).
    assert (Etm2 : rho2 tm = rho tm) by (apply Hag02; lia).
    assert (EBm : rbase rho2 tm rgm' = rho tm) by (unfold rbase; cbn [rgm' rg_abs]; exact Etm2).
    assert (Kd : forall t2 rg2, mget Mc t2 = Some rg2 -> rkind RT sp0 r xp (g_S RT g) (rbase rho2 t2 rg2) (to_Z (rg_size rg2)) (rg_wr rg2)).
    { intros t2 rg2 G2. destruct (CasesMc t2 rg2 G2) as [[-> ->]|[_ G2x]].
      - rewrite (rbase_same_dir rho2 tm rgm rgm' Hsdm) || rewrite <- (rbase_same_dir rho2 tm rgm rgm' Hsdm).
        all: first [ exact (region_loc RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho rho2 cd (s_mem S) (s_next S) m tm rgm HF Hag02 Egm)
                   | cbn [rgm' rg_size rg_wr]; exact (region_loc RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho rho2 cd (s_mem S) (s_next S) m tm rgm HF Hag02 Egm) ].
      - exact (region_loc_clobbered RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho rho2 cd (s_mem S) (s_next S) m rgs (wl o) t2 rg2 HF Hag02 Egs G2x). }
    split.
    + intros t3 rg3 G3. destruct (Hcases t3 rg3 G3) as [[-> ->]|[[-> ->]|(N1 & N2 & G)]].
      * (* [comment removed for export] *)
        apply (ushadow_region_ok rho2 (sh_tag t) (wl n) m' (shad p) Erho2s); fold nz; [lia | unfold two63; lia | lia |].
        exact (af_sh_live RT AF _ _ _ _ HART' HinP).
      * (* [comment removed for export] *)
        apply (fresh_region_ok rho2 t (wl n) 6 true m' p Erho2t); fold nz; try lia; [unfold two63, USTACK_TOP in *; lia | change (to_Z 6%uint63) with 6; lia | change (2 ^ to_Z 6%uint63) with 64; exact Hp16 | rewrite Enz; exact Hwr'].
      * destruct (CasesMc t3 rg3 G) as [[-> ->]|[N3t Gx]].
        -- (* [comment removed for export] *)
           pose proof (proj1 HRm2 tm rgm Egm) as Hokm2.
           apply (region_ok_upd ctasegs rho2 tm rgm rgm' m m' Hokm2 Hsdm). intros i Hi.
           pose proof Hokm2 as (_ & _ & _ & Bm3' & Bm4' & _ & _ & Hby2). unfold rbase in Hby2 |- *. rewrite Eabsm in Hby2 |- *. rewrite Etm2 in Hby2 |- *.
           assert (Hk3 : to_Z (wl om >> 3)%uint63 < 2 ^ Z.of_nat (rg_d rgm)).
           { rewrite phi_shr3. set (X := 2 ^ Z.of_nat (rg_d rgm)) in *. Z.div_mod_to_equations. lia. }
           destruct ((to_Z (wl om) <=? i) && (i <? to_Z (wl om) + 8)) eqn:Ein.
           ++ apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
              destruct Hmpc as [[_ Hbp] Hwp]. cbn [cells_bytes cbytes] in Hbp. rewrite app_nil_r in Hbp.
              pose proof (bytes_at_mrd m' mp (le8 (Z_to_bv 64 p)) (i - to_Z (wl om)) Hbp ltac:(rewrite length_le8; lia)) as Eb.
              replace (mp + (i - to_Z (wl om))) with (rho tm + i) in Eb by (unfold mp; lia).
              unfold le8, word_to_le_bytes in Eb. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 p)) as Hwp64.
              rewrite (nth_Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 p)) (Z.to_nat (i - to_Z (wl om))) ltac:(lia) ltac:(lia)) in Eb.
              rewrite Z2Nat.id in Eb by lia.
              exists (byte_of (bv_unsigned (Z_to_bv 64 p)) (i - to_Z (wl om))). split; [exact Eb|]. split.
              ** unfold rg_kb. destruct (cell_of_byte (wl om) (i - to_Z (wl om)) 8 ltac:(lia) ltac:(lia)) as [Ek Em].
                 replace (to_Z (wl om) + (i - to_Z (wl om))) with i in Ek, Em by lia. rewrite Ek.
                 rewrite Ergm', (rd_cell_wr_cell ctasegs rgm _ _ (CP t w_zero) Hk3 Hk3), Z.eqb_refl.
                 cbn [cell_kb kb_ok]. rewrite Em, Eom8, Z.add_0_l. rewrite byte_of_unsigned. unfold pword. rewrite Erho2t. change (wZ w_zero) with 0. rewrite Z.add_0_r. reflexivity.
              ** intros _. apply WM. destruct (Hby2 i Hi) as (b0 & _ & _ & W0). exact (W0 Ewrm).
           ++ destruct (Hby2 i Hi) as (b & Eb & Kb & Wb).
              assert (Hk : m' (wa (rho tm + i)) = m (wa (rho tm + i))).
              { apply Hpres; rewrite wa_unsigned by lia.
                - right; right; right; left. exists (rho tm), km. split; [exact HinFm | rewrite Efkm; lia].
                - apply andb_false_iff in Ein. rewrite Z.leb_gt, Z.ltb_ge in Ein. unfold mp. lia. }
              destruct (same_byte_kept m m' _ Hk) as [E W]. exists b. split; [rewrite E; exact Eb|]. split; [|intros Hwr; apply W, Wb, Hwr].
              unfold rg_kb in Kb |- *. rewrite Ergm'.
              assert (Hki : to_Z (of_Z (i / 8)) < 2 ^ Z.of_nat (rg_d rgm)).
              { rewrite of_Z_spec, Z.mod_small by (rewrite wB_eq; unfold two63; Z.div_mod_to_equations; lia).
                set (X := 2 ^ Z.of_nat (rg_d rgm)) in *. Z.div_mod_to_equations. lia. }
              rewrite (rd_cell_wr_cell ctasegs rgm _ _ (CP t w_zero) Hk3 Hki).
              destruct (Z.eqb_spec (to_Z (wl om >> 3)%uint63) (to_Z (of_Z (i / 8)))) as [Ec|Ec]; [|exact Kb].
              exfalso. apply andb_false_iff in Ein. rewrite phi_shr3, of_Z_spec, Z.mod_small in Ec by (rewrite wB_eq; unfold two63; Z.div_mod_to_equations; lia).
              rewrite Z.leb_gt, Z.ltb_ge in Ein. Z.div_mod_to_equations. lia.
        -- (* [comment removed for export] *)
           apply (regions_after_call RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk IMGSH_OK g rho rho2 cd (s_mem S) (s_next S) m m' Σ' (rt_live RT (g_S RT g)) o rgs (s_next S) tm mp 8
                    HF HRm2 Hag02 Egs Eabs Edf Ewr Ho16 Hosz HART' MI' Hstk' Hpres Es'); try assumption; try lia.
           ++ intros b Hb _. assert (Hin : In (rho b, rsize (s_mem S) b) (rt_live RT (g_S RT g))).
              { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists b. auto. }
              split; [exact Hin | rewrite El'; right; exact Hin].
           ++ intros e He. assert (Hin : In e (rt_live RT (g_S RT g))) by (rewrite Hlive; apply in_or_app; right; exact He).
              split; [exact Hin | rewrite El'; right; exact Hin].
           ++ intros t4 rg4 G4 Hne4 i Hi Hin.
              assert (EBm0 : rbase rho2 tm rgm = rho tm) by (unfold rbase; rewrite Eabsm; exact Etm2).
              destruct (proj2 HRm2 t4 tm rg4 rgm G4 Egm Hne4 (or_intror Ewrm)) as [D|D]; rewrite EBm0 in D; unfold mp in Hin; lia.
           ++ intros E. destruct (mget_mset_cases _ T_STK t3 _ rg3 (mget_lt _ _ _ Egs) Gx) as [[-> _]|[_ G']]; [pose proof (Htags _ _ Egs) as X | pose proof (Htags _ _ G') as X]; rewrite E in X; lia.
           ++ intros E. destruct (mget_mset_cases _ T_STK t3 _ rg3 (mget_lt _ _ _ Egs) Gx) as [[-> _]|[_ G']]; [pose proof (Htags _ _ Egs) as X | pose proof (Htags _ _ G') as X]; rewrite E in X; rewrite sh_tag_Z in X by lia; lia.
    + (* [comment removed for export] *)
      apply (regions_sep_new_wr rho2 _ (sh_tag t) shrg); [| exact HfreshS | exact Hst20 |].
      * apply (regions_sep_new rho2 Mc t newrg); [| exact HfreshT | exact Ht20 |].
        -- rewrite EMc. apply (regions_sep_mset_same rho2 _ tm rgm rgm').
           ++ rewrite (mget_mset _ T_STK tm _ (mget_lt _ _ _ Egs)). destruct (Z.eqb_spec (to_Z T_STK) (to_Z tm)) as [E|E]; [apply to_Z_inj in E; congruence | exact Egm].
           ++ exact Hsdm.
           ++ exact (regions_sep_mset_same rho2 _ T_STK rgs _ Egs (same_dir_drop_below rgs (wl o)) (proj2 HRm2)).
        -- intros t2 rg2 G2. rewrite EBt. cbn [newrg rg_size]. fold nz.
           assert (El'' : rt_live RT Σ' = (p, nz) :: rt_live RT (g_S RT g)) by (rewrite El', Enz; reflexivity).
           apply (kind_apart_block RT AF lo sp0 r xp H_r XP_stk (g_S RT g) Σ' m m' _ _ _ p nz 0 (rt_live RT (g_S RT g)) (Kd t2 rg2 G2) HART HB HART' El''); try assumption; try lia.
           ++ intros b0 s0 Hin _. exact Hin.
           ++ intros Hin _. destruct (af_live_range RT AF _ _ _ _ HART Hin) as (X & _). lia.
      * intros t2 rg2 G2 [Hw|Hw]; [rewrite USw in Hw; discriminate Hw|]. rewrite EBs, USsz.
        destruct (mget_mset_cases Mc t t2 _ rg2 Ht20 G2) as [[-> ->]|[N2 G2']].
        -- rewrite EBt. cbn [newrg rg_size]. fold nz. destruct (af_live_offshadow RT AF _ _ _ _ HART' HinP) as [D|D]; [right; lia | left; lia].
        -- pose proof (Kd t2 rg2 G2') as Kd2. rewrite Hw in Kd2.
           exact (kind_apart_bshadow RT AF lo sp0 r xp H_r XP_stk (g_S RT g) Σ' m m' _ _ p nz Kd2 HART HB HART' HinP Ef' Es' ltac:(lia) Hp8).
  - intros rho2 Hag2. exact (FMem_law RT CL lo sp0 r m0 cr0 anc xp (GH RT Σ') rho' rho2 _ _ _ m' HF' Hag2).
Qed.

End HkPmalign.
