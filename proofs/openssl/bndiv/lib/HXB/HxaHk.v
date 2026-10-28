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
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaInit HxaImage HxaInv HxaHooks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Definition traces_ok (TR : list (list int)) : Prop := forall tr, In tr TR -> In (map to_Z tr) SITE_TRACES.

Lemma list_eqb_eq : forall a b : list int, list_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Uint63.eqb_spec in H1. subst y. f_equal. exact (IH b H2).
Qed.

Section Hk.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis PMc_fdfs : fdfs_only PMc.
Hypothesis PMc_mat : mat_stable PMc.
Variable T : TSet.
Variables (CL : list (Z * Z)) (lo sp0 r : Z) (m0 : word -> option byte) (cr0 anc : Z) (xp : xpar).
Hypothesis H_r : r = 0 \/ r = 16.
Hypothesis XP_ro : rg_wr (xp_rgsh xp) = false.
Hypothesis XP_stk : stk_okx (xp_stk xp).
Hypothesis IMGSH_OK : forall Σ m rho t, ART RT Σ m -> region_ok bsegs rho t (xp_rgsh xp) m.
(* [comment removed for export] *)
Variable TR : list (list int).
Hypothesis TRACES_OK : traces_ok TR.

Notation FMemA := (FMem RT CL lo sp0 r m0 cr0 anc xp).
Notation FInvA := (FInv RT CL lo sp0 r m0 cr0 anc xp).
Notation JA := (J RT PMc T).
Notation B0A := (B0 sp0 r xp).
Notation XInvA := (XInv bsegs SHBW (ghost RT) FInvA).
Notation xhook_okA := (xhook_ok bsegs SHBW (ghost RT) JA FInvA).

Definition hkA_free : @hook xcd := hk_at PC_FREE (hkx_free_null bsegs TPV T_STK RT_STACK TR T_S0 IMG_TOP).

(* [comment removed for export] *)
Lemma call_geometry (g : ghost RT) (rho : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m : word -> option byte) (o : w64) (x2 : word) :
  FMemA g rho cd M nx m -> wh o = false -> to_Z (wl o) mod 16 = 0 -> to_Z RT_STACK <= to_Z (wl o) -> to_Z (wl o) <= xp_stk xp + r ->
  x2 = pword rho T_STK o ->
  bv_unsigned x2 = B0A + to_Z (wl o) /\ call_ok RT (g_S RT g) m x2 lo /\ B0A <= B0A + to_Z (wl o) <= sp0.
Proof.
  intros (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & _) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & _) Eho Ho16 Hrt Hsz ->.
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1). pose proof (to_Z_bounded (wl o)) as Bo.
  assert (E : bv_unsigned (pword rho T_STK o) = B0A + to_Z (wl o)).
  { unfold pword. rewrite Hrs, wZ_split, Eho. cbn [Z.b2z]. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus, B0, SEGTOP_A, STACK_WIN, USTACK_TOP in *. change (2 ^ Z.of_N 64) with (2 ^ 64). lia. }
  rewrite E. split; [reflexivity|]. split; [|unfold B0; lia].
  unfold call_ok. rewrite E. change (to_Z RT_STACK) with 65536 in Hrt. unfold RT_iface.RT_STACK.
  split; [exact (proj1 (stk_split bsegs m lo (B0A + to_Z (wl o)) sp0 Hstk ltac:(unfold B0 in *; lia)))|]. split; [exact Hl1|]. split; [unfold B0 in *; lia|].
  split; [unfold B0, USTACK_TOP in *; lia|].
  pose proof (Z.div_mod sp0 32 ltac:(lia)) as D. rewrite Hl4 in D. unfold B0.
  pose proof (Z.div_mod (xp_stk xp) 32 ltac:(lia)) as D2. rewrite ESTK32 in D2.
  replace (sp0 - r - xp_stk xp + to_Z (wl o)) with (to_Z (wl o) + (2 * (sp0 / 32) - 2 * (xp_stk xp / 32)) * 16) by lia. rewrite Z.mod_add by lia. exact Ho16.
Qed.

Lemma unwind_premise (g : ghost RT) (rho : valuation) (cd : xcd) (S : sstate) (m : word -> option byte) (x1 x2 x8 : word) :
  FMemA g rho cd (s_mem S) (s_next S) m -> Rmem bsegs rho (s_mem S) m ->
  unwind_okb bsegs T_STK TR T_S0 IMG_TOP S = true ->
  den rho (rget S X1) x1 -> den rho (rget S X2) x2 -> den rho (rget S X8) x8 ->
  unwind_ch m x1 x8 x2.
Proof.
  intros HF [HRg _] Hu D1 D2 D8. unfold unwind_okb in Hu.
  destruct (rget S X1) as [ra| | |]; try discriminate. destruct (rget S X2) as [|t o| |]; try discriminate.
  destruct ((t =? T_STK)%uint63 && negb (wh o) && negb (wh ra)) eqn:Ec; [|discriminate].
  apply andb_prop in Ec as [Ec Era]. apply andb_prop in Ec as [Et Eho]. apply Uint63.eqb_spec in Et. subst t.
  apply negb_true_iff in Era, Eho.
  destruct (mget (s_mem S) T_STK) as [rgs|] eqn:Egs; [|discriminate].
  destruct (rg_abs rgs) eqn:Eabs; [discriminate|].
  destruct (rg_wr rgs && (wl o <=? rg_size rgs)%uint63) eqn:Ec2; [|discriminate]. apply andb_prop in Ec2 as [Ewr Eosz]. apply leb_spec in Eosz.
  destruct (uw_walk bsegs T_STK T_S0 IMG_TOP 64 rgs (wl o) (rget S X8)) as [ras|] eqn:Ew; [|discriminate].
  apply existsb_exists in Hu as (tr & Hin & Heq). apply list_eqb_eq in Heq. subst tr.
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hr0 & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & _).
  destruct (stk_class RT CL lo sp0 r m0 cr0 anc xp g rho cd _ _ m rgs HF Egs Eabs) as [Esz _].
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1).
  exists (map to_Z ras). split.
  - cbn [den] in D1. subst x1. rewrite wbv_unsigned, wZ_split, Era. cbn [Z.b2z]. rewrite Z.mul_0_l, Z.add_0_l.
    exact (TRACES_OK _ Hin).
  - assert (E2 : bv_unsigned x2 = rho T_STK + to_Z (wl o)).
    { cbn [den] in D2. subst x2. unfold pword. rewrite wZ_split, Eho. cbn [Z.b2z]. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
      pose proof (HRg T_STK rgs Egs) as (Bx0 & Bx1 & _). unfold rbase in Bx0, Bx1. rewrite Eabs in Bx0, Bx1. unfold two63 in Bx1.
      pose proof (to_Z_bounded (wl o)). unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). lia. }
    rewrite E2. apply (uw_walk_sound rho rgs m lo (HRg T_STK rgs Egs) Eabs Ewr) with (fuel := 64%nat) (fp := rget S X8).
    + rewrite Hrs, Esz. unfold B0, USTACK_TOP in *. lia.
    + change (to_Z IMG_TOP) with 12570624. unfold SEGTOP_A, STACK_WIN in *. lia.
    + rewrite Hrs. exact Hl2.
    + rewrite Hrs. exact (B0_mod8 sp0 r xp XP_stk Hl4).
    + exact Hr0.
    + exact Hroot.
    + exact Ew.
    + exact D8.
    + exact Eosz.
Qed.

Lemma PC_FREE_Z : wbv PC_FREE = Z_to_bv 64 e_free. Proof. reflexivity. Qed.
Lemma TPV_Z : wbv TPV = Z_to_bv 64 0xbdae50. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Rmem_clobbered (g : ghost RT) (rho rho2 : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m m' : word -> option byte) (Σ' : rts RT)
    (o : w64) (rgs : region) :
  FMemA g rho cd M nx m -> Rmem bsegs rho2 M m -> agree_below nx rho rho2 ->
  mget M T_STK = Some rgs -> rg_abs rgs = None -> rg_dflt rgs = DUnk -> rg_wr rgs = true ->
  to_Z (wl o) mod 16 = 0 -> to_Z (wl o) <= to_Z (rg_size rgs) ->
  ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo (B0A + to_Z (wl o)) ->
  rt_pres (rt_live RT (g_S RT g)) (rt_frames RT (g_S RT g)) (B0A + to_Z (wl o)) m m' ->
  rt_live RT Σ' = rt_live RT (g_S RT g) -> rt_sp0 RT Σ' = rt_sp0 RT (g_S RT g) ->
  Rmem bsegs rho2 (mset M T_STK (drop_below rgs (wl o))) m'.
Proof.
  intros HF HRm2 Hag Egs Eabs Edf Ewr Ho16 Hosz HART' MI' Hstk' Hpres El Es.
  pose proof HF as (Hlive & _ & _ & _ & Htags & _ & Hnx & _).
  split; [|exact (regions_sep_mset_same rho2 M T_STK rgs _ Egs (same_dir_drop_below rgs (wl o)) (proj2 HRm2))].
  intros t3 rg3 G3.
  assert (Hlt : to_Z t3 < to_Z nx).
  { destruct (mget_mset_cases M T_STK t3 _ rg3 (mget_lt M T_STK rgs Egs) G3) as [[-> _]|[_ G3']]; [exact (Htags _ _ Egs) | exact (Htags _ _ G3')]. }
  apply (regions_after_call RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk IMGSH_OK g rho rho2 cd M nx m m' Σ' (rt_live RT (g_S RT g)) o rgs nx nx 0 0
           HF HRm2 Hag Egs Eabs Edf Ewr Ho16 Hosz HART' MI' Hstk' (pres_ex_of_pres _ _ _ m m' Hpres) Es); try assumption; try lia.
  - intros b Hb _. assert (Hin : In (rho b, rsize M b) (rt_live RT (g_S RT g))).
    { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists b. auto. }
    split; [exact Hin | rewrite El; exact Hin].
  - intros e He. assert (Hin : In e (rt_live RT (g_S RT g))) by (rewrite Hlive; apply in_or_app; right; exact He).
    split; [exact Hin | rewrite El; exact Hin].
  - intros E. pose proof (Htags _ _ Egs) as X. rewrite <- E in X. lia.
  - intros E. subst t3. lia.
  - intros E. subst t3. rewrite sh_tag_Z in Hlt by lia. lia.
  - intros E. subst t3. lia.
Qed.

Lemma hkA_free_ok : xhook_okA hkA_free.
Proof.
  intros g rho cd S cd' S' ms [[HRn Hlaw] [HF (Hro & Hnf)]] Hh K.
  unfold hkA_free, hk_at in Hh. destruct (w_eqb (s_pc S) PC_FREE) eqn:Epc; [|discriminate]. apply w_eqb_true_iff in Epc.
  unfold hkx_free_null in Hh.
  destruct (xtp_ok TPV S && xsp_ok T_STK S && unwind_okb bsegs T_STK TR T_S0 IMG_TOP S) eqn:Eg; [|discriminate].
  apply andb_prop in Eg as [Eg Eun]. apply andb_prop in Eg as [Etp Esp].
  destruct (rget S X10) as [a0w| | |] eqn:Ea10; try discriminate. destruct (is_zero a0w) eqn:Ez; [|discriminate]. apply is_zero_spec in Ez. subst a0w.
  destruct (xclobber_stack RT_STACK S (s_mem S)) as [Mc|] eqn:Ecl; [|discriminate].
  destruct (xret S VU Mc (s_next S)) as [S1|] eqn:Ert; [|discriminate]. injection Hh as <- <-.
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
  destruct (call_geometry g rho cd _ _ m o x2 HF Eho Ho16 Hrt ltac:(lia) D2') as (Espv & Hcall & Hspc).
  pose proof (unwind_premise g rho cd S m x1 x2 x8 HF (proj2 (HRall rho (agree_below_refl _ _))) Eun D1 D2 D8) as Hunw.
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrho & HART & Hmi & Hstk & Hbnd & Hcnt & Hagr).
  (* [comment removed for export] *)
  intros c Hc. rewrite Epc, PC_FREE_Z in Hc.
  apply (rc_free_null RT RTC (g_S RT g) PMc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           F fc m lo PMc_fdfs PMc_mat D10 ltac:(rewrite D4; exact TPV_Z) HART Hmi Hcall Hunw T c Hc).
  intros c' (v & Hc'). destruct (ASTA_unpack RT (g_S RT g) PMc _ c' Hc') as (ms' & (m' & Hret & (HART' & MI' & _ & Hstk') & Hpex & _) & Hc'').
  destruct Hret as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & Ems').
  rewrite Espv in Hstk', Hpex.
  assert (Hpres : rt_pres (rt_live RT (g_S RT g)) (rt_frames RT (g_S RT g)) (B0A + to_Z (wl o)) m m').
  { intros a Ha. apply Hpex; [exact Ha | lia]. }
  apply (K g rho ms' (agree_below_refl _ _)); [|exact Hc''].
  subst ms'.
  destruct (clobber_dirs xp XP_ro (s_mem S) rgs (wl o) Egs Ewr) as [Hd Hrs].
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof (to_Z_bounded (wl o)) as Bo.
  assert (HF' : FMemA g rho (XCD (x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd)) (mset (s_mem S) T_STK (drop_below rgs (wl o))) (s_next S) m').
  { apply (FMem_after_call RT CL lo sp0 r m0 cr0 anc xp XP_ro g rho cd (s_mem S) _ (s_next S) m m' (g_S RT g) (B0A + to_Z (wl o)) HF HART' MI' Hstk'); try reflexivity; try assumption; try lia.
    - apply (kept_stack sp0 _ _ _ 0 0 m m' (pres_ex_of_pres _ _ _ m m' Hpres)); [unfold B0, SEGTOP_A, STACK_WIN in *; lia | tauto | intros; lia].
    - rewrite Hlive in Hpres. apply (kept_caller CL sp0 xp _ _ _ 0 0 m m' (pres_ex_of_pres _ _ _ m m' Hpres)); [lia | intros; lia]. }
  split; [split|split; [exact HF' | split; [reflexivity | cbn [ms_regs MS]; do 31 eexists; reflexivity]]].
  - intros rho2 Hag. cbn [s_next] in Hag. destruct (HRall rho2 Hag) as [HRg2 HRm2].
    apply (R_return rho2 S VU _ (s_abs S) (s_next S) ra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
             t0' t1' t2' v a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F F' (wbv (s_pc S)) fc fc' None m' (seg_rom bsegs) HRg2 D1' I).
    exact (Rmem_clobbered g rho rho2 cd (s_mem S) (s_next S) m m' (g_S RT g) o rgs HF HRm2 Hag Egs Eabs Edf Ewr Ho16 Hosz HART' MI' Hstk' Hpres eq_refl eq_refl).
  - intros rho2 Hag. exact (FMem_law RT CL lo sp0 r m0 cr0 anc xp g rho rho2 _ _ _ m' HF' Hag).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hkA_memset : @hook xcd := hk_at PC_ASAN_MEMSET (hkx_memset8 T_STK RT_STACK).

Lemma PC_MEMSET_Z : wbv PC_ASAN_MEMSET = Z_to_bv 64 e_asan_memset. Proof. reflexivity. Qed.

Lemma ro_same_mset_wr (M : HxMem.mem) (t : int) (rg rg' : region) : mget M t = Some rg -> rg_wr rg = true -> ro_same M (mset M t rg').
Proof.
  intros Eg Hw t2 rg2 G W. rewrite (mget_mset M t t2 _ (mget_lt M t rg Eg)).
  destruct (Z.eqb_spec (to_Z t) (to_Z t2)) as [E|E]; [|exact G]. apply to_Z_inj in E. subst t2. congruence.
Qed.

Lemma hkA_memset_ok : xhook_okA hkA_memset.
Proof.
  intros g rho cd S cd' S' ms [[HRn Hlaw] [HF (Hro & Hnf)]] Hh K.
  unfold hkA_memset, hk_at in Hh. destruct (w_eqb (s_pc S) PC_ASAN_MEMSET) eqn:Epc; [|discriminate]. apply w_eqb_true_iff in Epc.
  unfold hkx_memset8 in Hh. destruct (xsp_ok T_STK S) eqn:Esp; [|discriminate].
  destruct (rget S X10) as [|t o| |] eqn:Ea0; try discriminate. destruct (rget S X11) as [c| | |] eqn:Ea1; try discriminate.
  destruct (rget S X12) as [n| | |] eqn:Ea2; try discriminate. destruct (wh o || wh n) eqn:Eh; [discriminate|].
  apply orb_false_elim in Eh as [Eho Ehn].
  destruct (mget (s_mem S) t) as [rg|] eqn:Eg; [|discriminate]. destruct (rg_abs rg) eqn:Eabs; [discriminate|].
  destruct ((wl o land 7 =? 0)%uint63 && (wl n land 7 =? 0)%uint63 && (wl o <=? rg_size rg)%uint63 && (wl n <=? rg_size rg)%uint63
            && (wl o + wl n <=? rg_size rg)%uint63 && rg_wr rg && tag_even t && existsb (fun x => (x =? t)%uint63) (x_blocks cd)
            && negb (wh c) && (wl c <? 256)%uint63 && (wl n <? 1099511627776)%uint63) eqn:Eck; [|discriminate].
  apply andb_prop in Eck as [Eck Ec11]. apply ltb_spec in Ec11. change (to_Z 1099511627776%uint63) with (2 ^ 40) in Ec11.
  apply andb_prop in Eck as [Eck Ec10]. apply andb_prop in Eck as [Eck Ec9]. apply andb_prop in Eck as [Eck Ec8]. apply andb_prop in Eck as [Eck Ec7].
  apply andb_prop in Eck as [Eck Ewr]. apply andb_prop in Eck as [Eck Ec5]. apply andb_prop in Eck as [Eck Ec4].
  apply andb_prop in Eck as [Eck Ec3]. apply andb_prop in Eck as [Ec1 Ec2].
  apply Uint63.eqb_spec in Ec1, Ec2. apply leb_spec in Ec3, Ec4, Ec5. apply negb_true_iff in Ec9. apply ltb_spec in Ec10. change (to_Z 256%uint63) with 256 in Ec10.
  apply existsb_exists in Ec8 as (t' & Hint & Et'). apply Uint63.eqb_spec in Et'. subst t'.
  cbv zeta in Hh.
  set (rg' := RG None (rg_size rg) (rg_al rg) (rg_wr rg) (rg_dflt rg) (rg_d rg)
                 (fill_cells (rg_d rg) (rg_cells rg) (wl o >> 3)%uint63 (Z.to_nat (to_Z (wl n >> 3)%uint63)) (rep8 (wl c)))) in *.
  destruct (xclobber_stack RT_STACK S (s_mem S)) as [Mc|] eqn:Ecl; [|discriminate].
  destruct (xret S (VP t o) (mset Mc t rg') (s_next S)) as [S1|] eqn:Ert; [|discriminate]. injection Hh as <- <-.
  destruct (xclobber_inv T_STK RT_STACK S _ _ Ecl Esp) as (os & rgs & Esp2 & Ehos & Egs & Eabss & Edfs & Ho16 & Hrt & Hosz & Ewrs & ->).
  destruct (xret_inv _ _ _ _ _ Ert) as (ra & Era & Erv & ->).
  destruct (ms_nf rho S ms (Rn_R bsegs rho S ms HRn) Erv Hro Hnf)
    as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
        & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Ems & HRg).
  set (m := ms_mem ms) in *. set (F := ms_fregs ms) in *. set (fc := ms_fcsr ms) in *. clearbody m F fc. subst ms.
  cbn [ms_mem ms_regs ms_rom MS] in HF, Hro, Hnf.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & D2 & _ & _ & D10 & D11 & D12).
  rewrite Era in D1. rewrite Esp2 in D2. rewrite Ea0 in D10. rewrite Ea1 in D11. rewrite Ea2 in D12. cbn [den] in D1, D2, D10, D11, D12.
  assert (HRall : forall rho2, agree_below (s_next S) rho rho2 ->
            Rregs rho2 (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wbv (s_pc S)) fc None)
            /\ Rmem bsegs rho2 (s_mem S) m).
  { intros rho2 Hag. destruct (HRn rho2 Hag) as (_ & _ & HRg2 & _ & HRm2). exact (conj HRg2 HRm2). }
  destruct (stk_class RT CL lo sp0 r m0 cr0 anc xp g rho cd _ _ m rgs HF Egs Eabss) as [Esz _].
  destruct (call_geometry g rho cd _ _ m os x2 HF Ehos Ho16 Hrt ltac:(lia) D2) as (Espv & Hcall & Hspc).
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrho & HART & Hmi & Hstk & Hbnd & Hcnt & Hagr).
  pose proof (proj2 (HRall rho (agree_below_refl _ _))) as HRm.
  (* [comment removed for export] *)
  pose proof (to_Z_bounded (wl o)) as Bo. pose proof (to_Z_bounded (wl n)) as Bn. pose proof (to_Z_bounded (rg_size rg)) as Bs.
  destruct (proj1 HRm t rg Eg) as (Bx0 & Bx1 & Bx2 & Bx3 & Bx4 & _). unfold two63 in Bx1. unfold rbase in Bx0, Bx1. rewrite Eabs in Bx0, Bx1.
  assert (Eon : to_Z (wl o + wl n)%uint63 = to_Z (wl o) + to_Z (wl n)) by (rewrite add_spec; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
  rewrite Eon in Ec5.
  assert (Eo8 : to_Z (wl o) mod 8 = 0) by (rewrite <- phi_land7, Ec1; reflexivity).
  assert (En8 : to_Z (wl n) mod 8 = 0) by (rewrite <- phi_land7, Ec2; reflexivity).
  assert (EwZo : wZ o = to_Z (wl o)) by (unfold wZ; rewrite Eho; lia).
  assert (EwZn : wZ n = to_Z (wl n)) by (unfold wZ; rewrite Ehn; lia).
  assert (EwZc : wZ c = to_Z (wl c)) by (unfold wZ; rewrite Ec9; lia).
  set (A := rho t + to_Z (wl o)).
  set (cb := Z_to_bv 8 (to_Z (wl c)) : byte).
  assert (Ecb : bv_unsigned cb = to_Z (wl c)).
  { unfold cb. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. pose proof (to_Z_bounded (wl c)). lia. }
  (* [comment removed for export] *)
  assert (HinL : In (rho t, to_Z (rg_size rg)) (rt_live RT (g_S RT g))).
  { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists t. rewrite (rsize_get _ t rg Eg). auto. }
  destruct (af_acc_live RT AF _ _ _ _ HART HinL) as [HwrL HaccL]. destruct (af_live_range RT AF _ _ _ _ HART HinL) as (P1 & P2 & P3).
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r.
  assert (Hwf : forall x, A <= x < A + to_Z (wl n) ->
            aclient (rt_live RT (g_S RT g)) (rt_frames RT (g_S RT g)) B0A x /\ ~ caller_mem CL sp0 xp x /\ 0 <= x < 2 ^ 47).
  { intros x Hx. apply (wr_facts RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd _ _ m t rg x HF Eg Ewr). unfold rbase. rewrite Eabs. unfold A in Hx. lia. }
  intros cfg Hc. rewrite Epc, PC_MEMSET_Z in Hc.
  apply (rc_asan_memset RT RTC (g_S RT g) PMc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           F fc m A (to_Z (wl n)) cb lo PMc_fdfs PMc_mat); try assumption.
  - rewrite D10. unfold pword, A. rewrite EwZo. reflexivity.
  - rewrite D11, Ecb. unfold wbv. rewrite EwZc. reflexivity.
  - rewrite D12. unfold wbv. rewrite EwZn. reflexivity.
  - unfold A. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *. lia.
  - lia.
  - split; [intros _; split|split].
    + apply (acc_sub bsegs m (rho t) (to_Z (rg_size rg))); [exact HaccL | unfold A; lia | unfold A; lia].
    + left. exists (rho t), (to_Z (rg_size rg)). split; [exact HinL | unfold A; lia].
    + intros i Hi. rewrite Espv. right; right; left. exists (rho t), (to_Z (rg_size rg)). split; [exact HinL | unfold A; lia].
    + destruct HwrL as (W1 & W2 & W3). split; [unfold A; lia|]. split; [unfold A; lia|]. intros i Hi.
      replace (A + i) with (rho t + (to_Z (wl o) + i)) by (unfold A; lia). apply W3. lia.
  - intros c' Hc'. destruct (ASTA_unpack RT (g_S RT g) PMc _ c' Hc') as (ms' & (m' & Hret & (HART' & MI' & WM & Hstk') & Hpex & Hbytes) & Hc'').
    destruct Hret as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & Ems').
    rewrite Espv in Hstk', Hpex.
    apply (K g rho ms' (agree_below_refl _ _)); [|exact Hc'']. subst ms'.
    destruct (clobber_dirs xp XP_ro (s_mem S) rgs (wl os) Egs Ewrs) as [Hd Hrs].
    assert (Hne : t <> T_STK).
    { intros ->. destruct (Htl T_STK ltac:(apply in_or_app; left; exact Hint)) as (_ & X & _). change (to_Z NEXT0) with 32 in X. change (to_Z T_STK) with 2 in X. lia. }
    assert (EgC : mget (mset (s_mem S) T_STK (drop_below rgs (wl os))) t = Some rg).
    { rewrite (mget_mset _ T_STK t _ (mget_lt _ _ _ Egs)). destruct (Z.eqb_spec (to_Z T_STK) (to_Z t)) as [E|E]; [apply to_Z_inj in E; congruence | exact Eg]. }
    assert (Hsd : same_dir rg rg') by (repeat split; cbn [rg' rg_abs]; symmetry; exact Eabs).
    pose proof (to_Z_bounded (wl os)) as Bos.
    assert (HF' : FMemA g rho (XCD (x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd)) (mset (mset (s_mem S) T_STK (drop_below rgs (wl os))) t rg') (s_next S) m').
    { apply (FMem_after_call RT CL lo sp0 r m0 cr0 anc xp XP_ro g rho cd (s_mem S) _ (s_next S) m m' (g_S RT g) (B0A + to_Z (wl os)) HF HART' MI' Hstk'); try reflexivity; try lia.
      - apply (kept_stack sp0 _ _ _ A (to_Z (wl n)) m m' Hpex); [unfold B0, SEGTOP_A, STACK_WIN in *; lia | tauto |].
        intros a Ha Hin. unfold A in Hin. unfold B0, SEGTOP_A, STACK_WIN in *. lia.
      - rewrite Hlive in Hpex. apply (kept_caller CL sp0 xp _ _ _ A (to_Z (wl n)) m m' Hpex); [lia|].
        intros a Hca Hin. exact (proj1 (proj2 (Hwf a Hin)) Hca).
      - eapply same_dirs_trans; [exact Hd | exact (same_dirs_mset _ t rg rg' EgC Hsd)].
      - eapply ro_same_trans; [exact Hrs | exact (ro_same_mset_wr _ t rg rg' EgC Ewr)]. }
    split; [split|split; [exact HF' | split; [reflexivity | cbn [ms_regs MS]; do 31 eexists; reflexivity]]].
    + intros rho2 Hag. cbn [s_next] in Hag. destruct (HRall rho2 Hag) as [HRg2 HRm2].
      destruct (nf_regs rho2 S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg2) as (_ & _ & _ & _ & D10' & _ & _). rewrite Ea0 in D10'.
      assert (Et : rho2 t = rho t) by (apply Hag; exact (Htags t rg Eg)).
      assert (EB : rbase rho2 t rg = rho t) by (unfold rbase; rewrite Eabs; exact Et).
      apply (R_return rho2 S (VP t o) _ (s_abs S) (s_next S) ra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
               t0' t1' t2' (Z_to_bv 64 A) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F F' (wbv (s_pc S)) fc fc' None m' (seg_rom bsegs) HRg2 D1).
      { cbn [den]. unfold pword, A. rewrite Et, EwZo. reflexivity. }
      split.
      * intros t3 rg3 G3. destruct (mget_mset_cases _ t t3 rg' rg3 (mget_lt _ t rg EgC) G3) as [[-> ->]|[Hne3 G3']].
        -- (* [comment removed for export] *)
           pose proof (proj1 HRm2 t rg Eg) as Hok2.
           apply (region_ok_upd bsegs rho2 t rg rg' m m' Hok2 Hsd). intros i Hi. rewrite EB.
           destruct Hok2 as (_ & _ & _ & _ & _ & _ & _ & Hby). rewrite EB in Hby.
           assert (Erg' : rg' = RG (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) (rg_dflt rg) (rg_d rg)
                                   (fill_cells (rg_d rg) (rg_cells rg) (wl o >> 3)%uint63 (Z.to_nat (to_Z (wl n >> 3)%uint63)) (rep8 (wl c))))
             by (unfold rg'; rewrite Eabs; reflexivity).
           assert (Ek0 : 8 * to_Z (wl o >> 3)%uint63 = to_Z (wl o)) by (rewrite phi_shr3; pose proof (Z.div_mod (to_Z (wl o)) 8 ltac:(lia)); lia).
           assert (Ecnt : 8 * Z.of_nat (Z.to_nat (to_Z (wl n >> 3)%uint63)) = to_Z (wl n)).
           { rewrite Z2Nat.id by (pose proof (to_Z_bounded (wl n >> 3)%uint63); lia). rewrite phi_shr3. pose proof (Z.div_mod (to_Z (wl n)) 8 ltac:(lia)). lia. }
           rewrite Erg'. rewrite (rg_kb_fill bsegs rg (wl o >> 3)%uint63 _ (wl c) i Hi Bx3 Bx4) by lia. rewrite Ek0.
           replace (8 * (to_Z (wl o >> 3)%uint63 + Z.of_nat (Z.to_nat (to_Z (wl n >> 3)%uint63)))) with (to_Z (wl o) + to_Z (wl n)) by lia.
           destruct ((to_Z (wl o) <=? i) && (i <? to_Z (wl o) + to_Z (wl n))) eqn:Ein.
           ++ apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
              exists cb. split.
              { pose proof (bytes_at_mrd m' A _ (i - to_Z (wl o)) Hbytes ltac:(rewrite repeat_length; lia)) as X.
                replace (A + (i - to_Z (wl o))) with (rho t + i) in X by (unfold A; lia). rewrite X. apply nth_error_repeat. lia. }
              split.
              { cbn [kb_ok]. rewrite Ecb. rewrite land_spec'. change (to_Z 255%uint63) with (Z.ones 8). rewrite Z.land_ones by lia.
                change (2 ^ 8) with 256. symmetry. apply Z.mod_small. pose proof (to_Z_bounded (wl c)). lia. }
              intros _. destruct HwrL as (_ & _ & W3). apply WM. exact (W3 i ltac:(lia)).
           ++ destruct (Hby i Hi) as (b & Eb & Kb & Wb).
              assert (Hk : m' (wa (rho t + i)) = m (wa (rho t + i))).
              { apply Hpex; rewrite wa_unsigned by lia.
                - right; right; left. exists (rho t), (to_Z (rg_size rg)). split; [exact HinL | lia].
                - apply andb_false_iff in Ein. rewrite Z.leb_gt, Z.ltb_ge in Ein. unfold A. lia. }
              destruct (same_byte_kept m m' _ Hk) as [E W]. exists b. split; [rewrite E; exact Eb|]. split; [exact Kb | intros Hwr; apply W, Wb, Hwr].
        -- (* [comment removed for export] *)
           assert (Hlt3 : to_Z t3 < to_Z (s_next S)).
           { destruct (mget_mset_cases _ T_STK t3 _ rg3 (mget_lt _ T_STK rgs Egs) G3') as [[-> _]|[_ G3'']]; [exact (Htags _ _ Egs) | exact (Htags _ _ G3'')]. }
           apply (regions_after_call RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk IMGSH_OK g rho rho2 cd (s_mem S) (s_next S) m m' (g_S RT g) (rt_live RT (g_S RT g)) os rgs (s_next S) t A (to_Z (wl n))
                    HF HRm2 Hag Egs Eabss Edfs Ewrs Ho16 Hosz HART' MI' Hstk' Hpex eq_refl); try assumption; try lia.
           ++ intros b Hb _. assert (Hin : In (rho b, rsize (s_mem S) b) (rt_live RT (g_S RT g))).
              { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists b. auto. }
              split; exact Hin.
           ++ intros e He. assert (Hin : In e (rt_live RT (g_S RT g))) by (rewrite Hlive; apply in_or_app; right; exact He).
              split; exact Hin.
           ++ intros t4 rg4 G4 Hne4 i Hi Hin.
              destruct (proj2 HRm2 t4 t rg4 rg G4 Eg Hne4 (or_intror Ewr)) as [D|D]; rewrite EB in D; unfold A in Hin; lia.
           ++ intros E. subst t3. lia.
           ++ intros E. subst t3. rewrite sh_tag_Z in Hlt3 by lia. lia.
      * apply (regions_sep_mset_same rho2 _ t rg rg' EgC Hsd). exact (regions_sep_mset_same rho2 _ T_STK rgs _ Egs (same_dir_drop_below rgs (wl os)) (proj2 HRm2)).
    + intros rho2 Hag. exact (FMem_law RT CL lo sp0 r m0 cr0 anc xp g rho rho2 _ _ _ m' HF' Hag).
Qed.

End Hk.
