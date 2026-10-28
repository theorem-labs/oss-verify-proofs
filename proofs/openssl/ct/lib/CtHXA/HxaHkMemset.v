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
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxQuery.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsStep HxsStepSound HxsHookSound.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXS Require Import HxsHookCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaInit HxaImage HxaInv HxaHooks HxaHk HxaHkDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section HkMemset.
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
Hypothesis IMGSH_OK : forall Σ m rho t, ART RT Σ m -> region_ok ctasegs rho t (xp_rgsh xp) m.

Notation FMemA := (FMem RT CL lo sp0 r m0 cr0 anc xp).
Notation FInvA := (FInv RT CL lo sp0 r m0 cr0 anc xp).
Notation JA := (J RT PMc T).
Notation B0A := (B0 sp0 r xp).
Notation XInvA := (XInv ctasegs SHBW (ghost RT) FInvA).
Notation xhook_okA := (xhook_ok ctasegs SHBW (ghost RT) JA FInvA).

Lemma PC_MEMSET_Z : wbv PC_ASAN_MEMSET = Z_to_bv 64 e_asan_memset. Proof. reflexivity. Qed.

Lemma ro_same_mset_wr (M : HxMem.mem) (t : int) (rg rg' : region) : mget M t = Some rg -> rg_wr rg = true -> ro_same M (mset M t rg').
Proof.
  intros Eg Hw t2 rg2 G W. rewrite (mget_mset M t t2 _ (mget_lt M t rg Eg)).
  destruct (Z.eqb_spec (to_Z t) (to_Z t2)) as [E|E]; [|exact G]. apply to_Z_inj in E. subst t2. congruence.
Qed.

(* [comment removed for export] *)
Lemma regions_after_call_gen (g : ghost RT) (rho rho2 : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m m' : word -> option byte)
    (Σ' : rts RT) (L : list (Z * Z)) (o : w64) (rgs : region) (tx td : int) (d n : Z) :
  FMemA g rho cd M nx m -> Rmem ctasegs rho2 M m -> agree_below nx rho rho2 ->
  mget M T_STK = Some rgs -> rg_abs rgs = None -> rg_dflt rgs = DUnk -> rg_wr rgs = true ->
  to_Z (wl o) mod 16 = 0 -> to_Z (wl o) <= to_Z (rg_size rgs) ->
  ART RT Σ' m' -> mem_inv ctasegs m' -> stk ctasegs m' lo (B0A + to_Z (wl o)) ->
  rt_pres_ex L (rt_frames RT (g_S RT g)) (B0A + to_Z (wl o)) d n m m' -> rt_sp0 RT Σ' = rt_sp0 RT (g_S RT g) ->
  (forall b, In b (x_blocks cd) -> b <> tx -> In (rho b, rsize M b) L /\ In (rho b, rsize M b) (rt_live RT Σ')) ->
  (forall e, In e CL -> In e L /\ In e (rt_live RT Σ')) ->
  to_Z tx < 1000000 ->
  (forall t3 rg3, mget M t3 = Some rg3 -> t3 <> td -> forall i, 0 <= i < to_Z (rg_size rg3) -> ~ (d <= rbase rho2 t3 rg3 + i < d + n)) ->
  forall t3 rg3, mget (mset M T_STK (drop_below rgs (wl o))) t3 = Some rg3 -> t3 <> tx -> t3 <> sh_tag tx -> t3 <> td ->
    region_ok ctasegs rho2 t3 rg3 m'.
Proof.
  intros HF HRm2 Hag Egs Eabs Edf Ewr Ho16 Hosz HART' MI' Hstk' Hpres Es HL HLc Htx Hdn t3 rg3 G3 N1 N2 N3.
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & Hcnt & Hagr).
  destruct (stk_class RT CL lo sp0 r m0 cr0 anc xp g rho cd M nx m rgs HF Egs Eabs) as [Esz _].
  assert (E2 : rho2 T_STK = B0A) by (rewrite (Hag T_STK) by (change (to_Z T_STK) with 2; change (to_Z NEXT0) with 32 in Hnx0; lia); exact Hrs).
  destruct (mget_mset_cases M T_STK t3 _ rg3 (mget_lt M T_STK rgs Egs) G3) as [[-> ->]|[Hne G3']].
  - apply (stack_after_call lo sp0 r xp XP_stk rho2 rgs (wl o) m m' (proj1 HRm2 T_STK rgs Egs) Eabs Edf Esz E2); try assumption.
    + replace (to_Z (wl o)) with (0 + (2 * (to_Z (wl o) / 16)) * 8) by (pose proof (Z.div_mod (to_Z (wl o)) 16 ltac:(lia)); lia). rewrite Z.mod_add by lia. reflexivity.
    + pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof (to_Z_bounded (wl o)) as Bo.
      apply (kept_stack sp0 L (rt_frames RT (g_S RT g)) (B0A + to_Z (wl o)) d n m m' Hpres); [unfold B0, SEGTOP_A, STACK_WIN in *; lia | exact Hl3 |].
      intros a Ha. pose proof (Hdn T_STK rgs Egs N3 (a - B0A)) as X. unfold rbase in X. rewrite Eabs, E2, Esz in X.
      replace (B0A + (a - B0A)) with a in X by lia. apply X. unfold B0 in *. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1). lia.
  - apply (region_after_rt RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk IMGSH_OK g rho rho2 cd M nx m m' Σ' L (B0A + to_Z (wl o)) tx d n HF HRm2 Hag HART' MI' Hpres Es HL HLc t3 rg3 G3' Hne N1 N2 Htx).
    exact (Hdn t3 rg3 G3' N3).
Qed.

(* [comment removed for export] *)
Lemma FMem_after_call2 (g : ghost RT) (rho : valuation) (cd : xcd) (M M' : HxMem.mem) (nx : int) (m m' : word -> option byte)
    (Σ' : rts RT) :
  FMemA g rho cd M nx m ->
  ART RT Σ' m' -> mem_inv ctasegs m' -> stk ctasegs m' lo sp0 ->
  (forall a : word, caller_mem CL sp0 xp (bv_unsigned a) -> m' a = m a) ->
  rt_live RT Σ' = rt_live RT (g_S RT g) -> rt_frames RT Σ' = rt_frames RT (g_S RT g) -> rt_sp0 RT Σ' = rt_sp0 RT (g_S RT g) ->
  rt_credit RT (g_S RT g) - 1 <= rt_credit RT Σ' ->
  same_dirs M M' -> ro_same M M' ->
  FMemA (GH RT Σ') rho (XCD (x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd)) M' nx m'.
Proof.
  intros (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrho & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & (Hc1 & Hc2 & Hc3 & Hc4) & Hagr & Hsp0a)
         HART' MI' Hstk' Hk2 El Ef Es Ecr Hd Hro.
  unfold FMem. cbv zeta. cbn [g_S x_blocks x_frames x_calls x_nb].
  split; [rewrite El, (blk_list_same_dirs rho M M' _ Hd); exact Hlive|]. split; [rewrite Ef, (frm_list_same_dirs rho M M' _ Hd); exact Hfr|]. split; [exact Hnd|]. split; [exact Htl|].
  split; [exact (same_dirs_tags M M' nx Hd Htags)|]. split; [exact Hnx0|]. split; [exact Hnx|].
  split; [exact (same_dirs_class r xp XP_ro M M' _ _ Hd Hro Hcls)|]. split; [exact (same_dirs_link M M' _ _ Hd Hlink)|]. split; [exact Hrho|].
  split; [exact HART'|]. split; [exact MI'|]. split; [exact Hstk'|].
  split; [rewrite Es; auto|]. split; [split; [assumption | repeat split; lia]|].      (* [comment removed for export] *) split; [|rewrite Es; exact Hsp0a].
  intros a Hc. rewrite <- (Hagr a Hc). exact (Hk2 a Hc).
Qed.

(* [comment removed for export] *)
Lemma zero_kbs_bytes (rho : valuation) : forall (k : nat) (bs : list byte), Forall2 (kb_ok rho) (repeat (KB 0) k) bs -> bs = repeat z8 k.
Proof.
  induction k as [|k IH]; intros bs H; cbn [repeat] in *.
  - inversion H. reflexivity.
  - inversion H as [|kk b ks bs' Hb Hbs]. subst. cbn [kb_ok] in Hb. f_equal; [|exact (IH _ Hbs)].
    apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma hkA_memset_ok : xhook_okA hkA_memset.
Proof.
  intros g rho cd S cd' S' ms [[HRn Hlaw] [HF (Hro & Hnf)]] Hh K.
  unfold hkA_memset, hk_at in Hh. destruct (w_eqb (s_pc S) PC_ASAN_MEMSET) eqn:Epc; [|discriminate]. apply w_eqb_true_iff in Epc.
  unfold hkx_memset8 in Hh.
  destruct (xtp_ok TPV S && xsp_ok T_STK S && (x_calls cd <? CALLS_MAX)) eqn:Eg; [|discriminate].
  apply andb_prop in Eg as [Eg Ecalls]. apply andb_prop in Eg as [Etp Esp]. apply Z.ltb_lt in Ecalls. unfold CALLS_MAX in Ecalls.
  destruct (rget S X10) as [|t o| |] eqn:Ea10; try discriminate. destruct (rget S X11) as [c| | |] eqn:Ea11; try discriminate.
  destruct (rget S X12) as [n| | |] eqn:Ea12; try discriminate. destruct (rget S X2) as [|ts osp| |] eqn:Ea2; try discriminate.
  destruct (wh o || wh n) eqn:Eh; [discriminate|]. apply orb_false_elim in Eh as [Eho Ehn].
  destruct (xclobber_stack RT_STACK S (s_mem S)) as [Mc|] eqn:Ecl; [|discriminate].
  destruct (mget Mc t) as [rg|] eqn:Egm; [|discriminate]. destruct (rg_abs rg) eqn:Eabs; [discriminate|].
  match type of Hh with (if ?cnd then _ else _) = _ => destruct cnd eqn:Eck; [|discriminate] end.
  apply andb_prop in Eck as [Eck Ec11]. apply ltb_spec in Ec11. change (to_Z 1099511627776%uint63) with (2 ^ 40) in Ec11.
  apply andb_prop in Eck as [Eck Ec10]. apply andb_prop in Eck as [Eck Ec9]. apply andb_prop in Eck as [Eck Ecase]. apply andb_prop in Eck as [Eck Eeven].
  apply andb_prop in Eck as [Eck Ewr]. apply andb_prop in Eck as [Eck Ec6]. apply andb_prop in Eck as [Eck Ec5]. apply andb_prop in Eck as [Eck Ec4].
  apply andb_prop in Eck as [Eck Ec3]. apply andb_prop in Eck as [Ec1 Ec2].
  apply Uint63.eqb_spec in Ec1. apply Uint63.eqb_spec in Ec2. apply ltb_spec in Ec3. change (to_Z 0%uint63) with 0 in Ec3. apply leb_spec in Ec4. apply leb_spec in Ec5. apply leb_spec in Ec6.
  apply negb_true_iff in Ec9. apply ltb_spec in Ec10. change (to_Z 256%uint63) with 256 in Ec10.
  cbv zeta in Hh.
  set (rg' := RG None (rg_size rg) (rg_al rg) (rg_wr rg) (rg_dflt rg) (rg_d rg)
                 (fill_cells (rg_d rg) (rg_cells rg) (wl o >> 3)%uint63 (Z.to_nat (to_Z (wl n >> 3)%uint63)) (rep8 (wl c)))) in *.
  destruct (xret S (VP t o) (mset Mc t rg') (s_next S)) as [S1|] eqn:Ert; [|discriminate]. injection Hh as <- <-.
  destruct (xclobber_inv T_STK RT_STACK S _ _ Ecl Esp) as (os & rgs & Esp2 & Ehos & Egs & Eabss & Edfs & Ho16 & Hrt & Hosz & Ewrs & EMc).
  rewrite Ea2 in Esp2. injection Esp2 as -> ->.
  destruct (xret_inv _ _ _ _ _ Ert) as (ra & Era & Erv & ->).
  destruct (ms_nf rho S ms (Rn_R ctasegs rho S ms HRn) Erv Hro Hnf)
    as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
        & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Ems & HRg).
  set (m := ms_mem ms) in *. set (F := ms_fregs ms) in *. set (fc := ms_fcsr ms) in *. clearbody m F fc. subst ms.
  cbn [ms_mem ms_regs ms_rom MS] in HF, Hro, Hnf.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & D2 & D4 & D8 & D10 & D11 & D12).
  pose proof D1 as D1'. pose proof D2 as D2'. rewrite Era in D1'. rewrite Ea2 in D2'. rewrite Ea10 in D10. rewrite Ea11 in D11. rewrite Ea12 in D12. cbn [den] in D1', D2', D10, D11, D12.
  unfold xtp_ok in Etp. destruct (rget S X4) as [tpw| | |]; try discriminate. apply w_eqb_true_iff in Etp. subst tpw. cbn [den] in D4.
  assert (HRall : forall rho2, agree_below (s_next S) rho rho2 ->
            Rregs rho2 (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wbv (s_pc S)) fc None)
            /\ Rmem ctasegs rho2 (s_mem S) m).
  { intros rho2 Hag. destruct (HRn rho2 Hag) as (_ & _ & HRg2 & _ & HRm2). exact (conj HRg2 HRm2). }
  destruct (stk_class RT CL lo sp0 r m0 cr0 anc xp g rho cd _ _ m rgs HF Egs Eabss) as [Esz _].
  destruct (call_geometry RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd _ _ m os x2 HF Ehos Ho16 Hrt ltac:(lia) D2') as (Espv & Hcall & Hspc).
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hr0 & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & (Hc1 & Hc2 & Hc3 & Hc4) & Hagr).
  change (to_Z NEXT0) with 32 in *.
  pose proof (proj2 (HRall rho (agree_below_refl _ _))) as HRm.
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1).
  pose proof (to_Z_bounded (wl o)) as Bo. pose proof (to_Z_bounded (wl n)) as Bn. pose proof (to_Z_bounded (rg_size rg)) as Bs. pose proof (to_Z_bounded (wl os)) as Bos.
  assert (Hos8 : to_Z (wl os) mod 8 = 0).
  { replace (to_Z (wl os)) with (0 + (2 * (to_Z (wl os) / 16)) * 8) by (pose proof (Z.div_mod (to_Z (wl os)) 16 ltac:(lia)); lia). rewrite Z.mod_add by lia. reflexivity. }
  (* [comment removed for export] *)
  assert (HRmc : forall rho2, Rmem ctasegs rho2 (s_mem S) m -> Rmem ctasegs rho2 Mc m).
  { intros rho2 H2. rewrite EMc. exact (Rmem_clobber ctasegs rho2 (s_mem S) T_STK rgs (wl os) m H2 Egs Edfs Hos8). }
  pose proof (proj1 (HRmc rho HRm) t rg Egm) as Hokt. pose proof Hokt as (Bx0 & Bx1 & Bx2 & Bx3 & Bx4 & Bx5 & Bx6 & Hby).
  unfold two63 in Bx1. unfold rbase in Bx0, Bx1, Bx6, Hby. rewrite Eabs in Bx0, Bx1, Bx6, Hby.
  (* [comment removed for export] *)
  assert (Eon : to_Z (wl o + wl n)%uint63 = to_Z (wl o) + to_Z (wl n)) by (rewrite add_spec; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
  rewrite Eon in Ec6.
  assert (Eo8 : to_Z (wl o) mod 8 = 0) by (rewrite <- phi_land7, Ec1; reflexivity).
  assert (En8 : to_Z (wl n) mod 8 = 0) by (rewrite <- phi_land7, Ec2; reflexivity).
  assert (EwZo : wZ o = to_Z (wl o)) by (unfold wZ; rewrite Eho; lia).
  assert (EwZn : wZ n = to_Z (wl n)) by (unfold wZ; rewrite Ehn; lia).
  assert (EwZc : wZ c = to_Z (wl c)) by (unfold wZ; rewrite Ec9; lia).
  set (A := rho t + to_Z (wl o)).
  set (nz := to_Z (wl n)) in *.
  set (cb := Z_to_bv 8 (to_Z (wl c)) : byte).
  assert (Ecb : bv_unsigned cb = to_Z (wl c)).
  { unfold cb. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. pose proof (to_Z_bounded (wl c)). lia. }
  (* [comment removed for export] *)
  assert (HM : exists rgM, mget (s_mem S) t = Some rgM /\ same_dir rgM rg /\ (t = T_STK -> rgM = rgs) /\ (t <> T_STK -> rgM = rg)).
  { rewrite EMc in Egm. destruct (mget_mset_cases _ T_STK t _ rg (mget_lt _ _ _ Egs) Egm) as [[-> ->]|[Hne G]].
    - exists rgs. split; [exact Egs|]. split; [apply same_dir_drop_below|]. split; [reflexivity | intros X; exfalso; exact (X eq_refl)].
    - exists rg. split; [exact G|]. split; [apply same_dir_refl|]. split; [intros X; exfalso; exact (Hne X) | reflexivity]. }
  destruct HM as (rgM & EgM & HsdM & HMs & HMo). pose proof HsdM as (EaM & EsM & ElM & EwM & EdM & EddM).
  pose proof (Htags t rgM EgM) as Hlt.
  (* [comment removed for export] *)
  assert (Hwf : forall x, rho t <= x < rho t + to_Z (rg_size rg) ->
            aclient (rt_live RT (g_S RT g)) (rt_frames RT (g_S RT g)) B0A x /\ ~ caller_mem CL sp0 xp x /\ 0 <= x < 2 ^ 47).
  { intros x Hx. apply (wr_facts RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd _ _ m t rgM x HF EgM ltac:(rewrite <- EwM; exact Ewr)). unfold rbase. rewrite <- EaM, Eabs, <- EsM. exact Hx. }
  (* [comment removed for export] *)
  assert (Hcase : (In t (x_blocks cd) /\ t <> T_STK) \/ (t = T_STK /\ to_Z (wl os) <= to_Z (wl o))
                  \/ (In t (x_frames cd) /\ t <> T_STK /\ exists rss, mget Mc (sh_tag t) = Some rss /\ fshadow_zero ctasegs rss (wl o) (wl n) = true)).
  { apply orb_prop in Ecase as [Ecase|Ecase]; [apply orb_prop in Ecase as [Ecase|Ecase]|].
    - left. apply existsb_exists in Ecase as (t' & Hin & Et'). apply Uint63.eqb_spec in Et'. subst t'. split; [exact Hin|].
      intros ->. destruct (Htl T_STK ltac:(apply in_or_app; left; exact Hin)) as (_ & X & _). change (to_Z T_STK) with 2 in X. lia.
    - right; left. apply andb_prop in Ecase as [E1 E2]. apply Uint63.eqb_spec in E1. apply leb_spec in E2. auto.
    - right; right. apply andb_prop in Ecase as [E1 E2]. apply existsb_exists in E1 as (t' & Hin & Et'). apply Uint63.eqb_spec in Et'. subst t'. split; [exact Hin|].
      split. { intros ->. destruct (Htl T_STK ltac:(apply in_or_app; right; exact Hin)) as (_ & X & _). change (to_Z T_STK) with 2 in X. lia. }
      destruct (mget Mc (sh_tag t)) as [rss|]; [|discriminate]. exists rss. auto. }
  (* [comment removed for export] *)
  assert (HCLS : (acc ctasegs m A nz /\ rng_class RT (g_S RT g) A nz)
                 /\ (forall x, rho t <= x < rho t + to_Z (rg_size rg) -> (t = T_STK -> B0A + to_Z (wl os) <= x) ->
                       aclient (rt_live RT (g_S RT g)) (rt_frames RT (g_S RT g)) (B0A + to_Z (wl os)) x)
                 /\ (t = T_STK -> B0A + to_Z (wl os) <= A)).
  { destruct Hcase as [[Hin Hne]|[[Et Hoso]|(Hin & Hne & rss & Egss & Hfz)]].
    - (* [comment removed for export] *)
      assert (HinL : In (rho t, to_Z (rg_size rg)) (rt_live RT (g_S RT g))).
      { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists t. rewrite (rsize_get _ t rgM EgM), <- EsM. auto. }
      destruct (af_acc_live RT AF _ _ _ _ HART HinL) as [HwrL HaccL].
      split; [split|split; [|intros X; exfalso; exact (Hne X)]].
      + apply (acc_sub ctasegs m (rho t) (to_Z (rg_size rg))); [exact HaccL | unfold A; lia | unfold A; lia].
      + left. exists (rho t), (to_Z (rg_size rg)). split; [exact HinL | unfold A; lia].
      + intros x Hx _. right; right; left. exists (rho t), (to_Z (rg_size rg)). split; [exact HinL | lia].
    - (* [comment removed for export] *)
      pose proof EsM as EsS. rewrite (HMs Et) in EsS.
      assert (EszR : to_Z (rg_size rg) = xp_stk xp + r) by (rewrite EsS; exact Esz).
      assert (Ert0 : rho t = B0A) by (rewrite Et; exact Hrs).
      pose proof Hcall as HC. unfold call_ok in HC. rewrite Espv in HC. destruct HC as (_ & Q1 & Q2 & Q3 & _). unfold RT_iface.RT_STACK in Q2.
      split; [split|split].
      + apply (af_acc_stack RT AF _ _ A nz HART); unfold A; rewrite Ert0; unfold B0, STACK_WIN, USTACK_TOP in *; lia.
      + right; right; left. unfold A. rewrite Ert0. unfold B0, STACK_WIN, USTACK_TOP in *. lia.
      + intros x Hx Hsp. left. specialize (Hsp Et). rewrite Ert0, EszR in Hx. unfold B0, USTACK_TOP in *. lia.
      + intros _. unfold A. rewrite Ert0. unfold B0 in *. lia.
    - (* [comment removed for export] *)
      destruct (Htl t ltac:(apply in_or_app; right; exact Hin)) as (_ & T1 & T2).
      destruct (proj2 Hlink t Hin) as (rgf & Egf & _ & _ & Hfsz). rewrite EgM in Egf. injection Egf as <-. rewrite <- EsM in Hfsz.
      set (k := fcls (to_Z (rg_size rg))).
      assert (Efk : fs_size k = to_Z (rg_size rg) + 8) by (unfold k; apply fcls_size; exact Hfsz).
      assert (HinF : In (rho t, k) (rt_frames RT (g_S RT g))).
      { rewrite Hfr. unfold frm_list. apply in_map_iff. exists t. rewrite (rsize_get _ t rgM EgM), <- EsM. auto. }
      destruct (Hrsh t ltac:(apply in_or_app; right; exact Hin)) as [Hsht Hal8].
      (* [comment removed for export] *)
      unfold fshadow_zero in Hfz. apply andb_prop in Hfz as [Hfz Hkb]. apply andb_prop in Hfz as [Hssabs Hssz].
      destruct (rg_abs rss) as [|] eqn:Eass; [discriminate|]. apply leb_spec in Hssz.
      set (ko := to_Z (wl o) / 8). set (kn := nz / 8).
      assert (Eko : 8 * ko = to_Z (wl o)) by (pose proof (Z.div_mod (to_Z (wl o)) 8 ltac:(lia)); unfold ko; lia).
      assert (Ekn : 8 * kn = nz) by (pose proof (Z.div_mod nz 8 ltac:(lia)); unfold kn; lia).
      assert (Eo3 : to_Z (wl o >> 3)%uint63 = ko) by apply phi_shr3.
      assert (En3 : to_Z (wl n >> 3)%uint63 = kn) by apply phi_shr3.
      assert (Esum : to_Z ((wl o >> 3) + (wl n >> 3))%uint63 = ko + kn).
      { rewrite add_spec, Eo3, En3. apply Z.mod_small. rewrite wB_eq. unfold two63. lia. }
      rewrite Esum in Hssz. pose proof (to_Z_bounded (rg_size rss)) as Bss.
      assert (Hst : sh_tag t <> T_STK).
      { intros E. pose proof (f_equal to_Z E) as E'. rewrite sh_tag_Z in E' by lia. change (to_Z T_STK) with 2 in E'. lia. }
      assert (Egss0 : mget (s_mem S) (sh_tag t) = Some rss).
      { rewrite EMc in Egss. destruct (mget_mset_cases _ T_STK (sh_tag t) _ rss (mget_lt _ _ _ Egs) Egss) as [[E _]|[_ G]]; [exfalso; exact (Hst E) | exact G]. }
      pose proof (proj1 HRm (sh_tag t) rss Egss0) as Hokss.
      rewrite Eo3, En3 in Hkb.
      destruct (kb_check_sound ctasegs rho (sh_tag t) rss m (repeat (KB 0) (Z.to_nat kn)) ko Hokss Hkb ltac:(lia) ltac:(rewrite repeat_length, Z2Nat.id by lia; lia))
        as (bs & HF2 & Hbs & _).
      pose proof (zero_kbs_bytes rho _ bs HF2) as Ebs. rewrite Ebs in Hbs. unfold rbase in Hbs. rewrite Eass, Hsht in Hbs.
      replace ko with (to_Z (wl o) / 8) in Hbs by reflexivity.
      rewrite <- (shad_aligned_add (rho t) (to_Z (wl o)) Hal8 ltac:(lia)) in Hbs.
      pose proof (acc_zero_run ctasegs m A _ ltac:(unfold A; rewrite Z.add_mod, Hal8, Eo8 by lia; reflexivity) ltac:(unfold A; lia) Hbs) as Hacc.
      rewrite Z2Nat.id in Hacc by lia. rewrite Ekn in Hacc.
      split; [split|split; [|intros X; exfalso; exact (Hne X)]].
      + exact Hacc.
      + right; left. exists (rho t), k. split; [exact HinF | unfold A; lia].
      + intros x Hx _. right; right; right; left. exists (rho t), k. split; [exact HinF | lia]. }
  destruct HCLS as ((HaccA & Hrng) & HACL & HspA).
  assert (HwrA : wr_at ctasegs m A nz).
  { split; [unfold A; lia|]. split; [unfold A; lia|]. intros i Hi. replace (A + i) with (rho t + (to_Z (wl o) + i)) by (unfold A; lia).
    destruct (Hby (to_Z (wl o) + i) ltac:(lia)) as (b & _ & _ & W). exact (W Ewr). }
  destruct (Hwf A ltac:(unfold A; lia)) as (_ & _ & BA).
  (* [comment removed for export] *)
  intros cfg Hc. rewrite Epc, PC_MEMSET_Z in Hc.
  apply (rc_asan_memset RT RTC (g_S RT g) PMc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           F fc m A nz cb lo PMc_fdfs PMc_mat); try assumption.
  - rewrite D10. unfold pword, A. rewrite EwZo. reflexivity.
  - rewrite D11, Ecb. unfold wbv. rewrite EwZc. reflexivity.
  - rewrite D12. unfold wbv. rewrite EwZn. reflexivity.
  - clear -BA. lia.
  - clear -Bn Ec3 Ec11. lia.
  - split; [intros _; exact (conj HaccA Hrng)|]. split; [|exact HwrA].
    intros i Hi. rewrite Espv. apply HACL; [unfold A; lia|]. intros E. unfold A. pose proof (HspA E). lia.
  - intros c' Hc'. destruct (ASTA_unpack RT (g_S RT g) PMc _ c' Hc') as (ms' & (m' & Hret & (HART' & MI' & WM & Hstk') & Hpex & Hbytes) & Hc'').
    destruct Hret as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & Ems').
    rewrite Espv in Hstk', Hpex.
    apply (K g rho ms' (agree_below_refl _ _)); [|exact Hc'']. subst ms'.
    destruct (clobber_dirs xp XP_ro (s_mem S) rgs (wl os) Egs Ewrs) as [Hd Hrs_].
    rewrite <- EMc in Hd, Hrs_.
    assert (Hsd : same_dir rg rg') by (repeat split; cbn [rg' rg_abs]; symmetry; exact Eabs).
    assert (Erg' : rg' = RG (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) (rg_dflt rg) (rg_d rg)
                            (fill_cells (rg_d rg) (rg_cells rg) (wl o >> 3)%uint63 (Z.to_nat (to_Z (wl n >> 3)%uint63)) (rep8 (wl c))))
      by (unfold rg'; rewrite Eabs; reflexivity).
    assert (Ek0 : 8 * to_Z (wl o >> 3)%uint63 = to_Z (wl o)) by (rewrite phi_shr3; pose proof (Z.div_mod (to_Z (wl o)) 8 ltac:(lia)); lia).
    assert (Ecnt : 8 * Z.of_nat (Z.to_nat (to_Z (wl n >> 3)%uint63)) = nz).
    { rewrite Z2Nat.id by (pose proof (to_Z_bounded (wl n >> 3)%uint63); lia). rewrite phi_shr3. pose proof (Z.div_mod nz 8 ltac:(lia)). lia. }
    (* [comment removed for export] *)
    assert (KEPT : forall x, rho t <= x < rho t + to_Z (rg_size rg) -> (t = T_STK -> B0A + to_Z (wl os) <= x) -> ~ (A <= x < A + nz) -> m' (wa x) = m (wa x)).
    { intros x Hx Hsp Hnin. destruct (Hwf x Hx) as (_ & _ & Bx). apply Hpex; rewrite wa_unsigned by lia; [exact (HACL x Hx Hsp) | exact Hnin]. }
    (* [comment removed for export] *)
    assert (Hstk0' : stk ctasegs m' lo sp0).
    { apply (stk_merge ctasegs m' lo (B0A + to_Z (wl os)) sp0 Hstk'); [|unfold B0 in *; lia].
      destruct (stk_split ctasegs m lo (B0A + to_Z (wl os)) sp0 Hstk ltac:(unfold B0 in *; lia)) as [_ (U1 & U2 & U3)].
      split; [exact U1|]. split; [exact U2|]. intros a Ha.
      destruct (Z_le_gt_dec A a) as [L1|L1]; [destruct (Z_lt_ge_dec a (A + nz)) as [L2|L2]|].
      - replace a with (A + (a - A)) by lia. split.
        + apply WM. exact (proj2 (proj2 HwrA) (a - A) ltac:(lia)).
        + exists cb. rewrite (bytes_at_mrd m' A _ (a - A) Hbytes ltac:(rewrite repeat_length; lia)). apply nth_error_repeat. lia.
      - assert (Hk : m' (wa a) = m (wa a)).
        { apply Hpex; rewrite wa_unsigned by (unfold B0, USTACK_TOP in *; lia); [left; unfold B0, USTACK_TOP in *; lia | lia]. }
        destruct (U3 a Ha) as [Hw Hb]. destruct (same_byte_kept m m' _ Hk) as [E W]. split; [exact (W Hw) | rewrite E; exact Hb].
      - assert (Hk : m' (wa a) = m (wa a)).
        { apply Hpex; rewrite wa_unsigned by (unfold B0, USTACK_TOP in *; lia); [left; unfold B0, USTACK_TOP in *; lia | lia]. }
        destruct (U3 a Ha) as [Hw Hb]. destruct (same_byte_kept m m' _ Hk) as [E W]. split; [exact (W Hw) | rewrite E; exact Hb]. }
    assert (EgC : mget Mc t = Some rg) by exact Egm.
    assert (HF' : FMemA g rho (XCD (x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd)) (mset Mc t rg') (s_next S) m').
    { apply (FMem_after_call2 g rho cd (s_mem S) _ (s_next S) m m' (g_S RT g) HF HART' MI' Hstk0'); try reflexivity; try lia.
      - rewrite Hlive in Hpex. apply (kept_caller CL sp0 xp _ _ _ A nz m m' Hpex); [lia|].
        intros a Hca Hin. exact (proj1 (proj2 (Hwf a ltac:(unfold A in Hin; lia))) Hca).
      - eapply same_dirs_trans; [exact Hd | exact (same_dirs_mset _ t rg rg' EgC Hsd)].
      - eapply ro_same_trans; [exact Hrs_ | exact (ro_same_mset_wr _ t rg rg' EgC Ewr)]. }
    split; [split|split; [exact HF' | split; [reflexivity | cbn [ms_regs MS]; do 31 eexists; reflexivity]]].
    + intros rho2 Hag. cbn [s_next] in Hag. destruct (HRall rho2 Hag) as [HRg2 HRm2].
      assert (Et : rho2 t = rho t) by (apply Hag; exact Hlt).
      assert (EB : rbase rho2 t rg = rho t) by (unfold rbase; rewrite Eabs; exact Et).
      apply (R_return rho2 S (VP t o) _ (s_abs S) (s_next S) ra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
               t0' t1' t2' (Z_to_bv 64 A) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F F' (wbv (s_pc S)) fc fc' None m' (seg_rom ctasegs) HRg2 D1').
      { cbn [den]. unfold pword, A. rewrite Et, EwZo. reflexivity. }
      pose proof (HRmc rho2 HRm2) as HRmc2.
      apply (Rmem_after rho2 Mc t rg rg' m m' HRmc2 EgC Hsd).
      * (* [comment removed for export] *)
        pose proof (proj1 HRmc2 t rg EgC) as Hok2.
        apply (region_ok_upd ctasegs rho2 t rg rg' m m' Hok2 Hsd). intros i Hi. rewrite EB.
        destruct Hok2 as (_ & _ & _ & _ & _ & _ & _ & Hby2). rewrite EB in Hby2.
        rewrite Erg'. rewrite (rg_kb_fill ctasegs rg (wl o >> 3)%uint63 _ (wl c) i Hi Bx3 Bx4) by lia. rewrite Ek0.
        replace (8 * (to_Z (wl o >> 3)%uint63 + Z.of_nat (Z.to_nat (to_Z (wl n >> 3)%uint63)))) with (to_Z (wl o) + nz) by lia.
        destruct ((to_Z (wl o) <=? i) && (i <? to_Z (wl o) + nz)) eqn:Ein.
        -- apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
           exists cb. split.
           { pose proof (bytes_at_mrd m' A _ (i - to_Z (wl o)) Hbytes ltac:(rewrite repeat_length; lia)) as X.
             replace (A + (i - to_Z (wl o))) with (rho t + i) in X by (unfold A; lia). rewrite X. apply nth_error_repeat. lia. }
           split.
           { cbn [kb_ok]. rewrite Ecb. rewrite land_spec'. change (to_Z 255%uint63) with (Z.ones 8). rewrite Z.land_ones by lia.
             change (2 ^ 8) with 256. symmetry. apply Z.mod_small. pose proof (to_Z_bounded (wl c)). lia. }
           intros _. apply WM. replace (rho t + i) with (A + (i - to_Z (wl o))) by (unfold A; lia). exact (proj2 (proj2 HwrA) (i - to_Z (wl o)) ltac:(lia)).
        -- apply andb_false_iff in Ein. rewrite Z.leb_gt, Z.ltb_ge in Ein.
           destruct (Uint63.eq_dec t T_STK) as [Et2|Nt2]; [destruct (Z_lt_le_dec i (to_Z (wl os))) as [Li|Li]|].
           ++ (* [comment removed for export] *)
              assert (Ergd : drop_below rgs (wl os) = rg).
              { pose proof Egm as G. rewrite EMc, Et2 in G. rewrite (mget_mset _ T_STK T_STK _ (mget_lt _ _ _ Egs)), Z.eqb_refl in G. injection G as G. exact G. }
              pose proof EsM as EsS. rewrite (HMs Et2) in EsS.
              pose proof (proj1 HRm T_STK rgs Egs) as (_ & _ & Q2 & Q3 & _).
              assert (Hany : rg_kb ctasegs rg i = KU).
              { rewrite <- Ergd. rewrite (rg_kb_drop_below ctasegs rgs (wl os) i ltac:(rewrite <- EsS; exact Hi) Q3 Q2 Edfs Hos8).
                destruct (Z.ltb_spec i (to_Z (wl os))); [reflexivity | lia]. }
              rewrite Hany.
              assert (Ert0 : rho t = B0A) by (rewrite Et2; exact Hrs).
              destruct Hstk' as (_ & _ & Hs). destruct (Hs (rho t + i) ltac:(rewrite Ert0; unfold B0 in *; lia)) as [Hw [b Hb]].
              exists b. split; [exact Hb|]. split; [exact I | intros _; exact Hw].
           ++ destruct (Hby2 i Hi) as (b & Eb & Kb & Wb).
              assert (Ert0 : rho t = B0A) by (rewrite Et2; exact Hrs).
              assert (Hk : m' (wa (rho t + i)) = m (wa (rho t + i))) by (apply KEPT; [lia | intros _; rewrite Ert0; lia | unfold A; lia]).
              destruct (same_byte_kept m m' _ Hk) as [E W]. exists b. split; [rewrite E; exact Eb|]. split; [exact Kb | intros Hwr; apply W, Wb, Hwr].
           ++ destruct (Hby2 i Hi) as (b & Eb & Kb & Wb).
              assert (Hk : m' (wa (rho t + i)) = m (wa (rho t + i))) by (apply KEPT; [lia | intros E; exfalso; exact (Nt2 E) | unfold A; lia]).
              destruct (same_byte_kept m m' _ Hk) as [E W]. exists b. split; [rewrite E; exact Eb|]. split; [exact Kb | intros Hwr; apply W, Wb, Hwr].
      * (* [comment removed for export] *)
        intros t3 rg3 G3 Hne3.
        assert (Hlt3 : to_Z t3 < to_Z (s_next S)).
        { rewrite EMc in G3. destruct (mget_mset_cases _ T_STK t3 _ rg3 (mget_lt _ T_STK rgs Egs) G3) as [[-> _]|[_ G3'']]; [exact (Htags _ _ Egs) | exact (Htags _ _ G3'')]. }
        rewrite EMc in G3.
        apply (regions_after_call_gen g rho rho2 cd (s_mem S) (s_next S) m m' (g_S RT g) (rt_live RT (g_S RT g)) os rgs (s_next S) t A nz
                 HF HRm2 Hag Egs Eabss Edfs Ewrs Ho16 Hosz HART' MI' Hstk' Hpex eq_refl); try assumption; try lia.
        -- intros b Hb _. assert (Hin : In (rho b, rsize (s_mem S) b) (rt_live RT (g_S RT g))).
           { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists b. auto. }
           split; exact Hin.
        -- intros e He. assert (Hin : In e (rt_live RT (g_S RT g))) by (rewrite Hlive; apply in_or_app; right; exact He).
           split; exact Hin.
        -- intros t4 rg4 G4 Hne4 i Hi Hin.
           assert (EBM : rbase rho2 t rgM = rho t) by (unfold rbase; rewrite <- EaM, Eabs; exact Et).
           destruct (proj2 HRm2 t4 t rg4 rgM G4 EgM Hne4 ltac:(right; rewrite <- EwM; exact Ewr)) as [D|D]; rewrite EBM in D; rewrite <- ?EsM in D; unfold A in Hin; lia.
        -- intros E. subst t3. lia.
        -- intros E. subst t3. rewrite sh_tag_Z in Hlt3 by lia. lia.
    + intros rho2 Hag. exact (FMem_law RT CL lo sp0 r m0 cr0 anc xp g rho rho2 _ _ _ m' HF' Hag).
Qed.

End HkMemset.
