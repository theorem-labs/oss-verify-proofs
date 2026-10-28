(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_G_pkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Th_mutex Fz_T_lock Fz_env Fz_M_malloc Fz_T_sk Fz_K_hash Fz_K_rep Fz_K_sk Fz_I2_ppis Fz_K_pstw Fz_K_pstw2 Fz_K_pstrs Fz_I2_ppi2a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ppi_live_remove_app : forall p (l1 l2 : list (Z * Z)), live_remove p (l1 ++ l2) = live_remove p l1 ++ live_remove p l2.
Proof. intros p l1 l2. unfold live_remove. apply list_basics.list.filter_app. Qed.

Section PpiKit.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.

(* [comment removed for export] *)
Lemma ppi_addr_unique : forall Σ m l1 D n l2 x, ART RT Σ m -> rt_live RT Σ = l1 ++ (D, n) :: l2 -> 0 < n -> In x (l1 ++ l2) -> 0 < snd x -> fst x <> D.
Proof using AF.
  intros Σ m l1 D n l2 [p k] HA EL Hn Hin Hk. cbn [fst snd] in *.
  pose proof (af_live_disj RT AF Σ m D n p k l1 l2 HA EL Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma ppi_live_remove_unique : forall Σ m l1 D n l2, ART RT Σ m -> rt_live RT Σ = l1 ++ (D, n) :: l2 -> 0 < n ->
  Forall (fun x => 0 < snd x) (l1 ++ l2) -> live_remove D (rt_live RT Σ) = l1 ++ l2.
Proof using AF.
  intros Σ m l1 D n l2 HA EL Hn POS. rewrite EL. rewrite ppi_live_remove_app.
  assert (NE : forall x, In x (l1 ++ l2) -> fst x <> D).
  { intros x Hx. apply (ppi_addr_unique Σ m l1 D n l2 x HA EL Hn Hx). exact (proj1 (Forall_forall _ _) POS x Hx). }
  rewrite (live_remove_notin D l1) by (intros e He; apply NE; apply in_or_app; left; exact He).
  rewrite (live_remove_head D n l2) by (intros e He; apply NE; apply in_or_app; right; exact He). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ppi_fresh : forall Σ m x l, ART RT Σ m -> rt_live RT Σ = x :: l -> 0 < snd x -> ~ In x l.
Proof using AF. intros Σ m [p n] l HA EL Hn Hin. cbn [snd] in Hn. pose proof (af_live_disj RT AF Σ m p n p n [] l HA EL Hin). lia. Qed.
(* [comment removed for export] *)
Lemma ppi_fresh_pre : forall Σ m pre l x, ART RT Σ m -> rt_live RT Σ = pre ++ l -> In x pre -> 0 < snd x -> ~ In x l.
Proof using AF.
  intros Σ m pre l [p n] HA EL Hin Hn Hl. cbn [snd] in Hn. destruct (in_split _ _ Hin) as (l1 & l2 & E). rewrite E, <- app_assoc in EL. cbn [app] in EL.
  pose proof (af_live_disj RT AF Σ m p n p n l1 (l2 ++ l) HA EL ltac:(apply in_or_app; right; apply in_or_app; right; exact Hl)). lia.
Qed.

(* [comment removed for export] *)
Lemma ppi_keep : forall Σ (m m' : mem) BASE frames spc LW A n,
  ART RT Σ m -> rt_pres_fp BASE frames spc (pstr_W LW) m m' -> (forall e, In e BASE -> In e (rt_live RT Σ)) -> incl LW (rt_live RT Σ) ->
  In (A, n) BASE -> 1 <= n <= 64512 -> ~ In (A, n) LW -> agree_on (fun x => A <= x < A + n) m m'.
Proof using AF AFP.
  intros Σ m m' BASE frames spc LW A n HA PR HB HLW Hin Hn NI a Ha. cbv beta in Ha.
  pose proof (HB _ Hin) as INL.
  pose proof (afp_live_hi RT GOBJ AFP Σ m A n HA INL ltac:(lia)) as AHI.
  apply PR; [right; right; left; exists A, n; split; [exact Hin| exact Ha]|].
  unfold pstr_W. cbn [outside]. split; [unfold G_ALLOW_CUST; lia|].
  unfold rngs. clear PR. induction LW as [|[p k] LW IH]; [exact I|]. cbn [map outside fst snd]. split.
  - assert (NE : (A, n) <> (p, k)) by (intros E; apply NI; left; symmetry; exact E).
    pose proof (live_ne_apart2 RT AF Σ m (A, n) (p, k) HA INL (HLW _ ltac:(left; reflexivity)) NE) as X. cbn [fst snd] in X. lia.
  - apply IH; [intros x Hx; apply HLW; right; exact Hx| intros Hx; apply NI; right; exact Hx].
Qed.

Lemma ppi_keep_cells : forall Σ (m m' : mem) BASE frames spc LW A n X cs,
  ART RT Σ m -> rt_pres_fp BASE frames spc (pstr_W LW) m m' -> (forall e, In e BASE -> In e (rt_live RT Σ)) -> incl LW (rt_live RT Σ) ->
  In (A, n) BASE -> 1 <= n <= 64512 -> ~ In (A, n) LW ->
  rw_cells asegs m X cs -> A <= X -> X + Z.of_nat (cells_size cs) <= A + n -> rw_cells asegs m' X cs.
Proof using AF AFP.
  intros Σ m m' BASE frames spc LW A n X cs HA PR HB HLW Hin Hn NI HC H1 H2.
  apply (rw_cells_agree_nw asegs m m' X cs HC). intros a Ha. cbv beta in Ha.
  apply (ppi_keep Σ m m' BASE frames spc LW A n HA PR HB HLW Hin Hn NI). cbv beta. lia.
Qed.

Lemma ppi_keep_plh : forall Σ (m m' : mem) BASE frames spc LW lh B items bks,
  ART RT Σ m -> rt_pres_fp BASE frames spc (pstr_W LW) m m' -> (forall e, In e BASE -> In e (rt_live RT Σ)) -> incl LW (rt_live RT Σ) ->
  plh_rep m lh B items bks -> incl (plh_L lh B bks) BASE -> (forall x, In x (plh_L lh B bks) -> ~ In x LW) -> plh_rep m' lh B items bks.
Proof using AF AFP.
  intros Σ m m' BASE frames spc LW lh B items bks HA PR HB HLW REP HI NI.
  apply (plh_rep_agree m m' lh B items bks REP). intros a Ha.
  destruct Ha as [Ha|[Ha|(nd & Hn & Ha)]].
  - apply (ppi_keep Σ m m' BASE frames spc LW lh 104 HA PR HB HLW (HI _ ltac:(left; reflexivity)) ltac:(lia) (NI _ ltac:(left; reflexivity))). exact Ha.
  - apply (ppi_keep Σ m m' BASE frames spc LW B 128 HA PR HB HLW (HI _ ltac:(right; left; reflexivity)) ltac:(lia) (NI _ ltac:(right; left; reflexivity))). exact Ha.
  - pose proof (plh_L_node lh B bks nd Hn) as INn.
    apply (ppi_keep Σ m m' BASE frames spc LW (fst nd) 24 HA PR HB HLW (HI _ INn) ltac:(lia) (NI _ INn)). exact Ha.
Qed.

(* [comment removed for export] *)
Lemma ppi_outside_above : forall Σ (m : mem) LW a, ART RT Σ m -> incl LW (rt_live RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= a -> outside (pstr_W LW) a.
Proof using AF.
  intros Σ m LW a HA HLW Ha. unfold pstr_W. cbn [outside].
  pose proof (af_sp0_range RT AF Σ m HA) as SR. split; [unfold G_ALLOW_CUST, SEGTOP_A, STACK_WIN in *; lia|].
  unfold rngs. induction LW as [|[p k] LW IH]; [exact I|]. cbn [map outside fst snd]. split.
  - pose proof (af_live_range RT AF Σ m p k HA (HLW _ ltac:(left; reflexivity))) as (_ & R & _). lia.
  - apply IH. intros x Hx. apply HLW. right. exact Hx.
Qed.
(* [comment removed for export] *)
Lemma ppi_outside_rngs : forall L a w, outside (rngs L) a -> In w L -> ~ (fst w <= a < fst w + snd w).
Proof.
  intros L a w. unfold rngs. induction L as [|[p k] L IH]; intros HO Hin; [destruct Hin|]. cbn [map outside fst snd] in HO. destruct HO as [H1 H2].
  destruct Hin as [<-|Hin]; [cbn [fst snd]; exact H1| exact (IH H2 Hin)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PpiStep.
Variable Σ0 : rts RT.
Variable PMc : Model -> Prop.
Variable m0 : mem.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable lo : Z.
Variable outer : list Z.
Variable canary : word.
Variable PSD : list (Z * Z).
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis ART0 : ART RT Σ0 m0.
Hypothesis CALL0 : call_ok RT Σ0 m0 sp lo.
Hypothesis HSTK : lo + RT_STACK + 0x400 <= bv_unsigned sp.
Hypothesis CTX0 : cg_ctx (rt_cg RT Σ0) e_property_parse_init (bv_unsigned ra :: outer).
Hypothesis UWC0 : uw_chain m0 sp s0 outer.
Hypothesis CGH : cg_has (rt_cg RT Σ0) PPI_SITES PPI_CALLS.
Hypothesis HFR : (length (rt_frames RT Σ0) < FRAMES_MAX)%nat.
Hypothesis HLEN : Z.of_nat (length (rt_live RT Σ0)) + 19 <= LIVE_MAX.
Hypothesis HCR : 8 <= rt_credit RT Σ0.
Hypothesis HPSD : incl PSD (rt_live RT Σ0).

Notation usp := (bv_unsigned sp).

(* [comment removed for export] *)
Definition ppi_std (Σ : rts RT) (m : mem) (news : list (Z * Z)) (k : Z) (lb : byte) (j : list byte) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ stk asegs m lo (usp + -64)
  /\ rw_cells asegs m (usp + -64) (ppi_fr j s5 s4 s3 s2 s1 s0 ra)
  /\ agree_on (fun x => usp <= x < USTACK_TOP) m0 m
  /\ rt_live RT Σ = news ++ rt_live RT Σ0
  /\ rt_frames RT Σ = rt_frames RT Σ0 /\ rt_sp0 RT Σ = rt_sp0 RT Σ0 /\ rt_cg RT Σ = rt_cg RT Σ0 /\ rt_credit RT Σ = rt_credit RT Σ0 - k
  /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) usp (pstr_W PSD) m0 m
  /\ cl_env m lb canary.

(* [comment removed for export] *)
Definition ppi_gpre (Σ : rts RT) (m : mem) (site : Z) (lb : byte) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ call_ok RT Σ m (Z_to_bv 64 (usp + -64)) lo /\ lo + RT_STACK + PSTR_STK <= bv_unsigned (Z_to_bv 64 (usp + -64))
  /\ cg_ctx (rt_cg RT Σ) e_property_string (bv_unsigned (Z_to_bv 64 site) :: bv_unsigned ra :: outer)
  /\ uw_chain m (Z_to_bv 64 (usp + -64)) sp (bv_unsigned ra :: outer)
  /\ cg_has (rt_cg RT Σ) PSTR_SITES PSTR_CALLS
  /\ (length (rt_frames RT Σ) < FRAMES_MAX)%nat /\ Z.of_nat (length (rt_live RT Σ)) + 3 <= LIVE_MAX /\ 1 <= rt_credit RT Σ
  /\ cl_env m lb canary.

(* [comment removed for export] *)
Definition ppi_upost (Σ : rts RT) (m : mem) (site res s2z s3z s4z : Z) (BASE LW : list (Z * Z)) (Q : rts RT -> list (Z * Z) -> mem -> Prop) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (NEW : list (Z * Z)),
    ASTA RT Σ' PMc (fun ms => exists m' : mem,
        ret_st (Z_to_bv 64 site) (Z_to_bv 64 (usp + -64)) gp tp sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 s2z) (Z_to_bv 64 s3z) (Z_to_bv 64 s4z) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11
               (Z_to_bv 64 res) m' ms
        /\ rt_after_f RT Σ' (bv_unsigned (Z_to_bv 64 (usp + -64))) lo m m'
        /\ rt_pres_fp BASE (rt_frames RT Σ) (bv_unsigned (Z_to_bv 64 (usp + -64))) (pstr_W LW) m m'
        /\ cl_env m' (Z_to_bv 8 1) canary
        /\ Q Σ' NEW m') c
    /\ rt_live RT Σ' = NEW ++ BASE /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_cg RT Σ' = rt_cg RT Σ.

(* [comment removed for export] *)
Lemma ppi_num : rt_sp0 RT Σ0 - STACK_WIN <= lo /\ lo + RT_STACK + 0x400 <= usp /\ 0x10007fff8000 <= lo /\ usp + 16 <= USTACK_TOP /\ usp <= 2 ^ 47 /\ usp mod 16 = 0
  /\ bv_unsigned (Z_to_bv 64 (usp + -64)) = usp + -64.
Proof using AF ART0 CALL0 HSTK.
  destruct CALL0 as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ0 m0 ART0) as SP0W. pose proof (af_sp0_range RT AF Σ0 m0 ART0) as SP0R.
  assert (X : 0x10007fff8000 <= lo /\ usp <= 2 ^ 47) by (clear - LOW SPT SP0W SP0R; unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  split; [exact LOW|]. split; [exact HSTK|]. split; [exact (proj1 X)|]. split; [exact SPT|]. split; [exact (proj2 X)|]. split; [exact SPA|].
  apply unsigned_lit. clear - LOW SPT SP0W SP0R HSTK. unfold RT_STACK, STACK_WIN, USTACK_TOP in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ppi_call : forall (Σ : rts RT) (m : mem) (news nb : list (Z * Z)) (k : Z) (lb : byte) (j : list byte)
    (site nmf lit s2z s3z s4z res : Z) (BASE LW : list (Z * Z)) (Q : rts RT -> list (Z * Z) -> mem -> Prop),
  ppi_std Σ m news k lb j -> (length news <= 16)%nat -> 0 <= k <= 7 ->
  In (site, e_property_parse_init) PPI_SITES -> In (site, e_property_string) PPI_CALLS -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
  BASE = nb ++ rt_live RT Σ0 -> (forall e, In e BASE -> In e (rt_live RT Σ)) ->
  incl LW (rt_live RT Σ) -> (forall w, In w LW -> In w PSD \/ In w news) ->
  (forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc, ppi_gpre Σ m site lb ->
     cps asegs (ASTA RT Σ PMc (eq (ppi_ent site sp gp tp t0 t1 t2 nmf lit a4 a5 a6 a7 s2z s3z s4z s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)))
               (ppi_upost Σ m site res s2z s3z s4z BASE LW Q)) ->
  forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc T c,
  ASTA RT Σ PMc (eq (ppi_ent site sp gp tp t0 t1 t2 nmf lit a4 a5 a6 a7 s2z s3z s4z s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)) c ->
  (forall (Σ' : rts RT) (NEW : list (Z * Z)) (m' : mem) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' c',
     ASTA RT Σ' PMc (eq (ppi_ret site sp gp tp t0' t1' t2' res a1' a2' a3' a4' a5' a6' a7' s2z s3z s4z s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m')) c' ->
     ppi_std Σ' m' (NEW ++ nb) (k + 1) (Z_to_bv 8 1) j ->
     rt_pres_fp BASE (rt_frames RT Σ) (usp + -64) (pstr_W LW) m m' -> Q Σ' NEW m' ->
     rt_live RT Σ' = NEW ++ BASE -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP FDO MST ART0 CALL0 HSTK CTX0 UWC0 CGH HFR HLEN HCR HPSD.
  intros Σ m news nb k lb j site nmf lit s2z s3z s4z res BASE LW Q
         STD LEN KR SIN CIN SR SE EB HB HLW HW HC t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc T c HA Hk.
  destruct STD as (ARTm & MIm & STm & FRm & AGm & LVm & FRSm & SP0m & CGm & CRm & PRm & ENVm).
  destruct ppi_num as (LOW & _ & HLOS & SPT & SPH & SPA & EU1).
  (* [comment removed for export] *)
  assert (FREC : rw_cells asegs m (usp - 16) [C8 s0; C8 ra]).
  { unfold ppi_fr in FRm. replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m (usp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FRm). }
  assert (CGHm : cg_has (rt_cg RT Σ) PPI_SITES PPI_CALLS) by (rewrite CGm; exact CGH).
  destruct (cl_chain_call (rt_cg RT Σ) e_property_parse_init e_property_string site m0 m ra s0 sp (Z_to_bv 64 (usp + -64)) outer
              ltac:(rewrite CGm; exact CTX0) (proj1 CGHm _ SIN) (proj2 CGHm _ CIN) UWC0 AGm FREC ltac:(rewrite EU1; lia) SPT) as (CTXc & UWCc).
  assert (GP : ppi_gpre Σ m site lb).
  { unfold ppi_gpre. rewrite (unsigned_lit site) by exact SR. rewrite EU1.
    split; [exact ARTm|]. split; [exact MIm|].
    split. { unfold call_ok. rewrite EU1. split; [exact STm|]. split; [rewrite SP0m; exact LOW|]. split; [clear - HSTK; unfold RT_STACK in *; lia|].
             split; [clear - SPT; lia|]. clear - SPA. Z.div_mod_to_equations. lia. }
    split; [clear - HSTK; unfold PSTR_STK, RT_STACK in *; lia|].
    split; [exact CTXc|]. split; [exact UWCc|].
    split; [exact (cg_has_sub _ _ _ _ _ CGHm (proj1 PSTR_in_PPI) (proj2 PSTR_in_PPI))|].
    split; [rewrite FRSm; exact HFR|].
    split; [rewrite LVm, length_app, Nat2Z.inj_add; clear - LEN HLEN; lia|].
    split; [rewrite CRm; clear - KR HCR; lia| exact ENVm]. }
  (* [comment removed for export] *)
  apply (cps_realizes asegs _ _ _ c (HC t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc GP) HA).
  intros c1 (Σ' & NEW & Hc1 & LV' & FRS' & SP0' & CR' & CG').
  destruct (ASTA_unpack RT Σ' _ _ c1 Hc1) as (ms1 & (m' & RS & (ART' & MI' & ST') & PRES & ENV' & HQ) & Hc1'). clear Hc1.
  destruct RS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
  rewrite EU1 in ST', PRES. rewrite (ret_pc_even site SR SE) in Hc1'.
  (* [comment removed for export] *)
  assert (AGc : agree_on (fun x => usp + -64 <= x < USTACK_TOP) m m').
  { intros a Ha. cbv beta in Ha. apply PRES; [left; exact Ha|]. apply (ppi_outside_above Σ m LW _ ARTm HLW). rewrite SP0m. clear - LOW HSTK Ha. unfold RT_STACK in *. lia. }
  assert (FR' : rw_cells asegs m' (usp + -64) (ppi_fr j s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m m' _ _ FRm). intros a Ha. apply AGc. unfold ppi_fr in Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta in *. clear - Ha SPT. lia. }
  assert (AG' : agree_on (fun x => usp <= x < USTACK_TOP) m0 m').
  { intros a Ha. cbv beta in Ha. rewrite (AGc a ltac:(cbv beta; clear - Ha; lia)). exact (AGm a Ha). }
  (* [comment removed for export] *)
  assert (PR' : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) usp (pstr_W PSD) m0 m').
  { intros a Ha Ho. rewrite <- (PRm a Ha Ho). apply PRES.
    - apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite EB; apply in_or_app; right; exact He| intros e He; rewrite FRSm; exact He| clear; lia].
    - unfold pstr_W in *. cbn [outside] in *. destruct Ho as [Ho1 Ho2]. split; [exact Ho1|].
      assert (G : forall w, In w LW -> ~ (fst w <= bv_unsigned a < fst w + snd w)).
      { intros w Hw. destruct (HW w Hw) as [Hp|Hn]; [exact (ppi_outside_rngs PSD _ w Ho2 Hp)|]. destruct w as [p n]. cbn [fst snd].
        destruct (Z_le_gt_dec 0 n) as [N0|N0]; [| clear - N0; lia].
        exact (wg_newchunk_apart RT AF Σ0 Σ m news p n usp (bv_unsigned a) ARTm LVm Hn FRSm SP0m ltac:(clear - LOW HSTK; unfold RT_STACK in *; lia) N0 Ha). }
      clear - G. unfold rngs. induction LW as [|[p n] LW IH]; [exact I|]. cbn [map outside fst snd]. split; [exact (G (p, n) ltac:(left; reflexivity))|].
      apply IH. intros w Hw. apply G. right. exact Hw. }
  assert (SP0'' : rt_sp0 RT Σ' = rt_sp0 RT Σ0) by (rewrite SP0'; exact SP0m).
  apply (Hk Σ' NEW m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' c1 Hc1'); [| exact PRES| exact HQ| exact LV'| exact SP0''].
  unfold ppi_std. split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact AG'|].
  split; [rewrite LV', EB, app_assoc; reflexivity|].
  split; [rewrite FRS'; exact FRSm|]. split; [exact SP0''|]. split; [rewrite CG'; exact CGm|]. split; [rewrite CR', CRm; clear; lia|].
  split; [exact PR'| exact ENV'].
Qed.

Lemma ppi_step : forall (Σ : rts RT) (m : mem) (news nb : list (Z * Z)) (k : Z) (lb : byte) (j : list byte)
    (site nmf lit s2z s3z s4z res : Z) (BASE LW : list (Z * Z)) (Q : rts RT -> list (Z * Z) -> mem -> Prop)
    (site' nmf' lit' s2z' s3z' s4z' : Z),
  ppi_std Σ m news k lb j -> (length news <= 16)%nat -> 0 <= k <= 7 ->
  In (site, e_property_parse_init) PPI_SITES -> In (site, e_property_string) PPI_CALLS -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
  BASE = nb ++ rt_live RT Σ0 -> (forall e, In e BASE -> In e (rt_live RT Σ)) ->
  incl LW (rt_live RT Σ) -> (forall w, In w LW -> In w PSD \/ In w news) ->
  (forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc, ppi_gpre Σ m site lb ->
     cps asegs (ASTA RT Σ PMc (eq (ppi_ent site sp gp tp t0 t1 t2 nmf lit a4 a5 a6 a7 s2z s3z s4z s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)))
               (ppi_upost Σ m site res s2z s3z s4z BASE LW Q)) ->
  (forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (Σx : rts RT) (mx : mem), ART RT Σx mx -> mem_inv asegs mx -> stk asegs mx lo (usp + -64) ->
     evt asegs (ppi_mid_post site' sp gp tp t0 t1 t2 nmf' lit' a4 a5 a6 a7 s2z' s3z' s4z' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo mx)
               (ppi_ret site sp gp tp t0 t1 t2 res a1 a2 a3 a4 a5 a6 a7 s2z s3z s4z s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mx)) ->
  forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc T c,
  ASTA RT Σ PMc (eq (ppi_ent site sp gp tp t0 t1 t2 nmf lit a4 a5 a6 a7 s2z s3z s4z s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)) c ->
  (forall (Σ' : rts RT) (NEW : list (Z * Z)) (m' m'' : mem) t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' c',
     ASTA RT Σ' PMc (eq (ppi_ent site' sp gp tp t0' t1' t2' nmf' lit' a4' a5' a6' a7' s2z' s3z' s4z' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m'')) c' ->
     ppi_std Σ' m'' (NEW ++ nb) (k + 1) (Z_to_bv 8 1) j ->
     ART RT Σ' m' -> rt_pres_fp BASE (rt_frames RT Σ) (usp + -64) (pstr_W LW) m m' -> Q Σ' NEW m' ->
     rt_live RT Σ' = NEW ++ BASE -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     munch [(usp - 80, usp - 64)] m' m'' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP FDO MST ART0 CALL0 HSTK CTX0 UWC0 CGH HFR HLEN HCR HPSD.
  intros Σ m news nb k lb j site nmf lit s2z s3z s4z res BASE LW Q site' nmf' lit' s2z' s3z' s4z'
         STD LEN KR SIN CIN SR SE EB HB HLW HW HC HSEG t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc T c HA Hk.
  destruct STD as (ARTm & MIm & STm & FRm & AGm & LVm & FRSm & SP0m & CGm & CRm & PRm & ENVm).
  destruct ppi_num as (LOW & _ & HLOS & SPT & SPH & SPA & EU1).
  (* [comment removed for export] *)
  assert (FREC : rw_cells asegs m (usp - 16) [C8 s0; C8 ra]).
  { unfold ppi_fr in FRm. replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m (usp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FRm). }
  assert (CGHm : cg_has (rt_cg RT Σ) PPI_SITES PPI_CALLS) by (rewrite CGm; exact CGH).
  destruct (cl_chain_call (rt_cg RT Σ) e_property_parse_init e_property_string site m0 m ra s0 sp (Z_to_bv 64 (usp + -64)) outer
              ltac:(rewrite CGm; exact CTX0) (proj1 CGHm _ SIN) (proj2 CGHm _ CIN) UWC0 AGm FREC ltac:(rewrite EU1; lia) SPT) as (CTXc & UWCc).
  assert (GP : ppi_gpre Σ m site lb).
  { unfold ppi_gpre. rewrite (unsigned_lit site) by exact SR. rewrite EU1.
    split; [exact ARTm|]. split; [exact MIm|].
    split. { unfold call_ok. rewrite EU1. split; [exact STm|]. split; [rewrite SP0m; exact LOW|]. split; [clear - HSTK; unfold RT_STACK in *; lia|].
             split; [clear - SPT; lia|]. clear - SPA. Z.div_mod_to_equations. lia. }
    split; [clear - HSTK; unfold PSTR_STK, RT_STACK in *; lia|].
    split; [exact CTXc|]. split; [exact UWCc|].
    split; [exact (cg_has_sub _ _ _ _ _ CGHm (proj1 PSTR_in_PPI) (proj2 PSTR_in_PPI))|].
    split; [rewrite FRSm; exact HFR|].
    split; [rewrite LVm, length_app, Nat2Z.inj_add; clear - LEN HLEN; lia|].
    split; [rewrite CRm; clear - KR HCR; lia| exact ENVm]. }
  (* [comment removed for export] *)
  apply (cps_realizes asegs _ _ _ c (HC t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc GP) HA).
  intros c1 (Σ' & NEW & Hc1 & LV' & FRS' & SP0' & CR' & CG').
  destruct (ASTA_unpack RT Σ' _ _ c1 Hc1) as (ms1 & (m' & RS & (ART' & MI' & ST') & PRES & ENV' & HQ) & Hc1'). clear Hc1.
  destruct RS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
  rewrite EU1 in ST', PRES. rewrite (ret_pc_even site SR SE) in Hc1'.

  (* [comment removed for export] *)
  assert (AGc : agree_on (fun x => usp + -64 <= x < USTACK_TOP) m m').
  { intros a Ha. cbv beta in Ha. apply PRES; [left; exact Ha|]. apply (ppi_outside_above Σ m LW _ ARTm HLW). rewrite SP0m. clear - LOW HSTK Ha. unfold RT_STACK in *. lia. }
  assert (FR' : rw_cells asegs m' (usp + -64) (ppi_fr j s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m m' _ _ FRm). intros a Ha. apply AGc. unfold ppi_fr in Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta in *. clear - Ha SPT. lia. }
  assert (AG' : agree_on (fun x => usp <= x < USTACK_TOP) m0 m').
  { intros a Ha. cbv beta in Ha. rewrite (AGc a ltac:(cbv beta; clear - Ha; lia)). exact (AGm a Ha). }
  (* [comment removed for export] *)
  assert (PR' : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) usp (pstr_W PSD) m0 m').
  { intros a Ha Ho. rewrite <- (PRm a Ha Ho). apply PRES.
    - apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite EB; apply in_or_app; right; exact He| intros e He; rewrite FRSm; exact He| clear; lia].
    - unfold pstr_W in *. cbn [outside] in *. destruct Ho as [Ho1 Ho2]. split; [exact Ho1|].
      assert (G : forall w, In w LW -> ~ (fst w <= bv_unsigned a < fst w + snd w)).
      { intros w Hw. destruct (HW w Hw) as [Hp|Hn]; [exact (ppi_outside_rngs PSD _ w Ho2 Hp)|]. destruct w as [p n]. cbn [fst snd].
        destruct (Z_le_gt_dec 0 n) as [N0|N0]; [| clear - N0; lia].
        exact (wg_newchunk_apart RT AF Σ0 Σ m news p n usp (bv_unsigned a) ARTm LVm Hn FRSm SP0m ltac:(clear - LOW HSTK; unfold RT_STACK in *; lia) N0 Ha). }
      clear - G. unfold rngs. induction LW as [|[p n] LW IH]; [exact I|]. cbn [map outside fst snd]. split; [exact (G (p, n) ltac:(left; reflexivity))|].
      apply IH. intros w Hw. apply G. right. exact Hw. }
  (* [comment removed for export] *)
  pose proof (HSEG t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' Σ' m' ART' MI' ST') as W.
  unfold ppi_ret in W.
  cl_lift W Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ' _ _ c2 Hc2) as (ms2 & (m'' & -> & MU & WM & MI'' & ST'') & Hc2'). clear Hc2.
  assert (SP0'' : rt_sp0 RT Σ' = rt_sp0 RT Σ0) by (rewrite SP0'; exact SP0m).
  assert (ART'' : ART RT Σ' m'').
  { apply (af_frame RT AF Σ' m' m'' (usp - 80) ART' ltac:(rewrite SP0''; clear - LOW HSTK; unfold RT_STACK in *; lia)); [| exact WM].
    intros a Ha. apply MU. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. clear - Hin SPT. lia. }
  assert (AGs : agree_on (fun x => usp + -64 <= x < USTACK_TOP) m' m'').
  { intros a Ha. cbv beta in Ha. apply MU. cbn [outside]. split; [clear - Ha; lia| exact I]. }
  apply (Hk Σ' NEW m' m'' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' c2 Hc2'); [| exact ART'| exact PRES| exact HQ| exact LV'| exact SP0''| exact MU].
  unfold ppi_std. split; [exact ART''|]. split; [exact MI''|]. split; [exact ST''|].
  split. { apply (rw_cells_agree_nw asegs m' m'' _ _ FR'). intros a Ha. apply AGs. unfold ppi_fr in Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta in *. clear - Ha SPT. lia. }
  split. { intros a Ha. cbv beta in Ha. rewrite (AGs a ltac:(cbv beta; clear - Ha; lia)). exact (AG' a Ha). }
  split; [rewrite LV', EB, app_assoc; reflexivity|].
  split; [rewrite FRS'; exact FRSm|]. split; [exact SP0''|]. split; [rewrite CG'; exact CGm|]. split; [rewrite CR', CRm; clear; lia|].
  split. { intros a Ha Ho. rewrite <- (PR' a Ha Ho). apply MU. cbn [outside]. split; [| exact I].
           destruct (aclient_split RT AF Σ0 m0 usp (bv_unsigned a) ART0 Ha) as [H|H]; [clear - H; lia| clear - H LOW HSTK; unfold RT_STACK in *; lia]. }
  apply (cl_env_seg _ m' m'' _ canary ENV' MU). cl_fp_lia.
Qed.

(* [comment removed for export] *)
Lemma ppi_tab_sh : forall (Σx : rts RT) (mx : mem) k, ART RT Σx mx -> GOBJ PPI_TAB 48 -> 0 <= k < 6 -> ro_cells asegs mx (PPI_TAB_SH + k) [C1 (Z_to_bv 8 0)].
Proof using AFP.
  intros Σx mx k HA GO Hk.
  pose proof (afp_gsh_byte RT GOBJ AFP Σx mx PPI_TAB 48 (PPI_TAB + 8 * k) HA GO ltac:(clear - Hk; lia) ltac:(clear - Hk; lia)) as X.
  assert (E1 : (PPI_TAB + 8 * k) mod 8 = 0) by (clear; unfold PPI_TAB; replace (5436128 + 8 * k) with (0 + (679516 + k) * 8) by lia; rewrite Z.mod_add by lia; reflexivity).
  specialize (X E1).
  assert (E2 : (PPI_TAB + 8 * k) / 8 + 2147450880 = PPI_TAB_SH + k).
  { clear. unfold PPI_TAB, PPI_TAB_SH. replace (5436128 + 8 * k) with (0 + (679516 + k) * 8) by lia. rewrite Z.div_add by lia. change (0 / 8) with 0. lia. }
  rewrite E2 in X.
  assert (E3 : (PPI_TAB + 48 - (PPI_TAB + 8 * k) <? 8) = false) by (apply Z.ltb_ge; clear - Hk; lia).
  rewrite E3 in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma ppi_enter : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (lb : byte) T c,
  GOBJ PPI_TAB 48 -> mem_inv asegs m0 -> cl_env m0 lb canary ->
  ASTA RT Σ0 PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PPI_CTX) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_property_parse_init m0)) c ->
  (forall (m1 : mem) (j : list byte) c',
     ASTA RT Σ0 PMc (eq (ppi_ent SITE_ppi_name sp gp tp t0 t1 t2 1 A_PROVIDER a4 a5 a6 a7 0 PPI_TAB PPI_TAB_SH s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1)) c' ->
     ppi_std Σ0 m1 [] 0 lb j -> munch [(usp - 80, usp)] m0 m1 -> realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP FDO MST ART0 CALL0 HSTK CTX0 UWC0 CGH HFR HLEN HCR HPSD.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lb T c GO MI0 ENV HA Hk.
  destruct ppi_num as (LOW & _ & HLOS & SPT & SPH & SPA & EU1). pose proof CALL0 as (ST & _).
  destruct (af_client_consts RT AF Σ0 m0 ART0) as (_ & SHC & _ & _ & UT).
  pose proof (ppi_tab_sh Σ0 m0 0 ART0 GO ltac:(clear; lia)) as TSH. rewrite Z.add_0_r in TSH.
  pose proof (ppi_w0 ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 lo
                ST ltac:(clear - HSTK; unfold RT_STACK in *; lia) HLOS SPH UT SHC TSH MI0) as W.
  unfold entry_st in HA.
  cl_lift W HA c1 Hc1.
  destruct (ASTA_unpack RT Σ0 _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU & WM & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  apply (Hk m1 j c1 Hc1'); [| exact MU].
  assert (ART1 : ART RT Σ0 m1).
  { apply (af_frame RT AF Σ0 m0 m1 (usp - 80) ART0 ltac:(clear - LOW HSTK; unfold RT_STACK in *; lia)); [| exact WM].
    intros a Ha. apply MU. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. clear - Hin SPT. lia. }
  unfold ppi_std. split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact FR1|].
  split. { intros a Ha. cbv beta in Ha. apply MU. cbn [outside]. split; [clear - Ha; lia| exact I]. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|].
  split. { intros a Ha Ho. apply MU. cbn [outside]. split; [| exact I].
           destruct (aclient_split RT AF Σ0 m0 usp (bv_unsigned a) ART0 Ha) as [H|H]; [clear - H; lia| clear - H LOW HSTK; unfold RT_STACK in *; lia]. }
  apply (cl_env_seg _ m0 m1 _ canary ENV MU). cl_fp_lia.
Qed.

(* [comment removed for export] *)
Lemma ppi_exit : forall (Σ : rts RT) (m : mem) news k lb j t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc T c,
  ppi_std Σ m news k lb j ->
  ASTA RT Σ PMc (eq (ppi_ret SITE_ppi_val2 sp gp tp t0 t1 t2 2 a1 a2 a3 a4 a5 a6 a7 1 (PPI_TAB + 48) (PPI_TAB_SH + 6) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)) c ->
  (forall c', ASTA RT Σ PMc (fun ms => ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m ms) c' -> stk asegs m lo usp -> realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP FDO MST ART0 CALL0 HSTK CTX0 UWC0 CGH HFR HLEN HCR HPSD.
  intros Σ m news k lb j t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc T c STD HA Hk.
  destruct STD as (ARTm & MIm & STm & FRm & _).
  destruct ppi_num as (LOW & _ & HLOS & SPT & SPH & SPA & EU1).
  pose proof (ppi_w8 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo j s5 s4 s3 s2 s1 s0 ra
                STm ltac:(clear - HSTK; unfold RT_STACK in *; lia) HLOS SPH FRm MIm) as W.
  cl_lift W HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (-> & ST1) & Hc1'). clear Hc1.
  apply (Hk c1); [| exact ST1].
  eapply ASTA_conseq; [exact Hc1'|]. intros ms <-. unfold ret_st. do 16 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ppi_Qfirst (nm : bool) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (pad comp cmpt freet copyt : word)
    : rts RT -> list (Z * Z) -> mem -> Prop :=
  fun _ NEW m' => exists (pn D pnn : Z) (junk' : list byte),
       NEW = [(pnn, 24); (D, 32); (pn, Z.of_nat (length str) + 16)]
    /\ pstr_post_mem m' canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pnn
    /\ rw_cells asegs m' (q_of nm pq1 pq2) (sk_cells (Z_to_bv 64 1) pad (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) comp cmpt freet copyt)
    /\ rw_cells asegs m' D [CB 32 junk']
    /\ blk_ok pn (Z.of_nat (length str) + 16) /\ blk_ok D 32 /\ blk_ok pnn 24.
Definition ppi_Qroom (nm : bool) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (D num nalloc : Z) (pad cmpt freet copyt : word)
    : rts RT -> list (Z * Z) -> mem -> Prop :=
  fun _ NEW m' => exists (pn pnn : Z) (junk' : list byte),
       NEW = [(pnn, 24); (pn, Z.of_nat (length str) + 16)]
    /\ pstr_post_mem m' canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pnn
    /\ rw_cells asegs m' (q_of nm pq1 pq2) (sk_cells (Z_to_bv 64 (num + 1)) pad (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 nalloc) (Z_to_bv 64 0) cmpt freet copyt)
    /\ rw_cells asegs m' D [CB (Z.to_nat (8 * nalloc)) junk']
    /\ blk_ok pn (Z.of_nat (length str) + 16) /\ blk_ok pnn 24.
Definition ppi_Qgrow (nm : bool) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (pad cmpt freet copyt : word)
    : rts RT -> list (Z * Z) -> mem -> Prop :=
  fun _ NEW m' => exists (pn D' pnn : Z) (junk' : list byte),
       NEW = [(pnn, 24); (D', 48); (pn, Z.of_nat (length str) + 16)]
    /\ pstr_post_mem m' canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pnn
    /\ rw_cells asegs m' (q_of nm pq1 pq2) (sk_cells (Z_to_bv 64 5) pad (Z_to_bv 64 D') (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 0) cmpt freet copyt)
    /\ rw_cells asegs m' D' [CB 48 junk']
    /\ blk_ok pn (Z.of_nat (length str) + 16) /\ blk_ok D' 48 /\ blk_ok pnn 24.

Lemma ppi_of_first : forall (Σ : rts RT) (m : mem) site s2z s3z s4z nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pad comp cmpt freet copyt c,
  pstr_first_post RT Σ PMc (Z_to_bv 64 site) (Z_to_bv 64 (usp + -64)) gp tp sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 s2z) (Z_to_bv 64 s3z) (Z_to_bv 64 s4z) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11
      lo m canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pad comp cmpt freet copyt c ->
  ppi_upost Σ m site (cnt_of nm ni vi + 1) s2z s3z s4z (rt_live RT Σ) (pstr_L nm ps pk pl1 pl2 pq1 pq2 B bks)
      (ppi_Qfirst nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pad comp cmpt freet copyt) c.
Proof using.
  intros Σ m site s2z s3z s4z nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pad comp cmpt freet copyt c
         (Σ' & pn & D & pnn & HA & LV & FRS & SP0 & CR & B1 & B2 & B3 & CG).
  exists Σ', [(pnn, 24); (D, 32); (pn, Z.of_nat (length str) + 16)].
  split; [| split; [exact LV| split; [exact FRS| split; [exact SP0| split; [exact CR| exact CG]]]]].
  eapply ASTA_conseq; [exact HA|]. intros ms (m' & junk' & RS & AFT & PR & PM & QC & DC). exists m'.
  split; [exact RS|]. split; [exact (rt_after_f_of _ _ _ _ _ _ AFT)|]. split; [exact PR|]. split; [exact (proj1 PM)|].
  exists pn, D, pnn, junk'. split; [reflexivity|]. split; [exact PM|]. split; [exact QC|]. split; [exact DC|]. split; [exact B1|]. split; [exact B2| exact B3].
Qed.

Lemma ppi_of_room : forall (Σ : rts RT) (m : mem) site s2z s3z s4z nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks D num nalloc pad cmpt freet copyt c,
  pstr_room_post RT Σ PMc (Z_to_bv 64 site) (Z_to_bv 64 (usp + -64)) gp tp sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 s2z) (Z_to_bv 64 s3z) (Z_to_bv 64 s4z) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11
      lo m canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks D num nalloc pad cmpt freet copyt c ->
  ppi_upost Σ m site (cnt_of nm ni vi + 1) s2z s3z s4z (rt_live RT Σ) ((D, 8 * nalloc) :: pstr_L nm ps pk pl1 pl2 pq1 pq2 B bks)
      (ppi_Qroom nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks D num nalloc pad cmpt freet copyt) c.
Proof using.
  intros Σ m site s2z s3z s4z nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks D num nalloc pad cmpt freet copyt c
         (Σ' & pn & pnn & HA & LV & FRS & SP0 & CR & B1 & B3 & CG).
  exists Σ', [(pnn, 24); (pn, Z.of_nat (length str) + 16)].
  split; [| split; [exact LV| split; [exact FRS| split; [exact SP0| split; [exact CR| exact CG]]]]].
  eapply ASTA_conseq; [exact HA|]. intros ms (m' & junk' & RS & AFT & PR & PM & QC & DC). exists m'.
  split; [exact RS|]. split; [exact (rt_after_f_of _ _ _ _ _ _ AFT)|]. split; [exact PR|]. split; [exact (proj1 PM)|].
  exists pn, pnn, junk'. split; [reflexivity|]. split; [exact PM|]. split; [exact QC|]. split; [exact DC|]. split; [exact B1| exact B3].
Qed.

Lemma ppi_of_grow : forall (Σ : rts RT) (m : mem) site s2z s3z s4z nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks D pad cmpt freet copyt c,
  pstr_grow_post RT Σ PMc (Z_to_bv 64 site) (Z_to_bv 64 (usp + -64)) gp tp sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 s2z) (Z_to_bv 64 s3z) (Z_to_bv 64 s4z) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11
      lo m canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks D pad cmpt freet copyt c ->
  ppi_upost Σ m site (cnt_of nm ni vi + 1) s2z s3z s4z (live_remove D (rt_live RT Σ)) (pstr_L nm ps pk pl1 pl2 pq1 pq2 B bks)
      (ppi_Qgrow nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pad cmpt freet copyt) c.
Proof using.
  intros Σ m site s2z s3z s4z nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks D pad cmpt freet copyt c
         (Σ' & pn & D' & pnn & HA & LV & FRS & SP0 & CR & B1 & B2 & B3 & CG).
  exists Σ', [(pnn, 24); (D', 48); (pn, Z.of_nat (length str) + 16)].
  split; [| split; [exact LV| split; [exact FRS| split; [exact SP0| split; [exact CR| exact CG]]]]].
  eapply ASTA_conseq; [exact HA|]. intros ms (m' & junk' & RS & AFT & PR & PM & QC & DC). exists m'.
  split; [exact RS|]. split; [exact AFT|]. split; [exact PR|]. split; [exact (proj1 PM)|].
  exists pn, D', pnn, junk'. split; [reflexivity|]. split; [exact PM|]. split; [exact QC|]. split; [exact DC|]. split; [exact B1|]. split; [exact B2| exact B3].
Qed.

(* [comment removed for export] *)
Lemma ppi_seg_cells : forall (Σx : rts RT) (mx mx' : mem) a b A n X cs,
  ART RT Σx mx -> rt_sp0 RT Σx = rt_sp0 RT Σ0 -> In (A, n) (rt_live RT Σx) -> munch [(a, b)] mx mx' -> lo <= a ->
  rw_cells asegs mx X cs -> X + Z.of_nat (cells_size cs) <= A + n -> rw_cells asegs mx' X cs.
Proof using AF ART0 CALL0 HSTK.
  intros Σx mx mx' a b A n X cs HA SP0 Hin MU Ha HC HX. destruct ppi_num as (LOW & _).
  pose proof (af_live_range RT AF Σx mx A n HA Hin) as (_ & R & _). rewrite SP0 in R.
  apply (rw_cells_agree_nw asegs mx mx' X cs HC). intros x Hx. cbv beta in Hx. apply MU. cbn [outside]. split; [clear - Hx HX R LOW Ha; lia| exact I].
Qed.
Lemma ppi_seg_static : forall (mx mx' : mem) a b X cs,
  munch [(a, b)] mx mx' -> lo <= a -> rw_cells asegs mx X cs -> X + Z.of_nat (cells_size cs) <= SEGTOP_A -> rw_cells asegs mx' X cs.
Proof using AF ART0 CALL0 HSTK.
  intros mx mx' a b X cs MU Ha HC HX. destruct ppi_num as (_ & _ & HLOS & _).
  apply (rw_cells_agree_nw asegs mx mx' X cs HC). intros x Hx. cbv beta in Hx. apply MU. cbn [outside]. split; [clear - Hx HX HLOS Ha; unfold SEGTOP_A in *; lia| exact I].
Qed.
Lemma ppi_seg_plh : forall (Σx : rts RT) (mx mx' : mem) a b lh B items bks,
  ART RT Σx mx -> rt_sp0 RT Σx = rt_sp0 RT Σ0 -> incl (plh_L lh B bks) (rt_live RT Σx) -> munch [(a, b)] mx mx' -> lo <= a ->
  plh_rep mx lh B items bks -> plh_rep mx' lh B items bks.
Proof using AF ART0 CALL0 HSTK.
  intros Σx mx mx' a b lh B items bks HA SP0 HI MU Ha REP. destruct ppi_num as (LOW & _).
  apply (plh_rep_munch [(a, b)] mx mx' lh B items bks REP MU). intros x Hx. cbn [outside]. split; [| exact I].
  assert (K : forall A n, In (A, n) (plh_L lh B bks) -> A <= x < A + n -> ~ a <= x < b).
  { intros A n Hin Hx'. pose proof (af_live_range RT AF Σx mx A n HA (HI _ Hin)) as (_ & R & _). rewrite SP0 in R. clear - Hx' R LOW Ha. lia. }
  destruct Hx as [Hx|[Hx|(nd & Hn & Hx)]].
  - exact (K lh 104 ltac:(left; reflexivity) Hx).
  - exact (K B 128 ltac:(right; left; reflexivity) Hx).
  - exact (K (fst nd) 24 (plh_L_node lh B bks nd Hn) Hx).
Qed.

(* [comment removed for export] *)
Lemma ppi_pre : forall (Σ : rts RT) (m : mem) (site : Z) (lb : byte) (nm : bool) (S : Z) (str : list byte) (kz : nat)
    (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)),
  tp = Z_to_bv 64 0xba3ef0 ->
  ppi_gpre Σ m site lb -> ppi_lit S str kz -> GOBJ S (Z.of_nat (length str) + 1) ->
  rw_cells asegs m CTX_PSD [C8 (Z_to_bv 64 ps)] ->
  In (ps, 48) (rt_live RT Σ) -> ps mod 16 = 0 -> rw_cells asegs m ps (psd_cells pk pl1 pl2 ni vi pq1 pq2) -> 0 <= ni < 2 ^ 20 -> 0 <= vi < 2 ^ 20 ->
  In (pk, 40) (rt_live RT Σ) -> pk mod 16 = 0 -> rw_cells asegs m pk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  plh_rep m (t_of nm pl1 pl2) B items bks -> incl (plh_L (t_of nm pl1 pl2) B bks) (rt_live RT Σ) -> items < 15 ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  In (q_of nm pq1 pq2, 56) (rt_live RT Σ) -> q_of nm pq1 pq2 mod 8 = 0 ->
  pstr_pre RT GOBJ Σ PMc (Z_to_bv 64 site) (Z_to_bv 64 (usp + -64)) tp sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 (nmz nm)) (Z_to_bv 64 1) (Z_to_bv 64 S) m lo
           (bv_unsigned ra :: outer) lb canary nm S S (Z.of_nat (length str) + 1) str (repeat (Z_to_bv 8 0) kz) ps pk pl1 pl2 ni vi pq1 pq2 B items bks.
Proof using FDO MST.
  intros Σ m site lb nm S str kz ps pk pl1 pl2 ni vi pq1 pq2 B items bks TPV
         (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11) (L1 & L2 & L3 & L4 & L5 & L6 & L7) GO
         CELL INps Aps PSC NI VI INpk Apk LKC REP INC IT HF INq Aq.
  unfold pstr_pre.
  split; [exact FDO|]. split; [exact MST|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact TPV|].
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
  split; [exact G8|]. split; [exact G9|]. split; [exact G10|]. split; [exact G11|].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|].
  split; [exact GO|]. split; [clear; lia|]. split; [clear; lia|]. split; [exact L6|]. split; [exact L7|].
  split; [exact CELL|]. split; [exact INps|]. split; [exact Aps|]. split; [exact PSC|]. split; [exact NI|]. split; [exact VI|].
  split; [exact INpk|]. split; [exact Apk|]. split; [exact LKC|]. split; [exact REP|]. split; [exact INC|]. split; [exact IT|]. split; [exact HF|].
  split; [exact INq| exact Aq].
Qed.

End PpiStep.
End PpiKit.
