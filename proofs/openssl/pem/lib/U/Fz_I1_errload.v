(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_kit_ra Fz_M_realloc Fz_I1_insert Fz_I1_insert1 Fz_cimg_rom. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_T_once Fz_I1_load.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_ERR_LOAD_ERR : Z := 0xe7d80.
Definition FZ_ERR_LOAD_CONST : Z := 0xe7fd0.
Definition ERR_ONCE_CELL : Z := 0x32e010.
Definition ELE_STACK : Z := 32 + ELS_STACK.
Definition ELC_STACK : Z := 32 + ELE_STACK.
Definition NBASE : nat := 82.
Definition ERR_TAB1 : Z := 0x2c0650.
Definition ERR_TAB2 : Z := 0x2c0910.

(* [comment removed for export] *)
Definition err_statics (LK lh : Z) : list cell := [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)].

Lemma etab_base1 : etab ERR_TAB1 43.
Proof. apply etab_okb_spec. vm_cast_no_check (eq_refl true). Qed.
Lemma etab_base2 : etab ERR_TAB2 39.
Proof. apply etab_okb_spec. vm_cast_no_check (eq_refl true). Qed.
Lemma trange_base1 : trange ERR_TAB1 43.
Proof. intros x Hx. unfold ERR_TAB1 in Hx. unfold cimg_addr, RMallocRep.RGOT_SSP. lia. Qed.
Lemma trange_base2 : trange ERR_TAB2 39.
Proof. intros x Hx. unfold ERR_TAB2 in Hx. unfold cimg_addr, RMallocRep.RGOT_SSP. lia. Qed.

(* [comment removed for export] *)
Lemma els_res_compose : forall (LBall : list block) (L : @clist bptr) lh pl pb nmb g bks (n1 n2 : nat) pk LK (LBall1 : list block) (L1 : @clist bptr)
    pb1 nmb1 g1 bks1 v2 LBall2 L2 m2,
  g_items g <= g_items g1 <= g_items g + Z.of_nat n1 -> nmb <= nmb1 ->
  cgrow L L1 (Z.of_nat n1 + (wA nmb1 - wA nmb)) (wB nmb1 - wB nmb) (wBig nmb1 - wBig nmb) ->
  (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> ~ lh_T pl pb bks q -> ~ lh_T pl pb1 bks1 q) ->
  In (pk, LK, 40) LBall1 -> ckeep (fun q => q = pk \/ lh_T pl pb bks q) LBall L LBall1 L1 ->
  els_res LBall1 L1 lh pl pb1 nmb1 g1 bks1 n2 pk LK v2 LBall2 L2 m2 ->
  els_res LBall L lh pl pb nmb g bks (n1 + n2) pk LK v2 LBall2 L2 m2.
Proof.
  intros LBall L lh pl pb nmb g bks n1 n2 pk LK LBall1 L1 pb1 nmb1 g1 bks1 v2 LBall2 L2 m2 IT1 NM1 GR1 TK1 INK1 [KP1 KP2]
         (-> & pb2 & B2 & nmb2 & g2 & bks2 & REP2 & IT2 & NM2 & GR2 & TK2 & MC2 & INK2).
  split; [reflexivity|]. exists pb2, B2, nmb2, g2, bks2.
  split; [exact REP2|]. split; [lia|]. split; [lia|].
  split. { eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2)| lia| lia| lia]. }
  split; [| split; [exact MC2| exact INK2]].
  intros q QIN NT. apply TK2; [| exact (TK1 q QIN NT)].
  destruct (bptr_eqb q pk) eqn:EQ.
  { apply bptr_eqb_eq in EQ. subst q. left. apply in_map_iff. exists (pk, LK, 40). split; [reflexivity| exact INK1]. }
  assert (NPK : q <> pk) by (intros E; subst q; rewrite bptr_eqb_refl in EQ; discriminate).
  assert (NTT : ~ (q = pk \/ lh_T pl pb bks q)) by (intros [E|E]; [exact (NPK E)| exact (NT E)]).
  destruct QIN as [X|X].
  - left. apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. exact (KP1 b Hb NTT).
  - right. apply in_map_iff in X. destruct X as ([q0 nm0] & <- & Hq). cbn [fst] in NTT |- *. apply in_map_iff. exists (q0, nm0). split; [reflexivity| exact (KP2 q0 nm0 Hq NTT)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition err_load_ERR_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo)
         (bks : list (list (bptr * Z))) (pk : bptr) (LK lo Bd : Z),
  (3 * NBASE <= f)%nat -> els_room L nmb (Z.of_nat NBASE) ->
  cstate s LBall LB L m sp tp lo Bd ->
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks -> 0 <= nmb <= 8 * g_na g -> g_items g + Z.of_nat NBASE <= LH_KMAX ->
  rw_cells usegs m ERR_ONCE_CELL (err_statics LK lh) ->
  In (pk, LK, 40) LBall -> ~ lh_T pl pb bks pk -> rw_cells usegs m LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  lo <= bv_unsigned sp - ELE_STACK -> bv_unsigned sp mod 16 = 0 ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FZ_ERR_LOAD_ERR) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun q => q = pk \/ lh_T pl pb bks q) [] (3 * NBASE) (Z.of_nat NBASE) 1 (LHA_MAX + 8192)
           (els_res LBall L lh pl pb nmb g bks NBASE pk LK)).

Theorem err_load_ERR_spec : err_load_strings_stmt -> err_load_ERR_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ELS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lh pl pb B nmb g bks pk LK lo Bd
         Hf ROOM CST REP NMB ITEMS HC INK NTK MC SLO SPAL.
  unfold err_load_strings_stmt in ELS.
  pose proof CST as (HP & CO & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold ELE_STACK, ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_ERR_LOAD_ERR, ERR_ONCE_CELL, err_statics, NBASE in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (RHEAP_block_range_proof _ _ _ (pk, LK, 40) HP INK) as (LK0 & _ & _ & LKC & LKIMG). unfold blk_addr, blk_size in LK0, LKC, LKIMG. cbn [fst snd] in LK0, LKC, LKIMG.
  unfold mutex_cells in MC.
  pose proof T_run_once_done_proof as RO. unfold T_run_once_done_stmt in RO.
  destruct ROOM as (RA & RB & RC).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  cprefix. step. carve_frame 32%nat ST. do 3 step. step. do 4 step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] with ([C4 (Z_to_bv 64 2)] ++ [C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]) in HC;
    pose proof (proj1 (proj1 (proj1 (rw_cells_app usegs mm _ _ _) HC)) : ro_cells usegs mm 3334160 [C4 (Z_to_bv 64 2)]) as ONro;
    cbn [app] in HC end.
  calle (eapply RO with (lo := lo)); try lia.
  clear RO.
  step. step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. if_cases K1; zify_cond K1. { exfalso. revert K1. vm_compute. intros X. first [discriminate X| apply X; reflexivity]. }
  do 2 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  set (TT := fun q : bptr => q = pk \/ lh_T pl pb bks q).
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe TT [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  assert (REPa : lh_rep DVERR ma LBall L ERR_FNS lh pl pb B nmb g bks).
  { eapply (rep_over_lock s LBall m ma L lh pl pb B nmb g bks pk LK (bv_unsigned sp - 48) (bv_unsigned sp)); [exact HP| exact REP| exact INK| exact NTK| | exact WM| lia].
    eapply munch_weaken; [| exact MU]. intros xx Hxx. cbn [outside] in Hxx |- *. tauto. }
  assert (LOCKC : forall mm, rw_cells usegs mm 3334160 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] ->
                             rw_cells usegs mm ERR_LOCK_CELL [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]).
  { intros mm H. change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] with ([C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] ++ [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]) in H.
    exact (proj2 (proj1 (rw_cells_app usegs mm _ _ _) H)). }
  chere. eapply climpl_seq.
  { eapply ELS with (T := ERR_TAB1) (n := 43%nat) (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := nmb) (g := g) (bks := bks) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [lia| unfold els_room; lia| exact CSTa| exact REPa| exact NMB| lia| exact etab_base1| exact (or_introl trange_base1)| apply LOCKC; eassumption| exact INK| exact NTK| unfold mutex_cells; eassumption
      | rewrite unsigned_lit by lia; unfold ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| rewrite unsigned_lit by lia; lia| reflexivity| reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1c & CST1 & FRM1 & (-> & pb1 & B1 & nmb1 & g1 & bks1 & REP1 & IT1 & NMB1 & GR1 & TK1 & MC1 & INK1)).
  destruct RET1 as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & ->).
  cret_lit.
  pose proof FRM1 as (CFR1 & KPa & _).
  lazymatch goal with FRh : rw_cells _ ma (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(rewrite unsigned_lit by lia; lia)) as FR1 end.
  lazymatch goal with HCh : rw_cells _ ma 3334160 _ |- _ => i1_static CFR1 HCh HC1 end.
  assert (NTK1 : ~ lh_T pl pb1 bks1 pk) by (apply TK1; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INK]| exact NTK]).
  destruct (w_delta nmb nmb1 ltac:(lia)) as (WD1 & _).
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. do 2 step. step.
  chere. eapply climpl_seq.
  { eapply ELS with (T := ERR_TAB2) (n := 39%nat) (lh := lh) (pl := pl) (pb := pb1) (B := B1) (nmb := nmb1) (g := g1) (bks := bks1) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [lia| unfold els_room, cgrow in *; destruct GR1 as (G1a & G1b & G1c); lia| exact CST1| exact REP1| lia| lia| exact etab_base2| exact (or_introl trange_base2)| apply LOCKC; exact HC1| exact INK1| exact NTK1| exact MC1
      | rewrite unsigned_lit by lia; unfold ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| rewrite unsigned_lit by lia; lia| reflexivity| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2c & CST2 & FRM2 & RES2).
  destruct RET2 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & ->).
  cret_lit.
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(rewrite unsigned_lit by lia; lia)) as FR2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof (munch_refl (@nil (Z * Z)) m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  pose proof (els_res_compose LBall L lh pl pb nmb g bks 43 39 pk LK LBall1 L1 pb1 nmb1 g1 bks1 v2 LBall2 L2 m2 IT1 ltac:(lia) GR1 TK1 INK1 KPa RES2) as RES.
  destruct RES2 as (-> & _).
  cprefix. step. do 3 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
  chere. apply climpl_done.
  exists (Z_to_bv 64 1), m2, LBall2.
  pose proof RES as (_ & pbf & Bf & nmbf & gf & bksf & REPf & ITf & NMBf & GRf & _).
  pose proof (lh_geo_bounds gf (proj1 REPf)) as GBf.
  destruct (w_delta nmb nmbf ltac:(lia)) as (WF1 & WF2 & WF3 & WF4).
  pose proof (w_nonneg nmb) as (_ & _ & WN3).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { eapply cgrow_weaken; [exact GRf| | |]; unfold LHA_MAX; change (Z.of_nat (43 + 39)) with 82; change (Z.of_nat 82) with 82; lia. }
  split. { eapply (cstate_seg [] _ _ _ _ m2 m2 _ sp tp lo Bd (bv_unsigned sp)); [exact CST2| apply munch_refl| apply wmono_refl| exact MI2| apply Forall_nil| lia| lia| exact I| exact ST2| exact SPB]. }
  split; [| exact RES].
  eapply cframe_call; [eapply cframe_call; [exact FRa| exact FRM1| rewrite unsigned_lit by lia; lia| intros a X; exact X| intros q _ X; exact X]| exact FRM2| rewrite unsigned_lit by lia; lia| intros a X; exact X|].
  intros q QIN NT [E|E]; [apply NT; left; exact E|]. apply (TK1 q QIN); [intros X; apply NT; right; exact X| exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition err_load_const_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (T : Z) (n : nat) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo)
         (bks : list (list (bptr * Z))) (pk : bptr) (LK lo Bd : Z),
  (3 * (NBASE + n) <= f)%nat -> els_room L nmb (Z.of_nat (NBASE + n)) ->
  cstate s LBall LB L m sp tp lo Bd ->
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks -> 0 <= nmb <= 8 * g_na g -> g_items g + Z.of_nat (NBASE + n) <= LH_KMAX ->
  etab T n -> tread T n ->
  rw_cells usegs m ERR_ONCE_CELL (err_statics LK lh) ->
  In (pk, LK, 40) LBall -> ~ lh_T pl pb bks pk -> rw_cells usegs m LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  lo <= bv_unsigned sp - ELC_STACK -> bv_unsigned sp mod 16 = 0 -> T mod 8 = 0 -> a0 = Z_to_bv 64 T ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FZ_ERR_LOAD_CONST) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun q => q = pk \/ lh_T pl pb bks q) [] (3 * (NBASE + n)) (Z.of_nat (NBASE + n)) 1
           (LHA_MAX + 8192) (els_res LBall L lh pl pb nmb g bks (NBASE + n) pk LK)).

Theorem err_load_const_spec : err_load_ERR_stmt -> err_load_strings_stmt -> err_load_const_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ELE ELS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f T n lh pl pb B nmb g bks pk LK lo Bd
         Hf ROOM CST REP NMB ITEMS ETAB TR HC INK NTK MC SLO SPAL TAL ->.
  unfold err_load_strings_stmt in ELS. unfold err_load_ERR_stmt in ELE.
  pose proof CST as (HP & CO & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold ELC_STACK, ELE_STACK, ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_ERR_LOAD_CONST, ERR_ONCE_CELL, err_statics in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (RHEAP_block_range_proof _ _ _ (pk, LK, 40) HP INK) as (LK0 & _ & _ & LKC & LKIMG). unfold blk_addr, blk_size in LK0, LKC, LKIMG. cbn [fst snd] in LK0, LKC, LKIMG.
  unfold mutex_cells in MC.
  destruct ROOM as (RA & RB & RC). rewrite Nat2Z.inj_add in RA, ITEMS. unfold NBASE in *. change (Z.of_nat 82) with 82 in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  cprefix. step. carve_frame 32%nat ST. do 3 step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  set (TT := fun q : bptr => q = pk \/ lh_T pl pb bks q).
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe TT [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  assert (REPa : lh_rep DVERR ma LBall L ERR_FNS lh pl pb B nmb g bks).
  { eapply (rep_over_lock s LBall m ma L lh pl pb B nmb g bks pk LK (bv_unsigned sp - 32) (bv_unsigned sp)); [exact HP| exact REP| exact INK| exact NTK| | exact WM| lia].
    eapply munch_weaken; [| exact MU]. intros xx Hxx. cbn [outside] in Hxx |- *. tauto. }
  assert (LOCKC : forall mm, rw_cells usegs mm 3334160 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] ->
                             rw_cells usegs mm ERR_LOCK_CELL [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]).
  { intros mm H. change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] with ([C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] ++ [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]) in H.
    exact (proj2 (proj1 (rw_cells_app usegs mm _ _ _) H)). }
  chere. eapply climpl_seq.
  { eapply ELE with (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := nmb) (g := g) (bks := bks) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [unfold NBASE; lia| unfold els_room, NBASE; change (Z.of_nat 82) with 82; lia| exact CSTa| exact REPa| exact NMB| unfold NBASE; change (Z.of_nat 82) with 82; lia
      | unfold ERR_ONCE_CELL, err_statics; eassumption| exact INK| exact NTK| unfold mutex_cells; eassumption
      | rewrite unsigned_lit by lia; unfold ELE_STACK, ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| rewrite unsigned_lit by lia; lia]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1c & CST1 & FRM1 & (-> & pb1 & B1 & nmb1 & g1 & bks1 & REP1 & IT1 & NMB1 & GR1 & TK1 & MC1 & INK1)).
  destruct RET1 as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. unfold NBASE in *. change (Z.of_nat 82) with 82 in *.
  pose proof FRM1 as (CFR1 & KPa & _).
  lazymatch goal with FRh : rw_cells _ ma (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(rewrite unsigned_lit by lia; lia)) as FR1 end.
  lazymatch goal with HCh : rw_cells _ ma 3334160 _ |- _ => i1_static CFR1 HCh HC1 end.
  assert (NTK1 : ~ lh_T pl pb1 bks1 pk) by (apply TK1; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INK]| exact NTK]).
  destruct (w_delta nmb nmb1 ltac:(lia)) as (WD1 & _).
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step.
  chere. eapply climpl_seq.
  { eapply ELS with (T := T) (n := n) (lh := lh) (pl := pl) (pb := pb1) (B := B1) (nmb := nmb1) (g := g1) (bks := bks1) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [lia| unfold els_room, cgrow in *; destruct GR1 as (G1a & G1b & G1c); lia| exact CST1| exact REP1| lia| lia| exact ETAB| exact TR| apply LOCKC; exact HC1| exact INK1| exact NTK1| exact MC1
      | rewrite unsigned_lit by lia; unfold ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| rewrite unsigned_lit by lia; lia| exact TAL| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2c & CST2 & FRM2 & RES2).
  destruct RET2 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & ->).
  cret_lit.
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(rewrite unsigned_lit by lia; lia)) as FR2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof (munch_refl (@nil (Z * Z)) m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  pose proof (els_res_compose LBall L lh pl pb nmb g bks 82 n pk LK LBall1 L1 pb1 nmb1 g1 bks1 v2 LBall2 L2 m2 IT1 ltac:(lia) GR1 TK1 INK1 KPa RES2) as RES.
  destruct RES2 as (-> & _).
  cprefix. step. do 3 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
  chere. apply climpl_done.
  exists (Z_to_bv 64 1), m2, LBall2.
  pose proof RES as (_ & pbf & Bf & nmbf & gf & bksf & REPf & ITf & NMBf & GRf & _).
  pose proof (lh_geo_bounds gf (proj1 REPf)) as GBf.
  destruct (w_delta nmb nmbf ltac:(lia)) as (WF1 & WF2 & WF3 & WF4).
  pose proof (w_nonneg nmb) as (_ & _ & WN3).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { eapply cgrow_weaken; [exact GRf| | |]; unfold LHA_MAX; lia. }
  split. { eapply (cstate_seg [] _ _ _ _ m2 m2 _ sp tp lo Bd (bv_unsigned sp)); [exact CST2| apply munch_refl| apply wmono_refl| exact MI2| apply Forall_nil| lia| lia| exact I| exact ST2| exact SPB]. }
  split; [| exact RES].
  eapply cframe_call; [eapply cframe_call; [exact FRa| exact FRM1| rewrite unsigned_lit by lia; lia| intros a X; exact X| intros q _ X; exact X]| exact FRM2| rewrite unsigned_lit by lia; lia| intros a X; exact X|].
  intros q QIN NT [E|E]; [apply NT; left; exact E|]. apply (TK1 q QIN); [intros X; apply NT; right; exact X| exact E].
Qed.
End WithCeiling0.
