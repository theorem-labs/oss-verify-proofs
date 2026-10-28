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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_kit_ra Fz_M_realloc Fz_I1_insert Fz_I1_insert1 Fz_cimg_rom. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_T_once Fz_I1_load Fz_I1_retrieve Fz_I1_errload Fz_I1_reason Fz_I1_stubs Fz_I1_stubs_a Fz_I1_stubs_b Fz_I1_stubs_c Fz_I1_stubs_z Fz_M_zalloc Fz_M_calloc Fz_I1_new Fz_T_lock_new Fz_I3_base Fz_T_ekit Fz_I1_first Fz_I1_efirst.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_ERR_LOAD_CRYPTO : Z := 0x2aca7c.
Definition NCRYPTO : nat := 4318.
Definition CRS_STACK : Z := 16 + ELF_STACK.

(* [comment removed for export] *)
Definition crypto_res (LBall : list block) (L : @clist bptr) (oldcb : word) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (pk pl pb : bptr) (LK lh B : Z),
    els_res ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall) ((pb, 128) :: (pl, 104) :: (pk, 40) :: L) lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) NCRYPTO pk LK
            v LBall' L' m'
    /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> q <> pk /\ q <> pl /\ q <> pb) /\ pk <> pl /\ pk <> pb
    /\ cgrow L ((pb, 128) :: (pl, 104) :: (pk, 40) :: L) 3 0 0
    /\ rw_cells usegs m' ERR_ONCE_CELL (err_statics LK lh)
    /\ rw_cells usegs m' (RATP + -96) [C8 oldcb].

Definition err_load_crypto_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z) (od r0 l0 h0 oldcb : word),
  (3 + 3 * NCRYPTO <= f)%nat -> croom L (3 + Z.of_nat NCRYPTO) 2 (2 * (LHA_MAX + 8192)) ->
  cstate s LBall LB L m sp tp lo Bd ->
  rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] -> rw_cells usegs m (IC_S + 96) [C8 od] ->
  rw_cells usegs m ERR_ONCE_CELL [C4 (Z_to_bv 64 0); C4 r0; C8 l0; C8 h0] ->
  rw_cells usegs m (RATP + -96) [C8 oldcb] ->
  lo <= bv_unsigned sp - CRS_STACK -> bv_unsigned sp mod 16 = 0 ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FZ_ERR_LOAD_CRYPTO) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun _ => False) ELF_W (3 + 3 * NCRYPTO) (3 + Z.of_nat NCRYPTO) 1
           (LHA_MAX + 8192) (crypto_res LBall L oldcb)).

Theorem err_load_crypto_spec : err_load_ERR_first_stmt -> err_load_const_stmt -> err_load_crypto_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ELF ELC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd od r0 l0 h0 oldcb
         Hf ROOM CST STOP ONCE OD HC CBC SLO SA.
  unfold err_load_ERR_first_stmt in ELF.
  pose proof CST as (HP & CO & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold CRS_STACK, ELF_STACK, STUB_STACK, ELC_STACK, ELE_STACK, ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_ERR_LOAD_CRYPTO, ERR_ONCE_CELL, RATP, IC_S, NCRYPTO, NBASE in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  change (3333664 + 8) with 3333672 in STOP. change (3333664 + 32) with 0x32de40 in ONCE. change (3333664 + 96) with 3333760 in OD.
  destruct ROOM as (RA & RB & RC). change (Z.of_nat 4318) with 4318 in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  cprefix. step. carve_frame 16%nat ST. do 3 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  set (TT := fun _ : bptr => False).
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -16)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe TT ELF_W (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  chere. eapply climpl_seq.
  { eapply ELF with (lo := lo) (Bd := Bd) (od := od) (r0 := r0) (l0 := l0) (h0 := h0) (oldcb := oldcb);
      [unfold NBASE; lia| unfold croom, NBASE; change (Z.of_nat 82) with 82; lia| exact CSTa| exact STOP| exact ONCE| exact OD
      | unfold ERR_ONCE_CELL; exact HC| unfold RATP; exact CBC
      | rewrite unsigned_lit by lia; unfold ELF_STACK; lia| rewrite unsigned_lit by lia; lia]. }
  intros f0 L0 st0 ms0 (v0 & m0 & LBall0 & RET0 & FU0 & _ & CST0 & FRMc & (pk & pl & pb & LK & lh & B & RES0 & FRESH & NEKL & NEKB & GRE & KPE0 & HCE & CBE)).
  destruct RET0 as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & ->).
  destruct RES0 as (-> & RES0).
  cret_lit. unfold NBASE in *.
  pose proof FRMc as (CFRc & _).
  lazymatch goal with FRh : rw_cells _ ma (bv_unsigned sp + -16) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FRh ltac:(rewrite unsigned_lit by lia; lia)) as FR0 end.
  unfold ERR_ONCE_CELL, err_statics in HCE. rename HCE into HC0. unfold RATP in CBE. rename CBE into CB0.
  assert (FRM0 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st0 LBall0 L0 m0).
  { eapply cframe_call; [exact FRa| exact FRMc| rewrite unsigned_lit by lia; lia| intros a X; exact X| intros q _ X; exact X]. }
  clear CFRc FRMc CSTa FRa.
  set (LBallE := (pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall) in *.
  set (LE := (pb, 128) :: (pl, 104) :: (pk, 40) :: L) in *.
  assert (INKE : In (pk, LK, 40) LBallE) by (subst LBallE; right; right; left; reflexivity).
  assert (NTKE : ~ lh_T pl pb (repeat [] 16) pk) by (unfold lh_T; cbn [repeat concat app map]; intros [E|[E|[]]]; [exact (NEKL E)| exact (NEKB E)]).
  assert (ENTRYQ : forall q, In q (map blk_id LBall) \/ In q (map fst L) -> (In q (map blk_id LBallE) \/ In q (map fst LE)) /\ ((q = pk \/ lh_T pl pb (repeat [] 16) q) -> False)).
  { intros q QIN. destruct (FRESH q QIN) as (N1 & N2 & N3). split.
    - subst LBallE LE. destruct QIN as [X|X]; [left| right]; cbn [map]; do 3 right; exact X.
    - unfold lh_T. cbn [repeat concat app map]. intros [E|[E|[E|[]]]]; [exact (N1 E)| exact (N2 E)| exact (N3 E)]. }
  assert (NMB : 0 <= 128 <= 8 * 16) by lia.
  destruct (wA_small 128 ltac:(unfold TIER_A_MAX; lia)) as (WS1 & WS2 & WS3).
  assert (ITEMS : 0 + 4318 <= LH_KMAX) by (unfold LH_KMAX; lia).
  destruct GRE as (GEa & GEb & GEc).
  assert (RESc0 : els_res LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 82 pk LK (Z_to_bv 64 1) LBall0 L0 m0) by (split; [reflexivity| exact RES0]). clear RES0.
  assert (FUc0 : Z.of_nat f - 249 <= Z.of_nat f0) by (clear - FU0; lia). clear FU0.
  assert (SLOc : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) - STUB_STACK)
    by (rewrite unsigned_lit by lia; unfold STUB_STACK, ELC_STACK, ELE_STACK, ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia).
  assert (SPc : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) <= bv_unsigned sp) by (rewrite unsigned_lit by lia; lia).
  assert (SPd : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) <= bv_unsigned sp + -16) by (rewrite unsigned_lit by lia; lia).
  assert (SAc : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) mod 16 = 0) by (rewrite unsigned_lit by lia; lia).
  pose proof (munch_refl (@nil (Z * Z)) m0) as MU0. pose proof (wmono_refl usegs m0) as WM0.
  cprefix. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc0 as (_ & pb0 & B0 & nmb0 & g0 & bks0 & REP0 & IT0 & NM0 & GR0 & TK0 & MC0 & INK0).
  cbn [g_items g_na] in IT0, NM0.
  assert (NTK0 : ~ lh_T pl pb0 bks0 pk) by (apply TK0; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb0 ltac:(lia)) as (WDa0 & WDb0 & WDc0 & WDd0).
  pose proof (lh_geo_bounds g0 (proj1 REP0)) as GB0.
  pose proof GR0 as GRu0. unfold cgrow in GRu0.
  assert (PF : (3 * (NBASE + 22) <= f0)%nat) by (clear - Hf FUc0; unfold NBASE; lia).
  assert (PR : els_room L0 nmb0 (Z.of_nat (NBASE + 22))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 22)) with 104. clear - RA RB RC GEa GEb GEc GRu0 WDa0 WDb0 WDc0 WDd0 NM0 NMB GB0 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb0 <= 8 * g_na g0) by (clear - NM0 NMB; lia).
  assert (PI : g_items g0 + Z.of_nat (NBASE + 22) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 22)) with 104; clear - IT0 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_s01 ELC) with (lh := lh) (pl := pl) (pb := pb0) (B := B0) (nmb := nmb0) (g := g0) (bks := bks0) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST0| exact REP0| exact PN| exact PI| exact HC0| exact INK0| exact NTK0| exact MC0| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & _ & CST1 & FRMc & RESn).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU1. assert (FUc1 : Z.of_nat f - 561 <= Z.of_nat f1) by (clear - FUc0 FU1; lia). clear FUc0 FU1.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR0 SPd) as FR1.
  i1_static CFRc HC0 HC1. i1_static CFRc CB0 CB1.
  assert (FRM1 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st1 LBall1 L1 m1).
  { eapply cframe_call; [exact FRM0| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK0 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE1 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall1 L1).
  { eapply ckeep_call; [exact KPE0| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK0 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 82 (NBASE + 22) pk LK LBall0 L0 pb0 nmb0 g0 bks0 v1 LBall1 L1 m1 IT0 ltac:(clear - NM0; lia) GR0 TK0 INK0 KPE0 RESn) as RESc1.
  change (82 + (NBASE + 22))%nat with 186%nat in RESc1. destruct RESn as (-> & _).
  clear CFRc FRMc REP0 IT0 NM0 GR0 GRu0 TK0 MC0 INK0 NTK0 WDa0 WDb0 WDc0 WDd0 GB0 KPE0 CST0 FRM0 RESc0 FR0 HC0 CB0.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc1 as (_ & pb1 & B1 & nmb1 & g1 & bks1 & REP1 & IT1 & NM1 & GR1 & TK1 & MC1 & INK1).
  cbn [g_items g_na] in IT1, NM1.
  assert (NTK1 : ~ lh_T pl pb1 bks1 pk) by (apply TK1; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb1 ltac:(lia)) as (WDa1 & WDb1 & WDc1 & WDd1).
  pose proof (lh_geo_bounds g1 (proj1 REP1)) as GB1.
  pose proof GR1 as GRu1. unfold cgrow in GRu1.
  assert (PF : (3 * (NBASE + 81) <= f1)%nat) by (clear - Hf FUc1; unfold NBASE; lia).
  assert (PR : els_room L1 nmb1 (Z.of_nat (NBASE + 81))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 81)) with 163. clear - RA RB RC GEa GEb GEc GRu1 WDa1 WDb1 WDc1 WDd1 NM1 NMB GB1 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb1 <= 8 * g_na g1) by (clear - NM1 NMB; lia).
  assert (PI : g_items g1 + Z.of_nat (NBASE + 81) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 81)) with 163; clear - IT1 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_2675dc ELC) with (lh := lh) (pl := pl) (pb := pb1) (B := B1) (nmb := nmb1) (g := g1) (bks := bks1) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST1| exact REP1| exact PN| exact PI| exact HC1| exact INK1| exact NTK1| exact MC1| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & _ & CST2 & FRMc & RESn).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU2. assert (FUc2 : Z.of_nat f - 1050 <= Z.of_nat f2) by (clear - FUc1 FU2; lia). clear FUc1 FU2.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR1 SPd) as FR2.
  i1_static CFRc HC1 HC2. i1_static CFRc CB1 CB2.
  assert (FRM2 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st2 LBall2 L2 m2).
  { eapply cframe_call; [exact FRM1| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK1 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE2 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall2 L2).
  { eapply ckeep_call; [exact KPE1| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK1 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 186 (NBASE + 81) pk LK LBall1 L1 pb1 nmb1 g1 bks1 v2 LBall2 L2 m2 IT1 ltac:(clear - NM1; lia) GR1 TK1 INK1 KPE1 RESn) as RESc2.
  change (186 + (NBASE + 81))%nat with 349%nat in RESc2. destruct RESn as (-> & _).
  clear CFRc FRMc REP1 IT1 NM1 GR1 GRu1 TK1 MC1 INK1 NTK1 WDa1 WDb1 WDc1 WDd1 GB1 KPE1 CST1 FRM1 RESc1 FR1 HC1 CB1.
  pose proof (munch_refl (@nil (Z * Z)) m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  cprefix. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc2 as (_ & pb2 & B2 & nmb2 & g2 & bks2 & REP2 & IT2 & NM2 & GR2 & TK2 & MC2 & INK2).
  cbn [g_items g_na] in IT2, NM2.
  assert (NTK2 : ~ lh_T pl pb2 bks2 pk) by (apply TK2; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb2 ltac:(lia)) as (WDa2 & WDb2 & WDc2 & WDd2).
  pose proof (lh_geo_bounds g2 (proj1 REP2)) as GB2.
  pose proof GR2 as GRu2. unfold cgrow in GRu2.
  assert (PF : (3 * (NBASE + 31) <= f2)%nat) by (clear - Hf FUc2; unfold NBASE; lia).
  assert (PR : els_room L2 nmb2 (Z.of_nat (NBASE + 31))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 31)) with 113. clear - RA RB RC GEa GEb GEc GRu2 WDa2 WDb2 WDc2 WDd2 NM2 NMB GB2 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb2 <= 8 * g_na g2) by (clear - NM2 NMB; lia).
  assert (PI : g_items g2 + Z.of_nat (NBASE + 31) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 31)) with 113; clear - IT2 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267624 ELC) with (lh := lh) (pl := pl) (pb := pb2) (B := B2) (nmb := nmb2) (g := g2) (bks := bks2) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST2| exact REP2| exact PN| exact PI| exact HC2| exact INK2| exact NTK2| exact MC2| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f3 L3 st3 ms3 (v3 & m3 & LBall3 & RET3 & FU3 & _ & CST3 & FRMc & RESn).
  destruct RET3 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU3. assert (FUc3 : Z.of_nat f - 1389 <= Z.of_nat f3) by (clear - FUc2 FU3; lia). clear FUc2 FU3.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR2 SPd) as FR3.
  i1_static CFRc HC2 HC3. i1_static CFRc CB2 CB3.
  assert (FRM3 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st3 LBall3 L3 m3).
  { eapply cframe_call; [exact FRM2| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK2 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE3 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall3 L3).
  { eapply ckeep_call; [exact KPE2| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK2 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 349 (NBASE + 31) pk LK LBall2 L2 pb2 nmb2 g2 bks2 v3 LBall3 L3 m3 IT2 ltac:(clear - NM2; lia) GR2 TK2 INK2 KPE2 RESn) as RESc3.
  change (349 + (NBASE + 31))%nat with 462%nat in RESc3. destruct RESn as (-> & _).
  clear CFRc FRMc REP2 IT2 NM2 GR2 GRu2 TK2 MC2 INK2 NTK2 WDa2 WDb2 WDc2 WDd2 GB2 KPE2 CST2 FRM2 RESc2 FR2 HC2 CB2.
  pose proof (munch_refl (@nil (Z * Z)) m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc3 as (_ & pb3 & B3 & nmb3 & g3 & bks3 & REP3 & IT3 & NM3 & GR3 & TK3 & MC3 & INK3).
  cbn [g_items g_na] in IT3, NM3.
  assert (NTK3 : ~ lh_T pl pb3 bks3 pk) by (apply TK3; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb3 ltac:(lia)) as (WDa3 & WDb3 & WDc3 & WDd3).
  pose proof (lh_geo_bounds g3 (proj1 REP3)) as GB3.
  pose proof GR3 as GRu3. unfold cgrow in GRu3.
  assert (PF : (3 * (NBASE + 125) <= f3)%nat) by (clear - Hf FUc3; unfold NBASE; lia).
  assert (PR : els_room L3 nmb3 (Z.of_nat (NBASE + 125))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 125)) with 207. clear - RA RB RC GEa GEb GEc GRu3 WDa3 WDb3 WDc3 WDd3 NM3 NMB GB3 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb3 <= 8 * g_na g3) by (clear - NM3 NMB; lia).
  assert (PI : g_items g3 + Z.of_nat (NBASE + 125) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 125)) with 207; clear - IT3 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_26766c ELC) with (lh := lh) (pl := pl) (pb := pb3) (B := B3) (nmb := nmb3) (g := g3) (bks := bks3) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST3| exact REP3| exact PN| exact PI| exact HC3| exact INK3| exact NTK3| exact MC3| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f4 L4 st4 ms4 (v4 & m4 & LBall4 & RET4 & FU4 & _ & CST4 & FRMc & RESn).
  destruct RET4 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU4. assert (FUc4 : Z.of_nat f - 2010 <= Z.of_nat f4) by (clear - FUc3 FU4; lia). clear FUc3 FU4.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR3 SPd) as FR4.
  i1_static CFRc HC3 HC4. i1_static CFRc CB3 CB4.
  assert (FRM4 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st4 LBall4 L4 m4).
  { eapply cframe_call; [exact FRM3| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK3 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE4 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall4 L4).
  { eapply ckeep_call; [exact KPE3| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK3 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 462 (NBASE + 125) pk LK LBall3 L3 pb3 nmb3 g3 bks3 v4 LBall4 L4 m4 IT3 ltac:(clear - NM3; lia) GR3 TK3 INK3 KPE3 RESn) as RESc4.
  change (462 + (NBASE + 125))%nat with 669%nat in RESc4. destruct RESn as (-> & _).
  clear CFRc FRMc REP3 IT3 NM3 GR3 GRu3 TK3 MC3 INK3 NTK3 WDa3 WDb3 WDc3 WDd3 GB3 KPE3 CST3 FRM3 RESc3 FR3 HC3 CB3.
  pose proof (munch_refl (@nil (Z * Z)) m4) as MU4. pose proof (wmono_refl usegs m4) as WM4.
  cprefix. step. if_cases K4; zify_cond K4. { exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc4 as (_ & pb4 & B4 & nmb4 & g4 & bks4 & REP4 & IT4 & NM4 & GR4 & TK4 & MC4 & INK4).
  cbn [g_items g_na] in IT4, NM4.
  assert (NTK4 : ~ lh_T pl pb4 bks4 pk) by (apply TK4; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb4 ltac:(lia)) as (WDa4 & WDb4 & WDc4 & WDd4).
  pose proof (lh_geo_bounds g4 (proj1 REP4)) as GB4.
  pose proof GR4 as GRu4. unfold cgrow in GRu4.
  assert (PF : (3 * (NBASE + 0) <= f4)%nat) by (clear - Hf FUc4; unfold NBASE; lia).
  assert (PR : els_room L4 nmb4 (Z.of_nat (NBASE + 0))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 0)) with 82. clear - RA RB RC GEa GEb GEc GRu4 WDa4 WDb4 WDc4 WDd4 NM4 NMB GB4 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb4 <= 8 * g_na g4) by (clear - NM4 NMB; lia).
  assert (PI : g_items g4 + Z.of_nat (NBASE + 0) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 0)) with 82; clear - IT4 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_2676b4 ELC) with (lh := lh) (pl := pl) (pb := pb4) (B := B4) (nmb := nmb4) (g := g4) (bks := bks4) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST4| exact REP4| exact PN| exact PI| exact HC4| exact INK4| exact NTK4| exact MC4| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f5 L5 st5 ms5 (v5 & m5 & LBall5 & RET5 & FU5 & _ & CST5 & FRMc & RESn).
  destruct RET5 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU5. assert (FUc5 : Z.of_nat f - 2256 <= Z.of_nat f5) by (clear - FUc4 FU5; lia). clear FUc4 FU5.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR4 SPd) as FR5.
  i1_static CFRc HC4 HC5. i1_static CFRc CB4 CB5.
  assert (FRM5 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st5 LBall5 L5 m5).
  { eapply cframe_call; [exact FRM4| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK4 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE5 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall5 L5).
  { eapply ckeep_call; [exact KPE4| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK4 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 669 (NBASE + 0) pk LK LBall4 L4 pb4 nmb4 g4 bks4 v5 LBall5 L5 m5 IT4 ltac:(clear - NM4; lia) GR4 TK4 INK4 KPE4 RESn) as RESc5.
  change (669 + (NBASE + 0))%nat with 751%nat in RESc5. destruct RESn as (-> & _).
  clear CFRc FRMc REP4 IT4 NM4 GR4 GRu4 TK4 MC4 INK4 NTK4 WDa4 WDb4 WDc4 WDd4 GB4 KPE4 CST4 FRM4 RESc4 FR4 HC4 CB4.
  pose proof (munch_refl (@nil (Z * Z)) m5) as MU5. pose proof (wmono_refl usegs m5) as WM5.
  cprefix. step. if_cases K5; zify_cond K5. { exfalso. rewrite ?unsigned_lit in K5 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc5 as (_ & pb5 & B5 & nmb5 & g5 & bks5 & REP5 & IT5 & NM5 & GR5 & TK5 & MC5 & INK5).
  cbn [g_items g_na] in IT5, NM5.
  assert (NTK5 : ~ lh_T pl pb5 bks5 pk) by (apply TK5; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb5 ltac:(lia)) as (WDa5 & WDb5 & WDc5 & WDd5).
  pose proof (lh_geo_bounds g5 (proj1 REP5)) as GB5.
  pose proof GR5 as GRu5. unfold cgrow in GRu5.
  assert (PF : (3 * (NBASE + 3) <= f5)%nat) by (clear - Hf FUc5; unfold NBASE; lia).
  assert (PR : els_room L5 nmb5 (Z.of_nat (NBASE + 3))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 3)) with 85. clear - RA RB RC GEa GEb GEc GRu5 WDa5 WDb5 WDc5 WDd5 NM5 NMB GB5 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb5 <= 8 * g_na g5) by (clear - NM5 NMB; lia).
  assert (PI : g_items g5 + Z.of_nat (NBASE + 3) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 3)) with 85; clear - IT5 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_2676f8 ELC) with (lh := lh) (pl := pl) (pb := pb5) (B := B5) (nmb := nmb5) (g := g5) (bks := bks5) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST5| exact REP5| exact PN| exact PI| exact HC5| exact INK5| exact NTK5| exact MC5| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f6 L6 st6 ms6 (v6 & m6 & LBall6 & RET6 & FU6 & _ & CST6 & FRMc & RESn).
  destruct RET6 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU6. assert (FUc6 : Z.of_nat f - 2511 <= Z.of_nat f6) by (clear - FUc5 FU6; lia). clear FUc5 FU6.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR5 SPd) as FR6.
  i1_static CFRc HC5 HC6. i1_static CFRc CB5 CB6.
  assert (FRM6 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st6 LBall6 L6 m6).
  { eapply cframe_call; [exact FRM5| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK5 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE6 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall6 L6).
  { eapply ckeep_call; [exact KPE5| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK5 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 751 (NBASE + 3) pk LK LBall5 L5 pb5 nmb5 g5 bks5 v6 LBall6 L6 m6 IT5 ltac:(clear - NM5; lia) GR5 TK5 INK5 KPE5 RESn) as RESc6.
  change (751 + (NBASE + 3))%nat with 836%nat in RESc6. destruct RESn as (-> & _).
  clear CFRc FRMc REP5 IT5 NM5 GR5 GRu5 TK5 MC5 INK5 NTK5 WDa5 WDb5 WDc5 WDd5 GB5 KPE5 CST5 FRM5 RESc5 FR5 HC5 CB5.
  pose proof (munch_refl (@nil (Z * Z)) m6) as MU6. pose proof (wmono_refl usegs m6) as WM6.
  cprefix. step. if_cases K6; zify_cond K6. { exfalso. rewrite ?unsigned_lit in K6 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc6 as (_ & pb6 & B6 & nmb6 & g6 & bks6 & REP6 & IT6 & NM6 & GR6 & TK6 & MC6 & INK6).
  cbn [g_items g_na] in IT6, NM6.
  assert (NTK6 : ~ lh_T pl pb6 bks6 pk) by (apply TK6; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb6 ltac:(lia)) as (WDa6 & WDb6 & WDc6 & WDd6).
  pose proof (lh_geo_bounds g6 (proj1 REP6)) as GB6.
  pose proof GR6 as GRu6. unfold cgrow in GRu6.
  assert (PF : (3 * (NBASE + 34) <= f6)%nat) by (clear - Hf FUc6; unfold NBASE; lia).
  assert (PR : els_room L6 nmb6 (Z.of_nat (NBASE + 34))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 34)) with 116. clear - RA RB RC GEa GEb GEc GRu6 WDa6 WDb6 WDc6 WDd6 NM6 NMB GB6 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb6 <= 8 * g_na g6) by (clear - NM6 NMB; lia).
  assert (PI : g_items g6 + Z.of_nat (NBASE + 34) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 34)) with 116; clear - IT6 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267740 ELC) with (lh := lh) (pl := pl) (pb := pb6) (B := B6) (nmb := nmb6) (g := g6) (bks := bks6) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST6| exact REP6| exact PN| exact PI| exact HC6| exact INK6| exact NTK6| exact MC6| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f7 L7 st7 ms7 (v7 & m7 & LBall7 & RET7 & FU7 & _ & CST7 & FRMc & RESn).
  destruct RET7 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU7. assert (FUc7 : Z.of_nat f - 2859 <= Z.of_nat f7) by (clear - FUc6 FU7; lia). clear FUc6 FU7.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR6 SPd) as FR7.
  i1_static CFRc HC6 HC7. i1_static CFRc CB6 CB7.
  assert (FRM7 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st7 LBall7 L7 m7).
  { eapply cframe_call; [exact FRM6| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK6 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE7 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall7 L7).
  { eapply ckeep_call; [exact KPE6| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK6 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 836 (NBASE + 34) pk LK LBall6 L6 pb6 nmb6 g6 bks6 v7 LBall7 L7 m7 IT6 ltac:(clear - NM6; lia) GR6 TK6 INK6 KPE6 RESn) as RESc7.
  change (836 + (NBASE + 34))%nat with 952%nat in RESc7. destruct RESn as (-> & _).
  clear CFRc FRMc REP6 IT6 NM6 GR6 GRu6 TK6 MC6 INK6 NTK6 WDa6 WDb6 WDc6 WDd6 GB6 KPE6 CST6 FRM6 RESc6 FR6 HC6 CB6.
  pose proof (munch_refl (@nil (Z * Z)) m7) as MU7. pose proof (wmono_refl usegs m7) as WM7.
  cprefix. step. if_cases K7; zify_cond K7. { exfalso. rewrite ?unsigned_lit in K7 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc7 as (_ & pb7 & B7 & nmb7 & g7 & bks7 & REP7 & IT7 & NM7 & GR7 & TK7 & MC7 & INK7).
  cbn [g_items g_na] in IT7, NM7.
  assert (NTK7 : ~ lh_T pl pb7 bks7 pk) by (apply TK7; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb7 ltac:(lia)) as (WDa7 & WDb7 & WDc7 & WDd7).
  pose proof (lh_geo_bounds g7 (proj1 REP7)) as GB7.
  pose proof GR7 as GRu7. unfold cgrow in GRu7.
  assert (PF : (3 * (NBASE + 16) <= f7)%nat) by (clear - Hf FUc7; unfold NBASE; lia).
  assert (PR : els_room L7 nmb7 (Z.of_nat (NBASE + 16))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 16)) with 98. clear - RA RB RC GEa GEb GEc GRu7 WDa7 WDb7 WDc7 WDd7 NM7 NMB GB7 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb7 <= 8 * g_na g7) by (clear - NM7 NMB; lia).
  assert (PI : g_items g7 + Z.of_nat (NBASE + 16) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 16)) with 98; clear - IT7 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267788 ELC) with (lh := lh) (pl := pl) (pb := pb7) (B := B7) (nmb := nmb7) (g := g7) (bks := bks7) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST7| exact REP7| exact PN| exact PI| exact HC7| exact INK7| exact NTK7| exact MC7| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f8 L8 st8 ms8 (v8 & m8 & LBall8 & RET8 & FU8 & _ & CST8 & FRMc & RESn).
  destruct RET8 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU8. assert (FUc8 : Z.of_nat f - 3153 <= Z.of_nat f8) by (clear - FUc7 FU8; lia). clear FUc7 FU8.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR7 SPd) as FR8.
  i1_static CFRc HC7 HC8. i1_static CFRc CB7 CB8.
  assert (FRM8 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st8 LBall8 L8 m8).
  { eapply cframe_call; [exact FRM7| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK7 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE8 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall8 L8).
  { eapply ckeep_call; [exact KPE7| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK7 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 952 (NBASE + 16) pk LK LBall7 L7 pb7 nmb7 g7 bks7 v8 LBall8 L8 m8 IT7 ltac:(clear - NM7; lia) GR7 TK7 INK7 KPE7 RESn) as RESc8.
  change (952 + (NBASE + 16))%nat with 1050%nat in RESc8. destruct RESn as (-> & _).
  clear CFRc FRMc REP7 IT7 NM7 GR7 GRu7 TK7 MC7 INK7 NTK7 WDa7 WDb7 WDc7 WDd7 GB7 KPE7 CST7 FRM7 RESc7 FR7 HC7 CB7.
  pose proof (munch_refl (@nil (Z * Z)) m8) as MU8. pose proof (wmono_refl usegs m8) as WM8.
  cprefix. step. if_cases K8; zify_cond K8. { exfalso. rewrite ?unsigned_lit in K8 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc8 as (_ & pb8 & B8 & nmb8 & g8 & bks8 & REP8 & IT8 & NM8 & GR8 & TK8 & MC8 & INK8).
  cbn [g_items g_na] in IT8, NM8.
  assert (NTK8 : ~ lh_T pl pb8 bks8 pk) by (apply TK8; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb8 ltac:(lia)) as (WDa8 & WDb8 & WDc8 & WDd8).
  pose proof (lh_geo_bounds g8 (proj1 REP8)) as GB8.
  pose proof GR8 as GRu8. unfold cgrow in GRu8.
  assert (PF : (3 * (NBASE + 47) <= f8)%nat) by (clear - Hf FUc8; unfold NBASE; lia).
  assert (PR : els_room L8 nmb8 (Z.of_nat (NBASE + 47))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 47)) with 129. clear - RA RB RC GEa GEb GEc GRu8 WDa8 WDb8 WDc8 WDd8 NM8 NMB GB8 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb8 <= 8 * g_na g8) by (clear - NM8 NMB; lia).
  assert (PI : g_items g8 + Z.of_nat (NBASE + 47) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 47)) with 129; clear - IT8 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_2677d0 ELC) with (lh := lh) (pl := pl) (pb := pb8) (B := B8) (nmb := nmb8) (g := g8) (bks := bks8) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST8| exact REP8| exact PN| exact PI| exact HC8| exact INK8| exact NTK8| exact MC8| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f9 L9 st9 ms9 (v9 & m9 & LBall9 & RET9 & FU9 & _ & CST9 & FRMc & RESn).
  destruct RET9 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU9. assert (FUc9 : Z.of_nat f - 3540 <= Z.of_nat f9) by (clear - FUc8 FU9; lia). clear FUc8 FU9.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR8 SPd) as FR9.
  i1_static CFRc HC8 HC9. i1_static CFRc CB8 CB9.
  assert (FRM9 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st9 LBall9 L9 m9).
  { eapply cframe_call; [exact FRM8| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK8 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE9 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall9 L9).
  { eapply ckeep_call; [exact KPE8| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK8 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 1050 (NBASE + 47) pk LK LBall8 L8 pb8 nmb8 g8 bks8 v9 LBall9 L9 m9 IT8 ltac:(clear - NM8; lia) GR8 TK8 INK8 KPE8 RESn) as RESc9.
  change (1050 + (NBASE + 47))%nat with 1179%nat in RESc9. destruct RESn as (-> & _).
  clear CFRc FRMc REP8 IT8 NM8 GR8 GRu8 TK8 MC8 INK8 NTK8 WDa8 WDb8 WDc8 WDd8 GB8 KPE8 CST8 FRM8 RESc8 FR8 HC8 CB8.
  pose proof (munch_refl (@nil (Z * Z)) m9) as MU9. pose proof (wmono_refl usegs m9) as WM9.
  cprefix. step. if_cases K9; zify_cond K9. { exfalso. rewrite ?unsigned_lit in K9 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc9 as (_ & pb9 & B9 & nmb9 & g9 & bks9 & REP9 & IT9 & NM9 & GR9 & TK9 & MC9 & INK9).
  cbn [g_items g_na] in IT9, NM9.
  assert (NTK9 : ~ lh_T pl pb9 bks9 pk) by (apply TK9; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb9 ltac:(lia)) as (WDa9 & WDb9 & WDc9 & WDd9).
  pose proof (lh_geo_bounds g9 (proj1 REP9)) as GB9.
  pose proof GR9 as GRu9. unfold cgrow in GRu9.
  assert (PF : (3 * (NBASE + 117) <= f9)%nat) by (clear - Hf FUc9; unfold NBASE; lia).
  assert (PR : els_room L9 nmb9 (Z.of_nat (NBASE + 117))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 117)) with 199. clear - RA RB RC GEa GEb GEc GRu9 WDa9 WDb9 WDc9 WDd9 NM9 NMB GB9 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb9 <= 8 * g_na g9) by (clear - NM9 NMB; lia).
  assert (PI : g_items g9 + Z.of_nat (NBASE + 117) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 117)) with 199; clear - IT9 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267818 ELC) with (lh := lh) (pl := pl) (pb := pb9) (B := B9) (nmb := nmb9) (g := g9) (bks := bks9) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST9| exact REP9| exact PN| exact PI| exact HC9| exact INK9| exact NTK9| exact MC9| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f10 L10 st10 ms10 (v10 & m10 & LBall10 & RET10 & FU10 & _ & CST10 & FRMc & RESn).
  destruct RET10 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU10. assert (FUc10 : Z.of_nat f - 4137 <= Z.of_nat f10) by (clear - FUc9 FU10; lia). clear FUc9 FU10.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR9 SPd) as FR10.
  i1_static CFRc HC9 HC10. i1_static CFRc CB9 CB10.
  assert (FRM10 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st10 LBall10 L10 m10).
  { eapply cframe_call; [exact FRM9| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK9 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE10 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall10 L10).
  { eapply ckeep_call; [exact KPE9| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK9 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 1179 (NBASE + 117) pk LK LBall9 L9 pb9 nmb9 g9 bks9 v10 LBall10 L10 m10 IT9 ltac:(clear - NM9; lia) GR9 TK9 INK9 KPE9 RESn) as RESc10.
  change (1179 + (NBASE + 117))%nat with 1378%nat in RESc10. destruct RESn as (-> & _).
  clear CFRc FRMc REP9 IT9 NM9 GR9 GRu9 TK9 MC9 INK9 NTK9 WDa9 WDb9 WDc9 WDd9 GB9 KPE9 CST9 FRM9 RESc9 FR9 HC9 CB9.
  pose proof (munch_refl (@nil (Z * Z)) m10) as MU10. pose proof (wmono_refl usegs m10) as WM10.
  cprefix. step. if_cases K10; zify_cond K10. { exfalso. rewrite ?unsigned_lit in K10 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc10 as (_ & pb10 & B10 & nmb10 & g10 & bks10 & REP10 & IT10 & NM10 & GR10 & TK10 & MC10 & INK10).
  cbn [g_items g_na] in IT10, NM10.
  assert (NTK10 : ~ lh_T pl pb10 bks10 pk) by (apply TK10; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb10 ltac:(lia)) as (WDa10 & WDb10 & WDc10 & WDd10).
  pose proof (lh_geo_bounds g10 (proj1 REP10)) as GB10.
  pose proof GR10 as GRu10. unfold cgrow in GRu10.
  assert (PF : (3 * (NBASE + 27) <= f10)%nat) by (clear - Hf FUc10; unfold NBASE; lia).
  assert (PR : els_room L10 nmb10 (Z.of_nat (NBASE + 27))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 27)) with 109. clear - RA RB RC GEa GEb GEc GRu10 WDa10 WDb10 WDc10 WDd10 NM10 NMB GB10 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb10 <= 8 * g_na g10) by (clear - NM10 NMB; lia).
  assert (PI : g_items g10 + Z.of_nat (NBASE + 27) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 27)) with 109; clear - IT10 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267860 ELC) with (lh := lh) (pl := pl) (pb := pb10) (B := B10) (nmb := nmb10) (g := g10) (bks := bks10) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST10| exact REP10| exact PN| exact PI| exact HC10| exact INK10| exact NTK10| exact MC10| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f11 L11 st11 ms11 (v11 & m11 & LBall11 & RET11 & FU11 & _ & CST11 & FRMc & RESn).
  destruct RET11 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU11. assert (FUc11 : Z.of_nat f - 4464 <= Z.of_nat f11) by (clear - FUc10 FU11; lia). clear FUc10 FU11.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR10 SPd) as FR11.
  i1_static CFRc HC10 HC11. i1_static CFRc CB10 CB11.
  assert (FRM11 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st11 LBall11 L11 m11).
  { eapply cframe_call; [exact FRM10| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK10 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE11 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall11 L11).
  { eapply ckeep_call; [exact KPE10| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK10 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 1378 (NBASE + 27) pk LK LBall10 L10 pb10 nmb10 g10 bks10 v11 LBall11 L11 m11 IT10 ltac:(clear - NM10; lia) GR10 TK10 INK10 KPE10 RESn) as RESc11.
  change (1378 + (NBASE + 27))%nat with 1487%nat in RESc11. destruct RESn as (-> & _).
  clear CFRc FRMc REP10 IT10 NM10 GR10 GRu10 TK10 MC10 INK10 NTK10 WDa10 WDb10 WDc10 WDd10 GB10 KPE10 CST10 FRM10 RESc10 FR10 HC10 CB10.
  pose proof (munch_refl (@nil (Z * Z)) m11) as MU11. pose proof (wmono_refl usegs m11) as WM11.
  cprefix. step. if_cases K11; zify_cond K11. { exfalso. rewrite ?unsigned_lit in K11 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc11 as (_ & pb11 & B11 & nmb11 & g11 & bks11 & REP11 & IT11 & NM11 & GR11 & TK11 & MC11 & INK11).
  cbn [g_items g_na] in IT11, NM11.
  assert (NTK11 : ~ lh_T pl pb11 bks11 pk) by (apply TK11; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb11 ltac:(lia)) as (WDa11 & WDb11 & WDc11 & WDd11).
  pose proof (lh_geo_bounds g11 (proj1 REP11)) as GB11.
  pose proof GR11 as GRu11. unfold cgrow in GRu11.
  assert (PF : (3 * (NBASE + 31) <= f11)%nat) by (clear - Hf FUc11; unfold NBASE; lia).
  assert (PR : els_room L11 nmb11 (Z.of_nat (NBASE + 31))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 31)) with 113. clear - RA RB RC GEa GEb GEc GRu11 WDa11 WDb11 WDc11 WDd11 NM11 NMB GB11 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb11 <= 8 * g_na g11) by (clear - NM11 NMB; lia).
  assert (PI : g_items g11 + Z.of_nat (NBASE + 31) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 31)) with 113; clear - IT11 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_2678a8 ELC) with (lh := lh) (pl := pl) (pb := pb11) (B := B11) (nmb := nmb11) (g := g11) (bks := bks11) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST11| exact REP11| exact PN| exact PI| exact HC11| exact INK11| exact NTK11| exact MC11| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f12 L12 st12 ms12 (v12 & m12 & LBall12 & RET12 & FU12 & _ & CST12 & FRMc & RESn).
  destruct RET12 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU12. assert (FUc12 : Z.of_nat f - 4803 <= Z.of_nat f12) by (clear - FUc11 FU12; lia). clear FUc11 FU12.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR11 SPd) as FR12.
  i1_static CFRc HC11 HC12. i1_static CFRc CB11 CB12.
  assert (FRM12 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st12 LBall12 L12 m12).
  { eapply cframe_call; [exact FRM11| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK11 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE12 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall12 L12).
  { eapply ckeep_call; [exact KPE11| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK11 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 1487 (NBASE + 31) pk LK LBall11 L11 pb11 nmb11 g11 bks11 v12 LBall12 L12 m12 IT11 ltac:(clear - NM11; lia) GR11 TK11 INK11 KPE11 RESn) as RESc12.
  change (1487 + (NBASE + 31))%nat with 1600%nat in RESc12. destruct RESn as (-> & _).
  clear CFRc FRMc REP11 IT11 NM11 GR11 GRu11 TK11 MC11 INK11 NTK11 WDa11 WDb11 WDc11 WDd11 GB11 KPE11 CST11 FRM11 RESc11 FR11 HC11 CB11.
  pose proof (munch_refl (@nil (Z * Z)) m12) as MU12. pose proof (wmono_refl usegs m12) as WM12.
  cprefix. step. if_cases K12; zify_cond K12. { exfalso. rewrite ?unsigned_lit in K12 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc12 as (_ & pb12 & B12 & nmb12 & g12 & bks12 & REP12 & IT12 & NM12 & GR12 & TK12 & MC12 & INK12).
  cbn [g_items g_na] in IT12, NM12.
  assert (NTK12 : ~ lh_T pl pb12 bks12 pk) by (apply TK12; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb12 ltac:(lia)) as (WDa12 & WDb12 & WDc12 & WDd12).
  pose proof (lh_geo_bounds g12 (proj1 REP12)) as GB12.
  pose proof GR12 as GRu12. unfold cgrow in GRu12.
  assert (PF : (3 * (NBASE + 10) <= f12)%nat) by (clear - Hf FUc12; unfold NBASE; lia).
  assert (PR : els_room L12 nmb12 (Z.of_nat (NBASE + 10))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 10)) with 92. clear - RA RB RC GEa GEb GEc GRu12 WDa12 WDb12 WDc12 WDd12 NM12 NMB GB12 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb12 <= 8 * g_na g12) by (clear - NM12 NMB; lia).
  assert (PI : g_items g12 + Z.of_nat (NBASE + 10) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 10)) with 92; clear - IT12 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_2678f0 ELC) with (lh := lh) (pl := pl) (pb := pb12) (B := B12) (nmb := nmb12) (g := g12) (bks := bks12) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST12| exact REP12| exact PN| exact PI| exact HC12| exact INK12| exact NTK12| exact MC12| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f13 L13 st13 ms13 (v13 & m13 & LBall13 & RET13 & FU13 & _ & CST13 & FRMc & RESn).
  destruct RET13 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU13. assert (FUc13 : Z.of_nat f - 5079 <= Z.of_nat f13) by (clear - FUc12 FU13; lia). clear FUc12 FU13.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR12 SPd) as FR13.
  i1_static CFRc HC12 HC13. i1_static CFRc CB12 CB13.
  assert (FRM13 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st13 LBall13 L13 m13).
  { eapply cframe_call; [exact FRM12| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK12 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE13 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall13 L13).
  { eapply ckeep_call; [exact KPE12| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK12 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 1600 (NBASE + 10) pk LK LBall12 L12 pb12 nmb12 g12 bks12 v13 LBall13 L13 m13 IT12 ltac:(clear - NM12; lia) GR12 TK12 INK12 KPE12 RESn) as RESc13.
  change (1600 + (NBASE + 10))%nat with 1692%nat in RESc13. destruct RESn as (-> & _).
  clear CFRc FRMc REP12 IT12 NM12 GR12 GRu12 TK12 MC12 INK12 NTK12 WDa12 WDb12 WDc12 WDd12 GB12 KPE12 CST12 FRM12 RESc12 FR12 HC12 CB12.
  pose proof (munch_refl (@nil (Z * Z)) m13) as MU13. pose proof (wmono_refl usegs m13) as WM13.
  cprefix. step. if_cases K13; zify_cond K13. { exfalso. rewrite ?unsigned_lit in K13 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc13 as (_ & pb13 & B13 & nmb13 & g13 & bks13 & REP13 & IT13 & NM13 & GR13 & TK13 & MC13 & INK13).
  cbn [g_items g_na] in IT13, NM13.
  assert (NTK13 : ~ lh_T pl pb13 bks13 pk) by (apply TK13; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb13 ltac:(lia)) as (WDa13 & WDb13 & WDc13 & WDd13).
  pose proof (lh_geo_bounds g13 (proj1 REP13)) as GB13.
  pose proof GR13 as GRu13. unfold cgrow in GRu13.
  assert (PF : (3 * (NBASE + 76) <= f13)%nat) by (clear - Hf FUc13; unfold NBASE; lia).
  assert (PR : els_room L13 nmb13 (Z.of_nat (NBASE + 76))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 76)) with 158. clear - RA RB RC GEa GEb GEc GRu13 WDa13 WDb13 WDc13 WDd13 NM13 NMB GB13 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb13 <= 8 * g_na g13) by (clear - NM13 NMB; lia).
  assert (PI : g_items g13 + Z.of_nat (NBASE + 76) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 76)) with 158; clear - IT13 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267938 ELC) with (lh := lh) (pl := pl) (pb := pb13) (B := B13) (nmb := nmb13) (g := g13) (bks := bks13) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST13| exact REP13| exact PN| exact PI| exact HC13| exact INK13| exact NTK13| exact MC13| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f14 L14 st14 ms14 (v14 & m14 & LBall14 & RET14 & FU14 & _ & CST14 & FRMc & RESn).
  destruct RET14 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU14. assert (FUc14 : Z.of_nat f - 5553 <= Z.of_nat f14) by (clear - FUc13 FU14; lia). clear FUc13 FU14.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR13 SPd) as FR14.
  i1_static CFRc HC13 HC14. i1_static CFRc CB13 CB14.
  assert (FRM14 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st14 LBall14 L14 m14).
  { eapply cframe_call; [exact FRM13| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK13 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE14 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall14 L14).
  { eapply ckeep_call; [exact KPE13| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK13 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 1692 (NBASE + 76) pk LK LBall13 L13 pb13 nmb13 g13 bks13 v14 LBall14 L14 m14 IT13 ltac:(clear - NM13; lia) GR13 TK13 INK13 KPE13 RESn) as RESc14.
  change (1692 + (NBASE + 76))%nat with 1850%nat in RESc14. destruct RESn as (-> & _).
  clear CFRc FRMc REP13 IT13 NM13 GR13 GRu13 TK13 MC13 INK13 NTK13 WDa13 WDb13 WDc13 WDd13 GB13 KPE13 CST13 FRM13 RESc13 FR13 HC13 CB13.
  pose proof (munch_refl (@nil (Z * Z)) m14) as MU14. pose proof (wmono_refl usegs m14) as WM14.
  cprefix. step. if_cases K14; zify_cond K14. { exfalso. rewrite ?unsigned_lit in K14 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc14 as (_ & pb14 & B14 & nmb14 & g14 & bks14 & REP14 & IT14 & NM14 & GR14 & TK14 & MC14 & INK14).
  cbn [g_items g_na] in IT14, NM14.
  assert (NTK14 : ~ lh_T pl pb14 bks14 pk) by (apply TK14; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb14 ltac:(lia)) as (WDa14 & WDb14 & WDc14 & WDd14).
  pose proof (lh_geo_bounds g14 (proj1 REP14)) as GB14.
  pose proof GR14 as GRu14. unfold cgrow in GRu14.
  assert (PF : (3 * (NBASE + 47) <= f14)%nat) by (clear - Hf FUc14; unfold NBASE; lia).
  assert (PR : els_room L14 nmb14 (Z.of_nat (NBASE + 47))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 47)) with 129. clear - RA RB RC GEa GEb GEc GRu14 WDa14 WDb14 WDc14 WDd14 NM14 NMB GB14 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb14 <= 8 * g_na g14) by (clear - NM14 NMB; lia).
  assert (PI : g_items g14 + Z.of_nat (NBASE + 47) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 47)) with 129; clear - IT14 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267980 ELC) with (lh := lh) (pl := pl) (pb := pb14) (B := B14) (nmb := nmb14) (g := g14) (bks := bks14) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST14| exact REP14| exact PN| exact PI| exact HC14| exact INK14| exact NTK14| exact MC14| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f15 L15 st15 ms15 (v15 & m15 & LBall15 & RET15 & FU15 & _ & CST15 & FRMc & RESn).
  destruct RET15 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU15. assert (FUc15 : Z.of_nat f - 5940 <= Z.of_nat f15) by (clear - FUc14 FU15; lia). clear FUc14 FU15.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR14 SPd) as FR15.
  i1_static CFRc HC14 HC15. i1_static CFRc CB14 CB15.
  assert (FRM15 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st15 LBall15 L15 m15).
  { eapply cframe_call; [exact FRM14| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK14 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE15 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall15 L15).
  { eapply ckeep_call; [exact KPE14| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK14 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 1850 (NBASE + 47) pk LK LBall14 L14 pb14 nmb14 g14 bks14 v15 LBall15 L15 m15 IT14 ltac:(clear - NM14; lia) GR14 TK14 INK14 KPE14 RESn) as RESc15.
  change (1850 + (NBASE + 47))%nat with 1979%nat in RESc15. destruct RESn as (-> & _).
  clear CFRc FRMc REP14 IT14 NM14 GR14 GRu14 TK14 MC14 INK14 NTK14 WDa14 WDb14 WDc14 WDd14 GB14 KPE14 CST14 FRM14 RESc14 FR14 HC14 CB14.
  pose proof (munch_refl (@nil (Z * Z)) m15) as MU15. pose proof (wmono_refl usegs m15) as WM15.
  cprefix. step. if_cases K15; zify_cond K15. { exfalso. rewrite ?unsigned_lit in K15 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc15 as (_ & pb15 & B15 & nmb15 & g15 & bks15 & REP15 & IT15 & NM15 & GR15 & TK15 & MC15 & INK15).
  cbn [g_items g_na] in IT15, NM15.
  assert (NTK15 : ~ lh_T pl pb15 bks15 pk) by (apply TK15; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb15 ltac:(lia)) as (WDa15 & WDb15 & WDc15 & WDd15).
  pose proof (lh_geo_bounds g15 (proj1 REP15)) as GB15.
  pose proof GR15 as GRu15. unfold cgrow in GRu15.
  assert (PF : (3 * (NBASE + 38) <= f15)%nat) by (clear - Hf FUc15; unfold NBASE; lia).
  assert (PR : els_room L15 nmb15 (Z.of_nat (NBASE + 38))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 38)) with 120. clear - RA RB RC GEa GEb GEc GRu15 WDa15 WDb15 WDc15 WDd15 NM15 NMB GB15 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb15 <= 8 * g_na g15) by (clear - NM15 NMB; lia).
  assert (PI : g_items g15 + Z.of_nat (NBASE + 38) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 38)) with 120; clear - IT15 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_2679c8 ELC) with (lh := lh) (pl := pl) (pb := pb15) (B := B15) (nmb := nmb15) (g := g15) (bks := bks15) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST15| exact REP15| exact PN| exact PI| exact HC15| exact INK15| exact NTK15| exact MC15| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f16 L16 st16 ms16 (v16 & m16 & LBall16 & RET16 & FU16 & _ & CST16 & FRMc & RESn).
  destruct RET16 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU16. assert (FUc16 : Z.of_nat f - 6300 <= Z.of_nat f16) by (clear - FUc15 FU16; lia). clear FUc15 FU16.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR15 SPd) as FR16.
  i1_static CFRc HC15 HC16. i1_static CFRc CB15 CB16.
  assert (FRM16 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st16 LBall16 L16 m16).
  { eapply cframe_call; [exact FRM15| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK15 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE16 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall16 L16).
  { eapply ckeep_call; [exact KPE15| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK15 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 1979 (NBASE + 38) pk LK LBall15 L15 pb15 nmb15 g15 bks15 v16 LBall16 L16 m16 IT15 ltac:(clear - NM15; lia) GR15 TK15 INK15 KPE15 RESn) as RESc16.
  change (1979 + (NBASE + 38))%nat with 2099%nat in RESc16. destruct RESn as (-> & _).
  clear CFRc FRMc REP15 IT15 NM15 GR15 GRu15 TK15 MC15 INK15 NTK15 WDa15 WDb15 WDc15 WDd15 GB15 KPE15 CST15 FRM15 RESc15 FR15 HC15 CB15.
  pose proof (munch_refl (@nil (Z * Z)) m16) as MU16. pose proof (wmono_refl usegs m16) as WM16.
  cprefix. step. if_cases K16; zify_cond K16. { exfalso. rewrite ?unsigned_lit in K16 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc16 as (_ & pb16 & B16 & nmb16 & g16 & bks16 & REP16 & IT16 & NM16 & GR16 & TK16 & MC16 & INK16).
  cbn [g_items g_na] in IT16, NM16.
  assert (NTK16 : ~ lh_T pl pb16 bks16 pk) by (apply TK16; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb16 ltac:(lia)) as (WDa16 & WDb16 & WDc16 & WDd16).
  pose proof (lh_geo_bounds g16 (proj1 REP16)) as GB16.
  pose proof GR16 as GRu16. unfold cgrow in GRu16.
  assert (PF : (3 * (NBASE + 73) <= f16)%nat) by (clear - Hf FUc16; unfold NBASE; lia).
  assert (PR : els_room L16 nmb16 (Z.of_nat (NBASE + 73))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 73)) with 155. clear - RA RB RC GEa GEb GEc GRu16 WDa16 WDb16 WDc16 WDd16 NM16 NMB GB16 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb16 <= 8 * g_na g16) by (clear - NM16 NMB; lia).
  assert (PI : g_items g16 + Z.of_nat (NBASE + 73) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 73)) with 155; clear - IT16 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267a10 ELC) with (lh := lh) (pl := pl) (pb := pb16) (B := B16) (nmb := nmb16) (g := g16) (bks := bks16) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST16| exact REP16| exact PN| exact PI| exact HC16| exact INK16| exact NTK16| exact MC16| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f17 L17 st17 ms17 (v17 & m17 & LBall17 & RET17 & FU17 & _ & CST17 & FRMc & RESn).
  destruct RET17 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU17. assert (FUc17 : Z.of_nat f - 6765 <= Z.of_nat f17) by (clear - FUc16 FU17; lia). clear FUc16 FU17.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR16 SPd) as FR17.
  i1_static CFRc HC16 HC17. i1_static CFRc CB16 CB17.
  assert (FRM17 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st17 LBall17 L17 m17).
  { eapply cframe_call; [exact FRM16| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK16 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE17 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall17 L17).
  { eapply ckeep_call; [exact KPE16| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK16 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 2099 (NBASE + 73) pk LK LBall16 L16 pb16 nmb16 g16 bks16 v17 LBall17 L17 m17 IT16 ltac:(clear - NM16; lia) GR16 TK16 INK16 KPE16 RESn) as RESc17.
  change (2099 + (NBASE + 73))%nat with 2254%nat in RESc17. destruct RESn as (-> & _).
  clear CFRc FRMc REP16 IT16 NM16 GR16 GRu16 TK16 MC16 INK16 NTK16 WDa16 WDb16 WDc16 WDd16 GB16 KPE16 CST16 FRM16 RESc16 FR16 HC16 CB16.
  pose proof (munch_refl (@nil (Z * Z)) m17) as MU17. pose proof (wmono_refl usegs m17) as WM17.
  cprefix. step. if_cases K17; zify_cond K17. { exfalso. rewrite ?unsigned_lit in K17 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc17 as (_ & pb17 & B17 & nmb17 & g17 & bks17 & REP17 & IT17 & NM17 & GR17 & TK17 & MC17 & INK17).
  cbn [g_items g_na] in IT17, NM17.
  assert (NTK17 : ~ lh_T pl pb17 bks17 pk) by (apply TK17; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb17 ltac:(lia)) as (WDa17 & WDb17 & WDc17 & WDd17).
  pose proof (lh_geo_bounds g17 (proj1 REP17)) as GB17.
  pose proof GR17 as GRu17. unfold cgrow in GRu17.
  assert (PF : (3 * (NBASE + 22) <= f17)%nat) by (clear - Hf FUc17; unfold NBASE; lia).
  assert (PR : els_room L17 nmb17 (Z.of_nat (NBASE + 22))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 22)) with 104. clear - RA RB RC GEa GEb GEc GRu17 WDa17 WDb17 WDc17 WDd17 NM17 NMB GB17 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb17 <= 8 * g_na g17) by (clear - NM17 NMB; lia).
  assert (PI : g_items g17 + Z.of_nat (NBASE + 22) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 22)) with 104; clear - IT17 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267a58 ELC) with (lh := lh) (pl := pl) (pb := pb17) (B := B17) (nmb := nmb17) (g := g17) (bks := bks17) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST17| exact REP17| exact PN| exact PI| exact HC17| exact INK17| exact NTK17| exact MC17| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f18 L18 st18 ms18 (v18 & m18 & LBall18 & RET18 & FU18 & _ & CST18 & FRMc & RESn).
  destruct RET18 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU18. assert (FUc18 : Z.of_nat f - 7077 <= Z.of_nat f18) by (clear - FUc17 FU18; lia). clear FUc17 FU18.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR17 SPd) as FR18.
  i1_static CFRc HC17 HC18. i1_static CFRc CB17 CB18.
  assert (FRM18 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st18 LBall18 L18 m18).
  { eapply cframe_call; [exact FRM17| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK17 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE18 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall18 L18).
  { eapply ckeep_call; [exact KPE17| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK17 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 2254 (NBASE + 22) pk LK LBall17 L17 pb17 nmb17 g17 bks17 v18 LBall18 L18 m18 IT17 ltac:(clear - NM17; lia) GR17 TK17 INK17 KPE17 RESn) as RESc18.
  change (2254 + (NBASE + 22))%nat with 2358%nat in RESc18. destruct RESn as (-> & _).
  clear CFRc FRMc REP17 IT17 NM17 GR17 GRu17 TK17 MC17 INK17 NTK17 WDa17 WDb17 WDc17 WDd17 GB17 KPE17 CST17 FRM17 RESc17 FR17 HC17 CB17.
  pose proof (munch_refl (@nil (Z * Z)) m18) as MU18. pose proof (wmono_refl usegs m18) as WM18.
  cprefix. step. if_cases K18; zify_cond K18. { exfalso. rewrite ?unsigned_lit in K18 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc18 as (_ & pb18 & B18 & nmb18 & g18 & bks18 & REP18 & IT18 & NM18 & GR18 & TK18 & MC18 & INK18).
  cbn [g_items g_na] in IT18, NM18.
  assert (NTK18 : ~ lh_T pl pb18 bks18 pk) by (apply TK18; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb18 ltac:(lia)) as (WDa18 & WDb18 & WDc18 & WDd18).
  pose proof (lh_geo_bounds g18 (proj1 REP18)) as GB18.
  pose proof GR18 as GRu18. unfold cgrow in GRu18.
  assert (PF : (3 * (NBASE + 45) <= f18)%nat) by (clear - Hf FUc18; unfold NBASE; lia).
  assert (PR : els_room L18 nmb18 (Z.of_nat (NBASE + 45))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 45)) with 127. clear - RA RB RC GEa GEb GEc GRu18 WDa18 WDb18 WDc18 WDd18 NM18 NMB GB18 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb18 <= 8 * g_na g18) by (clear - NM18 NMB; lia).
  assert (PI : g_items g18 + Z.of_nat (NBASE + 45) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 45)) with 127; clear - IT18 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267aa0 ELC) with (lh := lh) (pl := pl) (pb := pb18) (B := B18) (nmb := nmb18) (g := g18) (bks := bks18) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST18| exact REP18| exact PN| exact PI| exact HC18| exact INK18| exact NTK18| exact MC18| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f19 L19 st19 ms19 (v19 & m19 & LBall19 & RET19 & FU19 & _ & CST19 & FRMc & RESn).
  destruct RET19 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU19. assert (FUc19 : Z.of_nat f - 7458 <= Z.of_nat f19) by (clear - FUc18 FU19; lia). clear FUc18 FU19.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR18 SPd) as FR19.
  i1_static CFRc HC18 HC19. i1_static CFRc CB18 CB19.
  assert (FRM19 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st19 LBall19 L19 m19).
  { eapply cframe_call; [exact FRM18| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK18 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE19 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall19 L19).
  { eapply ckeep_call; [exact KPE18| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK18 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 2358 (NBASE + 45) pk LK LBall18 L18 pb18 nmb18 g18 bks18 v19 LBall19 L19 m19 IT18 ltac:(clear - NM18; lia) GR18 TK18 INK18 KPE18 RESn) as RESc19.
  change (2358 + (NBASE + 45))%nat with 2485%nat in RESc19. destruct RESn as (-> & _).
  clear CFRc FRMc REP18 IT18 NM18 GR18 GRu18 TK18 MC18 INK18 NTK18 WDa18 WDb18 WDc18 WDd18 GB18 KPE18 CST18 FRM18 RESc18 FR18 HC18 CB18.
  pose proof (munch_refl (@nil (Z * Z)) m19) as MU19. pose proof (wmono_refl usegs m19) as WM19.
  cprefix. step. if_cases K19; zify_cond K19. { exfalso. rewrite ?unsigned_lit in K19 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc19 as (_ & pb19 & B19 & nmb19 & g19 & bks19 & REP19 & IT19 & NM19 & GR19 & TK19 & MC19 & INK19).
  cbn [g_items g_na] in IT19, NM19.
  assert (NTK19 : ~ lh_T pl pb19 bks19 pk) by (apply TK19; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb19 ltac:(lia)) as (WDa19 & WDb19 & WDc19 & WDd19).
  pose proof (lh_geo_bounds g19 (proj1 REP19)) as GB19.
  pose proof GR19 as GRu19. unfold cgrow in GRu19.
  assert (PF : (3 * (NBASE + 16) <= f19)%nat) by (clear - Hf FUc19; unfold NBASE; lia).
  assert (PR : els_room L19 nmb19 (Z.of_nat (NBASE + 16))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 16)) with 98. clear - RA RB RC GEa GEb GEc GRu19 WDa19 WDb19 WDc19 WDd19 NM19 NMB GB19 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb19 <= 8 * g_na g19) by (clear - NM19 NMB; lia).
  assert (PI : g_items g19 + Z.of_nat (NBASE + 16) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 16)) with 98; clear - IT19 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267ae8 ELC) with (lh := lh) (pl := pl) (pb := pb19) (B := B19) (nmb := nmb19) (g := g19) (bks := bks19) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST19| exact REP19| exact PN| exact PI| exact HC19| exact INK19| exact NTK19| exact MC19| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f20 L20 st20 ms20 (v20 & m20 & LBall20 & RET20 & FU20 & _ & CST20 & FRMc & RESn).
  destruct RET20 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU20. assert (FUc20 : Z.of_nat f - 7752 <= Z.of_nat f20) by (clear - FUc19 FU20; lia). clear FUc19 FU20.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR19 SPd) as FR20.
  i1_static CFRc HC19 HC20. i1_static CFRc CB19 CB20.
  assert (FRM20 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st20 LBall20 L20 m20).
  { eapply cframe_call; [exact FRM19| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK19 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE20 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall20 L20).
  { eapply ckeep_call; [exact KPE19| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK19 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 2485 (NBASE + 16) pk LK LBall19 L19 pb19 nmb19 g19 bks19 v20 LBall20 L20 m20 IT19 ltac:(clear - NM19; lia) GR19 TK19 INK19 KPE19 RESn) as RESc20.
  change (2485 + (NBASE + 16))%nat with 2583%nat in RESc20. destruct RESn as (-> & _).
  clear CFRc FRMc REP19 IT19 NM19 GR19 GRu19 TK19 MC19 INK19 NTK19 WDa19 WDb19 WDc19 WDd19 GB19 KPE19 CST19 FRM19 RESc19 FR19 HC19 CB19.
  pose proof (munch_refl (@nil (Z * Z)) m20) as MU20. pose proof (wmono_refl usegs m20) as WM20.
  cprefix. step. if_cases K20; zify_cond K20. { exfalso. rewrite ?unsigned_lit in K20 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc20 as (_ & pb20 & B20 & nmb20 & g20 & bks20 & REP20 & IT20 & NM20 & GR20 & TK20 & MC20 & INK20).
  cbn [g_items g_na] in IT20, NM20.
  assert (NTK20 : ~ lh_T pl pb20 bks20 pk) by (apply TK20; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb20 ltac:(lia)) as (WDa20 & WDb20 & WDc20 & WDd20).
  pose proof (lh_geo_bounds g20 (proj1 REP20)) as GB20.
  pose proof GR20 as GRu20. unfold cgrow in GRu20.
  assert (PF : (3 * (NBASE + 39) <= f20)%nat) by (clear - Hf FUc20; unfold NBASE; lia).
  assert (PR : els_room L20 nmb20 (Z.of_nat (NBASE + 39))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 39)) with 121. clear - RA RB RC GEa GEb GEc GRu20 WDa20 WDb20 WDc20 WDd20 NM20 NMB GB20 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb20 <= 8 * g_na g20) by (clear - NM20 NMB; lia).
  assert (PI : g_items g20 + Z.of_nat (NBASE + 39) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 39)) with 121; clear - IT20 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267b30 ELC) with (lh := lh) (pl := pl) (pb := pb20) (B := B20) (nmb := nmb20) (g := g20) (bks := bks20) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST20| exact REP20| exact PN| exact PI| exact HC20| exact INK20| exact NTK20| exact MC20| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f21 L21 st21 ms21 (v21 & m21 & LBall21 & RET21 & FU21 & _ & CST21 & FRMc & RESn).
  destruct RET21 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU21. assert (FUc21 : Z.of_nat f - 8115 <= Z.of_nat f21) by (clear - FUc20 FU21; lia). clear FUc20 FU21.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR20 SPd) as FR21.
  i1_static CFRc HC20 HC21. i1_static CFRc CB20 CB21.
  assert (FRM21 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st21 LBall21 L21 m21).
  { eapply cframe_call; [exact FRM20| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK20 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE21 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall21 L21).
  { eapply ckeep_call; [exact KPE20| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK20 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 2583 (NBASE + 39) pk LK LBall20 L20 pb20 nmb20 g20 bks20 v21 LBall21 L21 m21 IT20 ltac:(clear - NM20; lia) GR20 TK20 INK20 KPE20 RESn) as RESc21.
  change (2583 + (NBASE + 39))%nat with 2704%nat in RESc21. destruct RESn as (-> & _).
  clear CFRc FRMc REP20 IT20 NM20 GR20 GRu20 TK20 MC20 INK20 NTK20 WDa20 WDb20 WDc20 WDd20 GB20 KPE20 CST20 FRM20 RESc20 FR20 HC20 CB20.
  pose proof (munch_refl (@nil (Z * Z)) m21) as MU21. pose proof (wmono_refl usegs m21) as WM21.
  cprefix. step. if_cases K21; zify_cond K21. { exfalso. rewrite ?unsigned_lit in K21 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc21 as (_ & pb21 & B21 & nmb21 & g21 & bks21 & REP21 & IT21 & NM21 & GR21 & TK21 & MC21 & INK21).
  cbn [g_items g_na] in IT21, NM21.
  assert (NTK21 : ~ lh_T pl pb21 bks21 pk) by (apply TK21; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb21 ltac:(lia)) as (WDa21 & WDb21 & WDc21 & WDd21).
  pose proof (lh_geo_bounds g21 (proj1 REP21)) as GB21.
  pose proof GR21 as GRu21. unfold cgrow in GRu21.
  assert (PF : (3 * (NBASE + 32) <= f21)%nat) by (clear - Hf FUc21; unfold NBASE; lia).
  assert (PR : els_room L21 nmb21 (Z.of_nat (NBASE + 32))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 32)) with 114. clear - RA RB RC GEa GEb GEc GRu21 WDa21 WDb21 WDc21 WDd21 NM21 NMB GB21 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb21 <= 8 * g_na g21) by (clear - NM21 NMB; lia).
  assert (PI : g_items g21 + Z.of_nat (NBASE + 32) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 32)) with 114; clear - IT21 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267b78 ELC) with (lh := lh) (pl := pl) (pb := pb21) (B := B21) (nmb := nmb21) (g := g21) (bks := bks21) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST21| exact REP21| exact PN| exact PI| exact HC21| exact INK21| exact NTK21| exact MC21| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f22 L22 st22 ms22 (v22 & m22 & LBall22 & RET22 & FU22 & _ & CST22 & FRMc & RESn).
  destruct RET22 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU22. assert (FUc22 : Z.of_nat f - 8457 <= Z.of_nat f22) by (clear - FUc21 FU22; lia). clear FUc21 FU22.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR21 SPd) as FR22.
  i1_static CFRc HC21 HC22. i1_static CFRc CB21 CB22.
  assert (FRM22 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st22 LBall22 L22 m22).
  { eapply cframe_call; [exact FRM21| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK21 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE22 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall22 L22).
  { eapply ckeep_call; [exact KPE21| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK21 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 2704 (NBASE + 32) pk LK LBall21 L21 pb21 nmb21 g21 bks21 v22 LBall22 L22 m22 IT21 ltac:(clear - NM21; lia) GR21 TK21 INK21 KPE21 RESn) as RESc22.
  change (2704 + (NBASE + 32))%nat with 2818%nat in RESc22. destruct RESn as (-> & _).
  clear CFRc FRMc REP21 IT21 NM21 GR21 GRu21 TK21 MC21 INK21 NTK21 WDa21 WDb21 WDc21 WDd21 GB21 KPE21 CST21 FRM21 RESc21 FR21 HC21 CB21.
  pose proof (munch_refl (@nil (Z * Z)) m22) as MU22. pose proof (wmono_refl usegs m22) as WM22.
  cprefix. step. if_cases K22; zify_cond K22. { exfalso. rewrite ?unsigned_lit in K22 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc22 as (_ & pb22 & B22 & nmb22 & g22 & bks22 & REP22 & IT22 & NM22 & GR22 & TK22 & MC22 & INK22).
  cbn [g_items g_na] in IT22, NM22.
  assert (NTK22 : ~ lh_T pl pb22 bks22 pk) by (apply TK22; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb22 ltac:(lia)) as (WDa22 & WDb22 & WDc22 & WDd22).
  pose proof (lh_geo_bounds g22 (proj1 REP22)) as GB22.
  pose proof GR22 as GRu22. unfold cgrow in GRu22.
  assert (PF : (3 * (NBASE + 25) <= f22)%nat) by (clear - Hf FUc22; unfold NBASE; lia).
  assert (PR : els_room L22 nmb22 (Z.of_nat (NBASE + 25))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 25)) with 107. clear - RA RB RC GEa GEb GEc GRu22 WDa22 WDb22 WDc22 WDd22 NM22 NMB GB22 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb22 <= 8 * g_na g22) by (clear - NM22 NMB; lia).
  assert (PI : g_items g22 + Z.of_nat (NBASE + 25) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 25)) with 107; clear - IT22 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267bc0 ELC) with (lh := lh) (pl := pl) (pb := pb22) (B := B22) (nmb := nmb22) (g := g22) (bks := bks22) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST22| exact REP22| exact PN| exact PI| exact HC22| exact INK22| exact NTK22| exact MC22| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f23 L23 st23 ms23 (v23 & m23 & LBall23 & RET23 & FU23 & _ & CST23 & FRMc & RESn).
  destruct RET23 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU23. assert (FUc23 : Z.of_nat f - 8778 <= Z.of_nat f23) by (clear - FUc22 FU23; lia). clear FUc22 FU23.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR22 SPd) as FR23.
  i1_static CFRc HC22 HC23. i1_static CFRc CB22 CB23.
  assert (FRM23 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st23 LBall23 L23 m23).
  { eapply cframe_call; [exact FRM22| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK22 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE23 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall23 L23).
  { eapply ckeep_call; [exact KPE22| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK22 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 2818 (NBASE + 25) pk LK LBall22 L22 pb22 nmb22 g22 bks22 v23 LBall23 L23 m23 IT22 ltac:(clear - NM22; lia) GR22 TK22 INK22 KPE22 RESn) as RESc23.
  change (2818 + (NBASE + 25))%nat with 2925%nat in RESc23. destruct RESn as (-> & _).
  clear CFRc FRMc REP22 IT22 NM22 GR22 GRu22 TK22 MC22 INK22 NTK22 WDa22 WDb22 WDc22 WDd22 GB22 KPE22 CST22 FRM22 RESc22 FR22 HC22 CB22.
  pose proof (munch_refl (@nil (Z * Z)) m23) as MU23. pose proof (wmono_refl usegs m23) as WM23.
  cprefix. step. if_cases K23; zify_cond K23. { exfalso. rewrite ?unsigned_lit in K23 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc23 as (_ & pb23 & B23 & nmb23 & g23 & bks23 & REP23 & IT23 & NM23 & GR23 & TK23 & MC23 & INK23).
  cbn [g_items g_na] in IT23, NM23.
  assert (NTK23 : ~ lh_T pl pb23 bks23 pk) by (apply TK23; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb23 ltac:(lia)) as (WDa23 & WDb23 & WDc23 & WDd23).
  pose proof (lh_geo_bounds g23 (proj1 REP23)) as GB23.
  pose proof GR23 as GRu23. unfold cgrow in GRu23.
  assert (PF : (3 * (NBASE + 13) <= f23)%nat) by (clear - Hf FUc23; unfold NBASE; lia).
  assert (PR : els_room L23 nmb23 (Z.of_nat (NBASE + 13))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 13)) with 95. clear - RA RB RC GEa GEb GEc GRu23 WDa23 WDb23 WDc23 WDd23 NM23 NMB GB23 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb23 <= 8 * g_na g23) by (clear - NM23 NMB; lia).
  assert (PI : g_items g23 + Z.of_nat (NBASE + 13) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 13)) with 95; clear - IT23 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267c08 ELC) with (lh := lh) (pl := pl) (pb := pb23) (B := B23) (nmb := nmb23) (g := g23) (bks := bks23) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST23| exact REP23| exact PN| exact PI| exact HC23| exact INK23| exact NTK23| exact MC23| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f24 L24 st24 ms24 (v24 & m24 & LBall24 & RET24 & FU24 & _ & CST24 & FRMc & RESn).
  destruct RET24 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU24. assert (FUc24 : Z.of_nat f - 9063 <= Z.of_nat f24) by (clear - FUc23 FU24; lia). clear FUc23 FU24.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR23 SPd) as FR24.
  i1_static CFRc HC23 HC24. i1_static CFRc CB23 CB24.
  assert (FRM24 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st24 LBall24 L24 m24).
  { eapply cframe_call; [exact FRM23| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK23 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE24 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall24 L24).
  { eapply ckeep_call; [exact KPE23| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK23 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 2925 (NBASE + 13) pk LK LBall23 L23 pb23 nmb23 g23 bks23 v24 LBall24 L24 m24 IT23 ltac:(clear - NM23; lia) GR23 TK23 INK23 KPE23 RESn) as RESc24.
  change (2925 + (NBASE + 13))%nat with 3020%nat in RESc24. destruct RESn as (-> & _).
  clear CFRc FRMc REP23 IT23 NM23 GR23 GRu23 TK23 MC23 INK23 NTK23 WDa23 WDb23 WDc23 WDd23 GB23 KPE23 CST23 FRM23 RESc23 FR23 HC23 CB23.
  pose proof (munch_refl (@nil (Z * Z)) m24) as MU24. pose proof (wmono_refl usegs m24) as WM24.
  cprefix. step. if_cases K24; zify_cond K24. { exfalso. rewrite ?unsigned_lit in K24 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc24 as (_ & pb24 & B24 & nmb24 & g24 & bks24 & REP24 & IT24 & NM24 & GR24 & TK24 & MC24 & INK24).
  cbn [g_items g_na] in IT24, NM24.
  assert (NTK24 : ~ lh_T pl pb24 bks24 pk) by (apply TK24; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb24 ltac:(lia)) as (WDa24 & WDb24 & WDc24 & WDd24).
  pose proof (lh_geo_bounds g24 (proj1 REP24)) as GB24.
  pose proof GR24 as GRu24. unfold cgrow in GRu24.
  assert (PF : (3 * (NBASE + 102) <= f24)%nat) by (clear - Hf FUc24; unfold NBASE; lia).
  assert (PR : els_room L24 nmb24 (Z.of_nat (NBASE + 102))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 102)) with 184. clear - RA RB RC GEa GEb GEc GRu24 WDa24 WDb24 WDc24 WDd24 NM24 NMB GB24 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb24 <= 8 * g_na g24) by (clear - NM24 NMB; lia).
  assert (PI : g_items g24 + Z.of_nat (NBASE + 102) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 102)) with 184; clear - IT24 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267c50 ELC) with (lh := lh) (pl := pl) (pb := pb24) (B := B24) (nmb := nmb24) (g := g24) (bks := bks24) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST24| exact REP24| exact PN| exact PI| exact HC24| exact INK24| exact NTK24| exact MC24| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f25 L25 st25 ms25 (v25 & m25 & LBall25 & RET25 & FU25 & _ & CST25 & FRMc & RESn).
  destruct RET25 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU25. assert (FUc25 : Z.of_nat f - 9615 <= Z.of_nat f25) by (clear - FUc24 FU25; lia). clear FUc24 FU25.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR24 SPd) as FR25.
  i1_static CFRc HC24 HC25. i1_static CFRc CB24 CB25.
  assert (FRM25 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st25 LBall25 L25 m25).
  { eapply cframe_call; [exact FRM24| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK24 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE25 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall25 L25).
  { eapply ckeep_call; [exact KPE24| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK24 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 3020 (NBASE + 102) pk LK LBall24 L24 pb24 nmb24 g24 bks24 v25 LBall25 L25 m25 IT24 ltac:(clear - NM24; lia) GR24 TK24 INK24 KPE24 RESn) as RESc25.
  change (3020 + (NBASE + 102))%nat with 3204%nat in RESc25. destruct RESn as (-> & _).
  clear CFRc FRMc REP24 IT24 NM24 GR24 GRu24 TK24 MC24 INK24 NTK24 WDa24 WDb24 WDc24 WDd24 GB24 KPE24 CST24 FRM24 RESc24 FR24 HC24 CB24.
  pose proof (munch_refl (@nil (Z * Z)) m25) as MU25. pose proof (wmono_refl usegs m25) as WM25.
  cprefix. step. if_cases K25; zify_cond K25. { exfalso. rewrite ?unsigned_lit in K25 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc25 as (_ & pb25 & B25 & nmb25 & g25 & bks25 & REP25 & IT25 & NM25 & GR25 & TK25 & MC25 & INK25).
  cbn [g_items g_na] in IT25, NM25.
  assert (NTK25 : ~ lh_T pl pb25 bks25 pk) by (apply TK25; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb25 ltac:(lia)) as (WDa25 & WDb25 & WDc25 & WDd25).
  pose proof (lh_geo_bounds g25 (proj1 REP25)) as GB25.
  pose proof GR25 as GRu25. unfold cgrow in GRu25.
  assert (PF : (3 * (NBASE + 30) <= f25)%nat) by (clear - Hf FUc25; unfold NBASE; lia).
  assert (PR : els_room L25 nmb25 (Z.of_nat (NBASE + 30))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 30)) with 112. clear - RA RB RC GEa GEb GEc GRu25 WDa25 WDb25 WDc25 WDd25 NM25 NMB GB25 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb25 <= 8 * g_na g25) by (clear - NM25 NMB; lia).
  assert (PI : g_items g25 + Z.of_nat (NBASE + 30) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 30)) with 112; clear - IT25 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267c98 ELC) with (lh := lh) (pl := pl) (pb := pb25) (B := B25) (nmb := nmb25) (g := g25) (bks := bks25) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST25| exact REP25| exact PN| exact PI| exact HC25| exact INK25| exact NTK25| exact MC25| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f26 L26 st26 ms26 (v26 & m26 & LBall26 & RET26 & FU26 & _ & CST26 & FRMc & RESn).
  destruct RET26 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU26. assert (FUc26 : Z.of_nat f - 9951 <= Z.of_nat f26) by (clear - FUc25 FU26; lia). clear FUc25 FU26.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR25 SPd) as FR26.
  i1_static CFRc HC25 HC26. i1_static CFRc CB25 CB26.
  assert (FRM26 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st26 LBall26 L26 m26).
  { eapply cframe_call; [exact FRM25| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK25 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE26 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall26 L26).
  { eapply ckeep_call; [exact KPE25| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK25 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 3204 (NBASE + 30) pk LK LBall25 L25 pb25 nmb25 g25 bks25 v26 LBall26 L26 m26 IT25 ltac:(clear - NM25; lia) GR25 TK25 INK25 KPE25 RESn) as RESc26.
  change (3204 + (NBASE + 30))%nat with 3316%nat in RESc26. destruct RESn as (-> & _).
  clear CFRc FRMc REP25 IT25 NM25 GR25 GRu25 TK25 MC25 INK25 NTK25 WDa25 WDb25 WDc25 WDd25 GB25 KPE25 CST25 FRM25 RESc25 FR25 HC25 CB25.
  pose proof (munch_refl (@nil (Z * Z)) m26) as MU26. pose proof (wmono_refl usegs m26) as WM26.
  cprefix. step. if_cases K26; zify_cond K26. { exfalso. rewrite ?unsigned_lit in K26 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc26 as (_ & pb26 & B26 & nmb26 & g26 & bks26 & REP26 & IT26 & NM26 & GR26 & TK26 & MC26 & INK26).
  cbn [g_items g_na] in IT26, NM26.
  assert (NTK26 : ~ lh_T pl pb26 bks26 pk) by (apply TK26; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb26 ltac:(lia)) as (WDa26 & WDb26 & WDc26 & WDd26).
  pose proof (lh_geo_bounds g26 (proj1 REP26)) as GB26.
  pose proof GR26 as GRu26. unfold cgrow in GRu26.
  assert (PF : (3 * (NBASE + 106) <= f26)%nat) by (clear - Hf FUc26; unfold NBASE; lia).
  assert (PR : els_room L26 nmb26 (Z.of_nat (NBASE + 106))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 106)) with 188. clear - RA RB RC GEa GEb GEc GRu26 WDa26 WDb26 WDc26 WDd26 NM26 NMB GB26 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb26 <= 8 * g_na g26) by (clear - NM26 NMB; lia).
  assert (PI : g_items g26 + Z.of_nat (NBASE + 106) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 106)) with 188; clear - IT26 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267ce0 ELC) with (lh := lh) (pl := pl) (pb := pb26) (B := B26) (nmb := nmb26) (g := g26) (bks := bks26) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST26| exact REP26| exact PN| exact PI| exact HC26| exact INK26| exact NTK26| exact MC26| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f27 L27 st27 ms27 (v27 & m27 & LBall27 & RET27 & FU27 & _ & CST27 & FRMc & RESn).
  destruct RET27 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU27. assert (FUc27 : Z.of_nat f - 10515 <= Z.of_nat f27) by (clear - FUc26 FU27; lia). clear FUc26 FU27.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR26 SPd) as FR27.
  i1_static CFRc HC26 HC27. i1_static CFRc CB26 CB27.
  assert (FRM27 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st27 LBall27 L27 m27).
  { eapply cframe_call; [exact FRM26| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK26 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE27 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall27 L27).
  { eapply ckeep_call; [exact KPE26| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK26 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 3316 (NBASE + 106) pk LK LBall26 L26 pb26 nmb26 g26 bks26 v27 LBall27 L27 m27 IT26 ltac:(clear - NM26; lia) GR26 TK26 INK26 KPE26 RESn) as RESc27.
  change (3316 + (NBASE + 106))%nat with 3504%nat in RESc27. destruct RESn as (-> & _).
  clear CFRc FRMc REP26 IT26 NM26 GR26 GRu26 TK26 MC26 INK26 NTK26 WDa26 WDb26 WDc26 WDd26 GB26 KPE26 CST26 FRM26 RESc26 FR26 HC26 CB26.
  pose proof (munch_refl (@nil (Z * Z)) m27) as MU27. pose proof (wmono_refl usegs m27) as WM27.
  cprefix. step. if_cases K27; zify_cond K27. { exfalso. rewrite ?unsigned_lit in K27 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc27 as (_ & pb27 & B27 & nmb27 & g27 & bks27 & REP27 & IT27 & NM27 & GR27 & TK27 & MC27 & INK27).
  cbn [g_items g_na] in IT27, NM27.
  assert (NTK27 : ~ lh_T pl pb27 bks27 pk) by (apply TK27; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb27 ltac:(lia)) as (WDa27 & WDb27 & WDc27 & WDd27).
  pose proof (lh_geo_bounds g27 (proj1 REP27)) as GB27.
  pose proof GR27 as GRu27. unfold cgrow in GRu27.
  assert (PF : (3 * (NBASE + 17) <= f27)%nat) by (clear - Hf FUc27; unfold NBASE; lia).
  assert (PR : els_room L27 nmb27 (Z.of_nat (NBASE + 17))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 17)) with 99. clear - RA RB RC GEa GEb GEc GRu27 WDa27 WDb27 WDc27 WDd27 NM27 NMB GB27 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb27 <= 8 * g_na g27) by (clear - NM27 NMB; lia).
  assert (PI : g_items g27 + Z.of_nat (NBASE + 17) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 17)) with 99; clear - IT27 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267d28 ELC) with (lh := lh) (pl := pl) (pb := pb27) (B := B27) (nmb := nmb27) (g := g27) (bks := bks27) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST27| exact REP27| exact PN| exact PI| exact HC27| exact INK27| exact NTK27| exact MC27| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f28 L28 st28 ms28 (v28 & m28 & LBall28 & RET28 & FU28 & _ & CST28 & FRMc & RESn).
  destruct RET28 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU28. assert (FUc28 : Z.of_nat f - 10812 <= Z.of_nat f28) by (clear - FUc27 FU28; lia). clear FUc27 FU28.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR27 SPd) as FR28.
  i1_static CFRc HC27 HC28. i1_static CFRc CB27 CB28.
  assert (FRM28 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st28 LBall28 L28 m28).
  { eapply cframe_call; [exact FRM27| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK27 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE28 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall28 L28).
  { eapply ckeep_call; [exact KPE27| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK27 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 3504 (NBASE + 17) pk LK LBall27 L27 pb27 nmb27 g27 bks27 v28 LBall28 L28 m28 IT27 ltac:(clear - NM27; lia) GR27 TK27 INK27 KPE27 RESn) as RESc28.
  change (3504 + (NBASE + 17))%nat with 3603%nat in RESc28. destruct RESn as (-> & _).
  clear CFRc FRMc REP27 IT27 NM27 GR27 GRu27 TK27 MC27 INK27 NTK27 WDa27 WDb27 WDc27 WDd27 GB27 KPE27 CST27 FRM27 RESc27 FR27 HC27 CB27.
  pose proof (munch_refl (@nil (Z * Z)) m28) as MU28. pose proof (wmono_refl usegs m28) as WM28.
  cprefix. step. if_cases K28; zify_cond K28. { exfalso. rewrite ?unsigned_lit in K28 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc28 as (_ & pb28 & B28 & nmb28 & g28 & bks28 & REP28 & IT28 & NM28 & GR28 & TK28 & MC28 & INK28).
  cbn [g_items g_na] in IT28, NM28.
  assert (NTK28 : ~ lh_T pl pb28 bks28 pk) by (apply TK28; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb28 ltac:(lia)) as (WDa28 & WDb28 & WDc28 & WDd28).
  pose proof (lh_geo_bounds g28 (proj1 REP28)) as GB28.
  pose proof GR28 as GRu28. unfold cgrow in GRu28.
  assert (PF : (3 * (NBASE + 9) <= f28)%nat) by (clear - Hf FUc28; unfold NBASE; lia).
  assert (PR : els_room L28 nmb28 (Z.of_nat (NBASE + 9))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 9)) with 91. clear - RA RB RC GEa GEb GEc GRu28 WDa28 WDb28 WDc28 WDd28 NM28 NMB GB28 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb28 <= 8 * g_na g28) by (clear - NM28 NMB; lia).
  assert (PI : g_items g28 + Z.of_nat (NBASE + 9) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 9)) with 91; clear - IT28 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267d70 ELC) with (lh := lh) (pl := pl) (pb := pb28) (B := B28) (nmb := nmb28) (g := g28) (bks := bks28) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST28| exact REP28| exact PN| exact PI| exact HC28| exact INK28| exact NTK28| exact MC28| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f29 L29 st29 ms29 (v29 & m29 & LBall29 & RET29 & FU29 & _ & CST29 & FRMc & RESn).
  destruct RET29 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU29. assert (FUc29 : Z.of_nat f - 11085 <= Z.of_nat f29) by (clear - FUc28 FU29; lia). clear FUc28 FU29.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR28 SPd) as FR29.
  i1_static CFRc HC28 HC29. i1_static CFRc CB28 CB29.
  assert (FRM29 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st29 LBall29 L29 m29).
  { eapply cframe_call; [exact FRM28| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK28 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE29 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall29 L29).
  { eapply ckeep_call; [exact KPE28| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK28 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 3603 (NBASE + 9) pk LK LBall28 L28 pb28 nmb28 g28 bks28 v29 LBall29 L29 m29 IT28 ltac:(clear - NM28; lia) GR28 TK28 INK28 KPE28 RESn) as RESc29.
  change (3603 + (NBASE + 9))%nat with 3694%nat in RESc29. destruct RESn as (-> & _).
  clear CFRc FRMc REP28 IT28 NM28 GR28 GRu28 TK28 MC28 INK28 NTK28 WDa28 WDb28 WDc28 WDd28 GB28 KPE28 CST28 FRM28 RESc28 FR28 HC28 CB28.
  pose proof (munch_refl (@nil (Z * Z)) m29) as MU29. pose proof (wmono_refl usegs m29) as WM29.
  cprefix. step. if_cases K29; zify_cond K29. { exfalso. rewrite ?unsigned_lit in K29 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc29 as (_ & pb29 & B29 & nmb29 & g29 & bks29 & REP29 & IT29 & NM29 & GR29 & TK29 & MC29 & INK29).
  cbn [g_items g_na] in IT29, NM29.
  assert (NTK29 : ~ lh_T pl pb29 bks29 pk) by (apply TK29; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb29 ltac:(lia)) as (WDa29 & WDb29 & WDc29 & WDd29).
  pose proof (lh_geo_bounds g29 (proj1 REP29)) as GB29.
  pose proof GR29 as GRu29. unfold cgrow in GRu29.
  assert (PF : (3 * (NBASE + 4) <= f29)%nat) by (clear - Hf FUc29; unfold NBASE; lia).
  assert (PR : els_room L29 nmb29 (Z.of_nat (NBASE + 4))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 4)) with 86. clear - RA RB RC GEa GEb GEc GRu29 WDa29 WDb29 WDc29 WDd29 NM29 NMB GB29 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb29 <= 8 * g_na g29) by (clear - NM29 NMB; lia).
  assert (PI : g_items g29 + Z.of_nat (NBASE + 4) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 4)) with 86; clear - IT29 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267db8 ELC) with (lh := lh) (pl := pl) (pb := pb29) (B := B29) (nmb := nmb29) (g := g29) (bks := bks29) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST29| exact REP29| exact PN| exact PI| exact HC29| exact INK29| exact NTK29| exact MC29| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f30 L30 st30 ms30 (v30 & m30 & LBall30 & RET30 & FU30 & _ & CST30 & FRMc & RESn).
  destruct RET30 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU30. assert (FUc30 : Z.of_nat f - 11343 <= Z.of_nat f30) by (clear - FUc29 FU30; lia). clear FUc29 FU30.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR29 SPd) as FR30.
  i1_static CFRc HC29 HC30. i1_static CFRc CB29 CB30.
  assert (FRM30 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st30 LBall30 L30 m30).
  { eapply cframe_call; [exact FRM29| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK29 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE30 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall30 L30).
  { eapply ckeep_call; [exact KPE29| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK29 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 3694 (NBASE + 4) pk LK LBall29 L29 pb29 nmb29 g29 bks29 v30 LBall30 L30 m30 IT29 ltac:(clear - NM29; lia) GR29 TK29 INK29 KPE29 RESn) as RESc30.
  change (3694 + (NBASE + 4))%nat with 3780%nat in RESc30. destruct RESn as (-> & _).
  clear CFRc FRMc REP29 IT29 NM29 GR29 GRu29 TK29 MC29 INK29 NTK29 WDa29 WDb29 WDc29 WDd29 GB29 KPE29 CST29 FRM29 RESc29 FR29 HC29 CB29.
  pose proof (munch_refl (@nil (Z * Z)) m30) as MU30. pose proof (wmono_refl usegs m30) as WM30.
  cprefix. step. if_cases K30; zify_cond K30. { exfalso. rewrite ?unsigned_lit in K30 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc30 as (_ & pb30 & B30 & nmb30 & g30 & bks30 & REP30 & IT30 & NM30 & GR30 & TK30 & MC30 & INK30).
  cbn [g_items g_na] in IT30, NM30.
  assert (NTK30 : ~ lh_T pl pb30 bks30 pk) by (apply TK30; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb30 ltac:(lia)) as (WDa30 & WDb30 & WDc30 & WDd30).
  pose proof (lh_geo_bounds g30 (proj1 REP30)) as GB30.
  pose proof GR30 as GRu30. unfold cgrow in GRu30.
  assert (PF : (3 * (NBASE + 14) <= f30)%nat) by (clear - Hf FUc30; unfold NBASE; lia).
  assert (PR : els_room L30 nmb30 (Z.of_nat (NBASE + 14))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 14)) with 96. clear - RA RB RC GEa GEb GEc GRu30 WDa30 WDb30 WDc30 WDd30 NM30 NMB GB30 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb30 <= 8 * g_na g30) by (clear - NM30 NMB; lia).
  assert (PI : g_items g30 + Z.of_nat (NBASE + 14) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 14)) with 96; clear - IT30 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267e00 ELC) with (lh := lh) (pl := pl) (pb := pb30) (B := B30) (nmb := nmb30) (g := g30) (bks := bks30) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST30| exact REP30| exact PN| exact PI| exact HC30| exact INK30| exact NTK30| exact MC30| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f31 L31 st31 ms31 (v31 & m31 & LBall31 & RET31 & FU31 & _ & CST31 & FRMc & RESn).
  destruct RET31 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU31. assert (FUc31 : Z.of_nat f - 11631 <= Z.of_nat f31) by (clear - FUc30 FU31; lia). clear FUc30 FU31.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR30 SPd) as FR31.
  i1_static CFRc HC30 HC31. i1_static CFRc CB30 CB31.
  assert (FRM31 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st31 LBall31 L31 m31).
  { eapply cframe_call; [exact FRM30| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK30 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE31 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall31 L31).
  { eapply ckeep_call; [exact KPE30| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK30 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 3780 (NBASE + 14) pk LK LBall30 L30 pb30 nmb30 g30 bks30 v31 LBall31 L31 m31 IT30 ltac:(clear - NM30; lia) GR30 TK30 INK30 KPE30 RESn) as RESc31.
  change (3780 + (NBASE + 14))%nat with 3876%nat in RESc31. destruct RESn as (-> & _).
  clear CFRc FRMc REP30 IT30 NM30 GR30 GRu30 TK30 MC30 INK30 NTK30 WDa30 WDb30 WDc30 WDd30 GB30 KPE30 CST30 FRM30 RESc30 FR30 HC30 CB30.
  pose proof (munch_refl (@nil (Z * Z)) m31) as MU31. pose proof (wmono_refl usegs m31) as WM31.
  cprefix. step. if_cases K31; zify_cond K31. { exfalso. rewrite ?unsigned_lit in K31 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc31 as (_ & pb31 & B31 & nmb31 & g31 & bks31 & REP31 & IT31 & NM31 & GR31 & TK31 & MC31 & INK31).
  cbn [g_items g_na] in IT31, NM31.
  assert (NTK31 : ~ lh_T pl pb31 bks31 pk) by (apply TK31; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb31 ltac:(lia)) as (WDa31 & WDb31 & WDc31 & WDd31).
  pose proof (lh_geo_bounds g31 (proj1 REP31)) as GB31.
  pose proof GR31 as GRu31. unfold cgrow in GRu31.
  assert (PF : (3 * (NBASE + 25) <= f31)%nat) by (clear - Hf FUc31; unfold NBASE; lia).
  assert (PR : els_room L31 nmb31 (Z.of_nat (NBASE + 25))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 25)) with 107. clear - RA RB RC GEa GEb GEc GRu31 WDa31 WDb31 WDc31 WDd31 NM31 NMB GB31 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb31 <= 8 * g_na g31) by (clear - NM31 NMB; lia).
  assert (PI : g_items g31 + Z.of_nat (NBASE + 25) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 25)) with 107; clear - IT31 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267e48 ELC) with (lh := lh) (pl := pl) (pb := pb31) (B := B31) (nmb := nmb31) (g := g31) (bks := bks31) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST31| exact REP31| exact PN| exact PI| exact HC31| exact INK31| exact NTK31| exact MC31| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f32 L32 st32 ms32 (v32 & m32 & LBall32 & RET32 & FU32 & _ & CST32 & FRMc & RESn).
  destruct RET32 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU32. assert (FUc32 : Z.of_nat f - 11952 <= Z.of_nat f32) by (clear - FUc31 FU32; lia). clear FUc31 FU32.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR31 SPd) as FR32.
  i1_static CFRc HC31 HC32. i1_static CFRc CB31 CB32.
  assert (FRM32 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st32 LBall32 L32 m32).
  { eapply cframe_call; [exact FRM31| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK31 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE32 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall32 L32).
  { eapply ckeep_call; [exact KPE31| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK31 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 3876 (NBASE + 25) pk LK LBall31 L31 pb31 nmb31 g31 bks31 v32 LBall32 L32 m32 IT31 ltac:(clear - NM31; lia) GR31 TK31 INK31 KPE31 RESn) as RESc32.
  change (3876 + (NBASE + 25))%nat with 3983%nat in RESc32. destruct RESn as (-> & _).
  clear CFRc FRMc REP31 IT31 NM31 GR31 GRu31 TK31 MC31 INK31 NTK31 WDa31 WDb31 WDc31 WDd31 GB31 KPE31 CST31 FRM31 RESc31 FR31 HC31 CB31.
  pose proof (munch_refl (@nil (Z * Z)) m32) as MU32. pose proof (wmono_refl usegs m32) as WM32.
  cprefix. step. if_cases K32; zify_cond K32. { exfalso. rewrite ?unsigned_lit in K32 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc32 as (_ & pb32 & B32 & nmb32 & g32 & bks32 & REP32 & IT32 & NM32 & GR32 & TK32 & MC32 & INK32).
  cbn [g_items g_na] in IT32, NM32.
  assert (NTK32 : ~ lh_T pl pb32 bks32 pk) by (apply TK32; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb32 ltac:(lia)) as (WDa32 & WDb32 & WDc32 & WDd32).
  pose proof (lh_geo_bounds g32 (proj1 REP32)) as GB32.
  pose proof GR32 as GRu32. unfold cgrow in GRu32.
  assert (PF : (3 * (NBASE + 11) <= f32)%nat) by (clear - Hf FUc32; unfold NBASE; lia).
  assert (PR : els_room L32 nmb32 (Z.of_nat (NBASE + 11))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 11)) with 93. clear - RA RB RC GEa GEb GEc GRu32 WDa32 WDb32 WDc32 WDd32 NM32 NMB GB32 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb32 <= 8 * g_na g32) by (clear - NM32 NMB; lia).
  assert (PI : g_items g32 + Z.of_nat (NBASE + 11) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 11)) with 93; clear - IT32 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267e90 ELC) with (lh := lh) (pl := pl) (pb := pb32) (B := B32) (nmb := nmb32) (g := g32) (bks := bks32) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST32| exact REP32| exact PN| exact PI| exact HC32| exact INK32| exact NTK32| exact MC32| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f33 L33 st33 ms33 (v33 & m33 & LBall33 & RET33 & FU33 & _ & CST33 & FRMc & RESn).
  destruct RET33 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU33. assert (FUc33 : Z.of_nat f - 12231 <= Z.of_nat f33) by (clear - FUc32 FU33; lia). clear FUc32 FU33.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR32 SPd) as FR33.
  i1_static CFRc HC32 HC33. i1_static CFRc CB32 CB33.
  assert (FRM33 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st33 LBall33 L33 m33).
  { eapply cframe_call; [exact FRM32| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK32 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE33 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall33 L33).
  { eapply ckeep_call; [exact KPE32| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK32 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 3983 (NBASE + 11) pk LK LBall32 L32 pb32 nmb32 g32 bks32 v33 LBall33 L33 m33 IT32 ltac:(clear - NM32; lia) GR32 TK32 INK32 KPE32 RESn) as RESc33.
  change (3983 + (NBASE + 11))%nat with 4076%nat in RESc33. destruct RESn as (-> & _).
  clear CFRc FRMc REP32 IT32 NM32 GR32 GRu32 TK32 MC32 INK32 NTK32 WDa32 WDb32 WDc32 WDd32 GB32 KPE32 CST32 FRM32 RESc32 FR32 HC32 CB32.
  pose proof (munch_refl (@nil (Z * Z)) m33) as MU33. pose proof (wmono_refl usegs m33) as WM33.
  cprefix. step. if_cases K33; zify_cond K33. { exfalso. rewrite ?unsigned_lit in K33 by lia. lia. }
  (* [comment removed for export] *)
  step. chere.
  pose proof RESc33 as (_ & pb33 & B33 & nmb33 & g33 & bks33 & REP33 & IT33 & NM33 & GR33 & TK33 & MC33 & INK33).
  cbn [g_items g_na] in IT33, NM33.
  assert (NTK33 : ~ lh_T pl pb33 bks33 pk) by (apply TK33; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INKE]| exact NTKE]).
  destruct (w_delta 128 nmb33 ltac:(lia)) as (WDa33 & WDb33 & WDc33 & WDd33).
  pose proof (lh_geo_bounds g33 (proj1 REP33)) as GB33.
  pose proof GR33 as GRu33. unfold cgrow in GRu33.
  assert (PF : (3 * (NBASE + 160) <= f33)%nat) by (clear - Hf FUc33; unfold NBASE; lia).
  assert (PR : els_room L33 nmb33 (Z.of_nat (NBASE + 160))).
  { unfold els_room, NBASE. change (Z.of_nat (82 + 160)) with 242. clear - RA RB RC GEa GEb GEc GRu33 WDa33 WDb33 WDc33 WDd33 NM33 NMB GB33 WS1 WS2 WS3. lia. }
  assert (PN : 0 <= nmb33 <= 8 * g_na g33) by (clear - NM33 NMB; lia).
  assert (PI : g_items g33 + Z.of_nat (NBASE + 160) <= LH_KMAX) by (unfold NBASE; change (Z.of_nat (82 + 160)) with 242; clear - IT33 ITEMS; lia).
  eapply climpl_seq.
  { eapply (stub_267ed8 ELC) with (lh := lh) (pl := pl) (pb := pb33) (B := B33) (nmb := nmb33) (g := g33) (bks := bks33) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact PF| exact PR| exact CST33| exact REP33| exact PN| exact PI| exact HC33| exact INK33| exact NTK33| exact MC33| exact SLOc| exact SAc]. }
  clear PF PR PN PI.
  intros f34 L34 st34 ms34 (v34 & m34 & LBall34 & RET34 & FU34 & _ & CST34 & FRMc & RESn).
  destruct RET34 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold NBASE in FU34. assert (FUc34 : Z.of_nat f - 12957 <= Z.of_nat f34) by (clear - FUc33 FU34; lia). clear FUc33 FU34.
  pose proof FRMc as (CFRc & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFRc FR33 SPd) as FR34.
  i1_static CFRc HC33 HC34. i1_static CFRc CB33 CB34.
  assert (FRM34 : cframe TT ELF_W (bv_unsigned sp) s LBall L m st34 LBall34 L34 m34).
  { eapply cframe_call; [exact FRM33| exact FRMc| exact SPc| intros a X; destruct X|].
    intros q QIN _ E. destruct (ENTRYQ q QIN) as [QIN' NT']. destruct E as [E|E]; [exact (NT' (or_introl E))|]. exact (TK33 q QIN' (fun X => NT' (or_intror X)) E). }
  assert (KPE34 : ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) LBallE LE LBall34 L34).
  { eapply ckeep_call; [exact KPE33| exact (proj1 (proj2 FRMc))|]. intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK33 q QIN (fun X => NT (or_intror X)) E). }
  pose proof (els_res_compose LBallE LE lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 4076 (NBASE + 160) pk LK LBall33 L33 pb33 nmb33 g33 bks33 v34 LBall34 L34 m34 IT33 ltac:(clear - NM33; lia) GR33 TK33 INK33 KPE33 RESn) as RESc34.
  change (4076 + (NBASE + 160))%nat with 4318%nat in RESc34. destruct RESn as (-> & _).
  clear CFRc FRMc REP33 IT33 NM33 GR33 GRu33 TK33 MC33 INK33 NTK33 WDa33 WDb33 WDc33 WDd33 GB33 KPE33 CST33 FRM33 RESc33 FR33 HC33 CB33.
  pose proof (munch_refl (@nil (Z * Z)) m34) as MU34. pose proof (wmono_refl usegs m34) as WM34.
  cprefix. step.
  (* [comment removed for export] *)
  pose proof CST34 as (HPz & _ & (errvz & _ & _ & STz & _ & _ & MIz & _) & _).
  rewrite unsigned_lit in STz by lia.
  do 2 step. release_frame FR34 STz (bv_unsigned sp). step. step.
  chere. apply climpl_done.
  exists (Z_to_bv 64 1), m34, LBall34.
  pose proof RESc34 as (_ & pbf & Bf & nmbf & gf & bksf & REPf & ITf & NMBf & GRf & _). cbn [g_items g_na] in ITf, NMBf.
  pose proof (lh_geo_bounds gf (proj1 REPf)) as GBf.
  destruct (w_delta 128 nmbf ltac:(lia)) as (WF1 & WF2 & WF3 & WF4).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ (conj GEa (conj GEb GEc)) GRf) as GR. eapply cgrow_weaken; [exact GR| | |]; rewrite ?WS1, ?WS2, ?WS3; unfold LHA_MAX; lia. }
  split. { eapply (cstate_seg [] _ _ _ _ m34 m34 _ sp tp lo Bd (bv_unsigned sp)); [exact CST34| apply munch_refl| apply wmono_refl| exact MIz| apply Forall_nil| lia| lia| exact I| exact STz| exact SPB]. }
  split; [exact FRM34|].
  exists pk, pl, pb, LK, lh, B. split; [exact RESc34|]. split; [exact FRESH|]. split; [exact NEKL|]. split; [exact NEKB|]. split; [exact (conj GEa (conj GEb GEc))|].
  split; [exact HC34| exact CB34].
Qed.
End WithCeiling0.
