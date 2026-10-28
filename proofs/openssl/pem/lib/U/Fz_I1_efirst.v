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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_kit_ra Fz_M_realloc Fz_I1_insert Fz_I1_insert1 Fz_cimg_rom. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex Th_once. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_T_once Fz_I1_load Fz_I1_retrieve Fz_I1_errload Fz_I1_reason Fz_M_zalloc Fz_M_calloc Fz_I1_new Fz_T_lock_new Fz_I3_base Fz_T_ekit Fz_I1_first.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma ckeep_call : forall (T T' : bptr -> Prop) LB0 L0 LB1 L1 LB2 L2,
  ckeep T LB0 L0 LB1 L1 -> ckeep T' LB1 L1 LB2 L2 -> (forall q, In q (map blk_id LB0) \/ In q (map fst L0) -> ~ T q -> ~ T' q) -> ckeep T LB0 L0 LB2 L2.
Proof.
  intros T T' LB0 L0 LB1 L1 LB2 L2 [K1 K1'] [K2 K2'] HT. split.
  - intros b Hb NT. apply K2; [apply K1; assumption|]. apply HT; [left; apply in_map; exact Hb| exact NT].
  - intros q nm Hq NT. apply K2'; [apply K1'; assumption|]. apply HT; [right; apply in_map_iff; exists (q, nm); auto| exact NT].
Qed.

Definition ELF_STACK : Z := 32 + 128 + 8352.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ELF_W : list (Z * Z) := [(0x32e010, 0x32e028); (RATP + -96, RATP + -88)].

Definition elf_res (LBall : list block) (L : @clist bptr) (oldcb : word) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (pk pl pb : bptr) (LK lh B : Z),
    els_res ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall) ((pb, 128) :: (pl, 104) :: (pk, 40) :: L) lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) NBASE pk LK
            v LBall' L' m'
    /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> q <> pk /\ q <> pl /\ q <> pb) /\ pk <> pl /\ pk <> pb
    /\ cgrow L ((pb, 128) :: (pl, 104) :: (pk, 40) :: L) 3 0 0
    /\ ckeep (fun q => q = pk \/ lh_T pl pb (repeat [] 16) q) ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall) ((pb, 128) :: (pl, 104) :: (pk, 40) :: L) LBall' L'
    /\ rw_cells usegs m' ERR_ONCE_CELL (err_statics LK lh)
    /\ rw_cells usegs m' (RATP + -96) [C8 oldcb].

Definition err_load_ERR_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z) (od r0 l0 h0 oldcb : word),
  (3 + 3 * NBASE <= f)%nat -> croom L (3 + Z.of_nat NBASE) 2 (2 * (LHA_MAX + 8192)) ->
  cstate s LBall LB L m sp tp lo Bd ->
  rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] -> rw_cells usegs m (IC_S + 96) [C8 od] ->
  rw_cells usegs m ERR_ONCE_CELL [C4 (Z_to_bv 64 0); C4 r0; C8 l0; C8 h0] ->
  rw_cells usegs m (RATP + -96) [C8 oldcb] ->
  lo <= bv_unsigned sp - ELF_STACK -> bv_unsigned sp mod 16 = 0 ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_ERR_LOAD_ERR) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun _ => False) ELF_W (3 + 3 * NBASE) (3 + Z.of_nat NBASE) 1 (LHA_MAX + 8192)
           (elf_res LBall L oldcb)).

Theorem err_load_ERR_first_spec : do_esi_stmt -> err_load_strings_stmt -> err_load_ERR_first_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ESI ELS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd od r0 l0 h0 oldcb
         Hf ROOM CST STOP ONCE OD HC CBC SLO SA.
  unfold do_esi_stmt in ESI. unfold err_load_strings_stmt in ELS.
  pose proof CST as (HP & CO & (errv & _ & SPB & ST & LO & _ & MI & TP) & _ & _ & CIMG & GLO).
  subst tp.
  unfold ELF_STACK, GLOBALS_TOP, FZ_ERR_LOAD_ERR, ERR_ONCE_CELL, RATP, IC_S, NBASE in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  change (3333664 + 8) with 3333672 in STOP. change (3333664 + 32) with 0x32de40 in ONCE. change (3333664 + 96) with 3333760 in OD.
  destruct ROOM as (RA & RB & RC).
  destruct (rheap_ssp _ _ _ HP) as [GOT GU]. unfold got_ssp, ssp_guard in GOT, GU.
  (* [comment removed for export] *)
  change [C4 (Z_to_bv 64 0); C4 r0; C8 l0; C8 h0] with ([C4 (Z_to_bv 64 0)] ++ [C4 r0; C8 l0; C8 h0]) in HC.
  apply (proj1 (rw_cells_app usegs m _ _ _)) in HC. destruct HC as [CC HC].
  lazymatch type of HC with rw_cells _ _ ?a _ => replace a with 3334164 in HC by (cbn; lia) end.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (3334160, 3334164); (3344744 + -96, 3344744 + -88)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 32%nat ST. do 3 step. step. do 4 step. step. step.
  pose proof T_run_once_enter_proof as OE. unfold T_run_once_enter_stmt, ssp_cells, got_ssp, ssp_guard in OE.
  tcall (OE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0xe7df0 oldcb rr_guard).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  clear OE. cbv beta delta [mkR]. try th_ret_lit. try cret_lit. chere.
  unfold ONCE_RET_INIT, RUN_ONCE_RET, once_full_cells, ONCE_UNDO, ONCE_RET_FULL in *.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mi end.
  lazymatch goal with H : rw_cells usegs mi 3334160 _ |- _ => rename H into CC1 end.
  lazymatch goal with H : rw_cells usegs mi (3344744 + -96) _ |- _ => rename H into CB1 end.
  lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -32 + -128) _ |- _ => rename H into OF1 end.
  lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -32 + -32) _ |- _ => rename H into OF2 end.
  lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -32 + -16) _ |- _ => rename H into OF3 end.
  lazymatch goal with H : stk usegs mi _ _ |- _ => rename H into STi end.
  lazymatch goal with H : mem_inv usegs mi |- _ => rename H into MIi end.
  assert (CSTi : cstate s LBall LB L mi (Z_to_bv 64 (bv_unsigned sp + -32 + -128)) (Z_to_bv 64 3344744) lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m mi _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIi| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply cwin_bss; lia|]. apply Forall_cons; [unfold cwin; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact STi.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRa : cframe (fun _ => False) ELF_W (bv_unsigned sp) s LBall L m s LBall L mi).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    repeat (apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold ELF_W, RATP; cbn [rin_ivs fst snd]; lia]|]). apply Forall_nil. }
  eapply climpl_seq.
  { eapply ESI with (lo := lo) (Bd := Bd) (od := od); [lia| unfold croom; unfold LHA_MAX in RC; change (Z.of_nat 82) with 82 in RA; lia| exact CSTi| exact STOP| exact ONCE| exact OD| exact HC
                                                 | rewrite unsigned_lit by lia; unfold ESI_STACK; lia]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pk & pl & pb & LK & lh & B & -> & -> & REP1 & MC1 & HCr)).
  destruct RET1 as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & ->).
  cret_lit.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(rewrite unsigned_lit by lia; lia)) as FR1.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OF1 ltac:(rewrite unsigned_lit by lia; lia)) as OF1b.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OF2 ltac:(rewrite unsigned_lit by lia; lia)) as OF2b.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OF3 ltac:(rewrite unsigned_lit by lia; lia)) as OF3b.
  assert (CC2 := cfr_cells_static _ _ _ _ _ _ _ _ CFR1 CC1). cbn [cells_size csize Nat.add] in CC2.
  specialize (CC2 ltac:(lia) ltac:(lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS, ESI_W; cbn [rin_ivs fst snd]; lia)).
  assert (CB2 := cfr_cells_static _ _ _ _ _ _ _ _ CFR1 CB1). cbn [cells_size csize Nat.add] in CB2.
  specialize (CB2 ltac:(lia) ltac:(lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS, ESI_W; cbn [rin_ivs fst snd]; lia)).
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  destruct (rheap_ssp _ _ _ HP1) as [GOT1 GU1]. unfold got_ssp, ssp_guard in GOT1, GU1.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 NDL1].
  assert (INK1 : In (pk, LK, 40) ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall)) by (right; right; left; reflexivity).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 INK1) as (LK0 & _ & _ & LKC & LKIMG).
  assert (FRESH : forall q, In q (map blk_id LBall) \/ In q (map fst L) -> q <> pk /\ q <> pl /\ q <> pb).
  { intros q [Hq|Hq].
    - cbn [map blk_id fst] in ND1. pose proof (t_nodup_prefix blk_id [(pb, B, 128); (pl, lh, 104); (pk, LK, 40)] LBall) as NP. cbn [app map blk_id fst] in NP.
      apply in_map_iff in Hq. destruct Hq as (b & <- & Hb).
      repeat split; intros E.
      + apply (NP (pk, LK, 40) ND1 ltac:(right; right; left; reflexivity)). cbn [blk_id fst]. rewrite <- E. apply in_map. exact Hb.
      + apply (NP (pl, lh, 104) ND1 ltac:(right; left; reflexivity)). cbn [blk_id fst]. rewrite <- E. apply in_map. exact Hb.
      + apply (NP (pb, B, 128) ND1 ltac:(left; reflexivity)). cbn [blk_id fst]. rewrite <- E. apply in_map. exact Hb.
    - cbn [map fst] in NDL1. pose proof (t_nodup_prefix fst [(pb, 128); (pl, 104); (pk, 40)] L) as NP. cbn [app map fst] in NP.
      apply in_map_iff in Hq. destruct Hq as (c & <- & Hc).
      repeat split; intros E.
      + apply (NP (pk, 40) NDL1 ltac:(right; right; left; reflexivity)). cbn [fst]. rewrite <- E. apply in_map. exact Hc.
      + apply (NP (pl, 104) NDL1 ltac:(right; left; reflexivity)). cbn [fst]. rewrite <- E. apply in_map. exact Hc.
      + apply (NP (pb, 128) NDL1 ltac:(left; reflexivity)). cbn [fst]. rewrite <- E. apply in_map. exact Hc. }
  assert (NEKL : pk <> pl) by (intros E; cbn [map blk_id fst] in ND1; apply NoDup_cons_iff in ND1; destruct ND1 as [_ X]; apply NoDup_cons_iff in X; destruct X as [NI _]; apply NI; left; exact E).
  assert (NEKB : pk <> pb) by (intros E; cbn [map blk_id fst] in ND1; apply NoDup_cons_iff in ND1; destruct ND1 as [NI _]; apply NI; right; left; exact E).
  assert (NTK1 : ~ lh_T pl pb (repeat [] 16) pk).
  { unfold lh_T. cbn [repeat concat app map]. intros [E|[E|[]]]; [exact (NEKL E)| exact (NEKB E)]. }
  unfold mutex_cells in MC1.
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp); (3334160, 3334164); (3344744 + -96, 3344744 + -88)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix.
  pose proof (T_run_once_leave_proof) as OL. unfold T_run_once_leave_stmt, ssp_cells, got_ssp, ssp_guard, ONCE_RET_INIT, once_full_cells, ONCE_UNDO, ONCE_RET_FULL, RUN_ONCE_RET in OL.
  tcall (OL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -32) 3334160).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  clear OL. cbv beta delta [mkR].
  try th_ret_lit. try cret_lit.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  lazymatch goal with H : rw_cells usegs ma 3334160 _ |- _ => rename H into CCa end.
  lazymatch goal with H : rw_cells usegs ma (3344744 + -96) _ |- _ => rename H into CBa end.
  lazymatch goal with H : rw_cells usegs ma 3334164 _ |- _ => rename H into HCa end.
  lazymatch goal with H : rw_cells usegs ma LK _ |- _ => rename H into MCa end.
  step. step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  step. step. if_cases K2; zify_cond K2. { exfalso. revert K2. vm_compute. intros X. first [discriminate X| apply X; reflexivity]. }
  do 2 step. step.
  assert (CSTa : cstate st1 ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall) LB ((pb, 128) :: (pl, 104) :: (pk, 40) :: L) ma (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 3344744) lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m1 ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIa| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply cwin_bss; lia|]. apply Forall_cons; [unfold cwin; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact STa.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRb : cframe (fun _ => False) ELF_W (bv_unsigned sp) s LBall L m st1 ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall) ((pb, 128) :: (pl, 104) :: (pk, 40) :: L) ma).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa| exact FRM1| rewrite unsigned_lit by lia; lia| intros a X; unfold ESI_W in X; unfold ELF_W; cbn [rin_ivs fst snd] in X |- *; lia| intros q0 _ X; exact X]
                       | exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    repeat (apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold ELF_W, RATP; cbn [rin_ivs fst snd]; lia]|]). apply Forall_nil. }
  assert (REPa : lh_rep DVERR ma ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall) ((pb, 128) :: (pl, 104) :: (pk, 40) :: L) ERR_FNS lh pl pb B 128 (mkGeo 8 16 0 8 0) (repeat [] 16)).
  { eapply (lh_rep_offheap st1 DVERR m1 ma); [exact HP1| exact REP1| exact MU1| exact WM1|]. intros a Ha HIMG. cbn [outside]. clear - Ha HIMG LO SLO SPR. lia. }
  assert (LOCKC : forall mm, rw_cells usegs mm 3334164 [C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] -> rw_cells usegs mm ERR_LOCK_CELL [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]).
  { intros mm H. change [C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] with ([C4 (Z_to_bv 64 1)] ++ [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]) in H.
    exact (proj2 (proj1 (rw_cells_app usegs mm _ _ _) H)). }
  destruct (wA_small 128 ltac:(unfold TIER_A_MAX; lia)) as (WS1 & WS2 & WS3).
  destruct GR1 as (G1a & G1b & G1c).
  chere. eapply climpl_seq.
  { eapply ELS with (T := ERR_TAB1) (n := 43%nat) (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := 128) (g := mkGeo 8 16 0 8 0) (bks := repeat [] 16) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [lia| unfold els_room; rewrite WS2, WS3; change (Z.of_nat 82) with 82 in RA; lia| exact CSTa| exact REPa| cbn [g_na]; lia| cbn [g_items]; unfold LH_KMAX; lia
      | exact etab_base1| exact (or_introl trange_base1)| apply LOCKC; exact HCa| exact INK1| exact NTK1| unfold mutex_cells; exact MCa
      | rewrite unsigned_lit by lia; unfold ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| rewrite unsigned_lit by lia; lia| unfold ERR_TAB1; reflexivity| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2c & CST2 & FRM2 & (-> & pb2 & B2 & nmb2 & g2 & bks2 & REP2 & IT2 & NMB2 & GR2 & TK2 & MC2 & INK2)).
  destruct RET2 as (z0 & z1 & z2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z3 & z4 & z5 & z6 & ->).
  cret_lit.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(rewrite unsigned_lit by lia; lia)) as FR2.
  i1_static CFR2 HCa HCb. i1_static CFR2 CCa CCb. i1_static CFR2 CBa CBb.
  assert (NTK2 : ~ lh_T pl pb2 bks2 pk) by (apply TK2; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INK1]| exact NTK1]).
  cbn [g_items g_na] in IT2, NMB2.
  pose proof (lh_geo_bounds g2 (proj1 REP2)) as GB2.
  destruct (w_delta 128 nmb2 ltac:(lia)) as (WD1 & WD2 & WD3 & WD4).
  pose proof (munch_refl (@nil (Z * Z)) m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. do 2 step. step.
  chere. eapply climpl_seq.
  { eapply ELS with (T := ERR_TAB2) (n := 39%nat) (lh := lh) (pl := pl) (pb := pb2) (B := B2) (nmb := nmb2) (g := g2) (bks := bks2) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [lia| unfold els_room, cgrow in *; destruct GR2 as (G2a & G2b & G2c); rewrite WS2, WS3 in *; change (Z.of_nat 82) with 82 in RA; change (Z.of_nat 43) with 43 in G2a; lia
      | exact CST2| exact REP2| lia| change (Z.of_nat 43) with 43 in IT2; unfold LH_KMAX; lia| exact etab_base2| exact (or_introl trange_base2)| apply LOCKC; exact HCb| exact INK2| exact NTK2| exact MC2
      | rewrite unsigned_lit by lia; unfold ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| rewrite unsigned_lit by lia; lia| unfold ERR_TAB2; reflexivity| reflexivity]. }
  intros f3 L3 st3 ms3 (v3 & m3 & LBall3 & RET3 & FU3 & GR3c & CST3 & FRM3 & RES3).
  destruct RET3 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & ->).
  cret_lit.
  pose proof FRM3 as (CFR3 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FR2 ltac:(rewrite unsigned_lit by lia; lia)) as FR3.
  i1_static CFR3 HCb HCc. i1_static CFR3 CCb CCc. i1_static CFR3 CBb CBc.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  rewrite unsigned_lit in ST3 by lia.
  pose proof (munch_refl (@nil (Z * Z)) m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
  pose proof (els_res_compose _ _ lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) 43 39 pk LK LBall2 L2 pb2 nmb2 g2 bks2 v3 LBall3 L3 m3 IT2 ltac:(lia) GR2 TK2 INK2 KP2 RES3) as RES.
  destruct RES3 as (-> & _).
  (* [comment removed for export] *)
  cprefix. step. do 3 step. release_frame FR3 ST3 (bv_unsigned sp). step. step.
  chere. apply climpl_done.
  exists (Z_to_bv 64 1), m3, LBall3.
  pose proof RES as (_ & pbf & Bf & nmbf & gf & bksf & REPf & ITf & NMBf & GRf & _).
  cbn [g_items g_na] in ITf, NMBf.
  pose proof (lh_geo_bounds gf (proj1 REPf)) as GBf.
  destruct (w_delta 128 nmbf ltac:(lia)) as (WF1 & WF2 & WF3 & WF4).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ (conj G1a (conj G1b G1c)) GRf) as GR. eapply cgrow_weaken; [exact GR| | |]; rewrite ?WS1, ?WS2, ?WS3; unfold LHA_MAX;
           change (Z.of_nat (43 + 39)) with 82; change (Z.of_nat 82) with 82; lia. }
  split. { eapply (cstate_seg [] _ _ _ _ m3 m3 _ sp _ lo Bd (bv_unsigned sp)); [exact CST3| apply munch_refl| apply wmono_refl| exact MI3| apply Forall_nil| lia| lia| exact I| exact ST3| exact SPB]. }
  split. { eapply cframe_call; [eapply cframe_call; [exact FRb| exact FRM2| rewrite unsigned_lit by lia; lia| intros a X; destruct X|]| exact FRM3| rewrite unsigned_lit by lia; lia| intros a X; destruct X|].
    - intros q QIN _ [E|E]; [exact (proj1 (FRESH q QIN) E)|]. unfold lh_T in E. cbn [repeat concat app map] in E.
      destruct E as [E|[E|[]]]; [exact (proj1 (proj2 (FRESH q QIN)) E)| exact (proj2 (proj2 (FRESH q QIN)) E)].
    - intros q QIN _ [E|E]; [exact (proj1 (FRESH q QIN) E)|]. revert E. apply TK2.
      + destruct QIN as [X|X]; [left; cbn [map]; do 3 right; exact X| right; cbn [map]; do 3 right; exact X].
      + unfold lh_T. cbn [repeat concat app map]. intros [X|[X|[]]]; [exact (proj1 (proj2 (FRESH q QIN)) X)| exact (proj2 (proj2 (FRESH q QIN)) X)]. }
  exists pk, pl, pb, LK, lh, B. split; [change NBASE with (43 + 39)%nat; exact RES|]. split; [exact FRESH|]. split; [exact NEKL|]. split; [exact NEKB|].
  split; [exact (conj G1a (conj G1b G1c))|].
  split. { pose proof FRM3 as (_ & KP3 & _). eapply ckeep_call; [exact KP2| exact KP3|].
           intros q QIN NT [E|E]; [exact (NT (or_introl E))|]. exact (TK2 q QIN (fun X => NT (or_intror X)) E). }
  split; [| exact CBc].
  unfold ERR_ONCE_CELL, err_statics. change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] with ([C4 (Z_to_bv 64 2)] ++ [C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]).
  apply rw_cells_app. split; [exact CCc| exact HCc].
Qed.
End WithCeiling0.
