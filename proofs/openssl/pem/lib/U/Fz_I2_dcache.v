(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_calloc Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_rep Fz_I1_new. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_lock_new.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_DECODER_CACHE_NEW : Z := 0x18cd84.
Definition DCN_STACK : Z := 32 + LHN_STACK.

Definition dcache_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (pc pk pl pb : bptr) (C LK lh B : Z),
    v = Z_to_bv 64 C /\ LBall' = (pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: (pc, C, 16) :: LBall /\ L' = (pb, 128) :: (pl, 104) :: (pk, 40) :: (pc, 16) :: L
    /\ rblock_range C 16 /\ rblock_range LK 40 /\ rblock_range lh 104 /\ rblock_range B 128.

Definition ossl_decoder_cache_new_fp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (4 <= f)%nat -> croom L 4 0 0 -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - DCN_STACK ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_DECODER_CACHE_NEW) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 4 4 0 0 (dcache_res LBall L)).

Theorem ossl_decoder_cache_new_fp_spec : crypto_malloc_stmt -> T_lock_new_stmt -> lh_new_stmt -> ossl_decoder_cache_new_fp_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM LKN LHN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd
         Hf ROOM CST SLO.
  unfold crypto_malloc_stmt in CM. unfold T_lock_new_stmt in LKN. unfold lh_new_stmt in LHN.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold DCN_STACK, LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_DECODER_CACHE_NEW in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  destruct (wA_small 16 ltac:(unfold TIER_A_MAX; lia)) as (W16a & W16b & W16c). destruct (wA_small 40 ltac:(unfold TIER_A_MAX; lia)) as (W40a & W40b & W40c).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. th_frame 32%nat [8; 8; 8; 8]%nat ST. do 3 step. step. do 4 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply CM with (n := 16) (lo := lo) (B := Bd); [lia| rewrite W16a, W16b, W16c; unfold croom in *; lia| lia| exact CSTa| rewrite unsigned_lit by lia; unfold CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pc & C & junkc & -> & -> & -> & RC & CBLK)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). rewrite W16a, W16b, W16c in GR1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RC as (C0 & _ & _ & CC & CIMG2).
  change (Z.to_nat 16) with 16%nat in CBLK.
  assert (FRM0 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st1 ((pc, C, 16) :: LBall) ((pc, 16) :: L) m1).
  { eapply cframe_call; [exact FRa| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRa CSTa CFR1 FRM1.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. chere.
  eapply climpl_seq.
  { eapply LKN with (lo := lo) (B := Bd); [lia| rewrite W40a, W40b, W40c; unfold croom, cgrow in *; lia| exact CST1| rewrite unsigned_lit by lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pk & LK & -> & -> & -> & RK & MC2)).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM2 by lia). rewrite W40a, W40b, W40c in GR2.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  assert (INC1 : In (pc, C, 16) ((pc, C, 16) :: LBall)) by (left; reflexivity).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pc, C, 16) CFR2 CBLK INC1 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as CBLK2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RK as (LK0 & _ & _ & LKC & LKIMG).
  assert (INC2 : In (pc, C, 16) ((pk, LK, 40) :: (pc, C, 16) :: LBall)) by (right; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _].
  assert (FRb : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st2 ((pk, LK, 40) :: (pc, C, 16) :: LBall) ((pk, 40) :: (pc, 16) :: L) m2).
  { eapply cframe_call; [exact FRM0| exact FRM2| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRM0 CFR2 FRM2.
  pose proof (munch_refl [(C, C + 8)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. step. step. rewrite ?(unsigned_lit C) by lia. rewrite (ubs_land7 C) by (destruct RC as (_ & RC16 & _); lia).
  if_cases KA; zify_cond KA. { exfalso. apply KA. reflexivity. } clear KA.
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  do 4 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into mc end.
  lazymatch goal with H : stk _ mc _ _ |- _ => rename H into STc end.
  lazymatch goal with H : mem_inv _ mc |- _ => rename H into MIc end.
  lazymatch goal with H : rw_cells usegs mc C _ |- _ => rename H into CBLKc end.
  assert (CSTc : cstate st2 ((pk, LK, 40) :: (pc, C, 16) :: LBall) LB ((pk, 40) :: (pc, 16) :: L) mc (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m2 mc _ _ _ lo Bd (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MIc| | lia| lia| | rewrite unsigned_lit by lia; exact STc| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [| apply Forall_nil]. apply (cwin_block _ _ _ (pc, C, 16)); [exact INC2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRc : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st2 ((pk, LK, 40) :: (pc, C, 16) :: LBall) ((pk, 40) :: (pc, 16) :: L) mc).
  { eapply cframe_seg; [exact FRb| exact MU2| exact WM2| exact HP2| lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (pc, C, 16)); [exact INC2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pk, LK, 40); (pc, C, 16)] LBall (pc, C, 16) ND2 ltac:(right; left; reflexivity)) as NI.
    apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
  clear FRb.
  eapply climpl_seq.
  { eapply LHN with (DV := fun _ => True) (h := 0x18ce4c) (c := 0x18cf20) (lo := lo) (B := Bd);
      [lia| unfold croom, cgrow in *; lia| lia| lia| exact CSTc| rewrite unsigned_lit by lia; unfold LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  intros f3 L3 st3 ms3 (v3 & m3 & LBall3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (pl & pb & lh & B & -> & -> & -> & REP)).
  destruct RET3 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM3 by lia).
  pose proof FRM3 as (CFR3 & KP3 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FR2 ltac:(lia)) as FR3.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pc, C, 16) CFR3 CBLKc INC2 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add length]; lia)) as CBLK3.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  rewrite unsigned_lit in ST3 by lia.
  pose proof REP as (_ & _ & _ & (y40 & y48 & err & pad & SC) & _).
  set (LB3 := (pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: (pc, C, 16) :: LBall) in *.
  assert (INL : In (pl, lh, 104) LB3) by (subst LB3; right; left; reflexivity).
  assert (INB : In (pb, B, 128) LB3) by (subst LB3; left; reflexivity).
  assert (INC3 : In (pc, C, 16) LB3) by (subst LB3; do 3 right; left; reflexivity).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST3 INL) as RL. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST3 INB) as RB.
  pose proof RL as (LH0 & LH16 & _ & LHC & LHIMG).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [ND3 _].
  assert (NElc : pl <> pc). { intros E1. destruct (cown_block_eq _ _ _ _ _ _ ND3 INL ltac:(rewrite E1; exact INC3)) as [_ X]. discriminate X. }
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST3 INL INC3 NElc) as APLC.
  unfold lh_cells, wz in SC. cbn [lf_comp lf_hash lf_hashw lf_compw g_nn g_na g_p g_pmax g_items] in SC.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp - 32); (lh + 24, lh + 56); (C + 8, C + 16)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
  (* [comment removed for export] *)
  cprefix. do 8 step. step.
  calle (eapply lh_set_thunks_spec with (f := mkFns 0x18cf20 0x18ce4c 0 0) (lh := lh) (B := B) (g := mkGeo 8 16 0 8 0) (lo := lo)); try lia.
  all: try (unfold lh_cells, wz; cbn [lf_comp lf_hash lf_hashw lf_compw g_nn g_na g_p g_pmax g_items]; exact SC).
  step. step. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit in K3 by lia. lia. } clear K3.
  step. do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into ST4 end.
  lazymatch goal with H : rw_cells usegs mf (bv_unsigned sp + -32) _ |- _ => rename H into FR4 end.
  release_frame FR4 ST4 (bv_unsigned sp). step. step.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  chere. apply climpl_done.
  eexists. exists mf, LB3.
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split; [pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) GR3) as GR; clear - GR; unfold cgrow in *; lia|].
  split. { eapply (cstate_seg _ _ _ _ _ m3 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST3| exact MU3| exact WM3| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pl, lh, 104)); [exact INL| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pc, C, 16)); [exact INC3| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRc| exact FRM3| lia| intros a X; exact X| intros q _ X; exact X]| exact MU3| exact WM3| exact HP3| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (pl, lh, 104)); [exact INL| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pb, B, 128); (pl, lh, 104); (pk, LK, 40); (pc, C, 16)] LBall (pl, lh, 104) ND3 ltac:(right; left; reflexivity)) as NI.
      apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
    apply Forall_cons; [| apply Forall_nil]. { apply (cseg_ok_block _ _ _ _ _ (pc, C, 16)); [exact INC3| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pb, B, 128); (pl, lh, 104); (pk, LK, 40); (pc, C, 16)] LBall (pc, C, 16) ND3 ltac:(do 3 right; left; reflexivity)) as NI.
      apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. } }
  exists pc, pk, pl, pb, C, LK, lh, B. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RC|]. split; [exact RK|]. split; [exact RL| exact RB].
Qed.
End WithCeiling0.
