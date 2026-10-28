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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_calloc Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_rep Fz_I1_new. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_PROP_DEFNS_NEW : Z := 0xf166c.
Definition PDN_STACK : Z := 16 + LHN_STACK.

Definition pdefns_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (pl pb : bptr) (lh B : Z),
    v = Z_to_bv 64 lh /\ LBall' = (pb, B, 128) :: (pl, lh, 104) :: LBall /\ L' = (pb, 128) :: (pl, 104) :: L /\ rblock_range lh 104 /\ rblock_range B 128.

Definition ossl_property_defns_new_fp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (2 <= f)%nat -> croom L 2 0 0 -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - PDN_STACK ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_PROP_DEFNS_NEW) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 2 2 0 0 (pdefns_res LBall L)).

Theorem ossl_property_defns_new_fp_spec : lh_new_stmt -> ossl_property_defns_new_fp_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LHN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd
         Hf ROOM CST SLO.
  unfold lh_new_stmt in LHN.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold PDN_STACK, LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_PROP_DEFNS_NEW in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. th_frame 16%nat [8; 8]%nat ST. do 2 step. step. do 4 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -16)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply LHN with (DV := fun _ => True) (h := 0xf16c0) (c := 0xf16f4) (lo := lo) (B := Bd);
      [lia| exact ROOM| lia| lia| exact CSTa| rewrite unsigned_lit by lia; unfold LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pl & pb & lh & B & -> & -> & -> & REP)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia).
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof REP as (_ & _ & _ & (x40 & x48 & err & pad & SC) & _).
  assert (INL : In (pl, lh, 104) ((pb, B, 128) :: (pl, lh, 104) :: LBall)) by (right; left; reflexivity).
  assert (INB : In (pb, B, 128) ((pb, B, 128) :: (pl, lh, 104) :: LBall)) by (left; reflexivity).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 INL) as RL. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 INB) as RB.
  pose proof RL as (LH0 & LH16 & _ & LHC & LHIMG).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  unfold lh_cells, wz in SC. cbn [lf_comp lf_hash lf_hashw lf_compw g_nn g_na g_p g_pmax g_items] in SC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (lh + 24, lh + 56)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. do 8 step. do 2 step.
  release_frame FR1 ST1 (bv_unsigned sp). step. step.
  calle (eapply lh_set_thunks_spec with (f := mkFns 0xf16f4 0xf16c0 0 0) (lh := lh) (B := B) (g := mkGeo 8 16 0 8 0) (lo := lo)); try lia.
  all: try (unfold lh_cells, wz; cbn [lf_comp lf_hash lf_hashw lf_compw g_nn g_na g_p g_pmax g_items]; exact SC).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  chere. apply climpl_done.
  eexists. exists mf, ((pb, B, 128) :: (pl, lh, 104) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [exact GR1|].
  split. { eapply (cstate_seg _ _ _ _ _ m1 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
      apply (cwin_block _ _ _ (pl, lh, 104)); [exact INL| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRa| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (pl, lh, 104)); [exact INL| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pb, B, 128); (pl, lh, 104)] LBall (pl, lh, 104) ND1 ltac:(right; left; reflexivity)) as NI.
    apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
  exists pl, pb, lh, B. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RL| exact RB].
Qed.
End WithCeiling0.
