(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W3_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Definition null_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' _ => v = wz 0 /\ LBall' = LBall /\ L' = L.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition crypto_malloc0_stmt (ENTRY STK : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - STK -> a0 = wz 0 ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz ENTRY) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 0 0 0 0 (null_res LBall L)).

Theorem crypto_malloc0_spec : crypto_malloc0_stmt FZ_CRYPTO_MALLOC CM_STACK.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo B CST SLO ->.
  pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & (_ & _ & GOTM & IMPL & _ & _) & _ & _ & GLO).
  unfold CM_STACK, RMALLOC_STACK, LX_GOT_FLAGS, LX_STORAGE_FN, FZ_CRYPTO_MALLOC, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 48%nat ST. do 5 step. do 8 step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
  step. do 6 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => release_frame FRh ST (bv_unsigned sp) end. step.
  chere. apply climpl_done.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mz end.
  lazymatch goal with H : stk usegs mz lo _ |- _ => rename H into STf end. lazymatch goal with H : mem_inv usegs mz |- _ => rename H into MIf end.
  exists (wz 0), mz, LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [unfold cgrow; lia|].
  split. { eapply (cstate_seg _ _ _ _ _ m mz _ sp _ lo B (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - constructor; [apply cwin_stack; lia| constructor]. - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  unfold null_res. auto.
Qed.

Theorem crypto_secure_malloc0_spec : crypto_malloc0_stmt FZ_SECURE_MALLOC CSM_STACK.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo B CST SLO ->.
  pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold CSM_STACK, CM_STACK, RMALLOC_STACK, FZ_SECURE_MALLOC, GLOBALS_TOP in *.
  cimg_cell CIMG m 0x32e030 [C1 (Z_to_bv 8 0)] SMI.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 144%nat ST. do 20 step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  do 18 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -144) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate s LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ s LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia. }
  assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_mono.
  { eapply crypto_malloc0_spec; [exact CSTc| unfold CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem pem_malloc_spec : crypto_malloc_stmt -> crypto_secure_malloc_stmt -> pem_malloc_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM CSM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f n flags lo B
         Hf ROOM N FL CST SLO -> ->.
  unfold crypto_malloc_stmt in CM. unfold crypto_secure_malloc_stmt in CSM.
  pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold PMAL_STACK, CSM_STACK, CM_STACK, RMALLOC_STACK, FZ_PEM_MALLOC, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 16%nat ST. do 3 step. step.
  assert (JOIN : forall mc (pc : Z) y1,
    (pc = FZ_CRYPTO_MALLOC \/ pc = FZ_SECURE_MALLOC) ->
    stk usegs mc lo (bv_unsigned sp) -> munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz n) y1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc) fc None mc (seg_rom usegs))
           (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 1 (wA n) (wB n) (wBig n) (cs_malloc_res n LBall L))).
  { intros mc pc y1 PC STc MUc WMc MIc.
    assert (CSTc : cstate s LBall LB L mc sp tp lo B).
    { eapply (cstate_seg _ s LBall LB L m mc sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
      - constructor; [apply cwin_stack; lia| constructor]. - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) s LBall L m s LBall L mc).
    { eapply cframe_seg; [apply cframe_refl| exact MUc| exact WMc| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
    eapply climpl_mono.
    { destruct PC as [-> | ->].
      - eapply CM with (n := n); [exact Hf| exact ROOM| lia| exact CSTc| unfold CM_STACK, RMALLOC_STACK; lia| reflexivity].
      - eapply CSM with (n := n); [exact Hf| exact ROOM| lia| exact CSTc| unfold CSM_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
    intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X]. }
  step. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    do 4 step. lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end. step. step.
    chere. eapply JOIN; [right; reflexivity| eassumption..].
  - do 4 step. lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end. step. step.
    chere. eapply JOIN; [left; reflexivity| eassumption..].
Qed.

Theorem pem_malloc0_spec : pem_malloc0_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f flags lo B FL CST SLO -> ->.
  pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold PMAL_STACK, CSM_STACK, CM_STACK, RMALLOC_STACK, FZ_PEM_MALLOC, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 16%nat ST. do 3 step. step.
  assert (JOIN : forall mc (pc : Z) y1,
    (pc = FZ_CRYPTO_MALLOC \/ pc = FZ_SECURE_MALLOC) ->
    stk usegs mc lo (bv_unsigned sp) -> munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) y1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc) fc None mc (seg_rom usegs))
           (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 0 0 0 0 (fun v LBall' L' _ => v = wz 0 /\ LBall' = LBall /\ L' = L))).
  { intros mc pc y1 PC STc MUc WMc MIc.
    assert (CSTc : cstate s LBall LB L mc sp tp lo B).
    { eapply (cstate_seg _ s LBall LB L m mc sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
      - constructor; [apply cwin_stack; lia| constructor]. - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) s LBall L m s LBall L mc).
    { eapply cframe_seg; [apply cframe_refl| exact MUc| exact WMc| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
    eapply climpl_mono.
    { destruct PC as [-> | ->].
      - eapply crypto_malloc0_spec; [exact CSTc| unfold CM_STACK, RMALLOC_STACK; lia| reflexivity].
      - eapply crypto_secure_malloc0_spec; [exact CSTc| unfold CSM_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
    intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X]. }
  step. if_cases K0; zify_cond K0.
  - do 4 step. lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end. step. step.
    chere. eapply JOIN; [right; reflexivity| eassumption..].
  - do 4 step. lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end. step. step.
    chere. eapply JOIN; [left; reflexivity| eassumption..].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem pem_free_spec : crypto_free_stmt -> crypto_secure_clear_free_stmt -> pem_free_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CF CSF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f p A n nm num flags lo B junk
         Hf OWN NUM PC FL CST SLO -> -> ->.
  unfold crypto_free_stmt in CF. unfold crypto_secure_clear_free_stmt in CSF.
  pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (PA0 & _ & PN0 & PAC & PAIMG).
  unfold PFREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK, FZ_PEM_FREE, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 16%nat ST. do 3 step. step.
  assert (JOIN : forall mc (pc : Z) y1 y2 y4,
    ((pc = FZ_CRYPTO_FREE) \/ (pc = FZ_SECURE_CLEAR_FREE /\ y1 = wz num)) ->
    stk usegs mc lo (bv_unsigned sp) -> munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc -> rw_cells usegs mc A [CB (Z.to_nat num) junk] ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) y1 y2 a3 y4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc) fc None mc (seg_rom usegs))
           (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 1 (- wA nm) (- wB nm) (- wBig nm) (pem_free_res p nm LBall L))).
  { intros mc pc y1 y2 y4 PCC STc MUc WMc MIc PCc.
    assert (CSTc : cstate s LBall LB L mc sp tp lo B).
    { eapply (cstate_seg _ s LBall LB L m mc sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
      - constructor; [apply cwin_stack; lia| constructor]. - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    assert (FR0 : cframe (eq p) [] (bv_unsigned sp) s LBall L m s LBall L mc).
    { eapply cframe_seg; [apply cframe_refl| exact MUc| exact WMc| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
    eapply climpl_mono.
    { destruct PCC as [-> | [-> ->]].
      - eapply CF with (p := p) (A := A); [exact Hf| exact OWN| exact CSTc| unfold CF_STACK, RFREE_STACK; lia| reflexivity].
      - eapply CSF with (p := p) (A := A) (num := num); [exact Hf| exact OWN| exact NUM| exact PCc| exact CSTc| unfold CSF_STACK, CF_STACK, RFREE_STACK; lia| reflexivity| reflexivity]. }
    intros f' L' s' ms'. unfold pem_free_res. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X]. }
  step. if_cases K0; zify_cond K0.
  - do 6 step. lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end. step. step.
    chere. eapply JOIN; [right; split; reflexivity| eassumption..].
  - do 5 step. lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end. step. step.
    chere. eapply JOIN; [left; reflexivity| eassumption..].
Qed.

Theorem pem_free_null_spec : pem_free_null_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f flags lo B FL CST SLO -> ->.
  pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & LXS & _ & _ & GLO).
  unfold PFREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK, FZ_PEM_FREE, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (FIN : forall mz (x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word),
    stk usegs mz lo (bv_unsigned sp) -> munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m mz -> wmono usegs m mz -> mem_inv usegs mz ->
    cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 0 0 0 0 (fun _ LBall' L' _ => LBall' = LBall /\ L' = L)
          f L s (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 y0 y1 y2 y3 y4 y5 y6 y7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6) F (ret_pc ra) fc None mz (seg_rom usegs))).
  { intros mz x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 STz MUz WMz MIz. exists y0, mz, LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [unfold cgrow; lia|].
    split. { eapply (cstate_seg _ _ _ _ _ m mz _ sp _ lo B (bv_unsigned sp)); [exact CST| exact MUz| exact WMz| exact MIz| | lia| exact SPB| | exact STz| exact SPB].
      - constructor; [apply cwin_stack; lia| constructor]. - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    split; [| auto]. eapply cframe_seg; [apply cframe_refl| exact MUz| exact WMz| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  cprefix. step. carve_frame 16%nat ST. do 3 step. step.
  step. if_cases K0; zify_cond K0.
  - do 6 step. lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end. step. step.
    tcallr crypto_secure_clear_free_null. all: try first [eassumption | reflexivity | lia].
    chere. apply climpl_done. eapply FIN; eassumption.
  - do 5 step. lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (LXSc : lx_statics mc) by (eapply lx_statics_agree; [eapply agree_on_of_munch; eassumption| | exact LXS];
        intros a Ha; unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha; cbn [outside]; lia) end.
    tcallr crypto_free_null. all: try first [eassumption | reflexivity | lia].
    chere. apply climpl_done. eapply FIN; eassumption.
Qed.
End WithCeiling0.
