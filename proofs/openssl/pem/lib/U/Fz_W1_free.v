(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_clear_free Fz_M_secure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W1_defs Fz_W1_bits.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition FZ_BUF_FREE : Z := 0x116b3c.
Definition BUF_FREE_STACK : Z := 32 + CSF_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W1_buf_free_nodata_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbm : bptr) (BM : Z) (lenw maxw flw : word),
  (1 <= f)%nat -> cown LBall L pbm BM 32 32 ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - BUF_FREE_STACK ->
  a0 = Z_to_bv 64 BM -> rw_cells usegs m BM [C8 lenw; C8 z64; C8 maxw; C8 flw] ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_BUF_FREE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (eq pbm) [] 1 (- wA 32) (- wB 32) (- wBig 32)
                (fun _ LBall' L' _ => LBall' = lb_remove pbm LBall /\ exists i, nth_error L i = Some (pbm, 32) /\ L' = cremove i L)).

Theorem W1_buf_free_nodata_spec : crypto_free_stmt -> W1_buf_free_nodata_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CFR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbm BM lenw maxw flw Hf OWN CST SLO -> BMC.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (BM0 & BM16 & _ & BMCe & _). assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  unfold BUF_FREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK, FZ_BUF_FREE, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 32%nat ST. do 4 step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. step. ubs_if. step. step. th_if_lit.
  do 4 step. do 3 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate st LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FR0 : cframe (eq pbm) [] (bv_unsigned sp) st LBall L m st LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_mono.
  { eapply CFR with (p := pbm) (A := BM) (n := 32) (nm := 32); [exact Hf| exact OWN| exact CSTc| unfold CF_STACK, RFREE_STACK; lia| reflexivity]. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W1_buf_free_data_stmt (sec : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbm : bptr) (BM : Z) (pd : bptr) (D len max nm : Z) (junk : list byte),
  (2 <= f)%nat -> cown LBall L pbm BM 32 32 -> cown LBall L pd D max nm -> pbm <> pd -> 0 <= max < 2 ^ 31 ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - BUF_FREE_STACK ->
  a0 = Z_to_bv 64 BM -> rw_cells usegs m BM (bufmem_cells len D max (Z_to_bv 64 sec)) -> rw_cells usegs m D [CB (Z.to_nat max) junk] ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_BUF_FREE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun q => q = pd \/ q = pbm) [] 2
                (- wA nm - wA 32) (- wB nm - wB 32) (- wBig nm - wBig 32)
                (fun _ LBall' L' _ => exists i j, nth_error L i = Some (pd, nm) /\ nth_error (cremove i L) j = Some (pbm, 32)
                                              /\ L' = cremove j (cremove i L) /\ LBall' = lb_remove pbm (lb_remove pd LBall))).

Theorem W1_buf_free_data_spec : crypto_clear_free_stmt -> crypto_free_stmt -> W1_buf_free_data_stmt 0.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CCF CFR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbm BM pd D len max nm junk Hf OWN OWND NEQ HMAX CST SLO -> BMC DBLK.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (BM0 & BM16 & _ & BMCe & _). assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (D0 & _ & _ & DCe & _).
  unfold BUF_FREE_STACK, CSF_STACK, CCF_STACK, CF_STACK, RFREE_STACK, FZ_BUF_FREE, GLOBALS_TOP, bufmem_cells in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  apply (th_cells_congr usegs m BM _ [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) in BMC;
    [| reflexivity | reflexivity | cbn; tauto].
  (* [comment removed for export] *)
  cprefix. step. carve_frame 32%nat ST. do 4 step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. step. ubs_if. step.
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 3 step. step. th_if_lit.
  do 4 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun q => q = pd \/ q = pbm) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply CCF with (p := pd) (A := D) (n := max) (nm := nm) (num := max) (junk := junk);
      [lia| exact OWND| lia| eassumption| exact CSTc| rewrite unsigned_lit by lia; unfold CCF_STACK, RFREE_STACK; lia| reflexivity| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & i & HN & ->)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  lazymatch goal with FRh : rw_cells _ m0 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. do 4 step. do 3 step.
  release_frame FR1 ST1 (bv_unsigned sp).
  step. step. chere.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST) as [ND NDL].
  assert (OWN1 : cown (lb_remove pd LBall) (cremove i L) pbm BM 32 32).
  { eapply cown_remove; [exact OWN| exact HN| exact NEQ]. }
  assert (CSTd : cstate st1 (lb_remove pd LBall) LB (cremove i L) m1 sp tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 m1 _ sp tp lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia| | eassumption| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRd : cframe (fun q => q = pd \/ q = pbm) [] (bv_unsigned sp) st LBall L m st1 (lb_remove pd LBall) (cremove i L) m1).
  { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ NT E; apply NT; left; symmetry; exact E]
                       | exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_mono.
  { eapply CFR with (p := pbm) (A := BM) (n := 32) (nm := 32); [lia| exact OWN1| exact CSTd| unfold CF_STACK, RFREE_STACK; lia| reflexivity]. }
  intros f' L' s' ms' (v2 & m3 & LB3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (-> & j & HJ & ->)).
  exists v2, m3, (lb_remove pbm (lb_remove pd LBall)).
  split; [exact RET3|]. split; [lia|].
  split. { eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR3)| lia| lia| lia]. }
  split; [exact CST3|].
  split. { eapply cframe_call; [exact FRd| exact FRM3| lia| intros a X; exact X| intros q0 _ NT E; apply NT; right; symmetry; exact E]. }
  exists i, j. auto.
Qed.

Theorem W1_buf_free_sec_spec : crypto_secure_clear_free_stmt -> crypto_free_stmt -> W1_buf_free_data_stmt 1.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CCF CFR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbm BM pd D len max nm junk Hf OWN OWND NEQ HMAX CST SLO -> BMC DBLK.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (BM0 & BM16 & _ & BMCe & _). assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (D0 & _ & _ & DCe & _).
  unfold BUF_FREE_STACK, CSF_STACK, CCF_STACK, CF_STACK, RFREE_STACK, FZ_BUF_FREE, GLOBALS_TOP, bufmem_cells in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  apply (th_cells_congr usegs m BM _ [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max); C1 (Z_to_bv 8 1); CB 7 (repeat (Z_to_bv 8 0) 7)]) in BMC;
    [| reflexivity | reflexivity | cbn; tauto].
  (* [comment removed for export] *)
  cprefix. step. carve_frame 32%nat ST. do 4 step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. step. ubs_if. step.
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 3 step. step. th_if_lit.
  do 4 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun q => q = pd \/ q = pbm) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply CCF with (p := pd) (A := D) (n := max) (nm := nm) (num := max) (junk := junk);
      [lia| exact OWND| lia| eassumption| exact CSTc| rewrite unsigned_lit by lia; unfold CSF_STACK, CF_STACK, RFREE_STACK; lia| reflexivity| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & i & HN & ->)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  lazymatch goal with FRh : rw_cells _ m0 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix.  do 4 step. do 3 step.
  release_frame FR1 ST1 (bv_unsigned sp).
  step. step. chere.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST) as [ND NDL].
  assert (OWN1 : cown (lb_remove pd LBall) (cremove i L) pbm BM 32 32).
  { eapply cown_remove; [exact OWN| exact HN| exact NEQ]. }
  assert (CSTd : cstate st1 (lb_remove pd LBall) LB (cremove i L) m1 sp tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 m1 _ sp tp lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia| | eassumption| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRd : cframe (fun q => q = pd \/ q = pbm) [] (bv_unsigned sp) st LBall L m st1 (lb_remove pd LBall) (cremove i L) m1).
  { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ NT E; apply NT; left; symmetry; exact E]
                       | exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_mono.
  { eapply CFR with (p := pbm) (A := BM) (n := 32) (nm := 32); [lia| exact OWN1| exact CSTd| unfold CF_STACK, RFREE_STACK; lia| reflexivity]. }
  intros f' L' s' ms' (v2 & m3 & LB3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (-> & j & HJ & ->)).
  exists v2, m3, (lb_remove pbm (lb_remove pd LBall)).
  split; [exact RET3|]. split; [lia|].
  split. { eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR3)| lia| lia| lia]. }
  split; [exact CST3|].
  split. { eapply cframe_call; [exact FRd| exact FRM3| lia| intros a X; exact X| intros q0 _ NT E; apply NT; right; symmetry; exact E]. }
  exists i, j. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_MEM_BUF_FREE : Z := 0x183b84.
Definition FZ_MEM_FREE : Z := 0x183a50.
Definition MBF_STACK : Z := 32 + BUF_FREE_STACK.
Definition MEM_FREE_STACK : Z := 32 + MBF_STACK.

Section Arms.
Variables (EVb : nat) (dab dbb dbigb : Z) (Tb : bptr -> Prop)
          (PREb : Z -> list block -> @clist bptr -> mem -> Prop)
          (Rb : list block -> @clist bptr -> list block -> @clist bptr -> Prop).

Definition buf_free_arm : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B BM : Z),
  (EVb <= f)%nat -> cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - BUF_FREE_STACK -> a0 = Z_to_bv 64 BM -> PREb BM LBall L m ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_BUF_FREE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B Tb [] EVb dab dbb dbigb
                (fun _ LBall' L' _ => Rb LBall L LBall' L')).

Definition PREb_stack : Prop :=
  forall BM LBall L m m' x y, PREb BM LBall L m -> munch [(x, y)] m m' -> wmono usegs m m' -> alloc_ceiling <= x -> PREb BM LBall L m'.

Definition W1_mem_buf_free_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbi : bptr) (BI nbi : Z) (pbb : bptr) (BB BM RP fl : Z) (rrw numw padw : word),
  (EVb <= f)%nat -> cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - MBF_STACK -> a0 = Z_to_bv 64 BI ->
  In (pbi, BI, nbi) LBall -> 72 <= nbi -> rw_cells usegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 4294967297) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (pbb, BB, 16) LBall -> rw_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
  PREb BM LBall L m ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_MEM_BUF_FREE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B Tb [] EVb dab dbb dbigb
                (fun v LBall' L' _ => Rb LBall L LBall' L')).

Theorem W1_mem_buf_free_spec : buf_free_arm -> PREb_stack -> W1_mem_buf_free_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros BF PTR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbi BI nbi pbb BB BM RP fl rrw numw padw Hf CST SLO -> INBI HNBI BW FLOK INBB BBC PRE.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBI) as (BI0 & BI16 & _ & BIC & _). assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBB) as (BB0 & BB16 & _ & BBCe & _). assert (BB8 : BB mod 8 = 0) by (clear - BB16; Z.div_mod_to_equations; lia).
  unfold MBF_STACK, BUF_FREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK, FZ_MEM_BUF_FREE, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (fl_ok_byte1 fl FLOK) as RDO.
  apply (proj1 (bio_w1_bytes_view usegs m (BI + 40) fl rrw numw padw _ (proj1 FLOK))) in BW. unfold bio_w1_bytes in BW.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 16%nat ST. do 3 step.
  step. step. ubs_if.
  step. step. th_if_lit. step. step. th_if_lit.
  step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  step. step. ubs_if.
  step. step. step.
  step. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. exact RDO. }
  step. step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 sp tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FR0 : cframe Tb [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  assert (PRE0 : PREb BM LBall L m0) by (eapply PTR; [exact PRE| exact MU| exact WM| lia]).
  eapply climpl_mono.
  { eapply BF with (BM := BM); [exact Hf| exact CSTc| unfold BUF_FREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; lia| reflexivity| exact PRE0]. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.

Definition W1_mem_free_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbi : bptr) (BI nbi : Z) (pbb : bptr) (BB BM : Z) (prp : bptr) (RP fl : Z) (rrw numw padw : word),
  (EVb + 2 <= f)%nat -> cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - MEM_FREE_STACK -> a0 = Z_to_bv 64 BI ->
  In (pbi, BI, nbi) LBall -> 72 <= nbi -> rw_cells usegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 4294967297) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  cown LBall L pbb BB 16 16 -> rw_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] -> cown LBall L prp RP 32 32 ->
  ~ Tb prp -> ~ Tb pbb -> prp <> pbb ->
  PREb BM LBall L m ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_MEM_FREE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun q => Tb q \/ q = prp \/ q = pbb) [] (EVb + 2)
                (dab - wA 32 - wA 16) (dbb - wB 32 - wB 16) (dbigb - wBig 32 - wBig 16)
                (fun v LBall' L' _ => v = Z_to_bv 64 1 /\ exists LB1 L1 i j, Rb LBall L LB1 L1 /\ nth_error L1 i = Some (prp, 32)
                    /\ nth_error (cremove i L1) j = Some (pbb, 16) /\ L' = cremove j (cremove i L1) /\ LBall' = lb_remove pbb (lb_remove prp LB1))).

Theorem W1_mem_free_spec : buf_free_arm -> PREb_stack -> crypto_free_stmt -> W1_mem_free_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros BF PTR CFR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbi BI nbi pbb BB BM prp RP fl rrw numw padw Hf CST SLO -> INBI HNBI BW FLOK OWNB BBC OWNR NTR NTB NERB PRE.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBI) as (BI0 & BI16 & _ & BIC & _). assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB)) as (BB0 & BB16 & _ & BBCe & _). assert (BB8 : BB mod 8 = 0) by (clear - BB16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNR)) as (RP0 & _ & _ & RPCe & _).
  unfold MEM_FREE_STACK, MBF_STACK, BUF_FREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK, FZ_MEM_FREE, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold bio_w1_cells in BW.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 32%nat ST. do 5 step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. ubs_if. step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun q => Tb q \/ q = prp \/ q = pbb) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  assert (PRE0 : PREb BM LBall L m0) by (eapply PTR; [exact PRE| exact MU| exact WM| lia]).
  eapply climpl_seq.
  { eapply (W1_mem_buf_free_spec BF PTR) with (pbi := pbi) (BI := BI) (nbi := nbi) (pbb := pbb) (BB := BB) (BM := BM) (RP := RP) (fl := fl);
      [lia| exact CSTc| rewrite unsigned_lit by lia; unfold MBF_STACK, BUF_FREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; lia| reflexivity| exact INBI| exact HNBI
      | unfold bio_w1_cells; eassumption| exact FLOK| exact (proj1 OWNB)| eassumption| exact PRE0]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & RES).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & [KB KL] & _).
  lazymatch goal with FRh : rw_cells _ m0 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  lazymatch goal with BBh : rw_cells _ m0 BB _ |- _ =>
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbb, BB, 16) CFR1 BBh (proj1 OWNB) NTB
                  ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BBC1 end.
  assert (OWNR1 : cown LB1 L1 prp RP 32 32) by (split; [exact (KB _ (proj1 OWNR) NTR)| exact (KL _ _ (proj2 OWNR) NTR)]).
  assert (OWNB1 : cown LB1 L1 pbb BB 16 16) by (split; [exact (KB _ (proj1 OWNB) NTB)| exact (KL _ _ (proj2 OWNB) NTB)]).
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. ubs_if. step. step. ubs_if. step. do 4 step. step. chere.
  assert (FRa : cframe (fun q => Tb q \/ q = prp \/ q = pbb) [] (bv_unsigned sp) st LBall L m st1 LB1 L1 m1).
  { eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ NT X; apply NT; left; exact X]. }
  eapply climpl_seq.
  { eapply CFR with (p := prp) (A := RP) (n := 32) (nm := 32); [lia| exact OWNR1| exact CST1| rewrite unsigned_lit by lia; unfold CF_STACK, RFREE_STACK; lia| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (-> & i & HI & ->)).
  destruct RET2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  assert (OWNB2 : cown (lb_remove prp LB1) (cremove i L1) pbb BB 16 16) by (eapply cown_remove; [exact OWNB1| exact HI| intros E; apply NERB; symmetry; exact E]).
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. do 4 step. chere.
  assert (FRb : cframe (fun q => Tb q \/ q = prp \/ q = pbb) [] (bv_unsigned sp) st LBall L m st2 (lb_remove prp LB1) (cremove i L1) m2).
  { eapply cframe_call; [exact FRa| exact FRM2| lia| intros a X; exact X| intros q0 _ NT E; apply NT; right; left; symmetry; exact E]. }
  eapply climpl_seq.
  { eapply CFR with (p := pbb) (A := BB) (n := 16) (nm := 16); [lia| exact OWNB2| exact CST2| rewrite unsigned_lit by lia; unfold CF_STACK, RFREE_STACK; lia| reflexivity]. }
  intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (-> & j & HJ & ->)).
  destruct RET3 as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM3 as (CFR3 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FR2 ltac:(lia)) as FR3.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  rewrite unsigned_lit in ST3 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
  (* [comment removed for export] *)
  cprefix. step. do 4 step.
  release_frame FR3 ST3 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  exists (Z_to_bv 64 1), m3, (lb_remove pbb (lb_remove prp LB1)).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) GR3)| lia| lia| lia]. }
  split. { eapply (cstate_seg _ _ _ _ _ m3 m3 _ sp tp lo B (bv_unsigned sp)); [exact CST3| exact MU3| exact WM3| eassumption| | lia| lia| | eassumption| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRb| exact FRM3| lia| intros a X; exact X| intros q0 _ NT E; apply NT; right; right; symmetry; exact E]
                              | exact MU3| exact WM3| exact HP3| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  split; [reflexivity|]. exists LB1, L1, i, j. auto.
Qed.
End Arms.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pre_nodata (pbm : bptr) (BM : Z) (lenw maxw flw : word) : Z -> list block -> @clist bptr -> mem -> Prop :=
  fun BM' LBall L m => BM' = BM /\ cown LBall L pbm BM 32 32 /\ BM + 32 <= alloc_ceiling /\ rw_cells usegs m BM [C8 lenw; C8 z64; C8 maxw; C8 flw].
Definition res_nodata (pbm : bptr) : list block -> @clist bptr -> list block -> @clist bptr -> Prop :=
  fun LBall L LBall' L' => LBall' = lb_remove pbm LBall /\ exists i, nth_error L i = Some (pbm, 32) /\ L' = cremove i L.

Lemma arm_nodata : crypto_free_stmt -> forall pbm BM lenw maxw flw,
  buf_free_arm 1 (- wA 32) (- wB 32) (- wBig 32) (eq pbm) (pre_nodata pbm BM lenw maxw flw) (res_nodata pbm).
Proof.
  intros CFR pbm BM lenw maxw flw. unfold buf_free_arm. intros until BM0. intros Hf CST SLO A0 (-> & OWN & _ & BMC).
  eapply (W1_buf_free_nodata_spec CFR); eassumption.
Qed.
Lemma pre_nodata_stack : forall pbm BM lenw maxw flw, PREb_stack (pre_nodata pbm BM lenw maxw flw).
Proof.
  intros pbm BM lenw maxw flw BM' LBall L m m' x y (-> & OWN & BC & BMC) MU WM HX. split; [reflexivity|]. split; [exact OWN|]. split; [exact BC|].
  eapply rw_cells_transport; [exact BMC| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.

Definition pre_data (sec : Z) (pbm : bptr) (BM : Z) (pd : bptr) (D len max nm : Z) : Z -> list block -> @clist bptr -> mem -> Prop :=
  fun BM' LBall L m => BM' = BM /\ cown LBall L pbm BM 32 32 /\ cown LBall L pd D max nm /\ pbm <> pd /\ 0 <= max < 2 ^ 31
     /\ BM + 32 <= alloc_ceiling /\ D + max <= alloc_ceiling
     /\ rw_cells usegs m BM (bufmem_cells len D max (Z_to_bv 64 sec)) /\ exists junk, rw_cells usegs m D [CB (Z.to_nat max) junk].
Definition res_data (pbm pd : bptr) (nm : Z) : list block -> @clist bptr -> list block -> @clist bptr -> Prop :=
  fun LBall L LBall' L' => exists i j, nth_error L i = Some (pd, nm) /\ nth_error (cremove i L) j = Some (pbm, 32)
                                    /\ L' = cremove j (cremove i L) /\ LBall' = lb_remove pbm (lb_remove pd LBall).

Lemma arm_data : crypto_clear_free_stmt -> crypto_free_stmt -> forall pbm BM pd D len max nm,
  buf_free_arm 2 (- wA nm - wA 32) (- wB nm - wB 32) (- wBig nm - wBig 32) (fun q => q = pd \/ q = pbm) (pre_data 0 pbm BM pd D len max nm) (res_data pbm pd nm).
Proof.
  intros CCF CFR pbm BM pd D len max nm. unfold buf_free_arm. intros until BM0. intros Hf CST SLO A0 (-> & OWN & OWND & NE & HM & _ & _ & BMC & (junk & DB)).
  eapply (W1_buf_free_data_spec CCF CFR); eassumption.
Qed.
Lemma arm_sec : crypto_secure_clear_free_stmt -> crypto_free_stmt -> forall pbm BM pd D len max nm,
  buf_free_arm 2 (- wA nm - wA 32) (- wB nm - wB 32) (- wBig nm - wBig 32) (fun q => q = pd \/ q = pbm) (pre_data 1 pbm BM pd D len max nm) (res_data pbm pd nm).
Proof.
  intros CCF CFR pbm BM pd D len max nm. unfold buf_free_arm. intros until BM0. intros Hf CST SLO A0 (-> & OWN & OWND & NE & HM & _ & _ & BMC & (junk & DB)).
  eapply (W1_buf_free_sec_spec CCF CFR); eassumption.
Qed.
Lemma pre_data_stack : forall sec pbm BM pd D len max nm, PREb_stack (pre_data sec pbm BM pd D len max nm).
Proof.
  intros sec pbm BM pd D len max nm BM' LBall L m m' x y (-> & OWN & OWND & NE & HM & BC & DC & BMC & (junk & DB)) MU WM HX.
  split; [reflexivity|]. split; [exact OWN|]. split; [exact OWND|]. split; [exact NE|]. split; [exact HM|]. split; [exact BC|]. split; [exact DC|].
  split.
  - eapply rw_cells_transport; [exact BMC| exact MU| exact WM| unfold bufmem_cells; cbn [disjoint_from cells_size csize Nat.add]; lia].
  - exists junk. eapply rw_cells_transport; [exact DB| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.
End WithCeiling0.
