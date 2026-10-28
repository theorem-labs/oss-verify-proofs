(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_BUF_NEW_EX : Z := 0x116ab8.
Definition BUF_NEW_STACK : Z := 32 + CZ_STACK.

Definition buf_new_res (flw : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists p A, v = Z_to_bv 64 A /\ LBall' = (p, A, 32) :: LBall /\ L' = (p, 32) :: L /\ rblock_range A 32
     /\ rw_cells usegs m' A (bufmem_cells 0 0 0 flw).

Definition W1_buf_new_ex_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (1 <= f)%nat -> croom L (wA 32) (wB 32) (wBig 32) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - BUF_NEW_STACK ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_BUF_NEW_EX) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) [] 1 (wA 32) (wB 32) (wBig 32)
                (buf_new_res a0 LBall L)).

Theorem W1_buf_new_ex_spec : crypto_zalloc_stmt -> W1_buf_new_ex_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         Hf ROOM CST SLO.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold BUF_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_BUF_NEW_EX, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 32%nat ST. do 4 step. do 6 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply CZ with (n := 32); [exact Hf| exact ROOM| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU & GR & CST1 & FRM1 & (p & A & -> & -> & -> & RNG & BLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  lazymatch goal with FRh : rw_cells _ m0 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (A0 & A16 & _ & AC & AIMG). assert (A8 : A mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
  change (Z.to_nat 32) with 32%nat in BLK.
  apply (th_cells_congr usegs m1 A _ (bufmem_cells 0 0 0 z64)) in BLK; [| reflexivity | reflexivity | cbn; tauto].
  unfold bufmem_cells in BLK.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 32)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  step. step. ubs_if. step. do 3 step.
  release_frame FR1 ST1 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  exists (Z_to_bv 64 A), m2, ((p, A, 32) :: LBall).
  assert (INB : In (p, A, 32) ((p, A, 32) :: LBall)) by (left; reflexivity).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU|]. split; [exact GR|].
  split. { eapply (cstate_seg [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 32)]%Z _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp));
           [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia| | eassumption | exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (p, A, 32)); [exact INB| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (p, A, 32)); [exact INB| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    destruct FR0 as (_ & KP0 & _). destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _]. exact (cfresh_new _ _ _ _ _ _ KP0 ND1). }
  exists p, A. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|]. unfold bufmem_cells. eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_MEM_INIT : Z := 0x183c00.
Definition MEM_INIT_STACK : Z := 48 + BUF_NEW_STACK.

Definition mem_init_res (BI : Z) (flw : word) (fl : Z) (rrw padw : word) (hd tl : list cell) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists prp RP pbm BM pbb BB,
       v = Z_to_bv 64 1
    /\ LBall' = (prp, RP, 32) :: (pbm, BM, 32) :: (pbb, BB, 16) :: LBall /\ L' = (prp, 32) :: (pbm, 32) :: (pbb, 16) :: L
    /\ rblock_range RP 32 /\ rblock_range BM 32 /\ rblock_range BB 16
    /\ rw_cells usegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 4294967297) (Z.lor fl 4096) rrw (Z_to_bv 64 (-1)) padw (Z_to_bv 64 BB))
    /\ rw_cells usegs m' BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)]
    /\ rw_cells usegs m' BM (bufmem_cells 0 0 0 flw) /\ rw_cells usegs m' RP (bufmem_cells 0 0 0 flw)
    (* [comment removed for export] *)
    /\ rw_cells usegs m' BI hd /\ rw_cells usegs m' (BI + 72) tl.

Definition W1_mem_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbi : bptr) (BI nbi fl : Z) (isw rrw numw padw ptrw : word) (hd tl : list cell),
  (3 <= f)%nat -> croom L (wA 16 + wA 32 + wA 32) (wB 16 + wB 32 + wB 32) (wBig 16 + wBig 32 + wBig 32) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - MEM_INIT_STACK ->
  a0 = Z_to_bv 64 BI -> In (pbi, BI, nbi) LBall -> 72 <= nbi ->
  rw_cells usegs m (BI + 40) (bio_w1_cells isw fl rrw numw padw ptrw) -> fl_ok fl ->
  rw_cells usegs m BI hd -> cells_size hd = 40%nat -> rw_cells usegs m (BI + 72) tl -> Z.of_nat (cells_size tl) <= nbi - 72 ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_MEM_INIT) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (eq pbi) [] 3
                (wA 16 + wA 32 + wA 32) (wB 16 + wB 32 + wB 32) (wBig 16 + wBig 32 + wBig 32) (mem_init_res BI a1 fl rrw padw hd tl LBall L)).

Theorem W1_mem_init_spec : crypto_zalloc_stmt -> W1_mem_init_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbi BI nbi fl isw rrw numw padw ptrw hd tl Hf ROOM CST SLO -> INBI HNBI BW FLOK HD HDS TL TLS.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBI) as (BI0 & BI16 & _ & BIC & _). assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  unfold MEM_INIT_STACK, BUF_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_MEM_INIT, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (w_bounds 16 ltac:(lia)) as W16. pose proof (w_bounds 32 ltac:(lia)) as W32.
  unfold bio_w1_cells in BW.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 48%nat ST. do 6 step. do 7 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (eq pbi) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply CZ with (n := 16); [lia| eapply croom_weaken; [exact ROOM| lia..]| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (pbb & BB & -> & -> & -> & RNGB & BBC)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNGB as (BB0 & BB16 & _ & BBCe & _). assert (BB8 : BB mod 8 = 0) by (clear - BB16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  do 3 step. chere.
  assert (INBB : In (pbb, BB, 16) ((pbb, BB, 16) :: LBall)) by (left; reflexivity).
  assert (FRa : cframe (eq pbi) [] (bv_unsigned sp) st LBall L m st1 ((pbb, BB, 16) :: LBall) ((pbb, 16) :: L) m1).
  { eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ _ X; exact X]. }
  eapply climpl_seq.
  { eapply (W1_buf_new_ex_spec CZ); [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| lia..]| exact CST1
      | rewrite unsigned_lit by lia; unfold BUF_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pbm & BM & -> & -> & -> & RNGM & BMC)).
  destruct RET2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  change (Z.to_nat 16) with 16%nat in BBC.
  apply (th_cells_congr usegs m1 BB _ [C8 z64; C8 z64]) in BBC; [| reflexivity | reflexivity | cbn; tauto].
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbb, BB, 16) CFR2 BBC INBB ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BBC2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RNGM as (BM0 & _ & _ & BMCe & _).
  unfold bufmem_cells in BMC.
  assert (INBB2 : In (pbb, BB, 16) ((pbm, BM, 32) :: (pbb, BB, 16) :: LBall)) by (right; left; reflexivity).
  assert (INBM2 : In (pbm, BM, 32) ((pbm, BM, 32) :: (pbb, BB, 16) :: LBall)) by (left; reflexivity).
  assert (NEMB : pbb <> pbm) by (eapply cstate_head_fresh; [exact CST2| left; reflexivity]).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INBB2 INBM2 NEMB) as APBM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (BB, BB + 16)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. step. step. ubs_if. ths. step. if_cases K4; zify_cond K4. { exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  do 5 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mb end.
  assert (INBI2 : In (pbi, BI, nbi) ((pbm, BM, 32) :: (pbb, BB, 16) :: LBall)) by (right; right; exact INBI).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (CSTb : cstate st2 ((pbm, BM, 32) :: (pbb, BB, 16) :: LBall) LB ((pbm, 32) :: (pbb, 16) :: L) mb (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m2 mb _ _ tp lo B (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MI2| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pbb, BB, 16)); [exact INBB2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - pose proof RNGB as (_ & _ & _ & _ & BBIMG). cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST2.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRb : cframe (eq pbi) [] (bv_unsigned sp) st LBall L m st2 ((pbm, BM, 32) :: (pbb, BB, 16) :: LBall) ((pbm, 32) :: (pbb, 16) :: L) mb).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa| exact FRM2| lia| intros a X; exact X| intros q0 _ _ X; exact X]| exact MU2| exact WM2| exact HP2| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (pbb, BB, 16)); [exact INBB2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    destruct FR0 as (_ & KP0 & _). exact (cfresh_new _ _ _ _ _ _ KP0 ND1). }
  eapply climpl_seq.
  { eapply CZ with (n := 32); [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2))| lia..]| lia| exact CSTb
      | rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (prp & RP & -> & -> & -> & RNGR & RPC)).
  destruct RET3 as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM3 as (CFR3 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FR2 ltac:(lia)) as FR3.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbb, BB, 16) CFR3 BBC2 INBB2 ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BBC3.
  (* [comment removed for export] *)
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbm, BM, 32) CFR3 BMC INBM2 ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BMC3.
  assert (NEIB : pbi <> pbb) by (eapply cstate_head_fresh; [exact CST1| exact INBI]).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (or_intror INBI) INBB NEIB) as APIB.
  unfold bio_w1_cells in BW.
  assert (BW3 : rw_cells usegs m3 (BI + 40) [C8 isw; C4 (Z_to_bv 64 fl); C4 rrw; C4 numw; C4 padw; C8 ptrw]).
  { eapply (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR3); [| exact INBI2| intros X; exact X| unfold blk_addr; cbn [fst snd]; lia
                                                                    | unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia].
    eapply rw_cells_transport; [| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia].
    eapply (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR2); [| right; exact INBI| intros X; exact X| unfold blk_addr; cbn [fst snd]; lia
                                                                    | unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia].
    eapply (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR1); [exact BW| exact INBI| intros X; exact X| unfold blk_addr; cbn [fst snd]; lia
                                                                    | unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia]. }
  (* [comment removed for export] *)
  assert (HD3 : rw_cells usegs m3 BI hd).
  { eapply (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR3); [| exact INBI2| intros X; exact X| unfold blk_addr; cbn [fst snd]; lia
                                                                    | unfold blk_addr, blk_size; cbn [fst snd]; rewrite HDS; lia].
    eapply rw_cells_transport; [| exact MU2| exact WM2| rewrite HDS; cbn [disjoint_from]; lia].
    eapply (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR2); [| right; exact INBI| intros X; exact X| unfold blk_addr; cbn [fst snd]; lia
                                                                    | unfold blk_addr, blk_size; cbn [fst snd]; rewrite HDS; lia].
    eapply (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR1); [exact HD| exact INBI| intros X; exact X| unfold blk_addr; cbn [fst snd]; lia
                                                                    | unfold blk_addr, blk_size; cbn [fst snd]; rewrite HDS; lia]. }
  assert (TL3 : rw_cells usegs m3 (BI + 72) tl).
  { eapply (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR3); [| exact INBI2| intros X; exact X| unfold blk_addr; cbn [fst snd]; lia
                                                                    | unfold blk_addr, blk_size; cbn [fst snd]; lia].
    eapply rw_cells_transport; [| exact MU2| exact WM2| cbn [disjoint_from]; lia].
    eapply (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR2); [| right; exact INBI| intros X; exact X| unfold blk_addr; cbn [fst snd]; lia
                                                                    | unfold blk_addr, blk_size; cbn [fst snd]; lia].
    eapply (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR1); [exact TL| exact INBI| intros X; exact X| unfold blk_addr; cbn [fst snd]; lia
                                                                    | unfold blk_addr, blk_size; cbn [fst snd]; lia]. }
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  rewrite unsigned_lit in ST3 by lia.
  pose proof RNGR as (RP0 & _ & _ & RPCe & _).
  assert (INRP3 : In (prp, RP, 32) ((prp, RP, 32) :: (pbm, BM, 32) :: (pbb, BB, 16) :: LBall)) by (left; reflexivity).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST3 (or_intror INBM2) INRP3 ltac:(eapply cstate_head_fresh; [exact CST3| exact INBM2])) as APMR.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST3 (or_intror INBB2) INRP3 ltac:(eapply cstate_head_fresh; [exact CST3| exact INBB2])) as APBR.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST3 (or_intror INBI2) INRP3 ltac:(eapply cstate_head_fresh; [exact CST3| exact INBI2])) as APIR.
  assert (NEIM : pbi <> pbm) by (eapply cstate_head_fresh; [exact CST2| right; exact INBI]).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INBI2 INBM2 NEIM) as APIM.
  change (Z.to_nat 32) with 32%nat in RPC.
  apply (th_cells_congr usegs m3 RP _ [C8 z64; C8 z64; C8 z64; C8 z64]) in RPC; [| reflexivity | reflexivity | cbn; tauto].
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (BB, BB + 16); (RP, RP + 32); (BI + 40, BI + 72)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
  (* [comment removed for export] *)
  cprefix. step. ths. step. if_cases K5; zify_cond K5. { exfalso. rewrite ?unsigned_lit in K5 by lia. lia. }
  ths. ths. ths. ths. ths. ths. ths. ths. step. ubs_if. step. step. ubs_if.
  step. rewrite (t_sx32_small fl) by (destruct FLOK; lia).
  do 6 step. ths. ths. ths. ths. step.
  do 5 step.
  th_release FR3 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
  clear APMR APBR APIR APIM APIB APBM.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _].
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [ND3 _].
  exists (Z_to_bv 64 1), m4, ((prp, RP, 32) :: (pbm, BM, 32) :: (pbb, BB, 16) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) GR3)|].
  pose proof RNGB as (_ & _ & _ & _ & BBIMG). pose proof RNGR as (_ & _ & _ & _ & RPIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBI) as (_ & _ & _ & _ & BIIMG).
  split. { eapply (cstate_seg _ _ _ _ _ m3 m4 _ sp tp lo B (bv_unsigned sp)); [exact CST3| exact MU3| exact WM3| exact MI3| | lia| lia| | exact ST3| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pbb, BB, 16)); [right; exact INBB2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (prp, RP, 32)); [exact INRP3| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pbi, BI, nbi)); [right; exact INBI2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRb| exact FRM3| lia| intros a X; exact X| intros q0 _ _ X; exact X]| exact MU3| exact WM3| exact HP3| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
    - apply (cseg_ok_block _ _ _ _ _ (pbb, BB, 16)); [right; exact INBB2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      destruct FR0 as (_ & KP0 & _). exact (cfresh_new _ _ _ _ _ _ KP0 ND1).
    - apply (cseg_ok_block _ _ _ _ _ (prp, RP, 32)); [exact INRP3| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      destruct FRb as (_ & KPb & _). exact (cfresh_new _ _ _ _ _ _ KPb ND3).
    - apply (cseg_ok_block _ _ _ _ _ (pbi, BI, nbi)); [right; exact INBI2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 _ NT E. apply NT. unfold blk_id in E. cbn [fst snd] in E. symmetry. exact E. }
  exists prp, RP, pbm, BM, pbb, BB. unfold bio_w1_cells, bufmem_cells.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNGR|]. split; [exact RNGM|]. split; [exact RNGB|].
  split. { rewrite unsigned_lit in BW3 by (destruct FLOK; lia). exact BW3. }
  split; [exact BBC3|]. split; [exact BMC3|]. split; [exact RPC|].
  split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W1_mem_new_stmt (ENTRY : Z) (flags : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbi : bptr) (BI nbi fl : Z) (isw rrw numw padw ptrw : word) (hd tl : list cell),
  (3 <= f)%nat -> croom L (wA 16 + wA 32 + wA 32) (wB 16 + wB 32 + wB 32) (wBig 16 + wBig 32 + wBig 32) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - MEM_INIT_STACK ->
  a0 = Z_to_bv 64 BI -> In (pbi, BI, nbi) LBall -> 72 <= nbi ->
  rw_cells usegs m (BI + 40) (bio_w1_cells isw fl rrw numw padw ptrw) -> fl_ok fl ->
  rw_cells usegs m BI hd -> cells_size hd = 40%nat -> rw_cells usegs m (BI + 72) tl -> Z.of_nat (cells_size tl) <= nbi - 72 ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (eq pbi) [] 3
                (wA 16 + wA 32 + wA 32) (wB 16 + wB 32 + wB 32) (wBig 16 + wBig 32 + wBig 32) (mem_init_res BI (Z_to_bv 64 flags) fl rrw padw hd tl LBall L)).

Theorem W1_mem_new_spec : crypto_zalloc_stmt -> W1_mem_new_stmt 0x183a2c 0.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbi BI nbi fl isw rrw numw padw ptrw hd tl Hf ROOM CST SLO -> INBI HNBI BW FLOK HD HDS TL TLS.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBI) as (BI0 & _ & _ & BIC & _).
  unfold MEM_INIT_STACK, BUF_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold bio_w1_cells in BW.
  cprefix. step. carve_frame 16%nat ST. do 3 step. step. do 2 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate st LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FR0 : cframe (eq pbi) [] (bv_unsigned sp) st LBall L m st LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_mono.
  { eapply (W1_mem_init_spec CZ) with (pbi := pbi) (BI := BI) (nbi := nbi) (fl := fl);
      [exact Hf| exact ROOM| exact CSTc| unfold MEM_INIT_STACK, BUF_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| exact INBI| exact HNBI| eassumption| exact FLOK| eassumption| exact HDS| eassumption| exact TLS]. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.
Theorem W1_secmem_new_spec : crypto_zalloc_stmt -> W1_mem_new_stmt 0x183d24 1.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbi BI nbi fl isw rrw numw padw ptrw hd tl Hf ROOM CST SLO -> INBI HNBI BW FLOK HD HDS TL TLS.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBI) as (BI0 & _ & _ & BIC & _).
  unfold MEM_INIT_STACK, BUF_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold bio_w1_cells in BW.
  cprefix. step. carve_frame 16%nat ST. do 3 step. step. do 2 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate st LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FR0 : cframe (eq pbi) [] (bv_unsigned sp) st LBall L m st LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_mono.
  { eapply (W1_mem_init_spec CZ) with (pbi := pbi) (BI := BI) (nbi := nbi) (fl := fl);
      [exact Hf| exact ROOM| exact CSTc| unfold MEM_INIT_STACK, BUF_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| exact INBI| exact HNBI| eassumption| exact FLOK| eassumption| exact HDS| eassumption| exact TLS]. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.
End WithCeiling0.
