(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc F_strlen F_memcpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_CRYPTO_STRDUP : Z := 0xea4cc.
Definition SD_STACK : Z := 48 + CM_STACK.

Definition sd_res (str : list byte) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists p A, v = Z_to_bv 64 A /\ LBall' = (p, A, Z.of_nat (length str) + 1) :: LBall /\ L' = (p, Z.of_nat (length str) + 1) :: L
                      /\ rblock_range A (Z.of_nat (length str) + 1) /\ rw_cells usegs m' A [CB (S (length str)) (str ++ [Z_to_bv 8 0])].

(* [comment removed for export] *)
Definition crypto_strdup_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (S lo B : Z) (str slack : list byte),
  (1 <= f)%nat -> croom L (wA (Z.of_nat (length str) + 1)) (wB (Z.of_nat (length str) + 1)) (wBig (Z.of_nat (length str) + 1)) ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SD_STACK -> a0 = Z_to_bv 64 S ->
  ro_bytes usegs S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0x10000 <= S -> S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 0x2c0000 -> Z.of_nat (length str) + 1 < 2 ^ 31 ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_CRYPTO_STRDUP) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 1
           (wA (Z.of_nat (length str) + 1)) (wB (Z.of_nat (length str) + 1)) (wBig (Z.of_nat (length str) + 1)) (sd_res str LBall L)).

Theorem crypto_strdup_spec : crypto_malloc_stmt -> crypto_strdup_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f S lo B str slack
         Hf ROOM CST SLO -> ROB NONUL PAD SLOW SHIGH NLEN.
  unfold crypto_malloc_stmt in CM.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold SD_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_CRYPTO_STRDUP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  set (len := Z.of_nat (length str)) in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 6 step. step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  do 3 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  lazymatch goal with H : mem_inv usegs ma |- _ =>
    assert (STRa : bytes_at usegs ma S (str ++ Z_to_bv 8 0 :: slack)) by (apply ro_bytes_at; [exact H| lia| rewrite length_app; cbn [length]; lia| exact ROB]) end.
  tcall (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str slack).
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. fold len.
  (* [comment removed for export] *)
  do 4 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into mb end.
  lazymatch goal with H : stk _ mb _ _ |- _ => rename H into STb end.
  lazymatch goal with H : mem_inv _ mb |- _ => rename H into MIb end.
  assert (CSTb : cstate s LBall LB L mb (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m mb _ _ _ lo B (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIb| | lia| lia| | rewrite unsigned_lit by lia; exact STb| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRb : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m s LBall L mb).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply CM with (n := len + 1) (lo := lo) (B := B); [lia| exact ROOM| lia| exact CSTb| rewrite unsigned_lit by lia; unfold CM_STACK, RMALLOC_STACK; lia| subst len; reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (p & A & junk1 & -> & -> & -> & RNG & BLK)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia).
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (A0 & _ & _ & AC & AIMG).
  assert (INA : In (p, A, len + 1) ((p, A, len + 1) :: LBall)) by (left; reflexivity).
  assert (STR1 : bytes_at usegs m1 S (str ++ Z_to_bv 8 0 :: slack)) by (apply ro_bytes_at; [exact MI1| lia| rewrite length_app; cbn [length]; lia| exact ROB]).
  apply bytes_at_app in STR1. destruct STR1 as [STRs _].
  assert (STRz : bytes_at usegs m1 S (str ++ [Z_to_bv 8 0])).
  { apply ro_bytes_at; [exact MI1| lia| rewrite length_app; cbn [length]; lia|].
    clear - ROB. revert ROB. generalize S. induction str as [|b str IH]; intros S0 H; cbn [app ro_bytes] in H |- *; [exact (conj (proj1 H) I)| exact (conj (proj1 H) (IH _ (proj2 H)))]. }
  pose proof (munch_refl [(A, A + (len + 1))]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. do 6 step.
  lazymatch goal with H : stk usegs m1 lo _ |- _ => rename H into ST2 end.
  release_frame FR1 ST2 (bv_unsigned sp). step. step.
  lazymatch goal with H : rw_cells usegs m1 A _ |- _ => rename H into BLK1 end.
  tcall (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (str ++ [Z_to_bv 8 0])).
  all: try first [eassumption | lia | rewrite length_app; cbn [length]; lia].
  cbv beta delta [mkR].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  lazymatch goal with H : rw_cells usegs mf A _ |- _ => rename H into BLKf end.
  chere. apply climpl_done.
  eexists. exists mf, ((p, A, len + 1) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [exact GR1|].
  split. { eapply (cstate_seg _ _ _ _ _ m1 mf _ sp _ lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [| apply Forall_nil]. apply (cwin_block _ _ _ (p, A, len + 1)); [exact INA| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRb| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (p, A, len + 1)); [exact INA| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros [[q A'] n'] Hb0 _ E1. cbn [blk_id fst] in E1. exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 Hb0 E1). }
  exists p, A. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|].
  replace (Datatypes.S (length str)) with (Z.to_nat (len + 1)) by lia. exact BLKf.
Qed.
End WithCeiling0.
