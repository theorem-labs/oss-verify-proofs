(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Stdio Prog ZTarget Target ZApi ZHarness ZInst.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocU Require Import RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Monad.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd Z_kit Z_infl_top_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Layout Drv_kit F_fwrite Zlib_iface Zh_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_irep Z_ikit Z_infl_pro Z_infl_loop Zg_infl_arms Z_updwin_pure Z_updwin Zg_updwin_pure Zg_updwin_iface Z_infl_leave Z_infl_leave2
  Z_inflate_glue Z_inflate_mem Zg_inflate_mem Zg_infl_iface Zg_zlib_iface Zg_inflate_top Z_infl_defs Zg_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate HarnessSmall RefInflateSafeD RefInflateSafeTY RefInflateEqS
  RefInflate_runA RefUpdWin1 RefInflateRel RefInflateEqB InflateFrameIn ZApiInst ZTaintI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
#[local] Transparent the_zapi.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section OK.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  Hypothesis ARMS : arms_okg 0.
  Hypothesis ADLER32 : adler32_stmt.
  Hypothesis UPDW_HAVE : updwin_have_stmt.
  Hypothesis UPDW_BLOCK : updwin_ret_block_stmt.
  Variable R : zreps.
  Hypothesis ER : zr_i R = zr_i_def.

  Theorem inflate_okG : inflate_stmtG R.
  Proof.
    unfold inflate_stmtG. intros until canary. intros ENV PUB ZR INC CARR LCL CBYT INU UARR LUC RTI1 RTI2 RTI3 RTI4 RNO1 RNO2 RNO3 RNO4 RTO1 RTO2 SEPCU SIF LOSP SP16 FRM0 -> ->.
    rewrite ER in ZR. destruct ZR as (s_a & L0 & w' & sp' & ES & EL & HW & HR & HI & HA & HP).
    destruct (iblocks_inv _ _ _ _ _ _ _ _ EL) as (-> & -> & EAs & EAw).
    rewrite EL in ENV. rewrite EAs in *.
    apply (IREPq_relay m L0 s_a _ (C + i_total_in the_zapi is) (U + no)) in HR. rewrite ES, EAs in HR. destruct HR as [HZQ HIST].
    unfold the_zapi in *. cbn [i_total_in i_total_out zinst] in *. change ZApi.Z_NO_FLUSH with 0.
    eapply (top_stmt MALLOC HFRAME HBR HND HBD ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB S C U cl size comprc uc is w Aw sp_ As p1 p2 lo B errv canary s_a (il_Aw L0) ain no aout);
      try eassumption; try lia.
    (* [comment removed for export] *)
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & HBK). exact HBK.
  Qed.
End OK.
End WithCeiling0.
