(* The op loop's latch, 0x1428c-0x142a4 (fuzz_transport.c:1165 `for (int ops = 0; ops < OPS_MAX && in.n; ops++)`):
   the pass counter is tested against 0x3fe, then raised, the cursor of the pass (s3 / s6) becomes the cursor of
   the next pass (s4 / s7), and the loop goes back to the head 0x138ac while the count left is not zero. Both
   ways out land at 0x14320. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_disp.
Import ListNotations.
Open Scope Z_scope.

Section LAT.
Context (data : Z) (D : list byte).

Lemma llvm_latch_go : forall Sp lo ops c B m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  llvm_latch data D m0 gp tp Sp lo ops c B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  (forall ms', llvm_head data D m0 gp tp Sp lo (ops + 1) c B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  (forall ms', (0x3fe < ops \/ fi_n c = 0) ->
     llvm_out data D m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros Sp lo ops c B m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q HL HH HO.
  destruct HL as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r20 & r23 &
                  t3 & t4 & t5 & t6 & m & j10 & j28 & -> & HOPS & HC & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  unfold llvm_cursor in HC. unfold OPS_MAX in HOPS.
  unfold LLVM_LATCH_PC.
  do 2 zstep.
  if_cases K1; zify_cond K1.
  - (* 0x3fe < ops: the loop is over *)
    apply HO; [left; lia|]. unfold llvm_out. do 31 eexists. split; [reflexivity|]. exact HM0.
  - (* ops <= 0x3fe: raise the counter and take the pass's cursor *)
    do 4 zstep.
    rewrite (swrap32_small (ops + 1)) by lia.
    if_cases K2; zify_cond K2.
    + (* the count left is not zero: back to the head *)
      apply HH. unfold llvm_head. do 22 eexists. split; [reflexivity|].
      split; [unfold OPS_MAX; lia|]. split; [lia|]. split; [unfold llvm_cursor; lia|]. exact HM0.
    + (* the count left is zero: out *)
      zstep. apply HO; [right; rewrite Z.mod_small in K2 by (unfold FUZZ_INPUT_MAX in *; lia); exact K2|]. unfold llvm_out. do 31 eexists. split; [reflexivity|]. exact HM0.
Qed.

End LAT.
