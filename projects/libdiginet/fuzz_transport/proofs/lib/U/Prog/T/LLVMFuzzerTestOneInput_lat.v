(* The op loop's latch in the ubsan image, 0x14574-0x1458c (fuzz_transport.c:1168
   `for (int ops = 0; ops < OPS_MAX && in.n; ops++)`): the pass counter s11 is tested against 0x3fe, raised by addiw,
   the cursor of the pass (s3 / s6) becomes the cursor of the next pass (s5 / s7), and the loop goes back to the head
   0x139dc while the count left s6 is not zero. Both ways out land at the exit 0x145e8, whose predicate keeps only
   the saved registers: the first nine cells of the frame (136 bytes) merge into one CB 136. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

Lemma lat_swrap32 : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. apply bv_swrap_small.
  assert (E : bv_half_modulus 32 = 2 ^ 31) by reflexivity. rewrite E. lia.
Qed.

(* the first cells of a frame merged into one byte cell *)
Lemma lat_merge_front : forall segs m A mid post,
  rw_cells segs m A (mid ++ post) -> rw_cells segs m A (CB (cells_size mid) (cells_bytes mid) :: post).
Proof. intros segs m A mid post H. exact (rw_cells_merge segs m A [] mid post H). Qed.

(* llvm_out's memory facts from the loop's invariant: the frame's first 136 bytes as one cell *)
Lemma lat_out_mem : forall data D regs0 m0 Sp lo B m j10 jio j60,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  exists jlow : list byte,
    Sp mod 16 = 0 /\ lo <= Sp /\ Sp + LH_FRAME <= 2 ^ 63 /\ mem_inv rsegs m /\
    munch [(lo, Sp + LH_FRAME); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m /\ wmono rsegs m0 m /\
    length jlow = 136%nat /\ rw_cells rsegs m Sp (CB 136 jlow :: llvm_saved regs0).
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 HM.
  unfold llvm_mem in HM.
  destruct HM as (_ & _ & _ & _ & HSP & _ & HLO & HSP2 & _ & HMI & _ & _ & _ & HMU & HWMO & HJ1 & HJ2 & HJ3 & HRW).
  unfold llvm_frame in HRW. apply lat_merge_front in HRW.
  eexists.
  split; [exact HSP|]. split; [unfold LH_K in HLO; lia|]. split; [exact HSP2|]. split; [exact HMI|].
  split; [exact HMU|]. split; [exact HWMO|].
  split; [| exact HRW].
  rewrite cells_bytes_length; [reflexivity|].
  exact (conj I (conj I (conj HJ1 (conj I (conj I (conj I (conj I (conj HJ2 (conj HJ3 I))))))))).
Qed.

Theorem llvm_latch_holds : llvm_latch_stmt.
Proof.
  unfold llvm_latch_stmt.
  intros data D regs0 m0 Sp lo ops c B F fc ms Q H HH HO.
  destruct H as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s5 & s7 & t3 & t4 & t5 & t6 &
                 m & j10 & jio & j60 & -> & HOPS & HC & HM).
  destruct (lat_out_mem data D regs0 m0 Sp lo B m j10 jio j60 HM) as (jlow & HOUT).
  pose proof HOPS as HOPS'. unfold OPS_MAX in HOPS'.
  pose proof HC as HC'. unfold llvm_cursor in HC'.
  pose proof HM as HM'. unfold llvm_mem in HM'.
  destruct HM' as (HD0 & HDL & _ & _ & _ & _ & HLO & HSP2 & _).
  unfold LH_K, LH_FRAME in HLO, HSP2.
  unfold LH_LATCH.
  zstep.                                       (* 0x14574 addi a0, zero, 0x3fe *)
  zstep.                                       (* 0x14578 bltu a0, s11 -> 0x145e8 *)
  if_cases K1; zify_cond K1.
  - (* 0x3fe < ops: the loop is over *)
    apply HO; [right; unfold OPS_MAX; lia|].
    unfold llvm_out. do 29 eexists. exists jlow. split; [reflexivity | exact HOUT].
  - (* ops <= 0x3fe: raise the counter, take the pass's cursor *)
    zstep.                                     (* 0x1457c addiw s11, s11, 1 *)
    rewrite (lat_swrap32 (ops + 1)) by lia.
    zstep.                                     (* 0x14580 mv s5, s3 *)
    zstep.                                     (* 0x14584 mv s7, s6 *)
    zstep.                                     (* 0x14588 bnez s6 -> 0x139dc *)
    if_cases K2; zify_cond K2.
    + (* the count left is not zero: back to the head *)
      apply HH; [lia | unfold OPS_MAX; lia |].
      unfold llvm_head. do 23 eexists. split; [reflexivity|].
      split; [unfold OPS_MAX; lia|]. split; [lia|]. split; [exact HC|]. exact HM.
    + (* the count left is zero: out *)
      zstep.                                   (* 0x1458c j 0x145e8 *)
      apply HO; [left; lia|].
      unfold llvm_out. do 29 eexists. exists jlow. split; [reflexivity | exact HOUT].
Qed.
