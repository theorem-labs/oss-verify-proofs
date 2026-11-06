(* The epilogue of LLVMFuzzerTestOneInput, 0x14320-0x1435c: the return value 0, the 13 saved registers back
   from the frame (sp + 0x78 .. sp + 0xd8, the cells llvm_saved names), the frame given back
   (addi sp, sp, 0xe0) and the return. Memory is only read here. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

Section EXIT.
Context (data : Z) (D : list byte).

(* The state the epilogue leaves: a0 = 0, the saved registers back, sp above the frame again, the memory of
   the loop's last world. *)
Definition llvm_ret (m0 : word -> option byte) (gp tp : word) (Sp lo : Z) (B : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (m : word -> option byte) (j10 j28 : list byte),
    ms = MS (mkR ra (Z_to_bv 64 (Sp + LLVM_FRAME)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m (seg_rom rsegs) /\
    llvm_mem data D Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28.

Lemma llvm_exit : forall m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  llvm_out data D m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  (forall ms', llvm_ret m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q HO HK.
  destruct HO as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r9 & r18 & r19 &
                  r20 & r21 & r22 & r23 & r24 & r25 & r26 & r27 & t3 & t4 & t5 & t6 & m & j10 & j28 & -> & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  unfold llvm_frame_consts, llvm_saved in HRW.
  unfold LLVM_OUT_PC, LLVM_LOOP_K, LLVM_FRAME in *.
  (* 0x14320 li a0, 0; 0x14324-0x14354 the 13 loads; 0x14358 addi sp, sp, 0xe0 *)
  do 16 zstep.
  apply HK. unfold llvm_ret, LLVM_FRAME. do 17 eexists. split; [reflexivity|]. exact HM0.
Qed.

End EXIT.
