(* Case 1 of the op loop of LLVMFuzzerTestOneInput, ubsan image (fuzz_transport.c:1175-1177, op_frame inlined,
   fuzz_transport.c:1035-1050): from the case entry 0x13b38 to the call of build_and_receive at 0x13dac, and the
   return 0x13db0 .. the latch 0x14574 (`j 0x13f70; mv s3, s0; j 0x14574`).
   The walk to the call: U/Prog/T/LLVMFuzzerTestOneInput_op1_h.v op1_head (0x13b38 .. 0x13cc8, the cursor reads)
   and U/Prog/T/LLVMFuzzerTestOneInput_op1_t.v op1_tail (0x13cc8 .. 0x13dac); the model's op 1 as one
   build_and_receive_m: U/Prog/T/LLVMFuzzerTestOneInput_op1_k.v o1_model. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_op1_k LLVMFuzzerTestOneInput_op1_h.
Import ListNotations.
Open Scope Z_scope.

Section RET.
Context (data : Z) (D : list byte) (regs0 : bvmap 5 word).

(* 0x13db0 .. the latch: j 0x13f70; mv s3, s0; j 0x14574 *)
Lemma op1_ret : forall m0' Sp lo ops B' F' fc' ms'' (Q' : machine_state -> Prop)
    (s0 s2 s3 s4 s5 s6 s7 : word) (c2 : fuzz_in),
  llvm_ret data D regs0 m0' Sp lo ops B' LH_RET_BAR1 s0 s2 s3 s4 s5 s6 s7 F' fc' ms'' ->
  (forall ms3, llvm_latch data D regs0 m0' Sp lo ops c2 B' F' fc' ms3 -> evt rsegs Q' ms3) ->
  s0 = Z_to_bv 64 (data + fi_off c2) -> s2 = Z_to_bv 64 0x39 -> s4 = Z_to_bv 64 7 ->
  s6 = Z_to_bv 64 (fi_n c2) -> llvm_cursor D c2 ->
  evt rsegs Q' ms''.
Proof.
  intros m0' Sp lo ops B' F' fc' ms'' Q' s0 s2 s3 s4 s5 s6 s7 c2 HR K -> -> -> -> HC.
  destruct HR as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 &
                  m & j10 & jio & j60 & -> & Hops & HM).
  unfold LH_RET_BAR1.
  step.                                      (* j 0x13f70 *)
  step.                                      (* mv s3, s0 *)
  step.                                      (* j 0x14574 *)
  apply K. unfold llvm_latch.
  do 23 eexists. split; [reflexivity|].
  split; [exact Hops|]. split; [exact HC|]. exact HM.
Qed.

End RET.

Theorem llvm_op1_holds : llvm_op_bar_stmt 1 LH_RET_BAR1.
Proof.
  unfold llvm_op_bar_stmt.
  intros data D regs0 m0 Sp lo ops c c1 B F fc ms HC.
  destruct HC as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 &
                  m & j10 & jio & j60 & Hms & Hops & Hn & Hcur & Hc1 & Hop & HM).
  destruct c as [off n]. unfold llvm_cursor in Hcur. cbn [fi_off fi_n] in Hn, Hcur.
  assert (E0 : fuzz_u8_m D (FuzzIn off n) = (FuzzIn (off + 1) (n - 1), at8 D (Z.to_nat off))).
  { unfold fuzz_u8_m. cbn [fi_off fi_n]. destruct (Z.eqb_spec n 0) as [E|E]; [lia | reflexivity]. }
  rewrite E0 in Hc1. cbn [fst] in Hc1. subst c1 ms. cbn [fi_off fi_n].
  change (LH_CASE 1) with 80696.
  apply (op1_head data D regs0 _ m0 Sp lo ops off n B F fc m j10 jio j60
           ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hops ltac:(lia) ltac:(lia) ltac:(lia) HM).
  intros ms' HP. apply evt_done. unfold o1_post in HP.
  pose proof (o1_len_rng (o1_w D off n) (fi_n (o1_c5 off n))
                ltac:(unfold o1_w; pose proof (o1_byt_rng D (o1_c1 off n) 6);
                      pose proof (o1_byt_rng D (o1_c1 off n) 7); unfold o1b; lia)
                ltac:(unfold o1_c5, o1_adv, o1_c1; cbn [fi_n]; lia)) as HL.
  do 17 eexists.
  exists (FuzzIn (fi_off (o1_c5 off n) + o1_len (o1_w D off n) (fi_n (o1_c5 off n)))
                 (fi_n (o1_c5 off n) - o1_len (o1_w D off n) (fi_n (o1_c5 off n)))).
  split; [exact HP|].
  split.
  - intros I A k. exact (o1_model I B A D off n k ltac:(lia) ltac:(lia) Hop).
  - intros m0' B' F' fc' ms'' Q' HFN HR K.
    eapply (op1_ret data D regs0 m0' Sp lo ops B' F' fc' ms'' Q');
      [ exact HR | exact K | | reflexivity | reflexivity | | ].
    + cbn [fi_off]. f_equal. lia.
    + cbn [fi_n]. reflexivity.
    + unfold llvm_cursor. cbn [fi_off fi_n]. unfold o1_c5, o1_adv, o1_c1 in HL |- *.
      cbn [fi_off fi_n] in HL |- *. lia.
Qed.
