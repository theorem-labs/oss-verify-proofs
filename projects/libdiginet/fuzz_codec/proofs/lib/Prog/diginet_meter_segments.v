(** diginet_meter_segments (diginet_codec.c:209-215; the leaf at 0x1575c) in fuzz_codec.plain. The walk is the one
    libdiginet/fuzz_decode proves, relocated to this image (diginet_meter_segments_dec.v over its contract
    diginet_meter_segments_dec_c.v: for a mask below 2^16 passed in a0, a0 becomes DgnLib.v's
    diginet_meter_segments mask). This file gives the contract of this unit (diginet_meter_segments_c.v) from it:
    arg_zx 16 is that premise, and DgnLib.v's meter_segments_spec_eq says the two models agree. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells diginet_meter_segments_c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require diginet_meter_segments_dec_c diginet_meter_segments_dec.
Open Scope Z_scope.

Theorem diginet_meter_segments_holds : diginet_meter_segments_contract.
Proof.
  unfold diginet_meter_segments_contract, diginet_meter_segments_pre, arg_zx.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask
         [HM ->].
  rewrite meter_segments_spec_eq.
  exact (diginet_meter_segments_dec.diginet_meter_segments_holds
           ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask HM).
Qed.
