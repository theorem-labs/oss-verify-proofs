(** diginet_meter_segments (diginet_codec.c:209-215; the leaf at 0x15ba4) in fuzz_codec.ubsan. The walk is the one
    libdiginet/fuzz_decode proves, relocated to this image (U/Prog/diginet_meter_segments_dec.v over its contract
    U/Prog/diginet_meter_segments_dec_c.v: for any a0 below 2^16, a0 becomes DgnLib.v's diginet_meter_segments of
    it). This file gives the contract of this unit (U/Prog/diginet_meter_segments_c.v) from it: arg_zx 16 puts the
    mask in a0 below 2^16, and DgnLib.v's meter_segments_spec_eq says the two models agree. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells diginet_meter_segments_c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require diginet_meter_segments_dec_c diginet_meter_segments_dec.
Open Scope Z_scope.

Theorem diginet_meter_segments_holds : diginet_meter_segments_contract.
Proof.
  unfold diginet_meter_segments_contract, diginet_meter_segments_pre, arg_zx.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask
         [HM ->].
  assert (E : bv_unsigned (Z_to_bv 64 mask) = mask) by (apply unsigned_lit; lia).
  rewrite meter_segments_spec_eq.
  replace (diginet_meter_segments mask) with (diginet_meter_segments (bv_unsigned (Z_to_bv 64 mask)))
    by (rewrite E; reflexivity).
  exact (diginet_meter_segments_dec.diginet_meter_segments_holds
           ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mask) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m ltac:(rewrite E; lia)).
Qed.
