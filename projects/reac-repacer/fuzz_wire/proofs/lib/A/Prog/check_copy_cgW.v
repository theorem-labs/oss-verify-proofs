(* check_copy_cgW: the frozen statement lib/A/Prog/check_copy_cg.v wire_check_copy_holds_stmt of reac-repacer/fuzz_wire's
   check_copy on image A (fuzz_wire.asan 0x80c38 = wire_sigma WS_check_copy): the walk of
   lib/A/Prog/check_copy_cgW_walk.v (cc_walk, which takes the footprint runs of the straight-line segments as
   premises) applied to their proofs in lib/A/Prog/check_copy_cgW_segs.v. Every other premise of the walk is a
   premise of the statement. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require check_copy_cg check_copy_cgW_segs
  check_copy_cgW_walk.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module CC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_copy_cg.
Module CCS := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_copy_cgW_segs.
Module CCW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_copy_cgW_walk.

Theorem wire_check_copy_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  @CC.wire_check_copy_holds_stmt fx rc B MT.
Proof.
  intros HMPC HFPC HCELLS LAWS MTL UFIX AMALLOC AFREE AMEMCPY ABCMP ARCU.
  apply CCW.cc_walk.
  all: first
    [ assumption
    | exact CCS.cc_seg_entry_ok | exact CCS.cc_seg_m_ok | exact CCS.cc_seg_z_ok | exact CCS.cc_seg_cp1_ok
    | exact CCS.cc_seg_short_ok | exact CCS.cc_seg_tag_yes_ok | exact CCS.cc_seg_tag_no_ok
    | exact CCS.cc_seg_cp2ret_ok | exact CCS.cc_seg_want_lo_ok | exact CCS.cc_seg_want_hi_ok
    | exact CCS.cc_seg_bcmpret_ok | exact CCS.cc_seg_end_ok ].
Qed.
