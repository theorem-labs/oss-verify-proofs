(* The walk of LLVMFuzzerTestOneInput in the ubsan image, as U/Prog/T/WalkAll.v states it:
   LLVMFuzzerTestOneInput_holds : LLVMFuzzerTestOneInput_walk (SR form, for ubsan_halts) and
   LLVMFuzzerTestOneInput_holds_cf : LLVMFuzzerTestOneInput_walk_cf (cut-free form, for ubsan_agrees), at the
   frame's allocator (src0_msyms, zlib_API) and sink words (src0_sink_head, src0_sink).
   The pieces (U/Prog/T/LLVMFuzzerTestOneInput_lh.v statements): entry (_entry.v), dispatch (_disp.v), the nine ops
   (_op0.v .. _op8.v), latch (_lat.v), exit (_exit.v); the SR glue that binds them with receive's and
   build_and_receive's SR contracts (_glue.v llvm_walk_sr / llvm_walk_cf), and the one fact of the frame's symbols
   the glue asks (_sink.v src0_lg_sink: the sink words lie in the image, apart from the allocator's statics, its
   context, errno and the world). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YM05 YL0i YH02 YH03 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Contract Img0 ZAllocator.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem receive_c build_and_receive_c
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_glue LLVMFuzzerTestOneInput_sink WalkAll.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require LLVMFuzzerTestOneInput_entry
  LLVMFuzzerTestOneInput_disp LLVMFuzzerTestOneInput_lat LLVMFuzzerTestOneInput_exit LLVMFuzzerTestOneInput_op0
  LLVMFuzzerTestOneInput_op1 LLVMFuzzerTestOneInput_op2 LLVMFuzzerTestOneInput_op3 LLVMFuzzerTestOneInput_op4
  LLVMFuzzerTestOneInput_op5 LLVMFuzzerTestOneInput_op6 LLVMFuzzerTestOneInput_op7 LLVMFuzzerTestOneInput_op8.
Import ListNotations.
Local Open Scope Z_scope.

Theorem LLVMFuzzerTestOneInput_holds : LLVMFuzzerTestOneInput_walk.
Proof.
  intros rc fx MCP MST SLN CFG INIT MWK SWK CSW CLS MSET MTK STK SETL BAR SUB CRS CLT RECV.
  apply (llvm_walk_sr (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc)).
  - exact src0_lg_sink.
  - exact (LLVMFuzzerTestOneInput_entry.llvm_entry_holds MCP MST CFG INIT).
  - exact LLVMFuzzerTestOneInput_disp.llvm_disp_holds.
  - exact LLVMFuzzerTestOneInput_lat.llvm_latch_holds.
  - exact LLVMFuzzerTestOneInput_exit.llvm_exit_holds.
  - exact LLVMFuzzerTestOneInput_op0.llvm_op0_holds.
  - exact LLVMFuzzerTestOneInput_op8.llvm_op8_holds.
  - exact LLVMFuzzerTestOneInput_op1.llvm_op1_holds.
  - exact (LLVMFuzzerTestOneInput_op2.llvm_op2_holds MST MCP SLN).
  - exact (LLVMFuzzerTestOneInput_op3.llvm_op3_holds MST MTK STK SETL).
  - exact (LLVMFuzzerTestOneInput_op4.llvm_op4_holds MST MCP SUB CRS CLT SETL).
  - exact (LLVMFuzzerTestOneInput_op5.llvm_op5_holds MST MWK SWK CSW SETL).
  - exact (LLVMFuzzerTestOneInput_op6.llvm_op6_holds MST MSET CLS SETL).
  - exact LLVMFuzzerTestOneInput_op7.llvm_op7_holds.
  - exact RECV.
  - exact BAR.
Qed.

Theorem LLVMFuzzerTestOneInput_holds_cf : LLVMFuzzerTestOneInput_walk_cf.
Proof.
  intros rc fx MCP MST SLN CFG INIT MWK SWK CSW CLS MSET MTK STK SETL BAR SUB CRS CLT RECV.
  apply (llvm_walk_cf (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc)).
  - exact src0_lg_sink.
  - exact (LLVMFuzzerTestOneInput_entry.llvm_entry_holds MCP MST CFG INIT).
  - exact LLVMFuzzerTestOneInput_disp.llvm_disp_holds.
  - exact LLVMFuzzerTestOneInput_lat.llvm_latch_holds.
  - exact LLVMFuzzerTestOneInput_exit.llvm_exit_holds.
  - exact LLVMFuzzerTestOneInput_op0.llvm_op0_holds.
  - exact LLVMFuzzerTestOneInput_op8.llvm_op8_holds.
  - exact LLVMFuzzerTestOneInput_op1.llvm_op1_holds.
  - exact (LLVMFuzzerTestOneInput_op2.llvm_op2_holds MST MCP SLN).
  - exact (LLVMFuzzerTestOneInput_op3.llvm_op3_holds MST MTK STK SETL).
  - exact (LLVMFuzzerTestOneInput_op4.llvm_op4_holds MST MCP SUB CRS CLT SETL).
  - exact (LLVMFuzzerTestOneInput_op5.llvm_op5_holds MST MWK SWK CSW SETL).
  - exact (LLVMFuzzerTestOneInput_op6.llvm_op6_holds MST MSET CLS SETL).
  - exact LLVMFuzzerTestOneInput_op7.llvm_op7_holds.
  - exact RECV.
  - exact BAR.
Qed.

Print Assumptions LLVMFuzzerTestOneInput_holds.
Print Assumptions LLVMFuzzerTestOneInput_holds_cf.
