(* crtA_bridge: the image-A half of the step that carries a footprint run of lib/Lib/ExecF.v into cgif's SRr walk,
   for the cgif-form walk of check_round_trip (lib/A/Prog/check_round_trip_cg.v).

   The image-neutral half (the transport of a run along ms_eqv, and the shape lemma for an arbitrary ROM) is
   lib/Lib/CrtBridge.v; image B's walk uses the same file.  What is left here is image A's instance: decode's run
   state for image A is `ms_of_regs` of lib/A/Prog/LeafCgKit.v:46, whose ROM is lib/A/Img0.v's rsegs.

   The walk's segments are footprint runs: the record on a working branch at dc455613c81 proves them
   (proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs_F.v, crt_loopF.v); the ported twins are lib/A/Prog/crtA_segs.v
   and lib/A/Prog/crtA_loop.v.  LeafCgKit.v:101 bridge_evtF_stmt (the kit's Section hypothesis, cgif's SRr_fevt
   read at decode's mstepsF) turns a run into SRr. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Regs6ss ExecF CrtBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11.
Import ListNotations.
Open Scope Z_scope.

Section ShapeA.
Context {fx : YK11.FPState}.

(* LeafCgKit's run state carries `mkR` of the register values, which is mkR_of of the map. *)
Lemma ms_of_regs_regs : forall pc (regs : bvmap 5 word) (mem : word -> option byte),
  ms_regs (@ms_of_regs fx pc regs mem) = mkR_of regs.
Proof.
  intros pc regs mem. unfold ms_of_regs, mkR_of, YK11.getr. cbn.
  first [reflexivity | f_equal].
Qed.

(* cgif's configuration state at a pc of image A, and the state decode's footprint runs start from. *)
Lemma mkst_eqv_ms_of_regs : forall pc (regs : bvmap 5 word) (mem : word -> option byte),
  ms_eqv (@YK11.mkst fx regs (w64 pc) mem (YK11.seg_rom rsegs)) (@ms_of_regs fx pc regs mem).
Proof.
  intros pc regs mem.
  pose proof (@mkst_eqv_mkR_of fx regs (w64 pc) mem (YK11.seg_rom rsegs)) as H.
  unfold ms_eqv in H |- *. rewrite (ms_of_regs_regs pc regs mem).
  unfold ms_of_regs. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in H |- *.
  exact H.
Qed.
End ShapeA.
