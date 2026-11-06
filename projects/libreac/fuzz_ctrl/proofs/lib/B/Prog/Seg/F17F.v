(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F17.v (not in this delivery) seg_F17 (the inline run of the sl_run bullet) at
     a working branch 3803efccea0 (blob e013a16d62b4fdb9840ec9ea0ff0b7293820c8ce);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: seg_F17_run (evtF_evt, no rng premise to discharge: the run touches no memory) re-derives the source
     run's statement in the lib.Lib Exec.evt form; the segment proof states that run in the UL engine's Exec.evt
     form and carries it to lib.Lib with SmLib.ul_entry inside Tac_slot.sl_run, and the two evt definitions are the
     same (lib/B/Tk/UL/Exec.v:37, lib/Lib/Exec.v:109). *)

(* The run of segment F17 (S_F17): the one instruction `bltz a0,0x82fa4` at 0x82464, not taken, to the split cut
   0x82468. It reads and writes no memory (no load, no store, no instrumented check), so its footprint twin needs
   no rng premise at all. The source bullet's K keeps every register and the memory; the equality Q below is that
   K read on the concrete state the step leaves. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module LE17 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* The footprint twin of F17's run 0x82464 -> 0x82468. The premise is the source cut's a0 fact (Inv_B82464_at
   carries a0 = the nonnegative result of the reac_identity_ingest call at 0x82460). *)
Lemma seg_F17_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 : Z),
    a0 = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 63 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v
                               s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          Fr (Z_to_bv 64 0x82468) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v
              s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82464) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v
    s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m v0 -> Hv0.
  assert (Ev0 : bv_signed (Z_to_bv 64 v0) = v0) by (apply signed_lit; lia).
  step. if_false.
  apply evtF_done. reflexivity.
Qed.

(* The source run, in the engine form the segment proof's bullet proves (lib/B/Prog/Seg/F17.v:102-123): no
   footprint, every access allowed. This is the `_of_F` compare for the run: its statement is the source's and its
   only proof step is evtF_evt at RNG_all. *)
Lemma seg_F17_run :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 : Z),
    a0 = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 63 ->
    LE17.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v
                               s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          Fr (Z_to_bv 64 0x82468) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v
              s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82464) fc None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all). eapply seg_F17_F; eassumption.
Qed.
