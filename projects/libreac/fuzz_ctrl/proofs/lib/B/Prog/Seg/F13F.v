(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F13.v f13_evt_n (:1109), f13_evt (:1178) at a working branch
     3803efccea0 (blob 7e3eed569c14334b0166d7ed1888d8289275645a);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
     lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: split stretch, no <run>_of_F. f13_pre_F re-runs F13.v:1178-1190 (the segment's own 7 steps
     0x82340 -> the callee entry 0x859e4); the call of reac_ctrl_identity_fragment at 0x82358 returns to
     0x8235c, which IS the run's exit cut (B8235c_at), so there is no _post_F stretch. The walk
     (a Theorem Labs lane) composes the callee itself (split rule, parent 23:50Z), so the contract-composing
     f13_evt_F / f13_evt_ro_F of dba073859bd are not published here.
   The text of f13_pre_F is dba073859bd:proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F13F.v:25-46 (blob
     4cda58e084cd24588e17666cc5964d8b57ac431a), re-checked against F13.v (blob unchanged between the two
     commits). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib memcmp_c
  bcmp_wrap_c reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import F13.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The footprint (evtF) twin of the pre-call stretch of F13.f13_evt_n / F13.f13_evt, in their binders: the
   segment's own 7 steps 0x82340 -> the callee entry 0x859e4 (a0 = s5, a1 = s2, a2 = s4, a3 = [s1+288],
   a4 = [s1+304], a5 = [s1+296], jal), whose only memory accesses are the three spill loads in
   [s1+288, s1+296) and [s1+296, s1+312). *)
Lemma f13_pre_F : forall (RNG : footprint)
    (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f frg len pa pp pn : Z),
  s1v = Z_to_bv 64 A -> s5 = Z_to_bv 64 f -> s2v = Z_to_bv 64 frg -> s4v = Z_to_bv 64 len ->
  0 <= A < 2 ^ 64 -> 0 <= f < 2 ^ 64 -> 0 <= frg < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  rw_cells rsegs m (A + 288) [C8 (Z_to_bv 64 pa)] ->
  rw_cells rsegs m (A + 296) [C8 (Z_to_bv 64 pn)] ->
  rw_cells rsegs m (A + 304) [C8 (Z_to_bv 64 pp)] ->
  rng RNG (A + 288) 8 -> rng RNG (A + 296) 16 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x8235c) sp gp tp t0 t1 t2 s0 s1v s5 s2v s4v
                              (Z_to_bv 64 pa) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a6 a7
                              s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 0x859e4) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82340) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f frg len pa pp pn -> -> -> -> HAb Hfb Hfrgb Hlenb Hc288 Hc296 Hc304 Rspa Rspnp.
  do 7 step.
  apply evtF_done. reflexivity.
Qed.
