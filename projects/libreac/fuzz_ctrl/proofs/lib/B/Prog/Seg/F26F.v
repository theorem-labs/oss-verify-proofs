(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/F26.v f26_lu_evt (:62) and seg_F26's own inline stretch 0x828a4 -> 0x828b4
     (:479-495) at a working branch 3803efccea0 (blob dafb3d337f8c529014a0acbf8990acdf34a2e73c);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f26_lu_evt is the UL bridge that carries the reac_ports_unknown contract into seg_F26's UL run; an
     _F stretch never runs a callee, so the bridge has no footprint twin.  The stretch is split at the call
     instead: seg_F26_pre_F re-runs F26.v:481-482 (0x828a4 -> the callee entry 0x88628, ra = 0x828b4) and
     seg_F26_post_F re-runs F26.v:488-495 (the return pc 0x828b4 -> the stretch's end, no step), with the
     callee post facts as premises.  The pre half makes no memory access, so it carries no rng premise. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F26.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module PUC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ports_unknown_c.

(* 0x828a4 mv s7,a0 ; 0x828a8 mv a0,s6 ; 0x828ac li a1,0 ; 0x828b0 jal reac_ports_unknown, stopping at the
   callee entry 0x88628 with ra = 0x828b4.  No memory access. *)
Lemma seg_F26_pre_F : forall (RNG : footprint)
  (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6v s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (blk : Z),
  s6v = Z_to_bv 64 blk ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x828b4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 blk) (Z_to_bv 64 0)
                              a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 blk) a0 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 PUC.REAC_PORTS_UNKNOWN) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x828a4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6v s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m blk ->.
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* The post half (F26.v:488-495): from the return pc 0x828b4 there is no further instruction before the
   stretch's exit cut, so the post is the callee post facts themselves, with the callee's write set at c = 0
   (its 16 stack bytes) and ro_agree carried across that write. *)
Lemma seg_F26_post_F : forall (RNG : footprint)
  (ra' sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6v s7v s8 s9 s10 s11 t3' t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (lo unk : Z),
  munch [(bv_unsigned sp - PUC.REAC_PORTS_UNKNOWN_FRAME, bv_unsigned sp)] m m' ->
  wmono rsegs m m' -> ro_agree rsegs m' ->
  stk rsegs m' lo (bv_unsigned sp) ->
  evtF rsegs RNG
    (fun ms'' => exists (ra'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' : word)
                        (m'' : word -> option byte),
       ms'' = MS (mkR ra'' sp gp tp t0'' t1'' t2'' s0 s1 (Z_to_bv 64 unk) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                      s2 s3 s4 s5 s6v s7v s8 s9 s10 s11 t3'' t4 t5 t6)
                 F (Z_to_bv 64 0x828b4) fc None m'' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - PUC.REAC_PORTS_UNKNOWN_FRAME, bv_unsigned sp)] m m''
       /\ wmono rsegs m m'' /\ ro_agree rsegs m'' /\ stk rsegs m'' lo (bv_unsigned sp))
    (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 unk) a1' a2' a3' a4' a5' a6' a7'
             s2 s3 s4 s5 s6v s7v s8 s9 s10 s11 t3' t4 t5 t6)
        F (Z_to_bv 64 0x828b4) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG ra' sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6v s7v s8 s9 s10 s11
    t3' t4 t5 t6 F fc m m' lo unk MU WM HRO ST.
  apply evtF_done.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact HRO | exact ST].
Qed.
