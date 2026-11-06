(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R19.v r19_evt_n, r19_evt at a working branch 3803efccea0
     (blob f86f9ca14323887a025e0986c8d7c8e9a83daa74);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: both source runs call the bcmp wrapper, so they are split at the call (parent a Theorem Labs lane, binding).
     r19_pre_F re-runs R19.v:128-130 (0x81a50 up to the wrapper_bcmp entry 0x42aac, ra = 0x81a68); it is the
     stretch of BOTH r19_evt_n (:93-154) and r19_evt (:157-245), which differ only in the memory the wrapper
     contract runs on (r19_evt is r19_evt_n on MemNorm.normalize, R19.v:190-244) and share this pre-call stretch
     verbatim. There is no post stretch: the runs' exit cut Inv_B81a68_at IS the return pc. No `_F` steps through
     a callee and this file states no callee contract. *)
(* rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcDecl RcLeaf RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot RHelp RtmB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R19.
(* Last: StepF's step / if_true (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF ExecF_all StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

(* ---- the footprint form of [0x81a50, the wrapper_bcmp entry) ---- *)

Lemma r19_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A phi D vd : Z),
    s1v = Z_to_bv 64 A -> s2v = Z_to_bv 64 (phi + 18) -> a0v = Z_to_bv 64 vd ->
    vd <> 0 -> 0 <= vd < 2 ^ 64 ->
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= D -> D + 32 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 D)) ->
    rng RNG (A + 96) 8 ->
    evtF rsegs RNG
      (fun ms' => exists R : bvmap 5 word,
         ms' = MS R Fr (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81a68 /\ getr R 10 = Z_to_bv 64 (phi + 18) /\
         getr R 11 = Z_to_bv 64 D /\ getr R 12 = Z_to_bv 64 32 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1v /\
         getr R 18 = s2v /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
         getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81a50) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A phi D vd -> -> -> Hvd Hvdb HA0 HAb HD0 HDb R96 Rg96.
  pose proof (rh_rdn m (A + 96) (le8 (Z_to_bv 64 D)) 8 R96 ltac:(apply length_le8)) as RD96.
  (* 81a50 bnez a0 : taken (vd <> 0) *)
  step. if_true_by (R19.r19_neqb0 vd ltac:(lia)).
  (* 81a58 li a2,32 ; 81a5c mv a0,s2 ; 81a60 ld a1,96(s1) ; 81a64 jal wrapper_bcmp *)
  step. step. step. step.
  apply evtF_done. eexists. split; [reflexivity|].
  do 18 (split; [first [ reflexivity | f_equal; lia ]|]). first [ reflexivity | f_equal; lia ].
Qed.
