(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/R6.v r6_evt (:347, call reac_ctrl_build_as) at
     a working branch 3803efccea0 (blob d8957c66823992660227d2960c0c48a0a1559330);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r6_evt is split at its single call into r6_evt_pre_F (stop at reac_ctrl_build_as entry 0x8528c,
     ra = 0x81710; re-runs R6.v:453 do-9-step) and r6_evt_post_F (from the return pc 0x81710, which is the run's
     exit, 0 further steps; re-runs R6.v:490-499 as a repackaging of the reac_ctrl_build_as post facts into the
     exit cut). Bridge inputs only to a Theorem Labs lane's cgif-form walk.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcLay RcEmit RcPorts RcFin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFinLib RcSynthLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcIdentModel RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_box_model_block_c.
(* Last: StepF's step / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module BAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module BAC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_as_c.
(* SlotModel is Imported (R6.v's header); the two statement names it provides are written qualified
   through this alias, so no bare frame-route name appears in an _F statement. *)
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.SlotModel.

(* 0x816ec ld a0,312(s1); 0x816f0 ld a1,272(s1); 0x816f4 mv a2,s6; 0x816f8 ld a3,264(s1); 0x816fc ld a4,256(s1);
   0x81700 ld a5,248(s1); 0x81704 li a6,0; 0x81708 li a7,0; 0x8170c jal reac_ctrl_build_as: stops AT the callee
   entry (pc = 0x8528c, ra = 0x81710). The data accesses are the five 8-byte loads of the argument spills. *)
Lemma r6_evt_pre_F : forall (RNG : footprint)
    (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr mdv : Z),
  s1 = Z_to_bv 64 A -> 0 <= A -> A + 320 <= 2 ^ 64 ->
  ro_cells rsegs m (A + 312) [C8 (Z_to_bv 64 (fr + 544))] ->
  ro_cells rsegs m (A + 272) [C8 (Z_to_bv 64 mdv)] ->
  ro_cells rsegs m (A + 264) [C8 (Z_to_bv 64 (fr + 2624))] ->
  ro_cells rsegs m (A + 256) [C8 (Z_to_bv 64 SM.BOXA)] ->
  ro_cells rsegs m (A + 248) [C8 (Z_to_bv 64 0x1234)] ->
  rng RNG (A + 312) 8 -> rng RNG (A + 272) 8 -> rng RNG (A + 264) 8 ->
  rng RNG (A + 256) 8 -> rng RNG (A + 248) 8 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81710) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fr + 544))
                             (Z_to_bv 64 mdv) s6 (Z_to_bv 64 (fr + 2624)) (Z_to_bv 64 SM.BOXA) (Z_to_bv 64 0x1234)
                             (Z_to_bv 64 0) (Z_to_bv 64 0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x8528c) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x816ec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr mdv -> HA0 HA320 RO312 RO272 RO264 RO256 RO248 R312 R272 R264 R256 R248.
  do 9 step.
  apply evtF_done. reflexivity.
Qed.

(* From the return pc 0x81710 (= the run's exit cut): 0 further steps; the reac_ctrl_build_as post facts the
   proved run used, stated over the post-call state, give the run's exit Q (R6.v:411-434). *)
Lemma r6_evt_post_F : forall (RNG : footprint)
    (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (R : bvmap 5 word)
    (fr FS bb mdv Rv : Z) (mbv nbv dbv sbv : list byte),
  getr R 1 = Z_to_bv 64 0x81710 -> getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp ->
  getr R 8 = s0 -> getr R 9 = s1 -> getr R 10 = Z_to_bv 64 Rv -> getr R 18 = s2 ->
  getr R 19 = s3 -> getr R 20 = s4 ->
  getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 -> getr R 24 = s8 -> getr R 25 = s9 ->
  getr R 26 = s10 -> getr R 27 = s11 ->
  munch ([(bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K, bv_unsigned sp); (fr + 544, fr + 544 + Rv)] ++
         fp_w [0%nat; 1%nat] FS ++
         [(shadow_addr (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K), shadow_addr (bv_unsigned sp))]) m m' ->
  wmono rsegs m m' ->
  stk rsegs m' (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) ->
  asan_cells m' -> shadow_rw m' ->
  addressable m' (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) BAC.REAC_CTRL_BUILD_AS_K ->
  fp [0%nat; 1%nat] m' (bv_unsigned tp) FS
     (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp)
     [(bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K, bv_unsigned sp); (fr + 544, fr + 544 + Rv)]
     [(BAC.BA_FR + 72, BAC.BA_FR + 240); (mdv, mdv + 296); (fr + 2624, fr + 2624 + 6); (SM.BOXA, SM.BOXA + 6);
      (fr + 544, fr + 544 + Rv)] ->
  (exists ob, bytes_at rsegs m' (fr + 544) ob /\ Z.of_nat (length ob) = Rv) ->
  (BAP.ba_go (fr + 544) mdv bb && BAP.ba_E (bm_uw mdv (firstn 8 (skipn 16 mbv))) mbv bb = true ->
     bytes_at rsegs m' (fr + 544)
       (em_fr dbv sbv SM.CNT16 (Z_to_bv 8 205) (Z_to_bv 8 234) (BAP.ba_X mdv mbv nbv bb) Rv)) ->
  evtF rsegs RNG
    (fun ms' => exists (R0 : bvmap 5 word) (m0 : word -> option byte),
       ms' = MS R0 F (Z_to_bv 64 0x81710) fc None m0 (seg_rom rsegs) /\
       getr R0 1 = Z_to_bv 64 0x81710 /\ getr R0 2 = sp /\ getr R0 3 = gp /\ getr R0 4 = tp /\
       getr R0 8 = s0 /\ getr R0 9 = s1 /\ getr R0 10 = Z_to_bv 64 Rv /\ getr R0 18 = s2 /\
       getr R0 19 = s3 /\ getr R0 20 = s4 /\
       getr R0 21 = s5 /\ getr R0 22 = s6 /\ getr R0 23 = s7 /\ getr R0 24 = s8 /\ getr R0 25 = s9 /\
       getr R0 26 = s10 /\ getr R0 27 = s11 /\
       munch ([(bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K, bv_unsigned sp); (fr + 544, fr + 544 + Rv)] ++
              fp_w [0%nat; 1%nat] FS ++
              [(shadow_addr (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K), shadow_addr (bv_unsigned sp))]) m m0 /\
       wmono rsegs m m0 /\
       stk rsegs m0 (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) /\
       asan_cells m0 /\ shadow_rw m0 /\
       addressable m0 (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) BAC.REAC_CTRL_BUILD_AS_K /\
       fp [0%nat; 1%nat] m0 (bv_unsigned tp) FS
          (bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp)
          [(bv_unsigned sp - BAC.REAC_CTRL_BUILD_AS_K, bv_unsigned sp); (fr + 544, fr + 544 + Rv)]
          [(BAC.BA_FR + 72, BAC.BA_FR + 240); (mdv, mdv + 296); (fr + 2624, fr + 2624 + 6); (SM.BOXA, SM.BOXA + 6);
           (fr + 544, fr + 544 + Rv)] /\
       (exists ob, bytes_at rsegs m0 (fr + 544) ob /\ Z.of_nat (length ob) = Rv) /\
       (BAP.ba_go (fr + 544) mdv bb && BAP.ba_E (bm_uw mdv (firstn 8 (skipn 16 mbv))) mbv bb = true ->
          bytes_at rsegs m0 (fr + 544)
            (em_fr dbv sbv SM.CNT16 (Z_to_bv 8 205) (Z_to_bv 8 234) (BAP.ba_X mdv mbv nbv bb) Rv)))
    (MS R F (Z_to_bv 64 0x81710) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' R fr FS bb mdv Rv mbv nbv dbv sbv
    G1 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27
    MU WM ST AC SW AW FP Hob Hfb.
  apply evtF_done. exists R, m'.
  split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.
