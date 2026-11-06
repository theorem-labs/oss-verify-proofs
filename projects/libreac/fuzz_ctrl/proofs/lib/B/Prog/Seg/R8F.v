(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/R8.v r8_evt (:59, call checked_memcpy) at
     a working branch 3803efccea0 (blob 7afb80277f83d4ac5559412f89ae1d19d67d112c);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r8_evt is split at its single call into r8_evt_pre_F (stop at checked_memcpy entry 0x52164,
     ra = 0x8177c; re-runs R8.v:96-97) and r8_evt_post_F (from the return pc 0x8177c, which is the run's exit,
     0 further steps; re-runs R8.v:128-134 as a repackaging of the asan_memcpy post facts into the exit cut).
     Bridge inputs only to a Theorem Labs lane's cgif-form walk.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R8.
(* Last: StepF's step / if_true_by (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* 0x81764 bnez a0 (taken, phi <> 0) ; 0x8176c mv s4,a0 ; 0x81770 ld a1,312(s1) ; 0x81774 mv a2,s2 ;
   0x81778 jal checked_memcpy: stops AT the callee entry (pc = 0x52164, ra = 0x8177c). The only data access
   is the 8-byte load of [s1 + 312] = S. *)
Lemma r8_evt_pre_F : forall (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi S : Z),
  a0 = Z_to_bv 64 phi -> 0 < phi < 2 ^ 64 -> 0 <= S < 2 ^ 64 ->
  ro_cells rsegs m (bv_unsigned s1 + 312) [C8 (Z_to_bv 64 S)] ->
  rng RNG (bv_unsigned s1 + 312) 8 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x8177c) sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 S) s2
                             a3 a4 a5 a6 a7 s2 s3 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x52164) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81764) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi S -> Hphi HS RO Rld.
  step. if_true_by (R8.r8_neqb0 phi ltac:(lia)).
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* From the return pc 0x8177c (= the run's exit cut): 0 further steps; the checked_memcpy post facts the
   proved run used, stated over the post-call state, give the run's exit Q. *)
Lemma r8_evt_post_F : forall (RNG : footprint)
    (sp gp tp s0 s1 s2 s3 a0 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (R : bvmap 5 word)
    (spv S N phi lo : Z) (src : list byte),
  getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 -> getr R 18 = s2 ->
  getr R 19 = s3 -> getr R 20 = a0 -> getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 ->
  getr R 24 = s8 -> getr R 25 = s9 -> getr R 26 = s10 -> getr R 27 = s11 ->
  munch [(phi, phi + N); (spv - 2224, spv)] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> stk rsegs m' lo spv -> asan_cells m' -> shadow_rw m' ->
  rw_cells rsegs m' phi [CB (Z.to_nat N) src] -> bytes_at rsegs m' S src ->
  evtF rsegs RNG
    (fun ms' => exists (R0 : bvmap 5 word) (m0 : word -> option byte),
       ms' = MS R0 F (Z_to_bv 64 0x8177c) fc None m0 (seg_rom rsegs) /\
       getr R0 2 = sp /\ getr R0 3 = gp /\ getr R0 4 = tp /\ getr R0 8 = s0 /\ getr R0 9 = s1 /\ getr R0 18 = s2 /\
       getr R0 19 = s3 /\ getr R0 20 = a0 /\ getr R0 21 = s5 /\ getr R0 22 = s6 /\ getr R0 23 = s7 /\
       getr R0 24 = s8 /\ getr R0 25 = s9 /\ getr R0 26 = s10 /\ getr R0 27 = s11 /\
       munch [(phi, phi + N); (spv - 2224, spv)] m m0 /\ wmono rsegs m m0 /\
       mem_inv rsegs m0 /\ stk rsegs m0 lo spv /\ asan_cells m0 /\ shadow_rw m0 /\
       rw_cells rsegs m0 phi [CB (Z.to_nat N) src] /\ bytes_at rsegs m0 S src)
    (MS R F (Z_to_bv 64 0x8177c) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp s0 s1 s2 s3 a0 s5 s6 s7 s8 s9 s10 s11 F fc m m' R spv S N phi lo src
    G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27
    MU WM MI ST AC SW RW HB.
  apply evtF_done. exists R, m'.
  split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.
