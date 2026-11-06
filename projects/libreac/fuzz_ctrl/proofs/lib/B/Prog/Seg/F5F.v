(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F5.v c_evt (:797) at a working branch 3803efccea0
     (blob 12bbc4e36f85d5cd15d37ae8e6d16742c295b499);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: c_pre_F re-runs F5.v:855 (the four instructions 0x8214c-0x82158, F5.v:795-796), stopping AT the
     reac_ctrl_parse entry. *)
(* rule 24: no function proved. *)
(* c_evt is split at its one call.  The pre stretch is 0x8214c mv a0,s2 / 0x82150 mv a1,s4 / 0x82154 li a2,0 /
   0x82158 jal reac_ctrl_parse: four register-only instructions on the REAL memory (F5.v steps them before
   evt_normalize), so c_pre_F needs no rng premise and no MemNorm lift.  There is no post stretch: the
   instruction after the call site is the run's exit 0x8215c.  The callee itself (its contract, taken on
   MemNorm.normalize of the memory) is not stated here; the walk composes it. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot F5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Lemma c_pre_F :
  forall (RNG : footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n S : Z),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x8215c) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v
                                (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                                (Z_to_bv 64 f) s3 (Z_to_bv 64 n) s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 f) s3 (Z_to_bv 64 n) s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8214c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m f n S.
  (* 0x8214c mv a0,s2 ; 0x82150 mv a1,s4 ; 0x82154 li a2,0 ; 0x82158 jal reac_ctrl_parse *)
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* ================= the inline stretch 0x82048 -> 0x8214c of seg_F5 ================= *)
(* seg_F5 (S_F5) has no stated run lemma for this stretch; it is CUT mechanically from seg_F5_run's own steps
   (F5.v:1874-1899, the c_run_lib bullet).  The short-frame arm: a0 = t_k j = 0 so `bnez a0,0x82fa4` is not
   taken; then [A+184] = [A+272] = [A+312] = 0, s8 = s9 = 0, a0 = 1 and [A+248] = 1.  No call, no instrumented
   check: four save-area word writes only.  Fr, fc are Section variables as in a Theorem Labs lane's F4F.v. *)
Section F5F.
Variables (Fr : bvmap 5 word) (fc : bv 32).

Lemma seg_F5_F :
  forall (RNG : footprint) (regs : bvmap 5 word) (mem : word -> option byte) (A : Z),
    rg regs 10 0 -> rg regs 9 A ->
    0 <= A -> A + 320 <= 2 ^ 64 ->
    wr_at rsegs mem (A + 184) 136 ->
    rng RNG (A + 184) 8 -> rng RNG (A + 272) 8 -> rng RNG (A + 312) 8 -> rng RNG (A + 248) 8 ->
    evtF rsegs RNG
      (fun ms => exists R pc' mem', ms = MS R Fr pc' fc None mem' (seg_rom rsegs) /\
         pc' = Z_to_bv 64 0x8214c /\
         mem' = write_to_mem (write_to_mem (write_to_mem (write_to_mem mem
                   (wa (A + 184)) (le8 (Z_to_bv 64 0)))
                   (wa (A + 272)) (le8 (Z_to_bv 64 0)))
                   (wa (A + 312)) (le8 (Z_to_bv 64 0)))
                   (wa (A + 248)) (le8 (Z_to_bv 64 1)) /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
         getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
         getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
         getr R 24 = Z_to_bv 64 0 /\ getr R 25 = Z_to_bv 64 0)
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x82048) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem A Ha0 Hr9 HA0 HA1 HW R184 R272 R312 R248.
  rewrite c_mkR_expand. c_slot Ha0. c_slot Hr9.
  (* 0x82048 bnez a0 : a0 = t_k j = 0, not taken *)
  step. try rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x8204c sd zero,184(s1) *)
  pose proof (wr_at_store_ok rsegs mem (A + 184) 136 0 8 HW ltac:(lia) ltac:(lia)) as HS1.
  replace (A + 184 + 0) with (A + 184) in HS1 by lia.
  step.
  (* 0x82050 sd zero,272(s1) *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HWa : wr_at rsegs mm (A + 184) 136) by (apply wr_at_write; exact HW) end.
  pose proof (wr_at_store_ok rsegs _ (A + 184) 136 88 8 HWa ltac:(lia) ltac:(lia)) as HS2.
  replace (A + 184 + 88) with (A + 272) in HS2 by lia.
  step.
  (* 0x82054 sd zero,312(s1) *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HWb : wr_at rsegs mm (A + 184) 136) by (apply wr_at_write; exact HWa) end.
  pose proof (wr_at_store_ok rsegs _ (A + 184) 136 128 8 HWb ltac:(lia) ltac:(lia)) as HS3.
  replace (A + 184 + 128) with (A + 312) in HS3 by lia.
  step.
  (* 0x82058 li s8,0 ; 0x8205c li s9,0 ; 0x82060 li a0,1 ; 0x82064 j 82148 *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HWc : wr_at rsegs mm (A + 184) 136) by (apply wr_at_write; exact HWb) end.
  step. step. step. step.
  (* 0x82148 sd a0,248(s1) *)
  pose proof (wr_at_store_ok rsegs _ (A + 184) 136 64 8 HWc ltac:(lia) ltac:(lia)) as HS4.
  replace (A + 184 + 64) with (A + 248) in HS4 by lia.
  step.
  finish.
  all: try reflexivity.
  all: try (symmetry; exact Hr9).
  all: try (apply bv_eq; vm_compute; reflexivity).
Qed.

(* The source run (lib.Lib Exec.evt, the form c_run_lib consumes): the compare. *)
Lemma seg_F5_run_of_F :
  forall (regs : bvmap 5 word) (mem : word -> option byte) (A : Z),
    rg regs 10 0 -> rg regs 9 A ->
    0 <= A -> A + 320 <= 2 ^ 64 ->
    wr_at rsegs mem (A + 184) 136 ->
    evt rsegs
      (fun ms => exists R pc' mem', ms = MS R Fr pc' fc None mem' (seg_rom rsegs) /\
         pc' = Z_to_bv 64 0x8214c /\
         mem' = write_to_mem (write_to_mem (write_to_mem (write_to_mem mem
                   (wa (A + 184)) (le8 (Z_to_bv 64 0)))
                   (wa (A + 272)) (le8 (Z_to_bv 64 0)))
                   (wa (A + 312)) (le8 (Z_to_bv 64 0)))
                   (wa (A + 248)) (le8 (Z_to_bv 64 1)) /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
         getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
         getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
         getr R 24 = Z_to_bv 64 0 /\ getr R 25 = Z_to_bv 64 0)
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x82048) fc None mem (seg_rom rsegs)).
Proof.
  intros regs mem A Ha0 Hr9 HA0 HA1 HW.
  apply (evtF_evt rsegs RNG_all).
  apply seg_F5_F with (A := A); try assumption; apply rng_all; lia.
Qed.

End F5F.
