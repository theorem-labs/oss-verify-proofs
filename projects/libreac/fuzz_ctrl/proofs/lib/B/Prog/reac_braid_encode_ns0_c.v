From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BRAID_ENCODE : Z := 0x87afc.
Definition REAC_BRAID_ENCODE_FRAME : Z := 128.

Definition reac_braid_encode_ns0_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ns : Z),
    -2^31 <= ns <= 0 -> a4 = Z_to_bv 64 ns ->
    stk rsegs m (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) (bv_unsigned sp) ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_BRAID_ENCODE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BRAID_ENCODE) fc None m (seg_rom rsegs)).

(* ---- the footprint form (RECIPE.md step 1 (a working note, not in this delivery)) ----
   The same run as an ExecF.evtF under a footprint RNG. On this path (ns <= 0) the run only saves and restores
   registers in its own frame, so its one data region is [sp - REAC_BRAID_ENCODE_FRAME, sp), the munch window of
   the post; that is the one rng premise. The run reads no cell by absolute address and takes no instrumented
   check: the plain contract carries no asan_cells / shadow_rw premise, so no shadow load could be shown, and an
   instruction fetch is not an access of ExecF.
   reac_braid_encode_ns0_contract_of_F gives the old statement back with RNG_all. *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.

Definition reac_braid_encode_ns0_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ns : Z),
    -2^31 <= ns <= 0 -> a4 = Z_to_bv 64 ns ->
    stk rsegs m (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) (bv_unsigned sp) ->
    rng RNG (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) REAC_BRAID_ENCODE_FRAME ->
    evtF rsegs RNG
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_BRAID_ENCODE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BRAID_ENCODE) fc None m (seg_rom rsegs)).

(* The old statement is the footprint form at RNG_all: the one rng premise by rng_all, from the bounds that stk
   already gives (0 <= sp - REAC_BRAID_ENCODE_FRAME and sp <= 2^64). So the footprint form asks for nothing the
   old contract lacks. *)
Lemma reac_braid_encode_ns0_contract_of_F :
  reac_braid_encode_ns0_contract_F -> reac_braid_encode_ns0_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ns Hns Ha4 ST.
  pose proof ST as (ST0 & ST1 & _).
  eapply evtF_evt,
    (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
        F fc m ns); try assumption.
  apply rng_all; lia.
Qed.
