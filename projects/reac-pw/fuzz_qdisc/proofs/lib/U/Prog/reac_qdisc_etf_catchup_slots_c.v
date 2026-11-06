From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require Import qdisc_spec.
Import ListNotations.
Open Scope Z_scope.

(** reac_qdisc_etf_catchup_slots (reac_qdisc.c; 96 bytes at 0x12ca0 in the ubsan image), called by
    LLVMFuzzerTestOneInput with the u16 lead in a0 and a frame rate of the harness's table in a1 (an int,
    sign-extended by the RV64 ABI). It returns slots_spec in a0, writes only a0-a3, and stores nothing and reads only the 8-byte constant 0x431BDE82D7B634DB at 0x103a8 (read-only segment, so mem_inv makes the read come from the image). *)
Definition QDISC_SLOTS : Z := 0x12ca0.

Definition qdisc_slots_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lead fps : Z),
    0 <= lead <= 65535 -> bv_unsigned a0 = lead ->
    -2^31 <= fps < 2^31 -> a1 = Z_to_bv 64 fps ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (slots_spec lead fps)) a1' a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 QDISC_SLOTS) fc None m (seg_rom rsegs)).
