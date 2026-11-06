From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require Import qdisc_spec.
Import ListNotations.
Open Scope Z_scope.

(** check_slots (fuzz_qdisc.c:72-87; 112 bytes at 0x12c00 in the plain image), called by
    LLVMFuzzerTestOneInput with the value reac_qdisc_etf_catchup_slots returned in a0, the u16 lead in a1 and
    the frame rate in a2 (an int, sign-extended). When a0 is slots_spec of lead and fps it returns without
    calling abort, writes only a1-a3, and stores nothing and reads only the 8-byte constant 0x431BDE82D7B634DB at 0x103a8 (read-only segment, so mem_inv makes the read come from the image) (the abort path is the only one that uses stack). *)
Definition QDISC_CHECK : Z := 0x12c00.

Definition qdisc_check_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lead fps : Z),
    0 <= lead <= 65535 -> bv_unsigned a1 = lead ->
    -2^31 <= fps < 2^31 -> a2 = Z_to_bv 64 fps ->
    a0 = Z_to_bv 64 (slots_spec lead fps) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 QDISC_CHECK) fc None m (seg_rom rsegs)).
