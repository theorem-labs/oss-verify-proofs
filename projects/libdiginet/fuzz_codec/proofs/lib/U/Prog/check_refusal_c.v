From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** check_refusal (fuzz_codec.c:283-291; 64 bytes at 0x1544c). Called by LLVMFuzzerTestOneInput at 0x14a38
    with a0 = &k (8-aligned: its alignment trap does not fire). As in the plain image. *)
Definition CHECK_REFUSAL : Z := 0x1544c.

Definition check_refusal_pre (a0 : word) (m : word -> option byte) (k : kcall) : Prop :=
  cells_at rsegs m (bv_unsigned a0) (kcall_cells k) /\
  kcall_wf k /\
  bv_unsigned a0 mod 8 = 0 /\
  ~ (k_kind k = 11 /\ k_b k = 0x70 /\ k_rc k = 0).

Definition check_refusal_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k : kcall),
    check_refusal_pre a0 m k ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REFUSAL) fc None m (seg_rom rsegs)).
