From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* rp_restamp (src/repace_wire.c:142-146): f[14] = ctr & 0xff; f[15] = (ctr >> 8) & 0xff.
   a0 = f, a1 = ctr. A leaf: it writes bytes 14 and 15 of f and nothing else. *)
Definition RP_RESTAMP : Z := 0x133e8.

Definition restamp_bytes (ctr : Z) : list byte :=
  [Z_to_bv 8 (ctr mod 256); Z_to_bv 8 (ctr / 256 mod 256)].

Definition rp_restamp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    0 < bv_unsigned a0 ->
    wr_at rsegs m (bv_unsigned a0 + 14) 2 ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned a0 + 14, bv_unsigned a0 + 16)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         bytes_at rsegs m' (bv_unsigned a0 + 14) (restamp_bytes (bv_unsigned a1)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_RESTAMP) fc None m (seg_rom rsegs)).
