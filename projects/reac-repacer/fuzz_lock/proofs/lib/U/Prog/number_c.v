(* Contract of the harness's static [number] (fuzz_lock.c:64-75) in fuzz_lock.ubsan, 0x131cc.
   number(s, len) on the bytes l of [s, s + len) returns LockSpec.digits l (-1 for a field that is empty, longer
   than 18 bytes or holds a byte that is no decimal digit). It writes no memory and uses no stack.
   0 < s: the UBSan pointer checks at 0x131fc-0x13208 branch to the trap [unimp] at 0x13254 when s is NULL
   (the caller passes a pointer into the input).
   The instructions are those of [digits] at 0x13540 (lib/U/Prog/digits_c.v) shifted by -0x374.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import LockSpec.
Import ListNotations.
Open Scope Z_scope.

Definition NUMBER : Z := 0x131cc.

Definition number_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (digits l)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Definition number_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : Z) (l : list byte),
    0 < s ->
    bytes_at rsegs m s l ->
    mem_inv rsegs m ->
    evt rsegs (number_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m l)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 (Z.of_nat (length l))) a2
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NUMBER) fc None m (seg_rom rsegs)).
