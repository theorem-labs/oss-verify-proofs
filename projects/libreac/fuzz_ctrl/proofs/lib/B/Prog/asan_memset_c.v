From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
Import ListNotations.
Open Scope bv_scope.

Definition ASAN_MEMSET : Z := 0x52600.
(* ASAN_MEMSET_K = 2208 is EXACT, not an over-approximation. It is the deepest stack that __asan_memset (0x52600)
   uses on a path that does not end in an ASan report, measured on this image (internal path,
   fuzz_ctrl):
     2128  the helper's own frame: addi sp,sp,-2032 at 0x52600 and addi sp,sp,-96 at 0x52624;
   +   64  __asan_region_is_poisoned (0x54ce0): addi sp,sp,-64 at 0x54ce0. The helper calls it at 0x527e4, with
           its own frame live;
   +   16  mem_is_zero (0x64a20), called by __asan_region_is_poisoned at 0x54e50: addi sp,sp,-16 at 0x64a20;
   = 2208  (64 + 16 = 80 = ASAN_REGION_IS_POISONED_K, asan_region_is_poisoned_c.v).
   No other callee adds to it. MemToShadow (0x54854), which __asan_region_is_poisoned also calls, has no frame on
   the normal path: its addi sp,sp,-16 at 0x54968 is only on the path to CheckFailed. REAL(memset), the jalr at
   0x52698 through REAL_MEMSET = 0xa2758, is musl memset at 0x98e34 (MUSL_MEMSET, AsanRT.v asan_cells): a leaf,
   with no stack frame and no call. The other calls of the helper (AsanInited, the report and stack-trace calls)
   are on paths that the premises of the contract exclude.
   __asan_region_is_poisoned is on a NON-error path, and that is why its frame counts: the helper calls it for
   N >= 65 always (0x52650, 0x52798), and for 1 <= N <= 64 when the aligned 8-byte shadow word check is nonzero
   (0x5268c) and the inline byte check does not clear it (0x527a0). When it returns 0, the helper continues to
   REAL(memset).
   DO NOT REDUCE K BELOW THIS DERIVATION. With a smaller K the contract is false: the post's munch would keep
   [sp - 2208, sp - K) unchanged, but __asan_region_is_poisoned and mem_is_zero write their frames there, and
   the footprint premise rng RNG (sp - K) K would not hold those accesses. A caller that uses such a contract
   reasons unsoundly. Before you change K, derive again the full call tree on the target image, non-error paths
   included. *)
Definition ASAN_MEMSET_K : Z := 2208.

Definition asan_memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2);
              (bv_unsigned sp - ASAN_MEMSET_K, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))]
    /\ asan_cells m' /\ shadow_rw m'.

Definition asan_memset_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte) (lo : Z),
  let D := bv_unsigned a0 in let N := bv_unsigned a2 in
  rw_cells rsegs m D [CB (Z.to_nat N) junk] ->
  (N <= 2^40)%Z -> addressable m D N -> end_in_app D N ->
  (N = 0 \/ app_mem (D + 7))%Z -> (D + N <= RT_LO \/ RT_HI <= D)%Z ->
  (D + N <= bv_unsigned sp - ASAN_MEMSET_K \/ bv_unsigned sp <= D)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + ASAN_MEMSET_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
  evt rsegs (asan_memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMSET) fc None m (seg_rom rsegs)).
