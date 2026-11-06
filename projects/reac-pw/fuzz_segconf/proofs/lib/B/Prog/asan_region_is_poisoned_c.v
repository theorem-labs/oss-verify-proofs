(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Prog/asan_region_is_poisoned_c.v: ported from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Prog/asan_region_is_poisoned_c.v, which equals the A->B relocation (asan-kit elfmap.py + remap.py) of lib/A/Prog/asan_region_is_poisoned_c.v at cold/port-fm-int 5d8d8a15571 modulo module paths; module paths for this tree. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import Img0 AsanRT.
Import ListNotations.
Open Scope bv_scope.

Definition ASAN_REGION_IS_POISONED : Z := 0x58724.
Definition ASAN_REGION_IS_POISONED_K : Z := 80.

Definition asan_region_is_poisoned_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - ASAN_REGION_IS_POISONED_K, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Definition asan_region_is_poisoned_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  let P := bv_unsigned a0 in let N := bv_unsigned a1 in
  (1 <= N <= 2^40)%Z -> app_mem P -> app_mem (P + N) -> app_mem (P + 7) -> addressable m P N ->
  asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + ASAN_REGION_IS_POISONED_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  evt rsegs (asan_region_is_poisoned_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_REGION_IS_POISONED) fc None m (seg_rom rsegs)).
