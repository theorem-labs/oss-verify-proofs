(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMss_memchr_wrap_c.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* lib/A/Prog/memchr_wrap_c.v (a Theorem Labs lane's port, unchanged from a working branch affce6489c8) with the one change
   of the local-shadow variant (FMss_shv.v): `shadow_rw m` becomes `shvis m P N` for the checked range, and the post's
   `shadow_rw m'` becomes `shvis m' P N`.  The constants and memchr_n stay in the original module. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import Img0 AsanRT FMss_shv.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog Require Import memchr_c memchr_wrap_c.
Import ListNotations.
Open Scope bv_scope.

Definition memchr_wrap_post_L (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - MEMCHR_WRAP_K, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m'
    /\ shvis m' (bv_unsigned a0) (memchr_n (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf)
    /\ bytes_at rsegs m' (bv_unsigned a0) buf.

Definition memchr_wrap_contract_L : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  let P := bv_unsigned a0 in let N := memchr_n P (bv_unsigned a1 mod 256) (bv_unsigned a2) buf in
  bytes_at rsegs m P buf ->
  memchr_ok P (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
  mem_inv rsegs m ->
  (N <= 2^40)%Z -> addressable m P N -> end_in_app P N -> (N = 0 \/ app_mem (P + 7))%Z ->
  (P + Z.of_nat (length buf) <= bv_unsigned sp - MEMCHR_WRAP_K \/ bv_unsigned sp <= P)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + MEMCHR_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shvis m P N ->
  bytes_at rsegs m REAL_MEMCHR (le8 (wa MEMCHR)) ->
  evt rsegs (memchr_wrap_post_L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MEMCHR_WRAP) fc None m (seg_rom rsegs)).
