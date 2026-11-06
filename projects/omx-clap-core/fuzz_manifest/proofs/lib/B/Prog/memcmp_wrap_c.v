(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Prog/memcmp_wrap_c.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Prog/memcmp_wrap_c.v, which equals the A->B relocation (Theorem Labs tools) of lib/A/Prog/memcmp_wrap_c.v at a working branch 5d8d8a15571 modulo module paths; module paths for this tree. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog Require Import memcmp_c.
Import ListNotations.
Open Scope bv_scope.

Definition MEMCMP_WRAP : Z := 0x41344.
Definition MEMCMP_WRAP_K : Z := 2320.
Definition REAL_MEMCMP : Z := 0x9b9d8.
Definition GOT_CF : Z := 0x99c88.
Definition CF : Z := 0x133ba8.

Definition memcmp_wrap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (ls rs : list byte) (v lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - MEMCMP_WRAP_K, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m' /\ shadow_rw m'
    /\ bytes_at rsegs m' (bv_unsigned a0) (firstn (Z.to_nat (bv_unsigned a2)) ls)
    /\ bytes_at rsegs m' (bv_unsigned a1) (firstn (Z.to_nat (bv_unsigned a2)) rs).

Definition memcmp_wrap_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  let L := bv_unsigned a0 in let R := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m L ls ->
  bytes_at rsegs m R rs ->
  memcmp_model ls rs (Z.to_nat N) = Some v ->
  mem_inv rsegs m ->
  (N <= 2^40)%Z -> addressable m L N -> addressable m R N -> end_in_app L N -> end_in_app R N ->
  (N = 0 \/ app_mem (L + 7))%Z -> (N = 0 \/ app_mem (R + 7))%Z ->
  (L + N <= bv_unsigned sp - MEMCMP_WRAP_K \/ bv_unsigned sp <= L)%Z ->
  (R + N <= bv_unsigned sp - MEMCMP_WRAP_K \/ bv_unsigned sp <= R)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + MEMCMP_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw m ->
  bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  evt rsegs (memcmp_wrap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MEMCMP_WRAP) fc None m (seg_rom rsegs)).
