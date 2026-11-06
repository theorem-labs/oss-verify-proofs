(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Prog/twoway_strstr_c.v: ported from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Prog/twoway_strstr_c.v, which equals the A->B relocation (asan-kit elfmap.py + remap.py) of lib/A/Prog/twoway_strstr_c.v at cold/port-fm-int 5d8d8a15571 modulo module paths; module paths for this tree. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Spec Require Import StrStr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require memchr_c memcmp_c memchr_wrap_c memcmp_wrap_c.
Import ListNotations.
Open Scope Z_scope.

Definition TWOWAY_STRSTR : Z := 0x9b99c.
Definition TWOWAY_STRSTR_K : Z := 4560.
Definition GOT_GUARD : Z := 0xa3e98.
Definition GUARD : Z := 0x5ff838.

Definition twoway_strstr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (hb hs nb : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strstr_val (bv_unsigned a0) hb nb)) a1' a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - TWOWAY_STRSTR_K, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m' /\ shadow_rw m'
    /\ bytes_at rsegs m' (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs)
    /\ bytes_at rsegs m' (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]).

Definition twoway_strstr_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (hb hs nb : list byte) (lo : Z) (g : word),
    stk rsegs m lo (bv_unsigned sp) -> lo + TWOWAY_STRSTR_K <= bv_unsigned sp ->
    bytes_at rsegs m (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs) -> ~ In (Z_to_bv 8 0) hb ->
    (- (bv_unsigned a0 + Z.of_nat (length hb) + 1)) mod 8 <= Z.of_nat (length hs) ->
    nb <> [] ->
    bytes_at rsegs m (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) nb ->
    mem_inv rsegs m ->
    (bv_unsigned a0 + Z.of_nat (length hb) + 1 + Z.of_nat (length hs) <= bv_unsigned sp - TWOWAY_STRSTR_K
       \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a1 + Z.of_nat (length nb) + 1 <= bv_unsigned sp - TWOWAY_STRSTR_K \/ bv_unsigned sp <= bv_unsigned a1) ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 g) ->
    GUARD + 8 <= bv_unsigned sp - TWOWAY_STRSTR_K -> GOT_GUARD + 8 <= bv_unsigned sp - TWOWAY_STRSTR_K ->
    (Z.of_nat (length hb) + 1 <= 2^40) -> (Z.of_nat (length nb) + 1 <= 2^40) ->
    addressable m (bv_unsigned a0) (Z.of_nat (length hb) + 1) -> addressable m (bv_unsigned a1) (Z.of_nat (length nb) + 1) ->
    end_in_app (bv_unsigned a0) (Z.of_nat (length hb) + 1) -> end_in_app (bv_unsigned a1) (Z.of_nat (length nb) + 1) ->
    (forall i, 0 <= i < Z.of_nat (length hb) + 1 -> app_mem (bv_unsigned a0 + i + 7)) ->
    (forall i, 0 <= i < Z.of_nat (length nb) + 1 -> app_mem (bv_unsigned a1 + i + 7)) ->
    (HIGHMEM_BEG <= lo) -> (bv_unsigned sp <= APPMEM_END) -> asan_cells m -> shadow_rw m ->
    bytes_at rsegs m memchr_wrap_c.REAL_MEMCHR (le8 (wa memchr_c.MEMCHR)) ->
    bytes_at rsegs m memcmp_wrap_c.REAL_MEMCMP (le8 (wa memcmp_c.MEMCMP)) ->
    bytes_at rsegs m memcmp_wrap_c.GOT_CF (le8 (wa memcmp_wrap_c.CF)) ->
    bytes_at rsegs m (memcmp_wrap_c.CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (memcmp_wrap_c.CF + 255) [Z_to_bv 8 1] ->
    evt rsegs (twoway_strstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 hb hs nb lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TWOWAY_STRSTR) fc None m (seg_rom rsegs)).
