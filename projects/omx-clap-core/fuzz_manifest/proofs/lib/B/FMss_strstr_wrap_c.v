(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMss_strstr_wrap_c.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* lib/A/Prog/strstr_wrap_c.v (a Theorem Labs lane's port, unchanged from a working branch affce6489c8) with the
   local-shadow change (FMss_shv.v): the premise `shadow_rw m` and the post's `shadow_rw m'` become
   `shv2 m a0 a1 hb nb` / `shv2 m' a0 a1 hb nb` (FMss_TwAsan.v): the shadow words of the haystack's bytes and NUL
   and of the needle's.  Same names as the original for the post and the contract, which shadow it: import
   strstr_wrap_c first (constants), then this module. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require Import StrStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog Require Import memchr_c memcmp_c strstr_wrap_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMss_TwAsan.
Import ListNotations.
Open Scope bv_scope.

Definition strstr_wrap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (hb hs nb : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strstr_val (bv_unsigned a0) hb nb)) a1' a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - STRSTR_WRAP_K, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m'
    /\ shv2 m' a0 a1 hb nb
    /\ bytes_at rsegs m' (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs)
    /\ bytes_at rsegs m' (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]).

Definition strstr_wrap_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (hb hs nb : list byte) (lo : Z) (g : word),
  let H := bv_unsigned a0 in let ND := bv_unsigned a1 in
  let NH := (Z.of_nat (length hb) + 1)%Z in let NN := (Z.of_nat (length nb) + 1)%Z in
  bytes_at rsegs m H (hb ++ Z_to_bv 8 0 :: hs) -> ~ In (Z_to_bv 8 0) hb ->
  ((- (H + Z.of_nat (length hb) + 1)) mod 8 <= Z.of_nat (length hs))%Z ->
  H <> 0%Z ->
  bytes_at rsegs m ND (nb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) nb ->
  mem_inv rsegs m ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 g) ->
  (NH <= 2^40)%Z -> (NN <= 2^40)%Z ->
  addressable m H NH -> addressable m ND NN -> end_in_app H NH -> end_in_app ND NN ->
  (forall i, (0 <= i < NH)%Z -> app_mem (H + i + 7)) -> (forall i, (0 <= i < NN)%Z -> app_mem (ND + i + 7)) ->
  (H + NH + Z.of_nat (length hs) <= bv_unsigned sp - STRSTR_WRAP_K \/ bv_unsigned sp <= H)%Z ->
  (ND + NN <= bv_unsigned sp - STRSTR_WRAP_K \/ bv_unsigned sp <= ND)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + STRSTR_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shv2 m a0 a1 hb nb ->
  bytes_at rsegs m REAL_STRSTR (le8 (wa STRSTR)) -> bytes_at rsegs m REAL_STRCHR (le8 (wa STRCHR)) ->
  bytes_at rsegs m REAL_MEMCHR (le8 (wa MEMCHR)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 245)%Z [Z_to_bv 8 0] -> bytes_at rsegs m (CF + 246)%Z [Z_to_bv 8 1] ->
  bytes_at rsegs m (CF + 253)%Z [Z_to_bv 8 1] ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  evt rsegs (strstr_wrap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 hb hs nb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRSTR_WRAP) fc None m (seg_rom rsegs)).
