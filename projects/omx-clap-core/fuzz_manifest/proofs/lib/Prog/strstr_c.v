From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Spec Require Import StrStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import twoway_strstr_c.
Import ListNotations.
Open Scope Z_scope.

Definition STRSTR : Z := 0x1c648.

Definition strstr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (hb hs nb : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strstr_val (bv_unsigned a0) hb nb)) a1' a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 2256, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs)
    /\ bytes_at rsegs m' (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]).

Definition strstr_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (hb hs nb : list byte) (lo : Z) (g : word),
    stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2256 ->
    bytes_at rsegs m (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs) -> ~ In (Z_to_bv 8 0) hb ->
    (- (bv_unsigned a0 + Z.of_nat (length hb) + 1)) mod 8 <= Z.of_nat (length hs) ->
    bv_unsigned a0 <> 0 ->
    bytes_at rsegs m (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) nb ->
    mem_inv rsegs m ->
    (bv_unsigned a0 + Z.of_nat (length hb) + 1 + Z.of_nat (length hs) <= bv_unsigned sp - 2256
       \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a1 + Z.of_nat (length nb) + 1 <= bv_unsigned sp - 2256 \/ bv_unsigned sp <= bv_unsigned a1) ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 g) ->
    GUARD + 8 <= bv_unsigned sp - 2256 -> GOT_GUARD + 8 <= bv_unsigned sp - 2256 ->
    evt rsegs (strstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 hb hs nb lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRSTR) fc None m (seg_rom rsegs)).
