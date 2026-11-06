(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/R_strchr.v, with its module paths and module names changed; 22 of its 39 lines of code are new or changed and 418 lines of the source are left out. *)
(* lib/A/Prog/strchr_wrap_c.v (a Theorem Labs lane's port, unchanged from a working branch affce6489c8) with the one change
   of the local-shadow variant (FMss_shv.v): `shadow_rw m` becomes `shvis m S N` for the checked range, and the post's
   `shadow_rw m'` becomes `shvis m' S N`.  The constants, strchr_val and strchr_n stay in the original module. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import Img0 AsanRT FMss_shv.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog Require Import strchr_wrap_c.
Import ListNotations.
Open Scope bv_scope.

Definition strchr_wrap_post_L (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strchr_val (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - STRCHR_WRAP_K, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m'
    /\ shvis m' (bv_unsigned a0) (strchr_n (bv_unsigned a0) (bv_unsigned a1 mod 256) str)
    /\ bytes_at rsegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Definition strchr_wrap_contract_L : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  let S := bv_unsigned a0 in let C := (bv_unsigned a1 mod 256)%Z in let N := strchr_n S C str in
  bytes_at rsegs m S (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv rsegs m ->
  C <> 0%Z ->
  (N <= 2^40)%Z -> addressable m S N -> end_in_app S N -> app_mem (S + 7) ->
  (S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - STRCHR_WRAP_K \/ bv_unsigned sp <= S)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + STRCHR_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shvis m S N ->
  bytes_at rsegs m REAL_STRCHR (le8 (wa STRCHR)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 245)%Z [Z_to_bv 8 0] -> bytes_at rsegs m (CF + 253)%Z [Z_to_bv 8 1] ->
  evt rsegs (strchr_wrap_post_L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRCHR_WRAP) fc None m (seg_rom rsegs)).
