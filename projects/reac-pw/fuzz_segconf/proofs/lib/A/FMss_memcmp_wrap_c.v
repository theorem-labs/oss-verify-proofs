(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 748 of its 797 lines of code are new or changed and 962 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F14.v, with its module paths, module names, addresses and numbers changed; 619 of its 695 lines of code are new or changed and 721 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F31F.v, with its module paths and module names changed; 23 of its 40 lines of code are new or changed and 678 lines of the source are left out. *)
(* lib/A/Prog/memcmp_wrap_c.v (RtStr's port, unchanged from cold/c-asan-rt-fmio-n affce6489c8) with the one change
   of the local-shadow variant (FMss_shv.v): `shadow_rw m` becomes `shvis m L N /\ shvis m R N` for the two checked
   ranges, and the post's `shadow_rw m'` the same of m'.  The constants stay in the original module. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import Img0 AsanRT FMss_shv.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import memcmp_c memcmp_wrap_c.
Import ListNotations.
Open Scope bv_scope.

Definition memcmp_wrap_post_L (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (ls rs : list byte) (v lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - MEMCMP_WRAP_K, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m'
    /\ (shvis m' (bv_unsigned a0) (bv_unsigned a2) /\ shvis m' (bv_unsigned a1) (bv_unsigned a2))
    /\ bytes_at rsegs m' (bv_unsigned a0) (firstn (Z.to_nat (bv_unsigned a2)) ls)
    /\ bytes_at rsegs m' (bv_unsigned a1) (firstn (Z.to_nat (bv_unsigned a2)) rs).

Definition memcmp_wrap_contract_L : Prop :=
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
  asan_cells m -> (shvis m L N /\ shvis m R N) ->
  bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  evt rsegs (memcmp_wrap_post_L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MEMCMP_WRAP) fc None m (seg_rom rsegs)).
