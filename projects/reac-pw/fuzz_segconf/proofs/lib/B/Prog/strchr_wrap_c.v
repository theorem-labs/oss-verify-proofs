(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/R_strchr.v, with its module paths and module names changed; 28 of its 47 lines of code are new or changed and 416 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Prog/strchr_wrap_c.v: ported from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Prog/strchr_wrap_c.v, which equals the A->B relocation (asan-kit elfmap.py + remap.py) of lib/A/Prog/strchr_wrap_c.v at cold/port-fm-int 5d8d8a15571 modulo module paths; module paths for this tree. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Spec Require Import StrFun StrFun2.
Import ListNotations.
Open Scope bv_scope.

Definition STRCHR_WRAP : Z := 0x43ab4.
Definition STRCHR_WRAP_K : Z := 2224.
Definition STRCHR : Z := 0x9b180.
Definition REAL_STRCHR : Z := 0xa4f40.
Definition GOT_CF : Z := 0xa3200.
Definition CF : Z := 0x13e2e8.

Definition strchr_val (A c : Z) (str : list byte) : Z :=
  if (c =? 0)%Z then (A + Z.of_nat (length str))%Z else strchr_res A c str.

Definition strchr_n (A c : Z) (str : list byte) : Z :=
  if (strchr_val A c str =? 0)%Z then (Z.of_nat (length str) + 1)%Z else (strchr_val A c str - A + 1)%Z.

Definition strchr_wrap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strchr_val (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - STRCHR_WRAP_K, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m' /\ shadow_rw m'
    /\ bytes_at rsegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Definition strchr_wrap_contract : Prop :=
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
  asan_cells m -> shadow_rw m ->
  bytes_at rsegs m REAL_STRCHR (le8 (wa STRCHR)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 245)%Z [Z_to_bv 8 0] -> bytes_at rsegs m (CF + 253)%Z [Z_to_bv 8 1] ->
  evt rsegs (strchr_wrap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRCHR_WRAP) fc None m (seg_rom rsegs)).
