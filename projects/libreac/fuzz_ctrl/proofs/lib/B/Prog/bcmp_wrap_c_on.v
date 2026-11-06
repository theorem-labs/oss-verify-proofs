(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 748 of its 797 lines of code are new or changed and 962 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F14.v, with its module paths, module names, addresses and numbers changed; 619 of its 695 lines of code are new or changed and 721 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F31F.v, with its module paths and module names changed; 28 of its 73 lines of code are new or changed and 650 lines of the source are left out. *)
(* lib/B/Prog/bcmp_wrap_c_on.v -- route (C) (a Theorem Labs lane 09:20Z; a Theorem Labs lane wave L1, writer a Theorem Labs lane): the `_on` STATEMENTS
   of bcmp_wrap_c.v (LEAF: it Requires only what bcmp_wrap_c.v Requires, plus B.ShadowRwOn and B.Prog.sh_word_on,
   so a caller that Requires it gets no twin module from a proof's closure; a Theorem Labs lane 10:24Z). The proofs are in
   lib/B/Prog/bcmp_wrap_on.v. bcmp_wrap_c.v stays byte-identical. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c.
Import ListNotations.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import bcmp_wrap_c sh_word_on.
Open Scope Z_scope.

(* The shadow bytes the run reads: the range-check words of both strings. *)
Definition bcmp_wrap_shadow_R (L R N : Z) (a : Z) : Prop := sh_word_on L N a \/ sh_word_on R N a.


Open Scope bv_scope.
Definition bcmp_wrap_post_on (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (ls rs : list byte) (v lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m')
    /\ bytes_at rsegs m' (bv_unsigned a0) (firstn (Z.to_nat (bv_unsigned a2)) ls)
    /\ bytes_at rsegs m' (bv_unsigned a1) (firstn (Z.to_nat (bv_unsigned a2)) rs).


Definition bcmp_wrap_contract_on : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  let L := bv_unsigned a0 in let R := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m L ls ->
  bytes_at rsegs m R rs ->
  memcmp_model ls rs (Z.to_nat N) = Some v ->
  mem_inv rsegs m ->
  (N <= 2^40)%Z -> addressable m L N -> addressable m R N -> end_in_app L N -> end_in_app R N ->
  (N = 0 \/ app_mem (L + 7))%Z -> (N = 0 \/ app_mem (R + 7))%Z ->
  (L + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L)%Z ->
  (R + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + BCMP_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw_on (bcmp_wrap_shadow_R L R N) m ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  evt rsegs (bcmp_wrap_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs)).
Close Scope bv_scope.

Definition bcmp_wrap_contract_F_on : Prop :=
  forall (RNG : footprint) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  let L := bv_unsigned a0 in let R := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m L ls ->
  bytes_at rsegs m R rs ->
  memcmp_model ls rs (Z.to_nat N) = Some v ->
  mem_inv rsegs m ->
  (N <= 2^40)%Z -> addressable m L N -> addressable m R N -> end_in_app L N -> end_in_app R N ->
  (N = 0 \/ app_mem (L + 7))%Z -> (N = 0 \/ app_mem (R + 7))%Z ->
  (L + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L)%Z ->
  (R + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + BCMP_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw_on (bcmp_wrap_shadow_R L R N) m ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  rng_bytes RNG ->
  rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
  rng RNG L N -> (N = 0 \/ rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + N - 1) / 8) + 8 - 8 * (shadow_addr L / 8))) ->
  rng RNG R N -> (N = 0 \/ rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + N - 1) / 8) + 8 - 8 * (shadow_addr R / 8))) ->
  evtF rsegs RNG (bcmp_wrap_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs)).
