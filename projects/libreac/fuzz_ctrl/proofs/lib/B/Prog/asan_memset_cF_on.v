(* Route (C) form of asan_memset_contract_F (asan_memset_cF.v, statement UNCHANGED): fuzz_ctrl's route (C) for the post-call
   shadow (a Theorem Labs lane, 2026-10-29 09:20Z; wave lead a Theorem Labs lane). The binders, the premises (footprint ones included) and
   the post are those of asan_memset_contract_F, with ONE change each way, the same as asan_memset_c_on.v's:
     - the universal premise `shadow_rw m` becomes `shadow_rw_on (asan_memset_shadow_R a0 a2) m`;
     - the post is asan_memset_post_on: its shadow conjunct is `forall P, shadow_rw_on P m -> shadow_rw_on P m'`.
   R (asan_memset_c_on.v) is the contiguous span of aligned shadow words of [D, D + N). The footprint premises are
   unchanged. Author a Theorem Labs lane. Proof: asan_memsetF_on.v asan_memset_holds_F_on. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memset_c asan_memset_cF sh_word_on asan_memset_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
Import ListNotations.
Open Scope Z_scope.

Definition asan_memset_contract_F_on : Prop :=
  forall (RNG : ExF.footprint)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte) (lo : Z),
  let D := bv_unsigned a0 in let N := bv_unsigned a2 in
  rw_cells rsegs m D [CB (Z.to_nat N) junk] ->
  (N <= 2^40)%Z -> addressable m D N -> end_in_app D N ->
  (N = 0 \/ app_mem (D + 7))%Z -> (D + N <= RT_LO \/ RT_HI <= D)%Z ->
  (D + N <= bv_unsigned sp - ASAN_MEMSET_K \/ bv_unsigned sp <= D)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + ASAN_MEMSET_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw_on (asan_memset_shadow_R a0 a2) m -> mem_inv rsegs m ->
  (* the footprint premises: the footprint is byte-wise, then one per region the call reads or writes *)
  RngBytes.rng_bytes RNG ->
  ExF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  ExF.rng RNG (bv_unsigned sp - ASAN_MEMSET_K) ASAN_MEMSET_K ->
  ExF.rng RNG D N ->
  sh_word_rng RNG D N ->
  sh_word_rng RNG (bv_unsigned sp - ASAN_MEMSET_K) ASAN_MEMSET_K ->
  ExF.evtF rsegs RNG (asan_memset_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMSET) fc None m (seg_rom rsegs)).
