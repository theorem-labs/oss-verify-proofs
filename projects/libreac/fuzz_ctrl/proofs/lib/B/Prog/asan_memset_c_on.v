(* Route (C) form of asan_memset_contract (asan_memset_c.v, statement UNCHANGED): fuzz_ctrl's route (C) for the post-call
   shadow (a Theorem Labs lane, 2026-10-29 09:20Z; wave lead a Theorem Labs lane). The binders, the premises and the post are those of
   asan_memset_contract, with ONE change each way:
     - the universal premise `shadow_rw m` becomes `shadow_rw_on (asan_memset_shadow_R a0 a2) m`;
     - the post's `shadow_rw m'` becomes `forall P, shadow_rw_on P m -> shadow_rw_on P m'` (the wave's post form,
       a Theorem Labs lane 09:38Z): the presence of ANY shadow region the caller holds before the call holds after it.
   asan_memset_shadow_R is sh_word_on D N: the CONTIGUOUS span of aligned 8-byte shadow words of the destination
   [D, D + N), from the first byte's word through the last byte's (sh_word_on.v). READS: the inline check reads the
   first and the last word, and the __asan_region_is_poisoned arm (N >= 65) reads the span between; the proof itself
   reads the first and the last word (asan_memset.v:139-140, qc_word). STORES: none into shadow (the post's munch is
   [D, D + N) and the helper's stack). A caller of the frozen contract closes the premise by
   ShadowRwOn.shadow_rw_on_of_shadow_rw; a caller that holds its own region Q carries `shadow_rw_on Q` across the call
   by the post's last conjunct at P := Q.
   Author a Theorem Labs lane. Proof: asan_memset_on.v asan_memset_holds_on. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memset_c sh_word_on.
Import ListNotations.
Open Scope bv_scope.

Definition asan_memset_shadow_R (a0 a2 : word) (a : Z) : Prop := sh_word_on (bv_unsigned a0) (bv_unsigned a2) a.

Definition asan_memset_post_on (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2);
              (bv_unsigned sp - ASAN_MEMSET_K, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))]
    /\ asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m').

Definition asan_memset_contract_on : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte) (lo : Z),
  let D := bv_unsigned a0 in let N := bv_unsigned a2 in
  rw_cells rsegs m D [CB (Z.to_nat N) junk] ->
  (N <= 2^40)%Z -> addressable m D N -> end_in_app D N ->
  (N = 0 \/ app_mem (D + 7))%Z -> (D + N <= RT_LO \/ RT_HI <= D)%Z ->
  (D + N <= bv_unsigned sp - ASAN_MEMSET_K \/ bv_unsigned sp <= D)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + ASAN_MEMSET_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw_on (asan_memset_shadow_R a0 a2) m -> mem_inv rsegs m ->
  evt rsegs (asan_memset_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMSET) fc None m (seg_rom rsegs)).
