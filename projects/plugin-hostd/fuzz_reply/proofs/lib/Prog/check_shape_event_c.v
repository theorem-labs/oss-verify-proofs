From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import next_line_c.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_SHAPE_EVENT : Z := 0x14a90.
Definition CHECK_SHAPE_EVENT_K : Z := 96.
Definition G_GONE : Z := 0x30fc8.

Definition check_shape_event_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo gone : Z)
         (nout out : word) (e slack ob : list byte),
    let EV := bv_unsigned a0 in
    let SP := bv_unsigned sp in
    let O := bv_unsigned nout in
    let W := [(SP - CHECK_SHAPE_EVENT_K, SP)] in
    stk rsegs m lo SP -> lo + CHECK_SHAPE_EVENT_K <= SP -> SP mod 16 = 0 ->
    mem_inv rsegs m ->
    bytes_at rsegs m EV (e ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) e ->
    (- (EV + Z.of_nat (length e) + 1)) mod 8 <= Z.of_nat (length slack) ->
    disjoint_from W EV (Z.of_nat (length (e ++ Z_to_bv 8 0 :: slack))) ->
    bytes_at rsegs m G_GONE [Z_to_bv 8 gone] -> (gone = 0 \/ gone = 1) -> disjoint_from W G_GONE 1 ->
    bytes_at rsegs m G_NOUT (le8 nout) -> disjoint_from W G_NOUT 8 ->
    bytes_at rsegs m G_OUT (le8 out) -> disjoint_from W G_OUT 8 ->
    bytes_at rsegs m (bv_unsigned out) ob -> Z.of_nat (length ob) = O -> disjoint_from W (bv_unsigned out) O ->
    (0 < O -> 0 < bv_unsigned out) ->
    ((gone = 1 /\ O = 0) \/ (gone = 0 /\ ob = e ++ [Z_to_bv 8 0])) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo SP /\
         bytes_at rsegs m' EV (e ++ Z_to_bv 8 0 :: slack) /\ bytes_at rsegs m' (bv_unsigned out) ob)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_SHAPE_EVENT) fc None m (seg_rom rsegs)).
