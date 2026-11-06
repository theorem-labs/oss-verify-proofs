From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_BOUNDED : Z := 0x149e8.
Definition CHECK_BOUNDED_FRAME : Z := 16.
Definition G_NSRC : Z := 0x318b8.
Definition G_SRC : Z := 0x318d0.

Definition source_bounded (m : word -> option byte) (P j : Z) : Prop :=
  exists used cap : word,
    bytes_at rsegs m (P + 56 * j + 24) (le8 used) /\
    bytes_at rsegs m (P + 56 * j + 32) (le8 cap) /\
    bv_unsigned used <= 6000 /\ bv_unsigned used <= bv_unsigned cap /\ bv_unsigned cap < 20192.

Definition check_bounded_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo n : Z) (src : word),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_BOUNDED_FRAME <= bv_unsigned sp ->
    -2^31 <= n < 2^31 ->
    bytes_at rsegs m G_NSRC (le4 (Z_to_bv 64 n)) ->
    bytes_at rsegs m G_SRC (le8 src) ->
    (0 < n -> bv_unsigned src <> 0 /\ bv_unsigned src mod 8 = 0 /\ bv_unsigned src + 56 * n <= 2^64) ->
    (forall j, 0 <= j < n -> source_bounded m (bv_unsigned src) j) ->
    G_NSRC + 4 <= bv_unsigned sp - CHECK_BOUNDED_FRAME \/ bv_unsigned sp <= G_NSRC ->
    G_SRC + 8 <= bv_unsigned sp - CHECK_BOUNDED_FRAME \/ bv_unsigned sp <= G_SRC ->
    (forall j, 0 <= j < n ->
       bv_unsigned src + 56 * j + 40 <= bv_unsigned sp - CHECK_BOUNDED_FRAME \/
       bv_unsigned sp <= bv_unsigned src + 56 * j + 24) ->
    evt rsegs
      (fun ms' => exists (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_BOUNDED_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_BOUNDED) fc None m (seg_rom rsegs)).
