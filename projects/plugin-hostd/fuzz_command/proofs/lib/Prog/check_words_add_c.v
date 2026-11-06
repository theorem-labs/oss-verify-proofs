From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_WORDS_ADD : Z := 0x15118.
Definition CHECK_WORDS_ADD_K : Z := 64.

Definition is_placement_b (s : list byte) : bool :=
  bytes_eqb s S_OWN || bytes_eqb s S_DEFAULT || prefixb s S_POOL.

Definition add_placement (r : Z) (w3 : list byte) : list byte :=
  if (3 <? r) && is_placement_b w3 then w3 else S_DASH.

Definition add_next (r : Z) (w3 : list byte) : Z :=
  if bytes_eqb (add_placement r w3) S_DASH then 3 else 4.

Definition add_client (r : Z) (w3 w4 : list byte) : list byte :=
  if add_next r w3 <? r then (if add_next r w3 =? 3 then w3 else w4) else S_DASH.

Definition check_words_add_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (r nargs : Z) (p3 p4 q2 q3 : word) (w3 w4 x2 x3 : list byte),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_WORDS_ADD_K <= bv_unsigned sp -> IMG_END <= lo ->
    0 <= r <= 64 -> a2 = Z_to_bv 64 r ->
    (3 < r -> word_slot m lo (bv_unsigned sp) (bv_unsigned a1 + 24) p3 w3) ->
    (4 < r -> word_slot m lo (bv_unsigned sp) (bv_unsigned a1 + 32) p4 w4) ->
    0 <= nargs <= 6 ->
    bytes_at rsegs m (bv_unsigned a0 + CALL_NARGS) (le4 (Z_to_bv 64 nargs)) ->
    outside_stack lo (bv_unsigned sp) (bv_unsigned a0 + CALL_NARGS) 4 ->
    (nargs = 4 -> word_slot m lo (bv_unsigned sp) (bv_unsigned a0 + CALL_ARGS + 16) q2 x2) ->
    (nargs = 4 -> word_slot m lo (bv_unsigned sp) (bv_unsigned a0 + CALL_ARGS + 24) q3 x3) ->
    nargs = 4 -> x2 = add_placement r w3 -> x3 = add_client r w3 w4 ->
    evt rsegs (void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_WORDS_ADD) fc None m (seg_rom rsegs)).
