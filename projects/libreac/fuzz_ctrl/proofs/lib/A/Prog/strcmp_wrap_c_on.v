(* lib/A/Prog/strcmp_wrap_c_on.v -- route (C) (a Theorem Labs lane 09:20Z; a Theorem Labs lane's wave, writer a Theorem Labs lane): the `_on` STATEMENTS
   of strcmp_wrap_c.v (LEAF: it Requires only what strcmp_wrap_c.v Requires, plus A.ShadowRwOn and A.Prog.sh_word_on,
   so a caller that Requires it gets no twin module from a proof's closure; a Theorem Labs lane 10:24Z). The proofs are in
   lib/A/Prog/strcmp_wrap_on.v (not in this delivery). strcmp_wrap_c.v stays byte-identical. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
Import ListNotations.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import strcmp_wrap_c sh_word_on.
Open Scope Z_scope.

(* The shadow bytes the run reads: the range-check words of [X, X + k + 1) and [Y, Y + k + 1) (a Theorem Labs lane 09:44Z). *)
Definition strcmp_wrap_shadow_R (X Y n : Z) (a : Z) : Prop := sh_word_on X n a \/ sh_word_on Y n a.

Definition strcmp_wrap_post_on (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (sx sy : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 r a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ r = Z_to_bv 64 (strcmp_wrap_res sx sy) /\ (r = Z_to_bv 64 0 <-> sx = sy)
    /\ munch [(bv_unsigned sp - STRCMP_WRAP_K, bv_unsigned sp)] m m' /\ wmono rsegs m m'
    /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (sx ++ [Z_to_bv 8 0]) /\ bytes_at rsegs m' (bv_unsigned a1) (sy ++ [Z_to_bv 8 0])
    /\ asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m').

Definition strcmp_wrap_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sx sy : list byte) (lo : Z),
    let X := bv_unsigned a0 in let Y := bv_unsigned a1 in let k := Z.of_nat (strcmp_k sx sy) in
    bytes_at rsegs m X (sx ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sx ->
    bytes_at rsegs m Y (sy ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sy ->
    k + 1 <= 2^40 -> addressable m X (k + 1) -> end_in_app X (k + 1) -> addressable m Y (k + 1) -> end_in_app Y (k + 1) ->
    app_mem (X + 7) -> app_mem (Y + 7) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + STRCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    (X + Z.of_nat (length sx) + 1 <= bv_unsigned sp - STRCMP_WRAP_K \/ bv_unsigned sp <= X) ->
    (Y + Z.of_nat (length sy) + 1 <= bv_unsigned sp - STRCMP_WRAP_K \/ bv_unsigned sp <= Y) ->
    asan_cells m -> shadow_rw_on (strcmp_wrap_shadow_R X Y (k + 1)) m ->
    mem_inv rsegs m ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 250) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 245) [Z_to_bv 8 0] ->
    evt rsegs (strcmp_wrap_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 sx sy lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRCMP_WRAP) fc None m (seg_rom rsegs)).
