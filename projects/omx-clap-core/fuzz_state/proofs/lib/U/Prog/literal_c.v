From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjIn.
Import ListNotations.
Open Scope Z_scope.

Definition LITERAL : Z := 0x15c28.

Definition lit_hit (txt : list byte) (k : Z) (cw : list byte) : Prop :=
  Z.of_nat (length cw) <= Z.of_nat (length txt) - k /\
  firstn (length cw) (skipn (Z.to_nat k) txt) = cw.

Definition literal_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (q text len p d : Z) (txt : list byte) (w : Z) (cw slack : list byte) (ty v lo : Z),
    a0 = Z_to_bv 64 q -> a1 = Z_to_bv 64 w -> a2 = Z_to_bv 64 ty -> a3 = Z_to_bv 64 v ->
    pj_in_ok rsegs m q text len p d txt ->
    0 <= w -> w + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= 2 ^ 64 ->
    ro_bytes rsegs w (cw ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) cw ->
    (- (w + Z.of_nat (length cw) + 1)) mod 8 <= Z.of_nat (length slack) ->
    0 <= ty <= 2 ->
    v <> 0 -> v mod 8 = 0 -> wr_at rsegs m v 4 ->
    disjoint_from [(q, q + 24); (text, text + len)] v 4 ->
    stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
    disjoint_from [(q, q + 24); (text, text + len); (v, v + 4)] (bv_unsigned sp - 64) 64 ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 64, bv_unsigned sp); (q, q + 8); (v, v + 4)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         ((lit_hit txt (p - text) cw /\ r = Z_to_bv 64 0 /\
           pj_in_ok rsegs m' q text len (p + Z.of_nat (length cw)) d txt /\
           bytes_at rsegs m' v (le4 (Z_to_bv 64 ty))) \/
          (~ lit_hit txt (p - text) cw /\ r = Z_to_bv 64 (-1) /\
           munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\
           pj_in_ok rsegs m' q text len p d txt)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LITERAL) fc None m (seg_rom rsegs)).
