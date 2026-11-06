From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model.
Import ListNotations.
Open Scope Z_scope.

Definition JSON_SCALAR : Z := 0x14970.
Definition JSON_SCALAR_K : Z := 112.
Definition JSON_SCALAR_L : Z := 0x205e0.

Definition json_scalar_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) (b i v : word) (B : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    match jscalar (map bv_unsigned B) (bv_unsigned i) with
    | Some (e, k, s, l) =>
        a0' = Z_to_bv 64 e /\
        munch [(bv_unsigned sp - JSON_SCALAR_K, bv_unsigned sp); (bv_unsigned v, bv_unsigned v + 20)] m m' /\
        bytes_at rsegs m' (bv_unsigned v) (le8 (Z_to_bv 64 (bv_unsigned b + s)) ++ le8 (Z_to_bv 64 l) ++ le4 (Z_to_bv 64 k))
    | None =>
        a0' = Z_to_bv 64 0 /\ munch [(bv_unsigned sp - JSON_SCALAR_K, bv_unsigned sp)] m m'
    end.

Definition json_scalar_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B : list byte),
    Z.of_nat (length B) = bv_unsigned a2 ->
    bv_unsigned a0 + bv_unsigned a2 <= 2^64 ->
    (bv_unsigned a1 < bv_unsigned a2 ->
       bytes_at rsegs m (bv_unsigned a0) B /\
       (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - JSON_SCALAR_K \/ bv_unsigned sp <= bv_unsigned a0)) ->
    bv_unsigned a3 mod 8 = 0 ->
    wr_at rsegs m (bv_unsigned a3) 20 ->
    (bv_unsigned a3 + 20 <= bv_unsigned sp - JSON_SCALAR_K \/ bv_unsigned sp <= bv_unsigned a3) ->
    bytes_at rsegs m JSON_SCALAR_L (le8 (Z_to_bv 64 0x103aa) ++ le8 (Z_to_bv 64 0x10298) ++ le8 (Z_to_bv 64 0x10326)) ->
    (JSON_SCALAR_L + 24 <= bv_unsigned sp - JSON_SCALAR_K \/ bv_unsigned sp <= JSON_SCALAR_L) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + JSON_SCALAR_K <= bv_unsigned sp ->
    evt rsegs (json_scalar_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m a0 a1 a3 B)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 JSON_SCALAR) fc None m (seg_rom rsegs)).
