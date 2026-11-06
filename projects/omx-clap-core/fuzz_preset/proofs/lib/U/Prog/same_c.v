From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
Import ListNotations.
Open Scope Z_scope.

Definition SAME : Z := 0x14520.
Definition SAME_FS : Z := 80.

Definition same_k (t : jv) : Z := SAME_FS * (Z.of_nat (depth t) + 1).

Definition same_ledger (L : Z -> Z -> Prop) : Prop :=
  forall x k, L x k -> 0 < x /\ x mod 8 = 0 /\ x + k <= 2 ^ 63.

Definition same_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (L : Z -> Z -> Prop) (lo pa pb : Z) (ta tb : jv) (Da Db : list (Z * Z))
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - same_k ta, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    (ta = tb /\ r = Z_to_bv 64 1 \/ ta <> tb /\ r = Z_to_bv 64 0) /\
    pj_node rsegs m' L pa ta Da /\ pj_node rsegs m' L pb tb Db.

Definition same_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (L : Z -> Z -> Prop) (lo pa pb : Z)
         (ta tb : jv) (Da Db : list (Z * Z)),
    a0 = Z_to_bv 64 pa -> a1 = Z_to_bv 64 pb -> pa <> 0 -> pb <> 0 ->
    same_ledger L ->
    pj_node rsegs m L pa ta Da -> pj_node rsegs m L pb tb Db ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + same_k ta <= bv_unsigned sp ->
    (forall z, pj_foot pa Da z -> outside [(bv_unsigned sp - same_k ta, bv_unsigned sp)] z) ->
    (forall z, pj_foot pb Db z -> outside [(bv_unsigned sp - same_k ta, bv_unsigned sp)] z) ->
    evt rsegs (same_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L lo pa pb ta tb Da Db)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SAME) fc None m (seg_rom rsegs)).
