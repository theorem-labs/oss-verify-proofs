From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memrchr_c.
Import ListNotations.
Open Scope Z_scope.

Definition STRRCHR : Z := 0x1df28.
Definition STRRCHR_K : Z := 32.

Definition strrchr_res (A c : Z) (str : list byte) : Z :=
  match rfind_byte c (str ++ [Z_to_bv 8 0]) with Some i => A + Z.of_nat i | None => 0 end.

Lemma strrchr_res_nonnul : forall A c str, c <> 0 ->
  strrchr_res A c str = match rfind_byte c str with Some i => A + Z.of_nat i | None => 0 end.
Proof.
  intros A c str H. unfold strrchr_res.
  assert (E : bv_unsigned (Z_to_bv 8 0) = 0) by reflexivity.
  rewrite rfind_byte_snoc_miss; [reflexivity|]. rewrite E. lia.
Qed.

Lemma strrchr_res_nul : forall A str, strrchr_res A 0 str = A + Z.of_nat (length str).
Proof. intros A str. unfold strrchr_res. rewrite rfind_byte_snoc_hit by reflexivity. reflexivity. Qed.

Definition strrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strrchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - STRRCHR_K, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Definition strrchr_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte) (lo : Z),
    bytes_at rsegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
    ~ In (Z_to_bv 8 0) str ->
    (- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + STRRCHR_K <= bv_unsigned sp ->
    (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - STRRCHR_K
       \/ bv_unsigned sp <= bv_unsigned a0) ->
    evt rsegs (strrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRRCHR) fc None m (seg_rom rsegs)).
