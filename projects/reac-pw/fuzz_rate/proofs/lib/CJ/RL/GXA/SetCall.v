(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/CJ/RL/GXA/SetCall.v at 2d2ff01bb6f2; module paths changed (the same text as proofs/plugin-hostd/fuzz_reply/lib/CJ/RL/GXA/SetCall.v at 2d2ff01bb6f2, module paths aside). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require Import RStep.
Import ListNotations.
Open Scope Z_scope.

Definition SET_DEPTH : Z := 2224.

Section Img.
Context {IMG : RImg}.
Variable set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop.

Definition memset_stack_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (a0 a1 a2 : word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2);
              (bv_unsigned sp - SET_DEPTH, bv_unsigned sp)] m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - SET_DEPTH) (bv_unsigned sp)
    /\ rw_cells img_segs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Definition memset_stack_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells img_segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  mem_inv img_segs m ->
  stk img_segs m (bv_unsigned sp - SET_DEPTH) (bv_unsigned sp) ->
  set_ready m (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2) ->
  evt img_segs (memset_stack_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21738)) fc None m (seg_rom img_segs)).

Lemma memset_stack_extend : forall m m' lo q D N,
  stk img_segs m lo q -> lo <= q - SET_DEPTH ->
  (D + N <= lo \/ q <= D) ->
  munch [(D, D + N); (q - SET_DEPTH, q)] m m' -> wmono img_segs m m' ->
  stk img_segs m' (q - SET_DEPTH) q -> stk img_segs m' lo q.
Proof.
  intros m m' lo q D N ST LO SEP MU WM ST'.
  unfold SET_DEPTH in *.
  destruct (stk_split img_segs m lo (q - SET_DEPTH) q ST ltac:(unfold SET_DEPTH; lia)) as [LOW _].
  eapply stk_merge; [|exact ST'|unfold SET_DEPTH; lia].
  eapply stk_transport_disjoint; [exact LOW|exact MU|exact WM|].
  cbn [disjoint_from]. unfold SET_DEPTH in *. lia.
Qed.

End Img.
