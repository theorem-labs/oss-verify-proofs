(* Modified by Theorem Labs, 2026-10: copied unchanged from plugin-hostd/fuzz_reply lib/CJ/RL/GXA at 568db058c1d; only the module path prefix is rewritten to this harness. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.G Require Import G_memchr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require Import RStep.
Import ListNotations.
Open Scope Z_scope.

Definition STRN_DEPTH : Z := 4384.

Section Img.
Context {IMG : RImg}.
Variable strn_ready : (word -> option byte) -> Z -> Z -> Z -> list byte -> Prop.

Definition strnlen_stack_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (a0 a1 : word) (buf : list byte)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
                  a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - STRN_DEPTH, bv_unsigned sp)] m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - STRN_DEPTH) (bv_unsigned sp)
    /\ bytes_at img_segs m' (bv_unsigned a0) buf.

Definition strnlen_stack_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  0 < bv_unsigned a0 ->
  bytes_at img_segs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) 0 (bv_unsigned a1) buf ->
  mem_inv img_segs m ->
  (bv_unsigned a0 + Z.of_nat (length buf) <= bv_unsigned sp - STRN_DEPTH \/ bv_unsigned sp <= bv_unsigned a0) ->
  stk img_segs m (bv_unsigned sp - STRN_DEPTH) (bv_unsigned sp) ->
  strn_ready m (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) buf ->
  evt img_segs (strnlen_stack_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21920)) fc None m (seg_rom img_segs)).

End Img.
