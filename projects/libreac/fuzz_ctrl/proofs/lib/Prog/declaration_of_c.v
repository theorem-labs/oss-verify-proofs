From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcDecl.
Import ListNotations.
Open Scope Z_scope.

Definition DECLARATION_OF : Z := 0x13e1c.
Definition DECLARATION_OF_FRAME : Z := 64.
Definition BOX_CATALOGUE : Z := 0x1ed30.

Definition declaration_of_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (lo : Z) (row ob : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if decl_ok row then 1 else 0)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - DECLARATION_OF_FRAME, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 32)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' (bv_unsigned a1) [CB 32 (if decl_ok row then decl row else ob)] /\
    bytes_at rsegs m' (bv_unsigned a0) row.

Definition declaration_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (row ob : list byte),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DECLARATION_OF_FRAME <= bv_unsigned sp ->
    bv_unsigned a0 mod 8 = 0 ->
    length row = 296%nat ->
    bytes_at rsegs m (bv_unsigned a0) row ->
    rw_cells rsegs m (bv_unsigned a1) [CB 32 ob] ->
    bv_unsigned a1 + 32 <= bv_unsigned a0 \/ bv_unsigned a0 + 296 <= bv_unsigned a1 ->
    bv_unsigned a0 + 296 <= bv_unsigned sp - DECLARATION_OF_FRAME \/ bv_unsigned sp <= bv_unsigned a0 ->
    bv_unsigned a1 + 32 <= bv_unsigned sp - DECLARATION_OF_FRAME \/ bv_unsigned sp <= bv_unsigned a1 ->
    mem_inv rsegs m ->
    evt rsegs (declaration_of_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m lo row ob)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DECLARATION_OF) fc None m (seg_rom rsegs)).

Definition declaration_of_rows : Prop :=
  forall i, (i < 11)%nat -> exists row,
    image_bytes rsegs (BOX_CATALOGUE + 296 * Z.of_nat i) 296 = Some row /\
    decl_ok row = true /\ map bv_unsigned (decl row) = nth i decl_table [].
