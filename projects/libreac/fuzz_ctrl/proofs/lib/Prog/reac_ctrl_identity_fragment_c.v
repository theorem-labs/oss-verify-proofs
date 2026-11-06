From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_IDENTITY_FRAGMENT : Z := 0x14a3c.
Definition REAC_CTRL_IDENTITY_FRAGMENT_FRAME : Z := 80.

Definition fg_mem (f pa pp pn : Z) (st g : list byte) (c : fg_case) (m' : word -> option byte) : Prop :=
  match c with
  | FgRefuse | FgNone => True
  | FgFirst => bytes_at rsegs m' f (fg_first st g)
  | FgDrop => bytes_at rsegs m' f (fg_clear st)
  | FgJoin => bytes_at rsegs m' f (fg_clear (fg_join st g))
  | FgClose =>
      bytes_at rsegs m' f (fg_clear (fg_join st g)) /\
      bytes_at rsegs m' pa (le2 (Z_to_bv 64 (fg_addr st g))) /\
      bytes_at rsegs m' pp (le8 (Z_to_bv 64 (f + 19))) /\
      bytes_at rsegs m' pn (le8 (Z_to_bv 64 (fg_T st g - 13)))
  end.

Definition reac_ctrl_identity_fragment_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f fr len pa pp pn : Z) (st g : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 fr -> a2 = Z_to_bv 64 len ->
    a3 = Z_to_bv 64 pa -> a4 = Z_to_bv 64 pp -> a5 = Z_to_bv 64 pn ->
    0 <= f < 2^64 -> 0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_FRAME) (bv_unsigned sp) ->
    length g = 50%nat -> length st = 72%nat ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m fr g) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (fr, fr + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_FRAME, bv_unsigned sp)]) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret (fg_class f fr pa pp pn len st g)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_FRAME f pa pp pn (bv_unsigned sp) (fg_class f fr pa pp pn len st g))
           m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_FRAME) (bv_unsigned sp) /\
         fg_mem f pa pp pn st g (fg_class f fr pa pp pn len st g) m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_FRAGMENT) fc None m (seg_rom rsegs)).
