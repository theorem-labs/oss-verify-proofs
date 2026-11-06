From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition NEXT_LINE : Z := 0x14958.
Definition NEXT_LINE_FRAME : Z := 48.
Definition G_NOUT : Z := 0x31000.
Definition G_OUT : Z := 0x31010.

Definition first_line (ob : list byte) (A : Z) (ln : list byte) : Prop :=
  exists rest, skipn (Z.to_nat A) ob = ln ++ Z_to_bv 8 0 :: rest /\ ~ In (Z_to_bv 8 0) ln.

Definition next_line_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo PA PL PN : Z)
         (at0 nout out : word) (jl jn ob : list byte),
    let A := bv_unsigned at0 in
    let O := bv_unsigned nout in
    let W := [(bv_unsigned sp - NEXT_LINE_FRAME, bv_unsigned sp); (PA, PA + 8); (PL, PL + 8); (PN, PN + 8)] in
    stk rsegs m lo (bv_unsigned sp) -> lo + NEXT_LINE_FRAME <= bv_unsigned sp ->
    mem_inv rsegs m ->
    rw_cells rsegs m PA [C8 at0] -> rw_cells rsegs m PL [CB 8 jl] -> rw_cells rsegs m PN [CB 8 jn] ->
    PA mod 8 = 0 -> PL mod 8 = 0 -> PN mod 8 = 0 ->
    disjoint_from [(bv_unsigned sp - NEXT_LINE_FRAME, bv_unsigned sp); (PL, PL + 8); (PN, PN + 8)] PA 8 ->
    disjoint_from [(bv_unsigned sp - NEXT_LINE_FRAME, bv_unsigned sp); (PN, PN + 8)] PL 8 ->
    disjoint_from [(bv_unsigned sp - NEXT_LINE_FRAME, bv_unsigned sp)] PN 8 ->
    bytes_at rsegs m G_NOUT (le8 nout) -> disjoint_from W G_NOUT 8 ->
    bytes_at rsegs m G_OUT (le8 out) -> disjoint_from W G_OUT 8 ->
    bytes_at rsegs m (bv_unsigned out) ob -> Z.of_nat (length ob) = O -> disjoint_from W (bv_unsigned out) O ->
    A <= O ->
    (A < O -> 0 < bv_unsigned out /\ In (Z_to_bv 8 0) (skipn (Z.to_nat A) ob)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' G_NOUT (le8 nout) /\ bytes_at rsegs m' G_OUT (le8 out) /\
         bytes_at rsegs m' (bv_unsigned out) ob /\
         ((A = O /\ a0' = Z_to_bv 64 0 /\
           rw_cells rsegs m' PA [C8 at0] /\ rw_cells rsegs m' PL [CB 8 jl] /\ rw_cells rsegs m' PN [CB 8 jn]) \/
          (exists ln, A < O /\ first_line ob A ln /\ a0' = Z_to_bv 64 1 /\
           rw_cells rsegs m' PA [C8 (Z_to_bv 64 (A + Z.of_nat (length ln) + 1))] /\
           rw_cells rsegs m' PL [C8 (Z_to_bv 64 (bv_unsigned out + A))] /\
           rw_cells rsegs m' PN [C8 (Z_to_bv 64 (Z.of_nat (length ln)))])))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PA) (Z_to_bv 64 PL) (Z_to_bv 64 PN) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NEXT_LINE) fc None m (seg_rom rsegs)).
