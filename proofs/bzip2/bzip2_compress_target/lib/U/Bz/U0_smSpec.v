From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib Frame.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpCutSM BzCFactsSmA BzCFactsSmB BzCFactsSd.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
Import ListNotations. Open Scope Z_scope.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition sendMTF_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (lo : Z) (sv : word),
    let usp := bv_unsigned sp in
    let eD := est_D e znew znew znew znew znew znew znew in
    a0 = Z_to_bv 64 (c_E cx) -> g_mtf g = true -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) ->
    emem cx s0segs g e m -> amem cx s0segs e m -> cimg_mem S0C m sv -> mem_inv s0segs m -> stk s0segs m lo usp -> (lo + 6528 <= usp)%Z -> (CEIL <= lo)%Z -> (usp mod 16 = 0)%Z ->
    cctx_ok cx -> cctx_sep cx -> cctx_img S0C cx ->
    zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE = zb8 (e_arr2 e) ARR2_SIZE -> bw_ok (e_bw e) -> (0 <= e_nblock e)%Z ->
    (e_nblock e + bw_numZ (e_bw eD) <= ARR2_SIZE)%Z ->
    smA_facts e -> smB_facts e znew znew znew znew znew ->
    sd_facts (est_C e znew znew znew znew znew znew) (smA_ng e) (smB_nsel e znew znew znew znew znew) ->
    evt s0segs (fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom s0segs)
        /\ munch [(c_E cx, c_E cx + ESTATE_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (usp - 6528, usp)]%Z m m' /\ wmono s0segs m m'
        /\ mem_inv s0segs m' /\ stk s0segs m' lo usp
        /\ emem cx s0segs g eD m' /\ u8arr s0segs m' (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE)
        /\ u8arr s0segs m' (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw eD)) ARR2_SIZE)
        /\ u32arr s0segs m' (c_FT cx) (zw32 (e_ftab e) FTAB_WORDS) /\ bw_ok (e_bw eD))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16f4c) fc None m (seg_rom s0segs)).

End ACeilS1.
