From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib Frame.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpCutSM CmpCutSmA BzCFactsSmA BzCFactsSd U0_cmp_sdBV U0_sd4P.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
Import ListNotations. Open Scope Z_scope.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition sdWe (cx : cctx) (usp : Z) : list (Z * Z) :=
  sdWd cx ++ [(usp + 976, usp + 992); (usp + 1024, usp + 1032)].

Definition MUe (cx : cctx) (g : eg) (e : est) (usp : Z) (m0 : word -> option byte) (b : bw) (m : word -> option byte) : Prop :=
  rw_cells s0segs m (c_E cx) (EHEAD1 cx g (est_set_bw e b)) /\
  rw_cells s0segs m (c_E cx + 640) (EHEAD2 cx g (est_set_bw e b)) /\
  u8arr s0segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) b) ARR2_SIZE) /\
  u8arr s0segs m (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) /\
  u8arr s0segs m (c_E cx + 37708) (ovb (e_len e) (jseg (c_J cx) 37708 1548) 1548) /\
  u32arr s0segs m (c_E cx + 39256) (ovw (e_code e) (jseg (c_J cx) 39256 6192) 1548) /\
  rw_cells s0segs m (usp + 1032) [C8 (Z_to_bv 64 (c_A1 cx))] /\
  mem_inv s0segs m /\
  munch (sdWe cx usp) m0 m /\ wmono s0segs m0 m.

Definition U0_sd_emit_spec : Prop :=
  forall (cx : cctx) (g : eg) (e0 : est) (c0 f0 p0 in160 h0 w0 q0 : zarr) (Q : machine_state -> Prop)
         (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP : Z) (m0 m : word -> option byte) (w976 w984 w1024 : word)
         (t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    let E := c_E cx in
    let eC := est_C e0 c0 f0 p0 h0 w0 q0 in
    let nG := smA_ng e0 in let nSel := smB_nsel e0 c0 f0 h0 w0 q0 in
    let BE := smD_b4 e0 c0 f0 p0 in160 h0 w0 q0 in let r := smD_bd e0 c0 f0 p0 in160 h0 w0 q0 in
    cctx_ok cx -> cctx_sep cx -> g_mtf g = true -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e0) ->
    0 <= e_nblock e0 -> CEIL <= SP -> SP + 1200 <= 2^64 ->
    sd_facts eC nG nSel -> bw_ok BE -> e_nblock e0 + bw_numZ (fst r) <= ARR2_SIZE ->
    MUd cx g eC SP m0 BE m ->
    u8arr s0segs m (E + 1704) (ovb (e_selector eC) (jseg (c_J cx) 1704 18002) 18002) ->
    rw_cells s0segs m (SP + 816) [C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (18446744073709551615 - (E + 1704)))] ->
    rw_cells s0segs m (SP + 904) [C8 (Z_to_bv 64 (flag6 nG))] ->
    rw_cells s0segs m (SP + 928) [C8 (Z_to_bv 64 nG)] ->
    rw_cells s0segs m (SP + 944) [C8 (Z_to_bv 64 nSel)] ->
    rw_cells s0segs m (SP + 960) [C8 (Z_to_bv 64 (E + 37708))] ->
    rw_cells s0segs m (SP + 992)
      [C8 (Z_to_bv 64 (18446744073709551615 - (E + 39256))); C8 (Z_to_bv 64 (E + 39256)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1)] ->
    rw_cells s0segs m (SP + 976) [C8 w976; C8 w984] -> rw_cells s0segs m (SP + 1024) [C8 w1024] ->
    (forall (m' : word -> option byte) (v976 v984 v1024 : word)
            (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word),
       MUe cx g eC SP m0 (fst r) m' ->
       rw_cells s0segs m' (SP + 976) [C8 v976; C8 v984] -> rw_cells s0segs m' (SP + 1024) [C8 v1024] ->
       bw_ok (fst r) ->
       evt s0segs Q (MS (mkR ra' (Z_to_bv 64 SP) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                             s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                         F (Z_to_bv 64 131736) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (18446744073709551615 - (E + 39256))) (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 E) s1
                          a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (18446744073709551615 - (E + 37708))) s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 115096) fc None m (seg_rom s0segs)).

Definition sm_post_ok : Prop :=
  forall (cx : cctx) (g : eg) (e : est) (lo usp : Z) (sv : word) (m m1 m2 m3 m0' : word -> option byte)
         (J0 Jm J3 Jx J44 Jf : list byte) (w16 w896 w912 w936 w1024 : word) (H' : sdw) (i16' : list byte) (v976 v984 v1024 : word)
         (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra : word),
    let SP := usp - 1200 in let E := c_E cx in
    let nG := smA_ng e in let A := sm_alpha e in let nMTF := sm_nmtf e in
    let nSel := smB_nsel e znew znew znew znew znew in
    let eB := est_B e znew znew znew znew znew in
    let eC := est_C e znew znew znew znew znew znew in
    let eD := est_D e znew znew znew znew znew znew znew in
    let BE := smD_b4 e znew znew znew znew znew znew znew in
    let r := smD_bd e znew znew znew znew znew znew znew in
    g_mtf g = true -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) ->
    emem cx s0segs g e m -> amem cx s0segs e m -> cimg_mem S0C m sv -> mem_inv s0segs m -> stk s0segs m lo usp ->
    lo + 6528 <= usp -> CEIL <= lo -> usp mod 16 = 0 ->
    cctx_ok cx -> cctx_sep cx -> cctx_img S0C cx ->
    bw_ok (e_bw e) -> 0 <= e_nblock e -> e_nblock e + bw_numZ (e_bw eD) <= ARR2_SIZE ->
    smA_facts e -> sd_facts eC nG nSel ->
    emem cx s0segs g eB m1 -> amem cx s0segs e m1 -> cimg_mem S0C m1 sv -> mem_inv s0segs m1 -> stk s0segs m1 lo usp ->
    munch [(E, E + ESTATE_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (usp - 6528, usp)] m m1 -> wmono s0segs m m1 ->
    length J0 = 16%nat -> length Jm = 792%nat -> length J3 = 56%nat -> length Jx = 4%nat -> length J44 = 16%nat -> length Jf = 36%nat ->
    u8arr s0segs m1 SP J0 ->
    rw_cells s0segs m1 (SP + 16) [C8 w16] ->
    u8arr s0segs m1 (SP + 24) Jm ->
    rw_cells s0segs m1 (SP + 816) [C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (18446744073709551615 - (E + 1704)))] ->
    u8arr s0segs m1 (SP + 832) J3 ->
    rw_cells s0segs m1 (SP + 888)
      [C8 (Z_to_bv 64 (1032 * nG)); C8 w896; C8 (Z_to_bv 64 (flag6 nG)); C8 w912; C8 (Z_to_bv 64 nMTF); C8 (Z_to_bv 64 nG); C8 w936;
       C8 (Z_to_bv 64 (18446744073709551615 - (E + 45448))); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 A);
       C8 (Z_to_bv 64 nSel); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (E + 51640));
       C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1); C8 w1024; C8 (Z_to_bv 64 (c_A1 cx))] ->
    u8arr s0segs m1 (SP + 1040) Jx -> u8arr s0segs m1 (SP + 1044) J44 -> u8arr s0segs m1 (SP + 1060) Jf ->
    rw_cells s0segs m1 (SP + 1096) [C8 x11; C8 x10; C8 x9; C8 x8; C8 x7; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra] ->
    MA3 cx g eC nG SP m0' H' i16' BE m2 -> sd_ro cx eC m2 -> stk s0segs m2 lo SP ->
    munch ([(E + 19706, E + 37708); (E + 39256, E + 45448); (SP + 888, SP + 1040); (SP + 1044, SP + 1060); (SP - 16, SP)] ++ sdWP cx SP) m1 m2 ->
    wmono s0segs m1 m2 -> Z.of_nat (length i16') = 16 -> bw_ok BE ->
    MUe cx g eC SP m2 (fst r) m3 ->
    rw_cells s0segs m3 (SP + 976) [C8 v976; C8 v984] -> rw_cells s0segs m3 (SP + 1024) [C8 v1024] -> bw_ok (fst r) ->
    munch [(E, E + ESTATE_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (usp - 6528, usp)] m m3 /\ wmono s0segs m m3 /\
    mem_inv s0segs m3 /\ stk s0segs m3 lo usp /\
    emem cx s0segs g eD m3 /\ u8arr s0segs m3 (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) /\
    u8arr s0segs m3 (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw eD)) ARR2_SIZE) /\
    u32arr s0segs m3 (c_FT cx) (zw32 (e_ftab e) FTAB_WORDS) /\ bw_ok (e_bw eD) /\
    rw_cells s0segs m3 (SP + 1096) [C8 x11; C8 x10; C8 x9; C8 x8; C8 x7; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra].

End ACeilS1.
