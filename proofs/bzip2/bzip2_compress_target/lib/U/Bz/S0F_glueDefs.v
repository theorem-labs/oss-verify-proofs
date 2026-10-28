(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface AllocCover AllocDcv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0B2BDStmt.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueAlloc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut S0_glueDefs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOKp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.

(* [comment removed for export] *)
Definition S0DI : B2BDImg := BDI 0x15f2c 0x33178 0x335b0 0x320e8 0x32098.

(* [comment removed for export] *)

Section Dec10F.
  Context (AI : AllocIface s0segs S0_layout) (AC : AllocCover s0segs S0_layout AI).
  Let L := S0_layout.

  Definition dec10F_spec : Prop :=
    forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp sv g1 errv x9 x24 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : word -> option byte) (MD : Model) (s : ai_AS AI) (LB : list ablock) (pS pD : bid) (k : nat)
           (S uspb src len dst dn small lo B : Z)
           (h0 : dsh) (nbu0 : Z) (cf0 : list word) (d0 : dsm) (r0 : drest) (js : list byte) (b0 : bzs) (payload : list byte)
           (K : TSet),
      ctx_ok (cx10 S uspb src len dst dn small) ->
      tp = Z_to_bv 64 (al_tp L) ->
      (* [comment removed for export] *)
      rw_cells s0segs m S (HEAD_CELLS h0) -> hwf10 h0 uspb small ->
      rw_cells s0segs m (S + 1092) [C4 (Z_to_bv 64 nbu0)] -> 0 <= nbu0 < 2 ^ 32 ->
      u32arr s0segs m (S + 1096) cf0 -> length cf0 = 257%nat ->
      rw_cells s0segs m (S + 3152) (MID_CELLS d0) -> sm_tt d0 = 0 -> sm_ll16 d0 = 0 -> sm_ll4 d0 = 0 -> 0 <= sm_nInUse d0 < 2 ^ 32 ->
      sm_cccrc d0 = Z_to_bv 64 0 ->
      drest_at s0segs m S r0 ->
      rw_cells s0segs m (S + 64036) [CB 108 js] ->
      (* [comment removed for export] *)
      rw_cells s0segs m uspb (STRM_CELLS b0) -> bzs_wf b0 ->
      bs_S b0 = S -> bs_src b0 = src -> bs_len b0 = len -> bs_dst b0 = dst -> bs_dlen b0 = dn ->
      bs_bzalloc b0 = Z_to_bv 64 0x13e24 -> bs_opaque b0 = Z_to_bv 64 0 -> bs_ai b0 = bs_len b0 -> bs_av b0 = bs_dlen b0 ->
      bs_til b0 = Z_to_bv 64 0 ->
      bytes_at s0segs m src payload -> Z.of_nat (length payload) = len -> client_range L LB (uspb + 128) src len ->
      rw_cells s0segs m 0x320e8 [C8 (Z_to_bv 64 0x32098); C8 g1; C8 (Z_to_bv 64 0x320a0); C8 (Z_to_bv 64 0x33178); C8 (Z_to_bv 64 0x335b0)] ->
      rw_cells s0segs m 0x32098 [C8 sv] -> u32arr s0segs m 0x335b0 rnums_words ->
      (* [comment removed for export] *)
      stk s0segs m lo (uspb + -112) -> alloc_ceiling <= lo -> lo <= uspb - 8640 -> mem_inv s0segs m ->
      ai_inv AI s LB m MD -> ac_vm AC (2 + k)%nat s MD -> In (pS, S, 64144) LB -> In (pD, dst, dn) LB -> ai_aux AI m B -> uspb + 128 <= B ->
      rw_cells s0segs m (errno_cell L) [C4 errv] ->
      (* [comment removed for export] *)
      (forall (m' : word -> option byte) (MD' : Model) (s' : ai_AS AI) (c : bcfg) (n : Z) (rc : Z) (errv' : word)
              (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          let cx' := cxN S uspb src len dst dn small n (cfg_tt c) (cfg_l16 c) (cfg_l4 c) in
          ai_inv AI s' (cfg_extra c ++ LB) m' MD' -> vm_only MD MD' -> ac_vm AC k s' MD' -> ai_aux AI m' B ->
          rw_cells s0segs m' (errno_cell L) [C4 errv'] -> mem_inv s0segs m' -> stk s0segs m' lo (uspb + -112) ->
          ctx_ok cx' -> cfg_sizes_ok c n -> cfg_shape_ok c small n -> 0 <= n <= 9 ->
          rw_cells s0segs m' 0x320e8 [C8 (Z_to_bv 64 0x32098); C8 g1; C8 (Z_to_bv 64 0x320a0); C8 (Z_to_bv 64 0x33178); C8 (Z_to_bv 64 0x335b0)] ->
          rw_cells s0segs m' 0x32098 [C8 sv] -> u32arr s0segs m' 0x335b0 rnums_words ->
          pres10 LB S uspb m m' ->
          ( (* [comment removed for export] *)
            (exists (junkD : BzDState.dst) (J' : jk),
               let '(rv, d1, s1) := decompress (dst_init junkD 0 small) (dstrm_init (map bv_unsigned payload) dn) in
               rc = rv /\
               dmem DI_S0 cx' g1 sv payload m' (dvF cx' J' d1 s1) /\
               dpureF cx' b0 payload J' d1 s1 /\   (* [comment removed for export] *)
               dpost14W (rv, d1, s1))
            \/
            (* [comment removed for export] *)
            ((rc = BZ_MEM_ERROR \/
              (* [comment removed for export] *)
              exists junkD : BzDState.dst,
                let '(rv, d1, s1) := decompress (dst_init junkD 0 small) (dstrm_init (map bv_unsigned payload) dn) in
                rc = rv /\ (rv = BZ_OK \/ rv = BZ_DATA_ERROR_MAGIC) /\ 10 <= d_state d1 <= 13 /\
                s_out s1 = [] /\ s_avail_out s1 = dn) /\
             exists (h : dsh) (d : dsm) (ai : Z) (til tih : word),
               rw_cells s0segs m' S (HEAD_CELLS h) /\ sh_strm h = uspb /\ 0 <= sh_state h < 2 ^ 31 /\ sh_state h <> BZ_X_OUTPUT /\
               rw_cells s0segs m' (S + 3152) (MID_CELLS d) /\ sm_tt d = cfg_tt c /\ sm_ll16 d = cfg_l16 c /\ sm_ll4 d = cfg_l4 c /\
               rw_cells s0segs m' uspb (STRM_CELLS (bupd b0 ai til tih)) /\ 0 <= ai <= bs_ai b0) ) ->
          realizes s0segs
            (mkCfg (MS (mkR (Z_to_bv 64 0x1481c) (Z_to_bv 64 (uspb + -112)) gp tp t0' t1' t2' (Z_to_bv 64 S) x9
                            (Z_to_bv 64 rc) a1' a2' a3' a4' a5' a6' a7'
                            (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1))
                            x24 (Z_to_bv 64 100000) (Z_to_bv 64 (S + 64080)) (Z_to_bv 64 10) t3' t4' t5' t6')
                       F (Z_to_bv 64 0x1481c) fc None m' (seg_rom s0segs)) MD') K) ->
      realizes s0segs
        (mkCfg (MS (mkR (Z_to_bv 64 0x1481c) (Z_to_bv 64 (uspb + -112)) gp tp t0 t1 t2 (Z_to_bv 64 S) x9
                        (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1))
                        x24 (Z_to_bv 64 100000) (Z_to_bv 64 (S + 64080)) (Z_to_bv 64 10) t3 t4 t5 t6)
                   F (Z_to_bv 64 0x2462c) fc None m (seg_rom s0segs)) MD) K.
End Dec10F.
End ACeilS1.
