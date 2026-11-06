(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel ImpModel Target Prog ImpImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_stage2_iface Imp_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition imp_okarm_X (q : Z) : list (Z * Z) := [LXW_SJ; (q + 40, q + 304); (q + 392, q + 440); (q + 848, q + 936)].

Definition imp_out (m : mem) (q : Z) (ocp : option block) : Prop :=
  match ocp with
  | None => exists (b0 : byte) j23, rw_cells psegs m (q + 416) (out_short b0 j23) /\ Z.land (bv_unsigned b0) 1 = 0
  | Some b => exists L, rw_cells psegs m (q + 416) (out_long (blk_size b) L (blk_addr b)) /\ Z.land (blk_size b + 1) 1 = 1
              /\ 0 < blk_size b < 2^32 /\ rblock_range (blk_addr b) (blk_size b)
  end.
Definition ocp_blocks (ocp : option block) : list block := match ocp with Some b => [b] | None => [] end.

Definition imp_okarm_post (q : Z) (gp s0 s1 s2 s3 s4 s5 s8 s9 s10 s11 : word) (s : PState) (LBall : list block) (lo B : Z) (m : mem)
    (cpy : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F' fc' m' (errv' : word) (ocp : option block),
    ms' = MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 IMP_OKARM_END) fc' None m' (seg_rom psegs)
    /\ cpy = option_map blk_id ocp
    /\ frm0 fc' /\ mem_inv psegs m' /\ stk psegs m' lo q /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (ocp_blocks ocp ++ LBall) m' /\ lx_pres LBall q (imp_okarm_X q) m m'
    /\ sj_statics m' true
    /\ imp_out m' q ocp
    /\ (exists bs, rw_cells psegs m' (q + 40) [CB 264 bs]) /\ (exists bs, rw_cells psegs m' (q + 392) [CB 24 bs]) /\ (exists bs, rw_cells psegs m' (q + 848) [CB 88 bs]).

Definition imp_okarm_stmt : Prop :=
  forall {A} (k : option bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
         (x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall : list block) (q lo B : Z) (errv canary : word)
         (len TAPE SBUF cap : Z) (ptp psb : bptr) (j20 jgap jel jsb : list byte),
  RHEAP s LBall m -> In (ptp, TAPE, 8 * roundup64 (cap + 3)) LBall -> In (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) LBall ->
  rauxv_ok m B -> q + IMP_FRAME <= B -> B < 2^62 ->
  stk psegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - IMP_OKARM_STACK ->
  rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m -> frm0 fc -> q mod 16 = 0 -> 0 <= q ->
  lx_statics m -> sj_statics m true -> ssp_cells m canary ->
  0 <= len <= 1048512 -> cap = Z.max len 32 ->
  rw_cells psegs m (q + 24) [C8 (Z_to_bv 64 IMP_SB_VPTR); C8 (Z_to_bv 64 IMP_IOS_VPTR)] ->
  rw_cells psegs m (q + 40) [C8 (Z_to_bv 64 (q + IMP_DOC)); C8 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); CB 4 j20] ->
  rw_cells psegs m (q + 64) [CB 240 jgap] ->
  rw_cells psegs m (q + 392) [CB 24 jel] ->
  rw_cells psegs m (q + 416) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells psegs m (q + 848) [CB 88 jsb] ->
  rw_cells psegs m (q + IMP_DOC) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 (Z_to_bv 64 cap)] ->
  s2_okres TAPE SBUF (roundup64 (cap + 3)) (roundup64 (5 * (cap / 3) + 64)) (Z_to_bv 64 0) m ->
  (forall cpy s' ms', imp_okarm_post q gp s0 s1 s2 s3 (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 (IMP_VTT + 8)) (Z_to_bv 64 IMP_SBB_VPTR) s9 (Z_to_bv 64 (q + IMP_IMPLS)) s11
                         s LBall lo B m cpy s' ms' ->
                       implM psegs (k cpy) s' Q ms') ->
  implM psegs (mbind (pj_chain lops PJ_FUEL len PJ_INLINE None) (fun blk =>
               mbind (pj_chain lops PJ_FUEL len IMP_SCAP0 None) (fun sblk =>
               mbind (del_opt lops blk) (fun _ =>
               mbind (imp_copy lops len) (fun cpy =>
               mbind (del_opt lops sblk) (fun _ =>
               mbind (pj_free_nulls lops) (fun _ => k cpy))))))) s Q
    (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
             (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 (IMP_VTT + 8)) s6 s7 (Z_to_bv 64 IMP_SBB_VPTR) s9 (Z_to_bv 64 (q + IMP_IMPLS)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 IMP_OKARM) fc None m (seg_rom psegs)).

End WithCeiling0.
