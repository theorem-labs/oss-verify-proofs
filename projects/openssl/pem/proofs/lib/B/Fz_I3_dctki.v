(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Th_tsd Th_key Fz_T_local Fz_T_master1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition e_dctki : Z := 0x1f29ec.          (* [comment removed for export] *)
Definition e_dcdi : Z := 0x1f2a28.           (* [comment removed for export] *)
Definition DC_KEY : Z := 0xbd1f20.           (* [comment removed for export] *)
Definition DC_KEY_ONCE : Z := 0xbd1f40.      (* [comment removed for export] *)
Definition DC_KEY_RET : Z := 0xbd1f60.       (* [comment removed for export] *)
Definition DC_ONCE : Z := 0xbd1f80.          (* [comment removed for export] *)
Definition DC_RET : Z := 0xbd1fa0.           (* [comment removed for export] *)
Definition DC_INITED : Z := 0xbd1d60.        (* [comment removed for export] *)
Definition DC_CTX : Z := 0xbd1d80.           (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dctki_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo nk j : Z) (sh kold w r : word),
    tp = Z_to_bv 64 TP_A ->
    rw_cells bsegs m 0xbd1f20 [C4 kold] -> rw_cells bsegs m 0xbd1f60 [C4 r] ->
    ro_cells bsegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] ->
    rw_cells bsegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells bsegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells bsegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells bsegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    stk bsegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv bsegs m ->
    evt bsegs (fun ms' => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom bsegs)
                 /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (0xbd1f20, 0xbd1f20 + 4); (0xbd1f60, 0xbd1f60 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8)] m m'
                 /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ stk bsegs m' lo (bv_unsigned sp)
                 /\ rw_cells bsegs m' 0xbd1f20 [C4 (Z_to_bv 64 j)] /\ rw_cells bsegs m' 0xbd1f60 [C4 (Z_to_bv 64 1)]
                 /\ rw_cells bsegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells bsegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells bsegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 NODTOR)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_dctki) fc None m (seg_rom bsegs)).

Theorem dctki_proof : dctki_stmt.
Proof.
  unfold dctki_stmt, e_dctki. intros until r. intros -> KC RC TC NK HNK KL KJ PROBE CASE ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (0xbd1f20, 0xbd1f20 + 4); (0xbd1f60, 0xbd1f60 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 7 ths.
  ths.
  pose proof init_local_main_proof as ILM. unfold init_local_main_stmt in ILM.
  tcall (ILM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w).
  all: try first [eassumption | reflexivity | rewrite unsigned_lit by lia; lia | lia].
  clear ILM. cbv beta delta [mkR].
  do 6 ths.
  th_release FR (bv_unsigned sp).
  change (if bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) then Z_to_bv 64 NODTOR else Z_to_bv 64 0) with (Z_to_bv 64 NODTOR) in POST.
  change (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 1)) with (Z_to_bv 64 1) in *.
  ths.
  finish.
Qed.
