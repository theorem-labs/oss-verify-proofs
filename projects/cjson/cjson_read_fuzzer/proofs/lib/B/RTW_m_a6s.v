(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface RT_art RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a6.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.
Set Printing Depth 100.

(* [comment removed for export] *)
Lemma alloc_a6s_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (n ub lo : Z) (sj0 sj1 sj2 sj3 : word) (j0 : list byte) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  leafc st m -> RTWF st -> mem_inv bsegs m -> fill_cells m -> tp = wz ATP ->
  s1 = wz (usz n) -> s3 = wz (needed n) -> s4 = wz ub ->
  0 <= n < 2^32 -> bprim n = false ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
  rw_cells bsegs m (st_t st + 2800) [C8 sj0; C8 sj1; C8 sj2] ->
  rw_cells bsegs m (st_t st + 2904) [C8 sj3] ->
  evt bsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (sj0' sj1' sj2' sj3' : word) (m' : word -> option byte),
      ms' = MS (mkR (wz 0x32600) sp gp tp t0' t1' t2' s0 s1 (wz ub) (wz MALLOC_FILL_BYTE) (wz (Z.min (usz n) MALLOC_FILL_MAX)) a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz A_MUSL_MEMSET) fc None m' (seg_rom bsegs)
      /\ munch [(st_t st + 2800, st_t st + 2824); (st_t st + 2904, st_t st + 2912); (bv_unsigned sp - 32, bv_unsigned sp)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11)
      /\ rw_cells bsegs m' (st_t st + 2800) [C8 sj0'; C8 sj1'; C8 sj2']
      /\ rw_cells bsegs m' (st_t st + 2904) [C8 sj3'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x3246c) fc None m (seg_rom bsegs)).
Proof.
  intros until v11. intros LC WF MI FC TP -> -> -> Hn HP ST HCL LO SPH FR TS TL.
  pose proof (munch_refl [(st_t st + 2800, st_t st + 2824); (st_t st + 2904, st_t st + 2912); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (sec_facts n HP) as (F1 & F2 & F3 & F4 & F5 & F6). pose proof (usz_le_rounded8 n) as (V1 & V2 & V3). pose proof (rounded8_range n Hn) as R8.
  pose proof (t_range st WF) as TR.
  unfold usz, KHIGHMEM_BEG, AIMG_HI, MALLOC_FILL_BYTE, MALLOC_FILL_MAX, A_MUSL_MEMSET in *. idtac. rewrite F6 in *.
  unfold alloc_frame in FR. leaf_prep. subst tp.
  lstep. (* [comment removed for export] *)
  call get_thread_stats_c; [exact LC| exact WF| exact MI| reflexivity| exact ST| idtac; lia| lia|].
  cbv beta delta [wz] in *. subst x2. rename PC into ST. unfold T_STATS.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. fl. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) lstep; if_lia. (* [comment removed for export] *)
  match goal with H : mem_inv _ _ |- _ => rename H into MI end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (FC1 : fill_cells mx) end.
  { eapply fill_cells_out; [exact MU| | exact FC]. pose proof (t_range st WF) as TRq. olin TRq. pose proof alloc_ceiling_range as ACRq.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_LO, AIMG_HI, CEIL in *; lia. }
  destruct FC1 as (K1' & K2' & K3' & K4' & K5'). unfold MALLOC_FILL_BYTE, A_MUSL_MEMSET in K3', K5'.
  lstep. lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. lstep. fl. lstep. lstep. (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 634228)) with (Z_to_bv 64 634228) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite (Z.min_r (n `max` 1) 4096) by lia.
  finish; eassumption.
Qed.


End CeilWrap.
