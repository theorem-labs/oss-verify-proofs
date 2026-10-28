(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_pid1A Atp_pidiA Pj_defsA Pj_hdefsA Imp_hdefsA Imp_ios_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section HStmts.
Variable RT : rt_sig.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section WithPM.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition imp_okarm_WA (E : pjenvA) : list (Z * Z) :=
  [(pa_F E + 32, pa_F E + 120); (pa_F E + 248, pa_F E + 296); (pa_F E + 832, pa_F E + 1096); (pa_F E + 1168, pa_F E + 1192);
   (shad (pa_F E) + 4, shad (pa_F E) + 15); (shad (pa_F E) + 104, shad (pa_F E) + 137); (shad (pa_F E) + 146, shad (pa_F E) + 149);
   (PJ_LOC_LO_A, PJ_LOC_HI_A)].

Definition imp_okarm_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (E : pjenvA) (S1 usp szw dw : Z)
         (ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : mem)
         (j20 jsb jel jos jtmp : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  pjenvA_ok E -> pa_kF E = 5%nat -> pa_SB E = pa_F E + 32 -> pa_DOC E = pa_F E + 192 ->
  pa_live RT Σ E (sbA0 (pa_SB E)) -> DOCREPA E m -> LOCBA m -> locx3 m -> libc_nl m -> lockwA m -> io_ssp m ->

  rw_cells bsegs m (S1 + 192) [C8 (wz (pa_F E + 192)); C8 (wz 1); C4 (wz 0); CB 4 j20] ->
  rw_cells bsegs m (S1 + 64) (imp_locals (pa_F E) szw dw) -> 0 <= szw < 2^64 -> 0 <= dw < 2^64 ->

  rw_cells bsegs m (pa_SB E) [CB 88 jsb] ->
  rw_cells bsegs m (pa_F E + 248) [CB 24 jel] ->
  rw_cells bsegs m (pa_F E + 272) [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  rw_cells bsegs m (pa_F E + 832) [CB 264 jos] ->
  rw_cells bsegs m (pa_F E + 1168) [CB 24 jtmp] ->
  rw_cells bsegs m (shad (pa_F E)) (map C1 imp_sh_pro) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (pa_lo E) S1 -> pa_lo E + IMP_OKARM_STACK_A <= S1 -> S1 + 320 + 16 <= USTACK_TOP -> S1 mod 32 = 0 ->
  S1 + 320 <= usp <= S1 + 336 -> frm0 fc ->
  rt_frames RT Σ = [(pa_F E, 5%nat)] -> Z.of_nat (length (pa_L E)) + IMP_OKARM_LIVE_A <= LIVE_MAX -> imp_okarm_costA (pa_n E) <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (ocp : option (Z * Z)) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' s7' s11' t3' t4' t5' t6' Fr' fc' m',
     frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (pa_lo E) S1 ->
     rt_live RT Σ' = ocp_chunks ocp ++ rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - imp_okarm_costA (pa_n E) <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) S1 (imp_okarm_WA E) m m' -> LOCBA m' -> locx3 m' ->
     imp_outA m' (pa_F E) ocp ->
     (exists jsb' jel' jos' jtmp', rw_cells bsegs m' (pa_SB E) [CB 88 jsb'] /\ rw_cells bsegs m' (pa_F E + 248) [CB 24 jel']
                                /\ rw_cells bsegs m' (pa_F E + 832) [CB 264 jos'] /\ rw_cells bsegs m' (pa_F E + 1168) [CB 24 jtmp']) ->
     rw_cells bsegs m' (shad (pa_F E)) (map C1 imp_sh_pro) ->
     aevt Σ' K (imp_regsA IMP_OKARM_END_A ra' S1 gp t0' t1' t2' usp a0' a1' a2' a3' a4' a5' a6' a7' (pa_F E) s2' s4' s6 s7' s8 s9 s10 s11' t3' t4' t5' t6' Fr' fc' m')) ->
  aevt Σ K (imp_regsA IMP_OKARM_A ra S1 gp t0 t1 t2 usp (wz 0) a1 a2 a3 a4 a5 a6 a7 (pa_F E) s2 s4 s6 (wz (pa_F E + 160)) s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m).

End WithPM.
End HStmts.
