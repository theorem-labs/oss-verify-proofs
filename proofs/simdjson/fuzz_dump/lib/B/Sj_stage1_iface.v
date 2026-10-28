(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Export Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_acps.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Export Sj_akit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition A1_ENTRY : Z := 0xb338c.
Definition A1_STACK : Z := 448.
Definition A1_GTOP : Z := 0x6cd000.
Definition A1_SHB : Z := 2147450880.
Notation env_ok := (env_ok_g A1_STACK A1_GTOP).

Definition a1_res (E : s1env) (code : Z) (out : list Z) (m' : mem) : Prop :=
  exists (ws' : list word) (nxt' : word),
    rw_cells bsegs m' (e_THIS E) (parser_cells E (wz (Z.of_nat (length out))) nxt' (wz (e_BUF E)) (wz (e_len E)))
    /\ (code <> 13 -> nxt' = wz 0)
    /\ u32arr bsegs m' (e_IDX E) ws' /\ length ws' = e_cap E
    /\ firstn (length out + 3) ws' = map wz (out ++ [e_len E; e_len E; 0])
    /\ bytes_at bsegs m' (e_BUF E) (padded_bytes (e_bs E)).

Definition a1_FP (E : s1env) : list (Z * Z) :=
  [(e_THIS E, e_THIS E + 96); (e_IDX E, e_IDX E + 4 * Z.of_nat (e_cap E))].

Section Stage1CPS.
Variable RT : rt_sig.

Definition a1_live (Σ : rts RT) (E : s1env) : Prop :=
  In (e_THIS E, 96) (rt_live RT Σ) /\ In (e_IDX E, 4 * Z.of_nat (e_cap E)) (rt_live RT Σ)
  /\ (exists pb nb, In (pb, nb) (rt_live RT Σ) /\ pb mod 8 = 0 /\ pb <= e_BUF E /\ e_BUF E + e_len E + 64 <= pb + nb)
  /\ e_THIS E mod 8 = 0 /\ e_IDX E mod 8 = 0 /\ e_len E + 4 <= Z.of_nat (e_cap E).

Definition stage1_cps : Prop :=
  forall (Σ : rts RT) PMc (E : s1env) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufo leno : word) (ws0 : list word),
  fdfs_only PMc -> mat_stable PMc ->
  env_ok E -> a1_live Σ E ->
  rt_sp0 RT Σ - STACK_WIN <= e_lo E -> e_lo E + 448 + RT_STACK <= bv_unsigned (e_sp E) ->
  bv_unsigned (e_sp E) + 16 <= USTACK_TOP -> bv_unsigned (e_sp E) mod 16 = 0 ->
  ART RT Σ (e_m0 E) -> mem_inv bsegs (e_m0 E) -> stk bsegs (e_m0 E) (e_lo E) (bv_unsigned (e_sp E)) ->
  rw_cells bsegs (e_m0 E) (e_THIS E) (parser_cells E nsi nxt bufo leno) ->
  u32arr bsegs (e_m0 E) (e_IDX E) ws0 -> length ws0 = e_cap E ->
  bytes_at bsegs (e_m0 E) (e_BUF E) (padded_bytes (e_bs E)) -> frm0 (e_fc E) ->
  cps_f
    (ASTA RT Σ PMc (eq (entry_st (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E)
                          (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_len E)) (Z_to_bv 64 0) a4 a5 a6 a7
                          (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E)
                          t3 t4 t5 t6 (e_F E) (e_fc E) A1_ENTRY (e_m0 E))))
    (ASTA RT Σ PMc (fun ms => exists m',
        ret_st (e_ra E) (e_sp E) (e_gp E) (e_tp E) (e_s0 E) (e_s1 E) (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E)
               (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) (Z_to_bv 64 (fst (stage1 (e_bs E)))) m' ms
        /\ frm0 (ms_fcsr ms) /\ rt_after RT Σ (bv_unsigned (e_sp E)) (e_lo E) (e_m0 E) m'
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned (e_sp E)) (a1_FP E) (e_m0 E) m'
        /\ a1_res E (fst (stage1 (e_bs E))) (snd (stage1 (e_bs E))) m')).

End Stage1CPS.
