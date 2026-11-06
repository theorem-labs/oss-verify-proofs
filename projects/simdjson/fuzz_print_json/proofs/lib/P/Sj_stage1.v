(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require F_memcpy.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage1_defs Sj_stage1_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma memcpy_stmt_holds : memcpy_stmt.
Proof. unfold memcpy_stmt, memcpy_stmt_g. intros. apply F_memcpy.memcpy_spec with (junk := junk); assumption. Qed.

Theorem stage1_spec : forall (E : s1env), env_ok E ->
  forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (nsi nxt bufo leno : word) (ws0 : list word),
    mem_inv psegs (e_m0 E) ->
    stk psegs (e_m0 E) (e_lo E) (bv_unsigned (e_sp E)) ->
    rw_cells psegs (e_m0 E) (e_THIS E) (parser_cells E nsi nxt bufo leno) ->
    u32arr psegs (e_m0 E) (e_IDX E) ws0 -> length ws0 = e_cap E ->
    bytes_at psegs (e_m0 E) (e_BUF E) (padded_bytes (e_bs E)) ->
    evt psegs (s1_post E (fst (stage1 (e_bs E))) (snd (stage1 (e_bs E))))
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E)
               (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_len E)) (Z_to_bv 64 0) a4 a5 a6 a7
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
          (e_F E) (Z_to_bv 64 S1_ENTRY) (e_fc E) None (e_m0 E) (seg_rom psegs)).
Proof. intros E OK. exact (s1_stage1_spec memcpy_stmt_holds E OK). Qed.

Corollary stage1_success_S1OUT : forall bs, fst (stage1 bs) = 0%Z -> S1OUT bs (snd (stage1 bs)).
Proof. intros bs H. apply stage1_S1OUT. rewrite <- H. apply surjective_pairing. Qed.
