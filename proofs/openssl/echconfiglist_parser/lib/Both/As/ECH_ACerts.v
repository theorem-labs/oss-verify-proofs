(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_ARep ECH_ALib ECH_Iface
     ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C7 ECH_AStmt_C9 ECH_AStmt_C11 ECH_AStmt_C14 ECH_AStmt_C15
     ECH_AC3 ECH_AC4 ECH_AC4_raise ECH_AC7 ECH_AC9 ECH_AC11 ECH_AC15_parse ECH_AC15_top
     AsIfaceMemalign AInstFacts.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require CertA_asan CertO3_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  (* [comment removed for export] *)
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).
  (* [comment removed for export] *)
  Hypothesis CERTA : asan_rt_hyps_x H -> getdefctx_fresh_stmt H.
  Hypothesis CERTO3 : asan_rt_hyps_x H -> egs_fresh_stmt H.

  Theorem C3_spec_x : asan_rt_hyps_x H -> C3_stmts H.
  Proof. intros HX. exact (AC3_spec H HX (CERTA HX)). Qed.

  Theorem C4_spec_x : asan_rt_hyps_x H -> C4_stmts H.
  Proof. intros HX. exact (AC4_spec H HX (CERTO3 HX)). Qed.

  Lemma egs_spec_x : asan_rt_hyps_x H -> egs_stmt H.
  Proof. intros HX. pose proof (C4_spec_x HX) as K. unfold C4_stmts in K. exact (proj1 (proj2 K)). Qed.

  Lemma errclear_spec_x : asan_rt_hyps_x H -> errclear_stmt H.
  Proof. intros HX. pose proof (C4_spec_x HX) as K. unfold C4_stmts in K. exact (proj2 (proj2 (proj2 (proj2 (proj2 K))))). Qed.

  Theorem araise_spec_x : asan_rt_hyps_x H -> araise_stmt H.
  Proof. intros HX. exact (araise_spec H HX (egs_spec_x HX)). Qed.

  Theorem C11_spec_x : asan_rt_hyps_x H -> C11_stmts H.
  Proof. intros HX. exact (AC11_spec H (proj1 HX) (araise_spec_x HX)). Qed.

  Lemma cnewex_spec_x : asan_rt_hyps_x H -> cnewex_stmt H.
  Proof. intros HX. pose proof (C3_spec_x HX) as K. unfold C3_stmts in K. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 K))))))). Qed.

  Lemma cfreeex_spec_x : asan_rt_hyps_x H -> cfreeex_stmt H.
  Proof. intros HX. pose proof (C3_spec_x HX) as K. unfold C3_stmts in K. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 K))))))). Qed.

  Theorem C7_spec_x : asan_rt_hyps_x H -> C7_stmts H.
  Proof. intros HX. exact (AC7_spec H HX (cnewex_spec_x HX) (cfreeex_spec_x HX)). Qed.

  Theorem C9_spec_x : asan_rt_hyps_x H -> C9_stmts H.
  Proof. intros HX. exact (AC9_spec H HX (cnewex_spec_x HX) (cfreeex_spec_x HX)). Qed.

  Theorem parse_one_spec_x : asan_rt_hyps_x H -> readcfg_stmt H PF9new PF9free -> parse_one_stmt H PF9new PF9free.
  Proof. intros HX RC. exact (parse_one_spec H HX (cnewex_spec_x HX) (cfreeex_spec_x HX) PF9new PF9free RC). Qed.

  (* [comment removed for export] *)
  Theorem fuzz_spec_x : asan_rt_hyps_x H -> readcfg_stmt H PF9new PF9free -> (atr_ok H -> fuzz_closed_ok H PF9new PF9free) -> fuzz_stmt H ECHL.
  Proof. intros HX RC HFC. exact (fuzz_spec H HX (cnewex_spec_x HX) (cfreeex_spec_x HX) (errclear_spec_x HX) PF9new PF9free RC HFC). Qed.
End W.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section I.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).

  (* [comment removed for export] *)
  Lemma certA_i : ainst_facts H -> asan_rt_hyps_x H -> getdefctx_fresh_stmt H.
  Proof. intros AIF HX. exact (CertA_asan.getdefctx_fresh_cert H HX (ainst_mal_lit H AIF)). Qed.

  Lemma certO3_i : ainst_facts H -> asan_rt_hyps_x H -> egs_fresh_stmt H.
  Proof. intros AIF HX. exact (CertO3_asan.egs_fresh_cert H HX (ainst_mal_lit H AIF)). Qed.

  Theorem C3_spec_i : asan_rt_hyps_x H -> ainst_facts H -> C3_stmts H.
  Proof. intros HX AIF. exact (C3_spec_x H (certA_i AIF) HX). Qed.

  Theorem C4_spec_i : asan_rt_hyps_x H -> ainst_facts H -> C4_stmts H.
  Proof. intros HX AIF. exact (C4_spec_x H (certO3_i AIF) HX). Qed.

  Lemma egs_spec_i : asan_rt_hyps_x H -> ainst_facts H -> egs_stmt H.
  Proof. intros HX AIF. exact (egs_spec_x H (certO3_i AIF) HX). Qed.

  Lemma errclear_spec_i : asan_rt_hyps_x H -> ainst_facts H -> errclear_stmt H.
  Proof. intros HX AIF. exact (errclear_spec_x H (certO3_i AIF) HX). Qed.

  Theorem araise_spec_i : asan_rt_hyps_x H -> ainst_facts H -> araise_stmt H.
  Proof. intros HX AIF. exact (araise_spec_x H (certO3_i AIF) HX). Qed.

  Theorem C11_spec_i : asan_rt_hyps_x H -> ainst_facts H -> C11_stmts H.
  Proof. intros HX AIF. exact (C11_spec_x H (certO3_i AIF) HX). Qed.

  Lemma cnewex_spec_i : asan_rt_hyps_x H -> ainst_facts H -> cnewex_stmt H.
  Proof. intros HX AIF. exact (cnewex_spec_x H (certA_i AIF) HX). Qed.

  Lemma cfreeex_spec_i : asan_rt_hyps_x H -> ainst_facts H -> cfreeex_stmt H.
  Proof. intros HX AIF. exact (cfreeex_spec_x H (certA_i AIF) HX). Qed.

  Theorem C7_spec_i : asan_rt_hyps_x H -> ainst_facts H -> C7_stmts H.
  Proof. intros HX AIF. exact (C7_spec_x H (certA_i AIF) HX). Qed.

  Theorem C9_spec_i : asan_rt_hyps_x H -> ainst_facts H -> C9_stmts H.
  Proof. intros HX AIF. exact (C9_spec_x H (certA_i AIF) HX). Qed.

  (* [comment removed for export] *)
  Lemma newmembuf_spec_i : asan_rt_hyps_x H -> ainst_facts H -> newmembuf_stmt H.
  Proof.
    intros HX AIF. pose proof (C7_spec_i HX AIF) as K. unfold C7_stmts in K.
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 K))))))))).
  Qed.

  Lemma bionew_b64_spec_i : asan_rt_hyps_x H -> ainst_facts H -> bionew_b64_stmt H.
  Proof. intros HX AIF. pose proof (C9_spec_i HX AIF) as K. unfold C9_stmts in K. exact (proj1 K). Qed.

  Lemma biopush_spec_i : asan_rt_hyps_x H -> ainst_facts H -> biopush_stmt H.
  Proof. intros HX AIF. pose proof (C9_spec_i HX AIF) as K. unfold C9_stmts in K. exact (proj1 (proj2 K)). Qed.

  Lemma bioread_b64_spec_i : asan_rt_hyps_x H -> ainst_facts H -> bioread_b64_stmt H.
  Proof. intros HX AIF. pose proof (C9_spec_i HX AIF) as K. unfold C9_stmts in K. exact (proj1 (proj2 (proj2 K))). Qed.

  Lemma biofreeall_spec_i : asan_rt_hyps_x H -> ainst_facts H -> biofreeall_stmt H.
  Proof. intros HX AIF. pose proof (C9_spec_i HX AIF) as K. unfold C9_stmts in K. exact (proj1 (proj2 (proj2 (proj2 K)))). Qed.

  Theorem parse_one_spec_i : asan_rt_hyps_x H -> ainst_facts H -> readcfg_stmt H PF9new PF9free -> parse_one_stmt H PF9new PF9free.
  Proof. intros HX AIF RC. exact (parse_one_spec_x H PF9new PF9free (certA_i AIF) HX RC). Qed.

  Theorem fuzz_spec_i : asan_rt_hyps_x H -> ainst_facts H -> readcfg_stmt H PF9new PF9free ->
                        (atr_ok H -> fuzz_closed_ok H PF9new PF9free) -> fuzz_stmt H ECHL.
  Proof. intros HX AIF RC HFC. exact (fuzz_spec_x H PF9new PF9free (certA_i AIF) (certO3_i AIF) HX RC HFC). Qed.
End I.
