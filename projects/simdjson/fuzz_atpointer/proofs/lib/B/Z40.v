(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z10d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Zm2 RT_rep Zl3 Zls Zm7 Zm3
  Zm4 Zm5 Zm6 Zlj Zi8 Zi9 Zl6 Zki Zis Zip Zim
  Zjl Zj1 Ziy Zju Zi7 RT_rtf RT_cli Zky D_defs Z82 Z7w
  Sj_rtf Zpo Zwn Z106 Zwc Zsl Zqf Zs4 Zqq Zqj
  Zxb Zy1 Zyo Z3q Z3p Z5f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition rta_rc : rt_contracts RTA :=
  rta_contracts (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
    (rta_free (drain_ok rhead_empty_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok (free_pass_ok munmap_ok madvise_ok)).
Definition rta_rc2 : rt_contracts2 RTA :=
  rta_contracts2 (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
    (rta_free (drain_ok rhead_empty_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok (free_pass_ok munmap_ok madvise_ok)).
Definition rta_rtf : rt_contracts_f RTA := rtf_of_rt RTA rta_rc.

Lemma rta_fcb : forall PMc, fdfs_only PMc -> mat_stable PMc -> fcb_stmt RTA PMc.
Proof. exact (fcb_closed RTA rta_art_facts rta_rtf). Qed.
Lemma rta_slowfa : slowfa_cps RTA.
Proof. exact (slowfa_closed RTA rta_art_facts rta_rtf rta_fcb). Qed.
Lemma rta_pffa : pffa_cps RTA.
Proof. exact (pffa_closed RTA rta_art_facts rta_rtf rta_fcb). Qed.
Theorem rta_numa : numa_stmt RTA.
Proof. exact (numa_world RTA rta_art_facts rta_slowfa rta_pffa). Qed.
Theorem rta_numo : numo_stmt RTA.
Proof. exact (numo_world RTA rta_art_facts rta_slowfa rta_pffa). Qed.
Theorem rta_rootnum : rootnum_stmt RTA.
Proof.
  exact (rootnum_world RTA rta_art_facts rta_rtf rta_slowfa rta_pffa (fun Σ m HA => rta_got_nothrow Σ m HA) rta_live_fresh).
Qed.
Theorem rta_stage2at : stage2at_cps RTA.
Proof. exact (stage2at_closed RTA rta_art_facts rta_rtf rta_numa rta_numo rta_rootnum). Qed.

Check (sj_lib_loc : fp_local LIB_FP sj_lib).
Check (HS_lib_ok : forall h ch, HS_both h = Some ch -> hs_lib_ok ch = true).
