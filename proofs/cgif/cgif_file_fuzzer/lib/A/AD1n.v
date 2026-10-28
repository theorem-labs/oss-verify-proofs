(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK0s YK15 YK18 YM02 YP0m YP09 YK04 YA0i YA0n YA0e YG00 YG01 YG05 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l AF0m AD1t AD20 AD1v AD1i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Lemma asptr_null_dec' : forall p : sptr, {p = PNull} + {p <> PNull}.
Proof. intros [| | |]; [left; reflexivity | right; discriminate ..]. Qed.
Theorem tfib_malloc_site : malloc_site_tfa B.
Proof.
intros ly S W regs mem md n KB HPRE Ha0 Hn Hlive Htr2 Htr1 HAI KBLK.
pose proof (acall_pre_of_drv B _ _ _ _ _ _ HPRE) as HAP. pose proof HPRE as (HAR & _ & Hnev & _).
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
set (trc := call_trace ly (pc_malloc_ra0 (as_code B)) regs []).
assert (Htr : In trc (as_universe B)).
{ subst trc. destruct (call_trace_drv ly regs (pc_malloc_ra0 (as_code B))) as [-> | ->]; assumption. }
pose proof (AMALLOC ly S W regs mem md n [] HAP Ha0 Hn Hlive Htr) as HREAL. fold trc in HREAL.
pose proof (ml_malloc_ns _ ML S n trc HWF (regime_ok_small _ Hnev) Hn Hlive Htr) as HTOK.
apply (SRr_srealizes tfibsegs W (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md) _ _
(amreal_SRr04 tfibsegs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)) HAI).
intros W' c' Hwle HAI' (r & tr & Hpath & Hgf & Hleaf). cbn [cfg_model] in HAI'.
pose proof (atok_apath_flag _ _ _ tr r HTOK Hpath) as [HQ HNS]. rewrite (last_flag_true tr Hgf) in HNS.
destruct r as [p S']. destruct Hleaf as (ly' & regs' & mem' & md' & -> & HPOST & Hres & _). cbn [fst snd] in HNS, HPOST, Hres, HAI'.
destruct (asptr_null_dec' p) as [-> | Hnn]; [exfalso; discriminate (HNS eq_refl)|].
apply (KBLK ly' S' W' regs' mem' md' trc tr p Hnn Htr Hpath); [| exact Hres | exact Hwle | exact HAI'].
pose proof HPOST as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [| exact P7].
intros a Ha Ho Ho' Hs HnE. apply P6; [exact Ha | exact Ho | exact Ho' | exact Hs |]. intros [_ X]. exact (HnE X).
Qed.
End c.
End b.
