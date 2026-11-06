(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit
  Lept_leaf RT_fk RT_fk_iface Bi_fkkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac ret_stF_tac ESP := split; [unfold ret_st; try rewrite ESP; do 16 eexists; reflexivity | cbn [ms_fregs MS]; fs_agree_tac].

Ltac hdr_null_post RT ESP AGF PF QF ::=
  apply cps_finish; let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; subst QF; cbv beta;
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, 0, (mkPixv 0 0 0 0 0 0 0 0 0 0 0) end;
  split; [| alg_tac];
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists;
  split; [ret_stF_tac ESP|];
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|];
  [ lazymatch goal with WMx : wmono asegs ?m0 ?mf |- wmono asegs ?m0 ?mf => exact WMx end
  | split; [| left; reflexivity];
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha _; apply AGF; exact Ha ].
