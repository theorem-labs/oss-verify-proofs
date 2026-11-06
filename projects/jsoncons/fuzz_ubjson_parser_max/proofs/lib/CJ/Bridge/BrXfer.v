(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import MState Mem Exec ITree Nodes Frame.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import Monad.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import BrRegs BrBase.
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Bridge_BrXfer () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.BrRegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "stdpp.bitvector.definitions."], [["1None"; "1option"; "2and"; "2eq"; "0F"; "3machine_state"; "3ms_regs"; "4bvmap"; "0M"; "0R"; "5canon_regs"; "5ms_eqv"; "5regs_eqv"; "6msteps"; "7MS"; "8msteps"]; ["9fp_csr"; "9fp_regs"; "9mkst"; "0a"; "0b"; "0fc"; "0fx"; "0m"; "0ms'"; "0pc"; "0rom"; "0segs"; ":bv"]]).
Section WithSegs.
Variable segs : list Segment.
Lemma cat_msteps_cj : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrXfer "<'5'?vKr2r1%43321'=r3%23615p041pQ::1pQ8;1").
Proof.
intros a b H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH].
- apply Exec.msteps_refl.
- eapply Exec.msteps_cons; [split; [exact Hsvc| exact Hstep]| exact IH].
Qed.
Lemma impl_eqv_transfer : forall {R} (t : itree node R) Q ms ms',
impl segs (at_node segs) t Q ms -> ms_eqv ms ms' ->
impl segs (at_node segs) t (fun r ms1' => exists ms1, Q r ms1 /\ ms_eqv ms1 ms1') ms'.
Proof.
intros R t. induction t as [r | n k IH]; intros Q ms ms' H Heqv; cbn [impl] in *.
- destruct (evt_eqv_transfer segs _ _ _ Heqv H) as (ms1 & ms1' & HQ & Heqv1 & Hms).
exists ms1'. split; [apply cat_msteps_cj; exact Hms|]. exists ms1. auto.
- destruct (evt_eqv_transfer segs _ _ _ Heqv H) as (ms1 & ms1' & [Hat Hk] & Heqv1 & Hms).
exists ms1'. split; [apply cat_msteps_cj; exact Hms|]. split; [eapply at_node_eqv; [exact Heqv1| exact Hat]|].
intros rsp. eapply IH; [apply Hk| apply nret_eqv; exact Heqv1].
Qed.
Lemma implM_eqv_transfer : forall {St A} (c : Monad.M St A) s Q ms ms',
implM segs c s Q ms -> ms_eqv ms ms' ->
implM segs c s (fun a s' ms1' => exists ms1, Q a s' ms1 /\ ms_eqv ms1 ms1') ms'.
Proof.
intros St A c s Q ms ms' H Heqv. unfold implM in *.
eapply impl_mono; [eapply impl_eqv_transfer; [exact H| exact Heqv]|].
intros [|[a s']] ms1' (ms1 & HQ & Heqv1); cbn in *; [exact I|]. exists ms1. auto.
Qed.
Context {fx : FPState}.
Lemma mkst_eqv_canon : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrXfer "Q2&7y5'LyR0%211%5241'1y8%611%311p061&;&>&:r4%211&AvF%211r3&@%114(0%11Cr2r1%>7;875321&B%15;>943%B231pQFD1pBE1pQDL1pDL1").
Proof.
intros R pc M rom. unfold ms_eqv, MS, mkst; cbn. repeat split; try reflexivity.
apply regs_eqv_sym, canon_regs_eqv.
Qed.
Lemma MS_is_mkst : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrXfer "Q1&7y5'LyR0%211%5241'1y8%611%311p061'3'5&>r4&AvF%211r3&@%114(0%11Br2r1%<7;875321&B%15;=943%A3@31pQFC1pBD1pQDK1pDK1").
Proof. reflexivity. Qed.
Lemma ms_eqv_MS_inv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrXfer "Q=&7y5'LyR0%211%5241yQ0%511'1y8%811%311p081'5&;&>r7r6r5r4(0%11Ar3r2%978765321r1%<221'2'3&6%117%@71?>=:<9%43C91&<r8%2215%9241p0;1pQBI1pQFK1pQ@L1pQ<Q21pQDQ61p:Q61pDQ71").
Proof.
intros R F pc fc m rom [R' F' pc' svc' rv' fc' m' rom'] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); cbn in *.
subst. split; [reflexivity| exact H1].
Qed.
End WithSegs.
