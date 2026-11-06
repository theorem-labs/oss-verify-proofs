(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Ported by Theorem Labs, 2026-10-29: ajournal_fp_nil and srz_enter only, from cgif_file_fuzzer lib/A/ACfh.v (origin/ossv/recipes) to libreac fuzz_identity image A; module paths rebased, proofs unchanged. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK15 YK18 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YA0i YA0n YG0f YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI16 YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Lemma ajournal_fp_nil : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply fp_spares_closed; intros Ho; exact (sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
End e.
Section f.
Variable segs : list Segment.
Lemma srz_enter : forall (W : world segs) (c : config) (T : TSet),
AI segs (w_H W) (w_A W) (cfg_model c) ->
SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) -> srealizes segs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.
End f.
End d.

(* Statement check: each lemma, closed, at the type of the binder it discharges. Each ascription type-checks only
   if the lemma's type and the binder's text agree. *)
Section binder_check.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* lib/A/Prog/LLVMFuzzerTestOneInput.v:327-329 AJ_FP_NIL and :335-338 SRZ_ENTER (also LLVMFuzzerTestOneInput_L.v:386-388
   AJ_FP_NIL), Section a/b/c: Context {fx} {rc} {SK}, SEGS := @pa_segs _ ident_listing PI, Variable B. SEGS is a
   term of type list Segment, so the check is at any SEGS. *)
Variable SEGS : list Segment.
Variable B : asyms.
Check (ajournal_fp_nil SEGS B : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k).
Check (srz_enter SEGS : forall (W : world SEGS) (c : config) (T : TSet),
AI SEGS (w_H W) (w_A W) (cfg_model c) ->
SRr SEGS W c (fun W' c' => AI SEGS (w_H W') (w_A W') (cfg_model c') -> srealizes SEGS c' T) ->
srealizes SEGS c T).
(* lib/A/Prog/IdentEntryLink.v:689-691 AJ_FP_NIL, Section L: SKA := ident_asan_sink_head (IdentEntryLink.v:68,
   {| YI16.sk_ofl_head := 0x5f8648 |}), SEGS := @pa_segs _ ident_listing (@PI_ident rc), Variable IdentB. *)
#[local] Abbreviation SKA := ({| YI16.sk_ofl_head := 0x5f8648 |} : YI16.sink_head).
Check (ajournal_fp_nil (SK := SKA) SEGS B : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
@ajournal rc SKA SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
@ajournal rc SKA SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k).
End binder_check.
