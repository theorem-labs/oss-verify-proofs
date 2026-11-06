(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/DMrcDefs.v (a working branch 5ad50e61fc6a, file sha256 4c6b0aaa171e), CfF2b's DoRecycle re-hide lane (image-free; row A25); module paths changed only: 7 modules to this unit's lib/Reusable. No other edit; no image numeral is stated here. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4; F1 row R3): new file. rule 24: no function proved here (kind: a
   definition moved out of DMrc.v, unchanged).
   [rc_split_t]: the model's ARM SPLIT of H4's read record, i.e. the recycled chunk is a primary chunk or a live
   secondary with its slot (cgif: wf_chunks + wf_secondary, DGif1drMr.rchunk_secRm / rchunkRm).  The text and the
   Section variables are DMrc.v's; DMrc.rc_split_t is this definition at DMrc's Section variable DRq, so a consumer of
   the split field (DMrcRhOk) needs neither DMrc nor DMrcPrim. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YA0n YB1v YG00 YG0f.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables NMAXD LMAXD RMAXD : Z.
Definition rc_split_t : Prop :=
forall X k ks zs, DRq X (k :: ks) zs ->
(exists off, ck_beg k = PPrim off) \/
(exists r o sm i, ck_beg k = PSec r o /\ nth_error (st_secs X) r = Some sm /\ nth_error (st_sec_arr X) i = Some r).
End h.
End d.
