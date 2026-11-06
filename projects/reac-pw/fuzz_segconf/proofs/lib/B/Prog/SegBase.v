(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the part of proofs/cgif/cgif_file_fuzzer/lib/YC20.v that carries no cgif name, copied for plugin-hostd/fuzz_command's program walk: the read-only range, the frame object and the shape of a call's post-condition. The cgif-specific stack and event constants and the cgif function contracts are left out; each function's walk states its own. *)
(* Modified by Theorem Labs, 2026-10: apost_baseF, the FP-existential post of a function that reaches the printf wrappers (libreac/fuzz_boxreg's BoxBase.v apost_baseF, with omx-clap-core/fuzz_manifest's Sem.reg_get form of the f-register clause). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdBase.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; only its Section d / e (ro_spares, arodata_ok_journalP), which the contracts' SegPgBase.v leaves out; the definitions before it and its Section j / l are SegPgBase.v's, Required from there. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/SegBase.v for fuzz_segconf.asan-ubsan: module paths. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variables rlo rhi : Z.
Hypothesis relro_img : forall a, rlo <= a < rhi -> in_img segs a.
Context {RO : ro_below_ofl segs rlo rhi}.
Lemma ro_spares : forall FP a, in_roP segs rlo rhi a -> ~ inFP FP a -> fp_spares FP a.
Proof. intros FP a Hro Hn. exact (fp_spares_below FP a (@ro_below_ofl_at segs rlo rhi SK RO a Hro) Hn). Qed.
(* after the core's journal change a footprint byte is not kept, so the read-only bytes must lie outside the
   call's footprint; every footprint of the program (heap blocks, the program's statics, the caller's stack, the
   sink token at 0) is *)
Lemma arodata_ok_journalP : forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
(forall a, in_roP segs rlo rhi a -> ~ inFP FP a) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> arodata_okP segs rlo rhi B (aview segs (w_H W') mem').
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HFP HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (ro_spares FP a Hro (HFP a Hro))].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (relro_img a Hgot).
Qed.
End e.
End d.
