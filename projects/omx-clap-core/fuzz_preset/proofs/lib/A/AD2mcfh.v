(* edited in place from cgif_file lib/A/AD2m.v by rules r1,r2,r6, generator 107cfa3ff571119170a251af71894ef99c74eb0651a9612aa72eb6730ba3621a *)
(* rC copy: the in-place output above under the set's module names Xcfh (the renaming is the last step), generator 107cfa3ff5711191 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2m.v, with its module paths changed; it holds no image address of either build (c-asan's checker e55e1b52a8a0 finds none). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f YG00 YG0n YG0d YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m AD20 AD1icfh AE31cfh AE33cfh.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0d2cf YG0lawscf YGcfNames.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.

Variable B : asyms.
Hypothesis HB : TfibSyms B.
Lemma tfib_AICPY : aintrin_realizes_cf tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Proof.
pose proof (memcpy_icpt_realizes B (AR_laws_ok_cf tfibsegs B) HB) as H.
unfold aintrin_realizes_cf, aintrin_realizes. rewrite (ts_code B HB). exact H.
Qed.
Lemma tfib_ARDCHK : aread_check_stmt B.
Proof.
exact (aread_check_realizes B (AR_laws_ok_cf tfibsegs B) HB).
Qed.
End a.
