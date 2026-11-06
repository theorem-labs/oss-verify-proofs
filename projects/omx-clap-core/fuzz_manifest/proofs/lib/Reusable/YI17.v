(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: module paths changed to omx-clap-core fuzz_manifest (copied from cgif_file_fuzzer, no other change). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK15 YI16.
Definition unlink_shape (fs : Fs.Fs) (TA TB : TSet) : TSet :=
if fs_under fs sink_path then TA
else match Fs.fs_lookup fs sink_path with Some _ => t_alt2 TA TB | None => TA end.
Definition openat_shape (fs : Fs.Fs) (TA TB : TSet) : TSet :=
if fs_under fs sink_path then TA else t_alt2 TA TB.
