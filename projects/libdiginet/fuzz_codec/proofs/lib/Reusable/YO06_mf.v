(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO06.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Reusable/YO06.v; 11 of its 26 lines of code are new or changed and 53 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK15 YM02.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO0i YO0f YO0g YO0x YO0d YO0e
YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06 YO0d_mf.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Definition SPEC_dir_mf (p : list byte) (fs : Fs) : TSet :=
tset_mf (dir_m init_state)
(fun r => if fst r then diag (msg_read_error p) fs else diag msg_oom fs).
Definition SPECX_loaded_mf (data : list byte) (fs : Fs) : TSet :=
tset_mf (driver_tree data) (leaf_shapeX data fs).
Definition SPECX_args_mf (argv : list (list byte)) (fs : Fs) : TSet :=
match argv with
| [_; p] =>
match classify_open p fs with
| OpenFails => diag (msg_cannot_open p) fs
| OpenDir => t_alt2 (diag (msg_cannot_open p) fs) (SPEC_dir_mf p fs)
| OpenFile data => t_alt2 (diag (msg_cannot_open p) fs) (SPECX_loaded_mf data fs)
end
| _ => diag (msg_usage (nth 0 argv [])) fs
end.
Definition SPECX_mf (inp : ProcInput) : TSet := SPECX_args_mf (in_argv inp) (in_fs inp).
End b.
