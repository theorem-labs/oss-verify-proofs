(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From Corelib Require Import PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIface LxLin LxState LxMem LxStep LxCheck LxUnitSplit LxEnvU LxUnitCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LXS LXM LXI LXC LXU.
Open Scope Z_scope.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxUnitUA_def.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma UA_part4 : leaves_ok (run_some UNIT_UA 0 (un_cuts UNIT_UA) [14; 17; 22; 24; 30; 33; 38; 46; 57; 62; 63; 64; 79; 82; 83; 86]%nat) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
