(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3 ItabFast ItabWS_ub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import SX2.

Definition ITABW : itab := itab_of_string ITABW_UB_S 77824%Z ITABW_UB_N.

Lemma ITABW_ok : itab_sound Ubsan.M.loaded_segments ITABW.
Proof. apply itab_agrees_sound. vm_cast_no_check (@eq_refl bool true). Qed.
