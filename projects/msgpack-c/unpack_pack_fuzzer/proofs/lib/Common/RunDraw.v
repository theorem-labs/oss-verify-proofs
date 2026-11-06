(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Export StackLayout.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Export RunConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma atop_range {rc : runConstT} : 0x7fff7f800000 <= ATOP <= 0x7FFFFF800000.
Proof. split; [apply ATOP_lo | apply ATOP_hi]. Qed.
Lemma sec_range {rc : runConstT} : 0 <= SECRET < 2^64.
Proof. apply SECRET_rng. Qed.

Ltac atop_facts :=
  lazymatch goal with
  | _ : 0x7fff7f800000 <= @ATOP _ <= 0x7FFFFF800000 |- _ => idtac
  | |- context [@ATOP _] => pose proof atop_range
  | _ : context [@ATOP _] |- _ => pose proof atop_range
  | _ => idtac
  end.
Ltac sec_facts :=
  lazymatch goal with
  | _ : 0 <= @SECRET _ < 2^64 |- _ => idtac
  | _ => pose proof sec_range
  end.

Ltac lia := atop_facts; Stdlib.micromega.Lia.lia.
Ltac nia := atop_facts; Stdlib.micromega.Lia.nia.
