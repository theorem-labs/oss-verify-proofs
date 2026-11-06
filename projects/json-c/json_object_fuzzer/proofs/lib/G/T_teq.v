(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0.
Import QlEo_c1.Mq0.Exc.

Inductive teq {node : Type} {A : Type} : itree node A -> itree node A -> Prop :=
| teq_ret : forall r, teq (Ret r) (Ret r)
| teq_vis : forall n k k', (forall x, teq (k x) (k' x)) -> teq (Vis n k) (Vis n k').
