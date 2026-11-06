(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode.
Import ListNotations.
Open Scope Z_scope.
Definition nf_node (n : node) : Prop :=
match n with NMmap _ _ _ _ | NMprotect _ _ _ => True | _ => False end.
Definition NF (n : node) (mo : Model) : Prop :=
match n with
| NMmap _ _ _ _ | NMprotect _ _ _ =>
forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
| _ => True
end.
Definition nstepB (B : Z) (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
nstep n mo rsp mo' evs
/\ (vm_live_bytes (m_vmmaps mo') <= B \/ vm_live_bytes (m_vmmaps mo') <= vm_live_bytes (m_vmmaps mo))
/\ NF n mo.
Fixpoint tlive {R} (B : Z) (t : itree node R) (mo : Model) : Prop :=
match t with
| Ret _ => True
| Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs -> vm_live_bytes (m_vmmaps mo') <= B /\ tlive B (k rsp) mo'
end.
Fixpoint tnf {R} (t : itree node R) (mo : Model) : Prop :=
match t with
| Ret _ => True
| Vis n k => NF n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> tnf (k rsp) mo'
end.
