(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FxLin FxCore FxSound FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChMain FxChFam.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PSum.
Context {P1 P2 : Type}.
Variable ppost1 : P1 -> sst -> smodel -> option sst.
Variable ppost2 : P2 -> sst -> smodel -> option sst.

Definition ppostS (p : P1 + P2) (S : sst) (M : smodel) : option sst :=
  match p with inl q => ppost1 q S M | inr q => ppost2 q S M end.
End PSum.

Section PSumSound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Context {P1 P2 : Type}.
Variable ppost1 : P1 -> sst -> smodel -> option sst.
Variable ppost2 : P2 -> sst -> smodel -> option sst.
Hypothesis H1 : forall p, pnode_ok segs cfg LIMIT ppost1 p.
Hypothesis H2 : forall p, pnode_ok segs cfg LIMIT ppost2 p.

#[using="H1 H2"] Theorem pnodeS_ok : forall p, pnode_ok segs cfg LIMIT (ppostS ppost1 ppost2) p.
Proof. LiaFast.lf_pins (fun (H1 H2 : LiaFast.U) => LiaFast.u0). intros [q|q]; [exact (H1 q) | exact (H2 q)]. Qed.
End PSumSound.
(* [comment removed for export] *)
