(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module O := QbrW.
Module D := QwAs.Mq0.

Lemma mstep_bridge : forall segs ms ms', O.mstep segs ms ms' <-> D.mstep segs ms ms'.
Proof. intros. unfold O.mstep, D.mstep. reflexivity. Qed.

Lemma msteps_bridge : forall segs ms ms', O.msteps segs ms ms' <-> D.msteps segs ms ms'.
Proof.
intros segs ms ms'. split; intros H.
- induction H as [ms | ms ms1 ms2 H1 _ IH]; [apply D.msteps_refl| eapply D.msteps_cons; [apply mstep_bridge; exact H1| exact IH]].
- induction H as [ms | ms ms1 ms2 H1 _ IH]; [apply O.msteps_refl| eapply O.msteps_cons; [apply mstep_bridge; exact H1| exact IH]].
Qed.

Theorem evt_bridge : forall segs (Q : machine_state -> Prop) ms, O.evt segs Q ms <-> D.evt segs Q ms.
Proof.
intros segs Q ms. unfold O.evt, D.evt. split; intros (ms' & H & HQ); exists ms'; (split; [apply msteps_bridge; exact H| exact HQ]).
Qed.
