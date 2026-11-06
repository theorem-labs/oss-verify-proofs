(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file (the reply twin of preset's YCsokLazyMaps.v role): the start-up invariant
   cs_ok (YA0e.v) gives ARcf_nil_init's lazy-in-maps premise (YGcfNilInit.v, ALedger_cf's alc_lazy_in_maps, YG0ncf.v) at
   every state it holds, so at the start-up hand-off: the noaccess half from co_nasub, the lazy half from co_lzsub.
   No function is proved here (a kit invariant). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0g YA0e.
Import ListNotations.
Import APSG.
Open Scope Z_scope.

Theorem cs_ok_lazy_in_maps_cf : forall SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model,
  cs_ok SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model ->
  forall x, YK0g.covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x = true ->
  YK0g.covered (vm_maps (m_vmmaps model)) x = true.
Proof.
intros SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model HC x Hx.
unfold YK0g.covered in Hx. rewrite existsb_app in Hx. apply orb_prop in Hx as [Hx|Hx].
- exact (co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HC x Hx).
- exact (co_lzsub _ _ _ _ _ _ _ _ _ _ _ _ HC x Hx).
Qed.
