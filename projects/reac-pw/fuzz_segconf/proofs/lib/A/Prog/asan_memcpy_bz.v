(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSstrlen.v, with its module paths changed; 142 of its 194 lines of code are new or changed and 691 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg: module paths changed, no other change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/RT_mem_bz.v, with its module paths changed; 7 of its 32 lines of code are new or changed and 169 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import Img0.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Step.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Mem.
Module BzI := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.ImageA.
Module BzCl := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Step.

Lemma msteps_to_bz : forall s s', msteps rsegs s s' -> BzE.msteps BzI.asegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply BzE.msteps_refl.
  - eapply BzE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma evt_to_bz : forall (Q : machine_state -> Prop) ms, evt rsegs Q ms -> BzE.evt BzI.asegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [exact (msteps_to_bz ms ms' H) | exact HQ].
Qed.

Lemma mem_inv_of_bz : forall m, BzM.mem_inv BzI.asegs m -> mem_inv rsegs m.
Proof. intros m H a b E. exact (BzM.mem_inv_ro BzI.asegs m a b H E). Qed.

Lemma rw_cb_of_bz : forall m a n bs, BzSt.rw_cells BzI.asegs m a [BzCl.CB n bs] -> rw_cells rsegs m a [CB n bs].
Proof. intros m a n bs ((Hwf & HB) & HW). split; [split|]; [exact Hwf | exact HB | exact HW]. Qed.

Lemma rw_cb_to_bz : forall m a n bs, rw_cells rsegs m a [CB n bs] -> BzSt.rw_cells BzI.asegs m a [BzCl.CB n bs].
Proof. intros m a n bs ((Hwf & HB) & HW). split; [split|]; [exact Hwf | exact HB | exact HW]. Qed.
