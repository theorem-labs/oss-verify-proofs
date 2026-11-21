(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: libreac/fuzz_identity image A: BFUEL 400000 / FUEL 3000 / KC0 0 and startup_shape as the collector's certificate run measured them on this image (idst/final/A/runs/cert-A.log: APG.check ... = COk <this shape>); IT0 is mk_itab_ranges over this image's startup_plan_tfib_ranges *)
(* Modified by Theorem Labs, 2026-11: made from A/AB1m.v's startup_cert, without importing AB1m: the same check of the ASan start-up, with the limit argument at Budgets.Standard.lim_source (16 GiB), the limit of asan_halts's budget premise, instead of YA02.LIMIT (512 GiB). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed lim_source_value, startup_cert16). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_identity.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB12 AB1h AB1k.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YB1j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1p AB1l AB05 AB01r.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.

(** AB1m's parameters of the start-up check, verbatim (AB1m.v:25-33). *)
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
Definition IT0 : itab := mk_itab_ranges TSEGS startup_plan_tfib_ranges.
Lemma IT0_ok : itab_sound TSEGS IT0.
Proof. apply mk_itab_ranges_sound. Qed.
Definition hole_le_tfib (h1 h2 : nat) : bool := true.
Definition startup_shape : shape :=
(SCase (EVar 6) 10 (SAlt2 (SAlt2 (SHole 8) (SHole 9)) (SAlt2 (SHole 0) (SHole 1))) (SCase (EVar 6) 1802 (SAlt2 (SAlt2 (SHole 24) (SHole 25)) (SAlt2 (SHole 16) (SHole 17))) (SAlt2 (SHole 36) (SHole 32)))).

(** The limit [Statements.asan_halts]'s budget premise names: 16 GiB. *)
Lemma lim_source_value : Budgets.Standard.lim_source = 0x400000000.
Proof. reflexivity. Qed.

(** AB1m's start-up check, with the limit argument at the statement's limit,
    succeeds with AB1m's own [startup_shape]. *)
(* LPS 727298f3: per CONFIG_RSEQ flag, over the hand-off states and the renumbered plan that
   A/AB01r.v computes from the run, as A/AB1m.v states its certificate. *)
Lemma startup_cert16 : forall rs : bool,
check TSEGS IT0 TFIB NX0G Budgets.Standard.lim_source (rseq_z rs) (XNG TSEGS tfib_XN1) XE0 XB0 (HS_tfib_r (rseq_z rs)) hole_le_tfib KC0 BFUEL FUEL None
(init_acs_of_g (rseq_z rs) TFIB) (startup_plan_tfib_r (rseq_z rs))
= COk startup_shape.
Proof. intros rs. destruct rs; vm_cast_no_check (@eq_refl cres (COk startup_shape)). Qed.
