(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the released proof of libdiginet/fuzz_codec's asan_halts, applied at the point BudgetWit/AsanWitness.v gives, where all three of its premises hold; made as libreac/fuzz_identity's lib/BudgetWit/AsanHaltsNV.v is made. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libdiginet.fuzz_codec Require Images Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit Require AsanWitness.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AD2o.

(** [Statements.asan_halts], which the released [AD2o.codec_asan_halts_closed]
    proves (proofs/asan_halts/Proof.v applies it), at an entry and an input that
    meet all three of its premises ([AsanWitness.asan_budget_witness]): its
    conclusion holds there with no hypothesis left. *)
Theorem asan_halts_not_vacuous :
exists en inp, valid_entry OSSVerify.libdiginet.fuzz_codec.Images.asan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libdiginet.fuzz_codec.Images.asan
    Budgets.Standard.lim_source en inp /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.libdiginet.fuzz_codec.Images.asan
    Budgets.Standard.lim_source en inp.
Proof.
destruct AsanWitness.asan_budget_witness as (en & inp & Hen & Hinp & Hnr).
exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
exact (OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.AD2o.codec_asan_halts_closed en inp Hen Hinp Hnr).
Qed.
