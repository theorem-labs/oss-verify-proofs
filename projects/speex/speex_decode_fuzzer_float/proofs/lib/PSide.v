(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1br X1bo X1bs X1c2 X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pw X0qx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevel TopE TopSides.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r3 X1r6 X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require X1h7 X1gm X1m9.
Import ListNotations.
Open Scope Z_scope.

Local Notation psegs := Plain.M.loaded_segments.

Definition RP (en : ExecEntry) : RunCeiling :=
run_params (en_sp en) (rnd_w1 (en_draw en)) (canary_of (rnd_w0 (en_draw en))).

Lemma alloc_ceiling_RP : forall segs pc ph en inp,
valid_entry (mkImage segs pc ph) en inp -> valid_input_core inp ->
@alloc_ceiling (RP en) = ceil_of en.
Proof.
intros segs pc ph [sp b mb dr] inp VE VI. pose proof (valid_entry_parts _ _ _ _ _ _ _ _ VI VE) as (Hsp & _).
destruct Hsp as (A & B & _). unfold sp_window_lo in A. unfold sp_window_hi in B.
unfold RP, ceil_of, stack_max_size. cbn [en_sp en_draw]. apply alloc_ceiling_run_params. lia.
Qed.

Theorem HP_plain :
impl_root psegs Plain.M.init_pc Plain.M.phdrs RSTAGE_plain.
Proof.
intros en inp Hv Hi.
pose proof (alloc_ceiling_RP _ _ _ _ _ Hv Hi) as EC.
pose proof (@Ref.X1m9.ref_impl_from_harness (RP en) (Ref.X1gm.harness_proof_final _) en inp Hv Hi
ltac:(rewrite EC; unfold ceil_of, stack_max_size; reflexivity) eq_refl eq_refl) as X.
rewrite EC in X. exact X.
Qed.

Theorem P_side_closed : side_canon Tc imgP source_alloc_limit.
Proof. exact (P_side HP_plain). Qed.

Theorem P_side_closed_at : forall lim, Spec.X1pe.LBUDGET <= lim -> side_canon Tc imgP lim.
Proof. intros lim Hlim. exact (P_side_at lim Hlim HP_plain). Qed.

Theorem P_side_closed_sanitizer : side_canon Tc imgP SanitizerBudgets.lim_source.
Proof. exact (P_side_sanitizer HP_plain). Qed.

