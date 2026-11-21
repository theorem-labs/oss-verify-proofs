(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: module paths changed to omx-clap-core fuzz_manifest (copied from cgif_file_fuzzer, no other change). *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YA06.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the node obligation sys_rob and the new system calls). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK16 YK0n YK11 YK0h YK0i YK14 YK1c YK0v YK02 YK0p YK15.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK0y YK1b YK00 YK01 YK13 YP0n YK04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YA0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YA0n_w YA05_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import RomBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Lemma region_free_forall : forall l (lo n : word),
region_free l lo n = true <->
(forall q, In q l -> bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned lo \/ bv_unsigned lo + bv_unsigned n <= bv_unsigned (fst q)).
Proof.
induction l as [|[a sz] l IH]; intros lo n; cbn [region_free].
- split; [intros _ q [] | reflexivity].
- rewrite Bool.andb_true_iff, IH. unfold iv_overlap. split.
+ intros [H1 H2] q [<-|Hq]; [|exact (H2 q Hq)]. cbn [fst snd].
apply Bool.negb_true_iff, Bool.andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
+ intros H. split; [|intros q Hq; apply H; right; exact Hq].
specialize (H (a, sz) (or_introl eq_refl)). cbn [fst snd] in H.
apply Bool.negb_true_iff, Bool.andb_false_iff. destruct H as [H|H]; [left | right]; apply Z.ltb_ge; lia.
Qed.
Lemma region_free_of_uncovered : forall l (lo n : word),
(forall q, In q l -> 0 < bv_unsigned (snd q)) -> 0 < bv_unsigned n ->
(forall x, bv_unsigned lo <= x < bv_unsigned lo + bv_unsigned n -> covered l x = false) ->
region_free l lo n = true.
Proof.
intros l lo n Hpos Hn Hcov. apply region_free_forall. intros q Hq. specialize (Hpos q Hq).
destruct (Z_le_gt_dec (bv_unsigned (fst q) + bv_unsigned (snd q)) (bv_unsigned lo)) as [|G1]; [left; assumption|].
destruct (Z_le_gt_dec (bv_unsigned lo + bv_unsigned n) (bv_unsigned (fst q))) as [|G2]; [right; assumption|]. exfalso.
set (x := Z.max (bv_unsigned lo) (bv_unsigned (fst q))).
assert (Hx : bv_unsigned lo <= x < bv_unsigned lo + bv_unsigned n) by (subst x; lia).
specialize (Hcov x Hx). assert (Hc : covered l x = true); [|congruence].
clear Hcov. induction l as [|p l IH]; [destruct Hq|]. cbn [covered]. apply Bool.orb_true_iff.
destruct Hq as [->|Hq]; [left | right; exact (IH Hq)].
unfold in_iv, B, S. apply Bool.andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; subst x; lia.
Qed.
