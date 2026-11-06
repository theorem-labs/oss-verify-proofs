(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the lemma text below the generated part is proofs/cgif/cgif_file_fuzzer/lib/A/ACej.v:545-592 (origin/ossv/recipes c8557374ad2) with a B prefix, using the boolean helpers of lib/A/Prog/BoxTraces.v; the data is fuzz_boxreg.asan-ubsan's, written by gen_traces.py. *)
(* The allocation-trace universe of libreac/fuzz_boxreg's asan-ubsan build, in cgif's A/ACej.v form, B-prefixed so
   that a file can import both builds (BCTX_<fn>, BTRACES_<fn>, BTfib_universe, BTfib_universe_ok).
   Image: the ORIGINAL fuzz_boxreg.asan-ubsan (sha256 7620eb05e0adf5cb...), symbols
   from fuzz_boxreg.debug (sha256 1d548458eac37ae1..., the same file as the unstripped fuzz_boxreg.asan-ubsan).
   Generator: a Theorem Labs lane's gen_traces.py (sha256 59966c8835106382...). The generated part is the output
   of the command below (paths shortened to file names), with each `CTX_`, `TRACES_` and `Tfib_universe` name given the prefix B:
     python3 gen_traces.py fuzz_boxreg.asan-ubsan fuzz_boxreg.debug --ipc malloc=0x526e8 --ipc free=0x52588 --fp LLVMFuzzerTestOneInput=0x7fea8 --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm --module OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable
   What each argument is (each measured on this image):
   - --ipc malloc=0x526e8: ___interceptor_malloc (0x52620; __wrap_malloc 0x5244c is `j 0x52620`): `bltu a1(=2),a0` at
     0x52680 -> 0x526e4 `jal GetCurrentPc`; 0x526e8 = ___interceptor_malloc + 0xc8; UnwindImpl at 0x52740.
   - --ipc free=0x52588: ___interceptor_free (0x52450; trampoline 0x52448 is `j 0x52450`): `bltu` at 0x52550 ->
     0x52584 `jal GetCurrentPc`; 0x52588 = ___interceptor_free + 0x138; UnwindImpl at 0x525e0. Both keep a frame
     record (sd ra,2024(sp); sd s0,2016(sp); addi s0,sp,2032 at 0x52624-0x52640 / 0x52454-0x52470).
   - --fp LLVMFuzzerTestOneInput=0x7fea8: addi s0,sp,256 at 0x7ffe8, ra at s0-8 (0x7ffb4), the caller's s0 at s0-16
     (0x7ffb8), no other write of s0 but the epilogue's ld at 0x80f6c; its one caller is target_run's jal at 0x7fea4.
   - No --fp for read_name (s0 = k <= 47: 0x813cc, 0x813d4, 0x813e8, before its malloc at 0x81434; BoxBReadName.v
     header), target_run (mv s0,a3 = payload_len at 0x7fe04, before 0x7fe3c and 0x7fed0) or main (s0 = 2 from 0x7fb34,
     at the last free 0x7fd04 also target_run's status, target_alloc_count's result or 251); each ends the walk.
   - --exclude: libunwind's FDE cache (malloc 0x82d5c, free 0x82d80), the runtime's error path (README.md).
   Cross-checks, recorded only: PauTrlen's out/fuzz_boxreg.asan-ubsan.json (ipc
   0x526e8 / 0x52588) closes to exactly these 17 entries (its WILD label on the read_name site is s0 = n <= 47, as
   in the A file); a Theorem Labs lane's depot/TRACES.md:202-203 has the same ipc offsets for fuzz_grant's asan-ubsan runtime,
   and its driver sites and the LLVMFuzzerTestOneInput frame continuation (target_run + 0xcc = 0x7fea8 here) match.
   Use: as in lib/A/Prog/BoxTraces.v, with boxb_* lemmas over BTfib_universe and boxb_malloc_ra0 / boxb_free_ra0;
   BoxBReadName.v:150's premise is boxb_read_name_universe (AB_read_name_mallocRA = 0x81318 + 0x120 = 0x81438). *)
(* Machine-generated data computed from the task's compiled program: the calls of the memory-checking runtime's allocation entries in fuzz_boxreg, with the traces the runtime stores. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition BCTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x7fea8]].
Definition BTRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x526e8; 0x80180];
[0x526e8; 0x80180; 0x7fea8];
[0x52588; 0x808b8];
[0x52588; 0x808b8; 0x7fea8];
[0x52588; 0x808f8];
[0x52588; 0x808f8; 0x7fea8];
[0x52588; 0x80e5c];
[0x52588; 0x80e5c; 0x7fea8]].
Definition BCTX_main : list (list Z) :=
[[]].
Definition BTRACES_main : list (list Z) :=
[[0x526e8; 0x7fb60];
[0x526e8; 0x7fbb4];
[0x52588; 0x7fbd8];
[0x52588; 0x7fd08]].
Definition BCTX_read_name : list (list Z) :=
[[]].
Definition BTRACES_read_name : list (list Z) :=
[[0x526e8; 0x81438]].
Definition BCTX_target_run : list (list Z) :=
[[]].
Definition BTRACES_target_run : list (list Z) :=
[[0x526e8; 0x7fe40];
[0x52588; 0x7fed4]].
Definition BTfib_universe : list (list Z) :=
[[0x52588];
[0x52588; 0x7fbd8];
[0x52588; 0x7fd08];
[0x52588; 0x7fed4];
[0x52588; 0x808b8];
[0x52588; 0x808b8; 0x7fea8];
[0x52588; 0x808f8];
[0x52588; 0x808f8; 0x7fea8];
[0x52588; 0x80e5c];
[0x52588; 0x80e5c; 0x7fea8];
[0x526e8];
[0x526e8; 0x7fb60];
[0x526e8; 0x7fbb4];
[0x526e8; 0x7fe40];
[0x526e8; 0x80180];
[0x526e8; 0x80180; 0x7fea8];
[0x526e8; 0x81438]].
(* 17 traces, from 11 call sites in 4 function(s): LLVMFuzzerTestOneInput, main, read_name, target_run *)
(* The boolean helpers (listZ_eqb, memZL, memZL_In, allb, allb_In, nodupZL, nodupZL_NoDup, prefixes_inb) are
   lib/A/Prog/BoxTraces.v's; they do not depend on the image. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxTraces.
Lemma BTRACES_LLVMFuzzerTestOneInput_U : forall t, In t BTRACES_LLVMFuzzerTestOneInput -> In t BTfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t BTfib_universe) BTRACES_LLVMFuzzerTestOneInput t ltac:(vm_compute; reflexivity) H). Qed.
Lemma BTRACES_main_U : forall t, In t BTRACES_main -> In t BTfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t BTfib_universe) BTRACES_main t ltac:(vm_compute; reflexivity) H). Qed.
Lemma BTRACES_read_name_U : forall t, In t BTRACES_read_name -> In t BTfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t BTfib_universe) BTRACES_read_name t ltac:(vm_compute; reflexivity) H). Qed.
Lemma BTRACES_target_run_U : forall t, In t BTRACES_target_run -> In t BTfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t BTfib_universe) BTRACES_target_run t ltac:(vm_compute; reflexivity) H). Qed.
Lemma BTfib_universe_ok : universe_ok BTfib_universe.
Proof.
split; [unfold DEPOT_MAX; (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split.
- apply Forall_forall. intros t Ht.
pose proof (allb_In (fun t : list Z => (length t <=? kUnwindMax)%nat) BTfib_universe t ltac:(vm_compute; reflexivity) Ht) as H.
apply Nat.leb_le in H. exact H.
- apply nodupZL_NoDup. vm_compute. reflexivity.
Qed.
Lemma BTfib_universe_prefix : forall t m, In t BTfib_universe -> (1 <= m)%nat -> In (firstn m t) BTfib_universe.
Proof.
intros t m Ht Hm.
pose proof (allb_In (fun t => prefixes_inb BTfib_universe t (length t)) BTfib_universe t ltac:(vm_compute; reflexivity) Ht) as H.
destruct (Nat.le_gt_cases m (length t)) as [Hle|Hgt]; [exact (prefixes_inb_In _ _ _ m H ltac:(lia))|].
rewrite firstn_all2 by lia. exact Ht.
Qed.
(* The trace entries the asyms instance names: pc_malloc_ra0 and pc_free_ra0 (Reusable/YG0f.v:138,141) are the two
   --ipc values. *)
Definition boxb_malloc_ra0 : Z := 0x526e8.
Definition boxb_free_ra0 : Z := 0x52588.
(* read_name's malloc (0x81438 = the return address of its call): the chain is empty (s0 = k), so the trace is
   [pc_malloc_ra0; ra]. *)
Lemma boxb_read_name_trace_in : In [boxb_malloc_ra0; 0x81438] BTfib_universe.
Proof. apply memZL_In. vm_compute. reflexivity. Qed.
(* LLVMFuzzerTestOneInput's registry malloc (0x80180 = the return address of its call): the trace through its frame
   record ([..; 0x7fea8]) and the prefix a walk cut at that frame stores. *)
Lemma boxb_registry_trace_in : In [boxb_malloc_ra0; 0x80180] BTfib_universe /\ In [boxb_malloc_ra0; 0x80180; 0x7fea8] BTfib_universe.
Proof. split; apply memZL_In; vm_compute; reflexivity. Qed.
Lemma boxb_ra0_in : In [boxb_malloc_ra0] BTfib_universe /\ In [boxb_free_ra0] BTfib_universe.
Proof. split; apply memZL_In; vm_compute; reflexivity. Qed.
(* The same facts for any asyms B whose universe is BTfib_universe and whose two trace pcs are the ones above: the form an
   instance's proof and the specs' premises (BoxBReadName.v:150; Reusable/YCbq.v:811 api_env) use. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0f.
Lemma boxb_universe_ok : forall B : asyms, as_universe B = BTfib_universe -> universe_ok (as_universe B).
Proof. intros B HU. rewrite HU. exact BTfib_universe_ok. Qed.
Lemma boxb_ra0_universe : forall B : asyms, as_universe B = BTfib_universe ->
pc_malloc_ra0 (as_code B) = boxb_malloc_ra0 -> pc_free_ra0 (as_code B) = boxb_free_ra0 ->
In [pc_malloc_ra0 (as_code B)] (as_universe B) /\ In [pc_free_ra0 (as_code B)] (as_universe B).
Proof. intros B HU HM HF. rewrite HU, HM, HF. exact boxb_ra0_in. Qed.
Lemma boxb_read_name_universe : forall B : asyms, as_universe B = BTfib_universe -> pc_malloc_ra0 (as_code B) = boxb_malloc_ra0 ->
In [pc_malloc_ra0 (as_code B); 0x81438] (as_universe B).
Proof. intros B HU HM. rewrite HU, HM. exact boxb_read_name_trace_in. Qed.
Lemma boxb_registry_universe : forall B : asyms, as_universe B = BTfib_universe -> pc_malloc_ra0 (as_code B) = boxb_malloc_ra0 ->
In [pc_malloc_ra0 (as_code B); 0x80180] (as_universe B) /\ In [pc_malloc_ra0 (as_code B); 0x80180; 0x7fea8] (as_universe B).
Proof. intros B HU HM. rewrite HU, HM. exact boxb_registry_trace_in. Qed.
