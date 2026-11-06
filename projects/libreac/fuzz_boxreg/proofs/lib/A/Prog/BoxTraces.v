(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the lemma text below the generated part is proofs/cgif/cgif_file_fuzzer/lib/A/ACej.v:528-592 (origin/ossv/recipes c8557374ad2), with the per-function lemmas of fuzz_boxreg.asan's callers; the data is fuzz_boxreg.asan's, written by gen_traces.py. *)
(* The allocation-trace universe of libreac/fuzz_boxreg's ASan build, in cgif's A/ACej.v form (CTX_<fn>, TRACES_<fn>,
   Tfib_universe, Tfib_universe_ok), for the asyms field as_universe (Reusable/YG0f.v:178).
   Image: the ORIGINAL fuzz_boxreg.asan (sha256 eacfa20547ad7dc0...), symbols from its
   twin fuzz_boxreg.debug (sha256 4532568b621d62be..., the same file as the unstripped fuzz_boxreg.asan the tree's
   BoxSyms / BoxList are read from). Generator: a Theorem Labs lane's gen_traces.py (sha256 59966c8835106382...).
   The generated part (from its first comment line to the "17 traces" comment) is the output of (paths shortened to file names):
     python3 gen_traces.py fuzz_boxreg.asan fuzz_boxreg.debug --ipc malloc=0x52688 --ipc free=0x52528 --fp LLVMFuzzerTestOneInput=0x7fe48 --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm --module OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable
   What each argument is (each measured on this image; objdump and elfdis listings):
   - --ipc malloc=0x52688: the pc the malloc interceptor stores as the trace's first entry. ___interceptor_malloc
     (0x525c0; __wrap_malloc / __interceptor_trampoline_malloc 0x523ec is `j 0x525c0`) tests GetMallocContextSize() > 2
     (`bltu a1(=2),a0` at 0x52620) and goes to 0x52684: `jal GetCurrentPc`; its return address 0x52688
     (___interceptor_malloc + 0xc8) is passed to UnwindImpl at 0x526e0 as a1 (mv s2,a0 at 0x52694), with a2 = s0.
   - --ipc free=0x52528: the same in ___interceptor_free (0x523f0; trampoline 0x523e8 is `j 0x523f0`): `bltu` at
     0x524f0 -> 0x52524 `jal GetCurrentPc`; 0x52528 = ___interceptor_free + 0x138; UnwindImpl at 0x52580.
     Both interceptors keep a frame record (addi sp,sp,-2032; sd ra,2024(sp); sd s0,2016(sp); addi s0,sp,2032 at
     0x525c0-0x525e0 / 0x523f0-0x52410), so the walk starts with the caller's ra and the caller's s0.
   - --fp LLVMFuzzerTestOneInput=0x7fe48: LLVMFuzzerTestOneInput keeps its frame pointer: addi s0,sp,256 at 0x7ff88,
     ra stored at sp+248 = s0-8 (0x7ff54), the caller's s0 at sp+240 = s0-16 (0x7ff58); the only other write of s0 is
     the epilogue's ld s0,240(sp) at 0x80f28. Its one caller is target_run's jal at 0x7fe44, so the next entry is
     0x7fe48 (BoxLibX.v RA_LLVMF). The walk then reads target_run's s0 and stops (below).
   - No --fp for the other callers on the unwind path, because none keeps s0 as a frame pointer at its allocator
     calls: read_name sets s0 = k = min (x mod 48, n) <= 47 (zext.b s0,a2 at 0x81350, li s0,0 at 0x81358, mv s0,a2
     at 0x8136c when n <= x mod 48) before its malloc at 0x8139c (the ReadName.v header: the chain is empty there);
     target_run sets s0 = a3 = payload_len (mv s0,a3 at 0x7fda4) before its malloc 0x7fddc and free 0x7fe70; main
     holds s0 = 2 (li s0,2 at 0x7fad4) at 0x7fafc, 0x7fb50, 0x7fb74, and at its free 0x7fca4 s0 is 2, target_run's
     status (mv s0,a0 at 0x7fc24), target_alloc_count's result (0x7fc34) or 251 (0x7fc3c). Each value is below the
     stack, so the fast unwinder stops there (the same driver code and the same stop reasons as fuzz_grant's,
     a Theorem Labs lane's depot/TRACES.md:591-601).
   - --exclude _ZN9libunwind13DwarfFDECache...addEmmmm: libunwind's FDE cache (malloc 0x82938, free 0x8295c), used
     only by the slow unwinder on the runtime's error path (gen_traces.py's documented invocation,
     README.md "gen_traces.py").
   No other program call of an allocation entry exists: the program's calls of __wrap_malloc / __wrap_free /
   ___interceptor_* are the 11 sites above (a census of the jal / j instructions in 0x7f000..0x82000 whose target
   is an allocation entry).
   Cross-checks, recorded only:
   - a Theorem Labs lane's PauTrlen output out/fuzz_boxreg.asan.json (ipc 0x52688 / 0x52528,
     no recursion, no icalls): the prefix closure of its traces is exactly the 17 entries below. It marks the
     read_name site WILD for s0 = load[S-280+8] (the cursor's n); the code only takes n when n <= x mod 48 <= 47,
     so that s0 also ends the walk.
   - a Theorem Labs lane's depot/TRACES.md (fuzz_grant's ORIGINAL images): the same ipc offsets
     (___interceptor_malloc + 0xc8, ___interceptor_free + 0x138; TRACES.md:25-26), the same driver sites (main + 0x54,
     + 0xa8, + 0xcc, + 0x1fc; target_run + 0x64, + 0xf8) and LLVMFuzzerTestOneInput's frame record continuing to
     target_run + 0xcc (TRACES.md:76-90; here 0x7fe48 = 0x7fd7c + 0xcc). Its statement TRLIST has 20 entries for
     grant's 12 interceptor traces; this list has 17 for boxreg's 11 (4 of them through LLVMFuzzerTestOneInput's
     frame). Neither list holds the start-up trace of __asan_register_globals.
   Use. An asyms instance B with as_universe B = Tfib_universe and pc_malloc_ra0 / pc_free_ra0 (as_code B) =
   box_malloc_ra0 / box_free_ra0 (no boxreg instance exists yet) gets: am_universe (universe_ok) from box_universe_ok;
   api_env's two one-entry traces (Reusable/YCbq.v:808-811) from box_ra0_universe; ReadName.v:143's premise from
   box_read_name_universe (A_read_name_mallocRA = box_text + AF_read_name + 0xf0 = 0x813a0 under PI_box); the
   registry malloc of LLVMFuzzerTestOneInput (0x80118) from box_registry_universe; every other call from
   TRACES_<fn>_U. *)
(* Machine-generated data computed from the task's compiled program: the calls of the memory-checking runtime's allocation entries in fuzz_boxreg, with the traces the runtime stores. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x7fe48]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x52688; 0x8011c];
[0x52688; 0x8011c; 0x7fe48];
[0x52528; 0x80600];
[0x52528; 0x80600; 0x7fe48];
[0x52528; 0x80aac];
[0x52528; 0x80aac; 0x7fe48];
[0x52528; 0x80e1c];
[0x52528; 0x80e1c; 0x7fe48]].
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x52688; 0x7fb00];
[0x52688; 0x7fb54];
[0x52528; 0x7fb78];
[0x52528; 0x7fca8]].
Definition CTX_read_name : list (list Z) :=
[[]].
Definition TRACES_read_name : list (list Z) :=
[[0x52688; 0x813a0]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x52688; 0x7fde0];
[0x52528; 0x7fe74]].
Definition Tfib_universe : list (list Z) :=
[[0x52528];
[0x52528; 0x7fb78];
[0x52528; 0x7fca8];
[0x52528; 0x7fe74];
[0x52528; 0x80600];
[0x52528; 0x80600; 0x7fe48];
[0x52528; 0x80aac];
[0x52528; 0x80aac; 0x7fe48];
[0x52528; 0x80e1c];
[0x52528; 0x80e1c; 0x7fe48];
[0x52688];
[0x52688; 0x7fb00];
[0x52688; 0x7fb54];
[0x52688; 0x7fde0];
[0x52688; 0x8011c];
[0x52688; 0x8011c; 0x7fe48];
[0x52688; 0x813a0]].
(* 17 traces, from 11 call sites in 4 function(s): LLVMFuzzerTestOneInput, main, read_name, target_run *)
(* The lemma text of cgif's A/ACej.v:528-592, with the TRACES_<fn>_U of this image's callers. *)
Fixpoint listZ_eqb (a b : list Z) : bool :=
match a, b with [], [] => true | x :: a', y :: b' => Z.eqb x y && listZ_eqb a' b' | _, _ => false end.
Fixpoint memZL (t : list Z) (l : list (list Z)) : bool :=
match l with [] => false | u :: l' => listZ_eqb t u || memZL t l' end.
Lemma listZ_eqb_eq : forall a b, listZ_eqb a b = true -> a = b.
Proof.
induction a as [|x a IH]; destruct b as [|y b]; cbn; intros H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [exact H1 | apply IH, H2].
Qed.
Lemma memZL_In : forall t l, memZL t l = true -> In t l.
Proof.
induction l as [|u l IH]; cbn; intros H; [discriminate|].
apply Bool.orb_prop in H as [H|H]; [left; symmetry; apply listZ_eqb_eq, H | right; apply IH, H].
Qed.
Fixpoint allb {X} (f : X -> bool) (l : list X) : bool := match l with [] => true | x :: l' => f x && allb f l' end.
Lemma allb_In : forall {X} (f : X -> bool) l x, allb f l = true -> In x l -> f x = true.
Proof. induction l; cbn; intros x H Hin; [destruct Hin|]. apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; auto. Qed.
Lemma TRACES_LLVMFuzzerTestOneInput_U : forall t, In t TRACES_LLVMFuzzerTestOneInput -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_LLVMFuzzerTestOneInput t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_main_U : forall t, In t TRACES_main -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_main t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_read_name_U : forall t, In t TRACES_read_name -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_read_name t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_target_run_U : forall t, In t TRACES_target_run -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_target_run t ltac:(vm_compute; reflexivity) H). Qed.
Fixpoint nodupZL (l : list (list Z)) : bool :=
match l with [] => true | t :: l' => negb (memZL t l') && nodupZL l' end.
Lemma memZL_false : forall t l, memZL t l = false -> ~ In t l.
Proof.
induction l as [|u l IH]; cbn; intros H Hin; [exact Hin|].
apply Bool.orb_false_elim in H as [H1 H2]. destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)].
assert (E : forall a, listZ_eqb a a = true) by (induction a; cbn; [reflexivity|]; rewrite Z.eqb_refl; assumption).
rewrite E in H1. discriminate.
Qed.
Lemma nodupZL_NoDup : forall l, nodupZL l = true -> NoDup l.
Proof.
induction l as [|t l IH]; cbn; intros H; [constructor|].
apply andb_prop in H as [H1 H2]. constructor; [apply memZL_false; destruct (memZL t l); [discriminate|reflexivity] | apply IH, H2].
Qed.
Lemma Tfib_universe_ok : universe_ok Tfib_universe.
Proof.
split; [unfold DEPOT_MAX; (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split.
- apply Forall_forall. intros t Ht.
pose proof (allb_In (fun t : list Z => (length t <=? kUnwindMax)%nat) Tfib_universe t ltac:(vm_compute; reflexivity) Ht) as H.
apply Nat.leb_le in H. exact H.
- apply nodupZL_NoDup. vm_compute. reflexivity.
Qed.
(* gen_traces.py closes the set under prefixes; checked here. *)
Fixpoint prefixes_inb (U : list (list Z)) (t : list Z) (n : nat) : bool :=
match n with O => true | S n' => memZL (firstn n t) U && prefixes_inb U t n' end.
Lemma prefixes_inb_In : forall U t n m, prefixes_inb U t n = true -> (1 <= m <= n)%nat -> In (firstn m t) U.
Proof.
intros U t n. induction n as [|n IH]; intros m H Hm; cbn [prefixes_inb] in H; [lia|].
apply andb_prop in H as [H1 H2]. destruct (Nat.eq_dec m (S n)) as [->|Hne]; [apply memZL_In; exact H1|].
apply IH; [exact H2 | lia].
Qed.
Lemma Tfib_universe_prefix : forall t m, In t Tfib_universe -> (1 <= m)%nat -> In (firstn m t) Tfib_universe.
Proof.
intros t m Ht Hm.
pose proof (allb_In (fun t => prefixes_inb Tfib_universe t (length t)) Tfib_universe t ltac:(vm_compute; reflexivity) Ht) as H.
destruct (Nat.le_gt_cases m (length t)) as [Hle|Hgt]; [exact (prefixes_inb_In _ _ _ m H ltac:(lia))|].
rewrite firstn_all2 by lia. exact Ht.
Qed.
(* The trace entries the asyms instance names: pc_malloc_ra0 and pc_free_ra0 (Reusable/YG0f.v:138,141) are the two
   --ipc values. *)
Definition box_malloc_ra0 : Z := 0x52688.
Definition box_free_ra0 : Z := 0x52528.
(* read_name's malloc (0x813a0 = the return address of its call): the chain is empty (s0 = k), so the trace is
   [pc_malloc_ra0; ra]. *)
Lemma box_read_name_trace_in : In [box_malloc_ra0; 0x813a0] Tfib_universe.
Proof. apply memZL_In. vm_compute. reflexivity. Qed.
(* LLVMFuzzerTestOneInput's registry malloc (0x8011c = the return address of its call): the trace through its frame
   record ([..; 0x7fe48]) and the prefix a walk cut at that frame stores. *)
Lemma box_registry_trace_in : In [box_malloc_ra0; 0x8011c] Tfib_universe /\ In [box_malloc_ra0; 0x8011c; 0x7fe48] Tfib_universe.
Proof. split; apply memZL_In; vm_compute; reflexivity. Qed.
Lemma box_ra0_in : In [box_malloc_ra0] Tfib_universe /\ In [box_free_ra0] Tfib_universe.
Proof. split; apply memZL_In; vm_compute; reflexivity. Qed.
(* The same facts for any asyms B whose universe is Tfib_universe and whose two trace pcs are the ones above: the form an
   instance's proof and the specs' premises (ReadName.v:143; Reusable/YCbq.v:811 api_env) use. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0f.
Lemma box_universe_ok : forall B : asyms, as_universe B = Tfib_universe -> universe_ok (as_universe B).
Proof. intros B HU. rewrite HU. exact Tfib_universe_ok. Qed.
Lemma box_ra0_universe : forall B : asyms, as_universe B = Tfib_universe ->
pc_malloc_ra0 (as_code B) = box_malloc_ra0 -> pc_free_ra0 (as_code B) = box_free_ra0 ->
In [pc_malloc_ra0 (as_code B)] (as_universe B) /\ In [pc_free_ra0 (as_code B)] (as_universe B).
Proof. intros B HU HM HF. rewrite HU, HM, HF. exact box_ra0_in. Qed.
Lemma box_read_name_universe : forall B : asyms, as_universe B = Tfib_universe -> pc_malloc_ra0 (as_code B) = box_malloc_ra0 ->
In [pc_malloc_ra0 (as_code B); 0x813a0] (as_universe B).
Proof. intros B HU HM. rewrite HU, HM. exact box_read_name_trace_in. Qed.
Lemma box_registry_universe : forall B : asyms, as_universe B = Tfib_universe -> pc_malloc_ra0 (as_code B) = box_malloc_ra0 ->
In [pc_malloc_ra0 (as_code B); 0x8011c] (as_universe B) /\ In [pc_malloc_ra0 (as_code B); 0x8011c; 0x7fe48] (as_universe B).
Proof. intros B HU HM. rewrite HU, HM. exact box_registry_trace_in. Qed.
