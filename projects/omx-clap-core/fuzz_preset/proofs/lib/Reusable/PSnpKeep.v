(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, c-libc-stdio's keep kit for the snprintf chain (the memnorm keep
   `YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'` that the engine's YGcallSnp.asnprintf_realizes_xrom
   ends in; c-omx-alloc 17:03Z ruling (b), parent c-libc-stdio 17:1xZ). memnorm (YAkMemnorm.v:41) is a property of the
   ADDRESSES of defined bytes only (not read-only, in a segment or below TASK_SIZE), so a memory that defines a subset of
   another's bytes keeps it, and a byte that a run defines anew keeps it when its address is present at entry or
   writable_at the restricted entry memory.  The four lemmas take the keep from a RAW (sub-)frame:
   - memnorm_of_subframe: over any footprint FP whose addresses are present at entry or writable_at;
   - memnorm_of_subframe_dw: its instance at a destination [d, d + w) (writable_at) and a window [lo, hi) (present);
   - memnorm_of_frame_of: the walk kit's own steps (PSnpSk.sw_run: YP09.frame_of is a raw frame, the written ranges
     lie in the window);
   - memnorm_munrestrict_sub: a leaf's run from a sub-store m0 of mrestrict H mem (L3: cjstore / cjnormv; L1:
     CL.clean) whose end store m' is m0 off its footprint, the post memory being munrestrict H mem m'.
   The proof of memnorm_of_subframe is c-libc-stdio rows-cpy 532cf8bd849e PRowKit.prk_memnorm_keep's argument with a
   sub-frame and a footprint predicate.  Closure: YAkMemnorm, YK04, YP09, YG0n (PRowKit.v's header).
   rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YP09 YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YK0i.
Open Scope Z_scope.

Module MN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YAkMemnorm.

(* the keep from a SUB-frame over any footprint FP whose bytes are present at entry or writable_at the restricted
   entry memory: a byte mem' defines outside FP is mem's byte; mem' may lack bytes mem had (memnorm is about the
   addresses of defined bytes only, so dropping is free) *)
Lemma memnorm_of_subframe : forall segs (H : word -> bool) (mem mem' : word -> option byte) (FP : Z -> Prop),
  MN.memnorm segs mem ->
  (forall z : word, mem' z <> None -> ~ FP (bv_unsigned z) -> mem' z = mem z) ->
  (forall a, 0 <= a < 2 ^ 64 -> FP a -> apresent H mem a \/ writable_at segs (mrestrict H mem) a) ->
  MN.memnorm segs mem'.
Proof.
intros segs H mem mem' FP (Hi & Ht) Hfr Hfp.
assert (NEW : forall (z : word) b, mem' z = Some b ->
  (exists b0, mem z = Some b0) \/ (mem z = None /\ wview segs mem z <> None)).
{ intros z b Ez. destruct (mem z) as [b0|] eqn:E0; [left; exists b0; reflexivity|]. right. split; [reflexivity|].
  pose proof (bv_unsigned_in_range 64 z) as Rz. unfold bv_modulus in Rz.
  assert (Rz' : 0 <= bv_unsigned z < 2 ^ 64) by (change (2 ^ 64) with (2 ^ Z.of_N 64); lia).
  assert (NNEM : forall P : Prop, ~ ~ (P \/ ~ P))
    by (intros P k; apply k; right; intros p; apply k; left; exact p).
  intros Hn. apply (NNEM (FP (bv_unsigned z))). intros [IN|OUT].
  - destruct (Hfp (bv_unsigned z) Rz' IN) as [[_ [b0 Hb0]] | Hw].
    + rewrite Z_to_bv_bv_unsigned, E0 in Hb0. discriminate.
    + unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw.
      assert (Er : mrestrict H mem z = mem z) by (unfold mrestrict; rewrite E0; destruct (H z); reflexivity).
      assert (Ew : wview segs (mrestrict H mem) z = wview segs mem z) by (unfold wview; rewrite Er; reflexivity).
      rewrite Ew in Hw. exact (Hw Hn).
  - rewrite (Hfr z ltac:(rewrite Ez; discriminate) OUT), E0 in Ez. discriminate. }
split.
- intros z b Ez. destruct (NEW z b Ez) as [[b0 E0] | [E0 Hw]]; [exact (Hi z b0 E0)|].
  unfold MN.ro_addr. unfold wview in Hw. rewrite E0 in Hw.
  destruct (find_segment segs (bv_unsigned z) 1) as [sg|]; [|reflexivity].
  destruct (seg_writable sg); [reflexivity|]. exfalso. apply Hw. reflexivity.
- intros z b Ez. destruct (NEW z b Ez) as [[b0 E0] | [E0 Hw]]; [exact (Ht z b0 E0)|].
  left. unfold wview in Hw. rewrite E0 in Hw.
  destruct (find_segment segs (bv_unsigned z) 1); [discriminate|]. exfalso. apply Hw. reflexivity.
Qed.

(* the parent's instance: the destination [d, d + w) writable, the callee's window [lo, hi) present *)
Lemma memnorm_of_subframe_dw : forall segs (H : word -> bool) (mem mem' : word -> option byte) d w lo hi,
  MN.memnorm segs mem ->
  (forall z : word, mem' z <> None -> ~ (d <= bv_unsigned z < d + w) -> ~ (lo <= bv_unsigned z < hi) ->
     mem' z = mem z) ->
  (forall a, lo <= a < hi -> apresent H mem a) ->
  (forall a, d <= a < d + w -> writable_at segs (mrestrict H mem) a) ->
  MN.memnorm segs mem'.
Proof.
intros segs H mem mem' d w lo hi HMN Hfr Hwin Hdst.
apply (memnorm_of_subframe segs H mem mem' (fun a => (d <= a < d + w) \/ (lo <= a < hi)) HMN).
- intros z Hz Hn. apply Hfr; [exact Hz | intros X; apply Hn; left; exact X | intros X; apply Hn; right; exact X].
- intros a _ [X|X]; [right; exact (Hdst a X) | left; exact (Hwin a X)].
Qed.

(* the walk kit's own steps (PSnpSk.sw_run): the symbolic run's raw frame_of, written ranges inside the window *)
Lemma memnorm_of_frame_of : forall segs (H : word -> bool) (mem memB : word -> option byte) E rs lo hi,
  MN.memnorm segs mem -> frame_of E rs mem memB ->
  (forall a, in_wrange E rs a -> lo <= a < hi) -> (forall a, lo <= a < hi -> apresent H mem a) ->
  MN.memnorm segs memB.
Proof.
intros segs H mem memB E rs lo hi HMN Hfr Hin Hwin.
apply (memnorm_of_subframe segs H mem memB (fun a => lo <= a < hi) HMN).
- intros z _ Hn. apply Hfr. intros X. exact (Hn (Hin _ X)).
- intros a _ X. left. exact (Hwin a X).
Qed.

(* the leaves (L3's GXA run on cjnormv, L1's Bz run on clean): the run starts from a SUB-store m0 of the restricted
   entry memory, ends in m' that is m0 off its footprint FP (raw: GXA's munch, the Bz frame), and the post memory is
   munrestrict H mem m' *)
Lemma memnorm_munrestrict_sub : forall segs (H : word -> bool) (mem m0 m' : word -> option byte) (FP : Z -> Prop),
  MN.memnorm segs mem ->
  (forall (z : word) b, m0 z = Some b -> mrestrict H mem z = Some b) ->
  (forall z : word, m' z <> None -> ~ FP (bv_unsigned z) -> m' z = m0 z) ->
  (forall a, 0 <= a < 2 ^ 64 -> FP a -> apresent H mem a \/ writable_at segs (mrestrict H mem) a) ->
  MN.memnorm segs (munrestrict H mem m').
Proof.
intros segs H mem m0 m' FP HMN Hsub Hfr Hfp.
apply (memnorm_of_subframe segs H mem (munrestrict H mem m') FP HMN); [|exact Hfp].
intros z Hz Hn. unfold munrestrict in *. destruct (H z) eqn:Eh; [reflexivity|].
rewrite (Hfr z Hz Hn). destruct (m0 z) as [b|] eqn:E0; [|rewrite (Hfr z Hz Hn), E0 in Hz; contradiction].
pose proof (Hsub z b E0) as X. unfold mrestrict in X. rewrite Eh in X. exact (eq_sym X).
Qed.
