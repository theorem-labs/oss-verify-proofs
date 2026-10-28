(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bs X1c2 X1bn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ra X1qu X1ri X1r3 X1r4
X1rm X1o8 X1r6 X1og X1qw X1pe X1ot X1r7
X1r8 X1nu X1o3 X1o5 X1o4 X1o6 X1o7 X1nx.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Local Notation psegs := Plain.M.loaded_segments.
Local Notation usegs := Ubsan.M.loaded_segments.

Definition Xcanon (sel : option bool) (argv : list (list Z)) (fs : Fs) (tr : list event) : Prop :=
exists b, compat sel b /\ tr = ct_events fs (ctrace_of argv fs b) /\ run_defined fs argv b.

Lemma exit_code_small : forall c, c = 0 \/ c = 1 \/ c = 2 -> exit_code c = Z_to_bv 64 c.
Proof. intros c [->|[->| ->]]; apply bv_eq; vm_compute; reflexivity. Qed.

Section Whole.
Variable sel : option bool.
Variable rstage : Z.
Variable fs : Fs.
Variable argv : list (list Z).

Let X := Xcanon sel argv fs.

Lemma startup_E : forall (P : assnE PState),
(forall s mo tr mo', P s mo tr -> m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> P s mo' tr) ->
mspecE sel X P startup (fun _ => P).
Proof.
intros P HP. unfold startup.
eapply mspecE_seq with (R := P); [|intros _; apply mspecE_ret; auto].
apply msysE_node; [exact I| intros; apply nprog_set_tid|].
intros s mo tr rsp mo' evs a H Hst _. destruct (stepR_set_tid sel mo rsp mo' evs Hst) as (-> & Hfd & Hfs).
rewrite app_nil_r. eapply HP; eauto.
Qed.

Lemma io_exit_E : forall code,
mspecE sel X (Qmain sel fs [] argv code) (io_exit code) (fun _ _ _ _ => False).
Proof.
intros code. unfold io_exit, stdio_exit_model. apply mspecE_pointwise. intros s0 mo0 tr0 (b & Hb & Hcode & Hfs & Htr & Hdef).
eapply mspecE_seq.
{ eapply mspecE_pre; [apply (stdout_exit_flush_E ps_so set_so_ps sel X (fun _ _ => eq_refl) (fun mo => m_fs mo = fs) (ps_so s0) tr0)|].
intros s mo tr (-> & -> & ->). unfold SoA. auto. }
intros _. apply msysE_exit. intros s mo tr (Hfs' & ->). exists b. split; [exact Hb|]. split; [|exact Hdef].
rewrite Htr, Hfs', Hcode, exit_code_small by apply ct_code_cases. rewrite ct_events_flat. cbn [app]. reflexivity.
Qed.

Lemma prog_with_E : forall (P0 : assnE PState),
(forall s mo tr, P0 s mo tr -> m_fds mo = fds_std /\ m_fs mo = fs /\ ps_so s = stdout_init /\ tr = []) ->
mspecE sel X P0 (prog_with rstage argv) (fun _ _ _ _ => False).
Proof.
intros P0 HP0. unfold prog_with.
eapply mspecE_seq with (R := fun s mo tr => m_fds mo = fds_std /\ m_fs mo = fs /\ ps_so s = stdout_init /\ tr = []).
{ eapply mspecE_pre; [apply startup_E|exact HP0]. intros s mo tr mo' (H1 & H2 & H3 & H4) E1 E2. splits; congruence. }
intros _. eapply mspecE_bind; [apply (main_model_E sel X rstage fs [] argv)|].
intros code. apply io_exit_E.
Qed.

End Whole.

Lemma prog_twfE : forall sel segs rstage ceil argv mo,
m_fds mo = fds_std ->
twfE sel (Xcanon sel (argv_Z argv) (m_fs mo)) (prog segs rstage ceil argv) mo [] (fun _ _ _ => True).
Proof.
intros sel segs rstage ceil argv mo Hfd. unfold prog. apply twfE_ebind.
eapply twfE_mono.
- apply (prog_with_E sel rstage (m_fs mo) (argv_Z argv) (fun s mo' tr => s = ps_init ceil (reservedZ segs) /\ mo' = mo /\ tr = [])).
+ intros s mo' tr (-> & -> & ->). splits; auto.
+ auto.
- intros p mo' tr' [].
Qed.

Section Gen.
Variables (segs : list Segment) (rs : Z) (pc : N) (ph : PhdrInfo) (lim : Z).
Hypothesis Hpos : 0 < reserved_top (segments_reserved segs).
Hypothesis Hceil : reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo.
Hypothesis H40 : reserved_top (segments_reserved segs) + brk_aslr_max + PGSZ <= 2^40.
Hypothesis Hlim : LBUDGET <= lim.
Variables (en : ExecEntry) (inp : ProcInput).
Hypothesis VE : valid_entry (mkImage segs pc ph) en inp.
Hypothesis VI : valid_input_core inp.

Let t := prog segs rs (ceil_of en) (in_argv inp).
Let mo := mo0 segs lim en inp.

Lemma gen_Pn : tsafe nstep Pn t mo.
Proof.
destruct (X1r7.prog_model_ok segs rs pc ph lim en inp Hpos Hceil H40 Hlim VE VI) as [_ Hs].
apply tsafe_Pn; [exact Hs| exact (X1ot.prog_no_enomem segs rs pc ph lim en inp Hpos Hceil H40 Hlim VE VI)| apply mo0_minv| apply mo0_not_halted].
Qed.

Lemma gen_leaves : leaves_unreachable_m nstep t mo.
Proof. exact (proj1 (X1r7.prog_model_ok segs rs pc ph lim en inp Hpos Hceil H40 Hlim VE VI)). Qed.

Lemma gen_fds : m_fds mo = fds_std.
Proof. unfold mo, TopLevel.mo0. rewrite m_fds_init_model. reflexivity. Qed.
Lemma gen_fs : m_fs mo = in_fs inp.
Proof. unfold mo, TopLevel.mo0. rewrite m_fs_init_model. reflexivity. Qed.

Lemma gen_exists : forall ok, exists full,
texit nstep nexit t mo full /\ full = ct_events (in_fs inp) (ctrace_of (argv_Z (in_argv inp)) (in_fs inp) ok)
/\ run_defined (in_fs inp) (argv_Z (in_argv inp)) ok.
Proof.
intros ok.
pose proof (prog_twfE (Some ok) segs rs (ceil_of en) (in_argv inp) mo gen_fds) as Htw.
destruct (twfE_exists (Some ok) _ t mo [] _ Htw gen_Pn gen_leaves) as (full & Hx).
pose proof (twfE_texit (Some ok) _ t mo [] _ full Htw Hx) as (b & Hb & E & Hdef).
rewrite (Hb ok eq_refl) in E, Hdef. cbn [app] in E. rewrite gen_fs in E, Hdef.
exists full. split; [exact (texit_stepR_nstep (Some ok) t mo full Hx)|]. split; [exact E| exact Hdef].
Qed.

Theorem prog_det_gen : forall tr, tree_traces t mo tr <-> canonT (argv_Z (in_argv inp)) (in_fs inp) tr.
Proof.
intros tr. split.
- intros (full & Hfull & Hp).
apply ttrace_split in Hfull. destruct Hfull as [Hx|(r & mo' & Hpath)]; [|exfalso; exact (gen_leaves _ _ _ Hpath)].
pose proof (texit_nstep_stepR t mo full gen_Pn Hx) as HxR.
pose proof (twfE_texit None _ t mo [] _ full (prog_twfE None segs rs (ceil_of en) (in_argv inp) mo gen_fds) HxR) as (b & _ & E & _).
cbn [app] in E. rewrite gen_fs in E. exists b. rewrite <- E. exact Hp.
- intros (ok & Hp). destruct (gen_exists ok) as (full & Hx & E & _).
exists full. split; [apply ttrace_split; left; exact Hx|]. rewrite E. exact Hp.
Qed.

Theorem canon_fuzz_defined_gen : forall ok, run_defined (in_fs inp) (argv_Z (in_argv inp)) ok.
Proof. intros ok. destruct (gen_exists ok) as (full & _ & _ & H). exact H. Qed.

End Gen.

Theorem prog_det_plain : forall en inp,
valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_core inp ->
forall tr, tree_traces (prog psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs source_alloc_limit en inp) tr
<-> canonT (argv_Z (in_argv inp)) (in_fs inp) tr.
Proof.
intros en inp VE VI. eapply prog_det_gen; [apply reserved_top_psegs| apply ceil_psegs| apply sbk_psegs| apply LBUDGET_le_source| exact VE| exact VI].
Qed.

Theorem prog_det_plain_at : forall lim en inp, LBUDGET <= lim ->
valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_core inp ->
forall tr, tree_traces (prog psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs lim en inp) tr
<-> canonT (argv_Z (in_argv inp)) (in_fs inp) tr.
Proof.
intros lim en inp Hlim VE VI. eapply prog_det_gen; [apply reserved_top_psegs| apply ceil_psegs| apply sbk_psegs| exact Hlim| exact VE| exact VI].
Qed.

Theorem prog_det_ubsan : forall en inp,
valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp -> valid_input_core inp ->
forall tr, tree_traces (prog usegs RSTAGE_ubsan (ceil_of en) (in_argv inp)) (mo0 usegs target_alloc_limit en inp) tr
<-> canonT (argv_Z (in_argv inp)) (in_fs inp) tr.
Proof.
intros en inp VE VI. eapply prog_det_gen; [apply reserved_top_usegs| apply ceil_usegs| apply sbk_usegs| apply LBUDGET_le_target| exact VE| exact VI].
Qed.

Theorem canon_fuzz_defined : forall en inp ok,
valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_core inp ->
run_defined (in_fs inp) (argv_Z (in_argv inp)) ok.
Proof.
intros en inp ok VE VI.
eapply (canon_fuzz_defined_gen psegs RSTAGE_plain _ _ source_alloc_limit); [apply reserved_top_psegs| apply ceil_psegs| apply sbk_psegs| apply LBUDGET_le_source| exact VE| exact VI].
Qed.

Lemma plain_entry_exists : forall inp, valid_input_either inp ->
exists en, valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp.
Proof.
intros inp (Hargv & Henvp & _ & _ & _ & _ & _ & _ & Hsize & _).
assert (Hsat : image_brk_satisfiable psegs = true) by (vm_compute; reflexivity).
destruct (image_brk_satisfiable_sound psegs Hsat) as [brk Hbrk].
pose proof (entry_stack_span_bound _ _ Hargv Henvp) as Hspan.
exists (mkEntry (Z_to_bv 64 sp_window_lo) brk (Z_to_bv 64 mmap_base_max) (mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0))).
rewrite (valid_entry_sv48 _ _ _ Hsize).
cbn. split; [| split; [exact Hbrk | split]].
- unfold valid_sp, sp_window_lo, sp_window_hi.
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). lia.
- unfold valid_mmap_base, mmap_base_min, mmap_base_max, sp_window_hi, page_size.
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). lia.
- unfold entry_stack_fits.
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus, sp_window_lo; cbn; lia).
unfold entry_stack_span_max in Hspan. unfold sp_window_lo, sp_window_hi. lia.
Qed.

Lemma valid_input_core_of_either : forall inp, valid_input_either inp -> valid_input_core inp.
Proof. intros inp (A & B & C & _ & D & E & F & G & I & _). exact (conj A (conj B (conj C (conj D (conj E (conj F (conj G I))))))). Qed.

Theorem run_defined_valid : forall inp ok, valid_input_either inp -> run_defined (in_fs inp) (argv_Z (in_argv inp)) ok.
Proof.
intros inp ok Hv. destruct (plain_entry_exists inp Hv) as [en VE].
exact (canon_fuzz_defined en inp ok VE (valid_input_core_of_either inp Hv)).
Qed.
