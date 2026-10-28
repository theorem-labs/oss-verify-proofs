(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2 X1bn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ri X1qu X1r0 X1rm X1o8 X1r3 X1r4 X1r6
X1og X1qw X1pe X1oa X1ph X1p1 X1oq X1p0 X1os X1oz X1oy X1op X1p5 X1ok
X1ov X1ow X1ou.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevel.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Local Notation psegs := Plain.M.loaded_segments.
Local Notation usegs := Ubsan.M.loaded_segments.

Definition mal_okQ (X : list (bptr * Z)) (n : Z) : Prop := ROOMX X P0 n /\ PHI P0 + R63X X + bigb n <= LBUDGET.

Lemma size_to_class_65536 : size_to_class 65536 = 44.
Proof. vm_compute. reflexivity. Qed.

Lemma OK_firstQ : mal_okQ [] 65536.
Proof.
split.
- apply ROOMX_intro; [| intros H; unfold MMAP_THRESHOLD in H; lia| lia]. intros _. rewrite size_to_class_65536.
pose proof (LRX_le_length [] 44). cbn [length] in H. rewrite (P0_small 44) by lia. lia.
- rewrite R63X_nil, bigb_small by (unfold MMAP_THRESHOLD; lia). pose proof PHI_P0. lia.
Qed.

Lemma OK_growQ : forall b k, (k <= 9)%nat -> mal_okQ [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).
Proof.
intros b k Hk. pose proof (X1o9.pow2_le_1024 k ltac:(lia)) as Hp. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)) as Hq.
assert (BIG : MMAP_THRESHOLD <= 65536 * 2 ^ Z.of_nat k * 2) by (unfold MMAP_THRESHOLD; lia).
split.
- apply ROOMX_intro; [intros H; lia| |].
2:{
assert (H9 : 2 ^ Z.of_nat k <= 512) by (change 512 with (2 ^ 9); apply Z.pow_le_mono_r; lia). change (2 ^ 26) with 67108864. lia. }
intros _. rewrite P0_63. pose proof (n63X_le_length [(b, 65536 * 2 ^ Z.of_nat k)]). cbn [length] in H. lia.
- rewrite R63X_cons, R63X_nil. pose proof PHI_P0.
pose proof (bigb_le (65536 * 2 ^ Z.of_nat k) ltac:(lia)). pose proof (bigb_le (65536 * 2 ^ Z.of_nat k * 2) ltac:(lia)).
unfold IB, UNIT in *. lia.
Qed.

Definition QX : assn PState := fun s mo => exists X, QI X P0 s mo.
Lemma QX_live : forall s mo, QX s mo -> step_live LBUDGET mo.
Proof. intros s mo [X H]. exact (QI_step_live _ _ _ _ H). Qed.
Lemma QX_so : forall v s mo, QX s mo -> QX (set_so_ps v s) mo.
Proof. intros v s mo [X H]. exists X. apply QI_set_so. exact H. Qed.

Lemma QI_vm X s mo mo' : QI X P0 s mo -> m_vm mo' = m_vm mo -> minv mo' -> m_halted mo' = None -> QI X P0 s mo'.
Proof. intros. eapply QI_fds; eauto. Qed.

Lemma prog_with_L : forall rs argv, mspecL LBUDGET (QI [] P0) (prog_with rs argv) (fun _ _ _ => False).
Proof.
intros rs argv. unfold prog_with.
eapply mspecL_seq.
{ apply (startup_L LBUDGET (QI [] P0) (QI_step_live [] P0) (QI_minv [] P0) (QI_vm [])). }
intros _. eapply mspecL_bind.
- apply (main_model_L LBUDGET io_diag raw_malloc raw_free rs (target_alloc_init (St:=PState)) run (target_alloc_count (St:=PState))
(fun X => QI X P0) mal_okQ).
+ intros X n Hn. eapply mspecL_pre; [apply (raw_malloc_LQ X P0 n Hn)|]. intros s mo [HQ [HR HB]]. auto.
+ intros X p n. apply raw_free_LQ.
+ intros X Y s mo HP. apply QI_perm. exact HP.
+ intros X d. apply (io_diag_L LBUDGET (QI X P0) (QI_step_live X P0)).
+ intros X bm. unfold target_alloc_init. apply mspecL_ret. intros s mo H; exact H.
+ intros X. unfold target_alloc_count. apply mspecL_ret. intros s mo H; exact H.
+ intros b cap cfg payload Hcap Hpl Hb. apply run_L; [lia| exact Hpl| exact Hb].
+ intros X s mo H. exact (QI_minv _ _ _ _ H).
+ intros X s mo mo' H. exact (QI_vm _ _ _ _ H).
+ intros X s mo H. exact (QI_step_live _ _ _ _ H).
+ exact OK_firstQ.
+ exact OK_growQ.
- intros code. apply (io_exit_L LBUDGET QX QX_live QX_so code). intros s mo H. exact H.
Qed.

Theorem prog_live_bound : forall segs rs pc ph lim en inp,
0 < reserved_top (segments_reserved segs) ->
reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
reserved_top (segments_reserved segs) + brk_aslr_max + PGSZ <= 2^40 ->
LBUDGET <= lim ->
valid_entry (mkImage segs pc ph) en inp -> valid_input_core inp ->
tlive LBUDGET (prog segs rs (ceil_of en) (in_argv inp)) (mo0 segs lim en inp).
Proof.
intros segs rs pc ph lim [sp brk0 mbase dr] inp Hpos Hceil H40 Hlim VE VI.
pose proof (valid_entry_parts _ _ _ _ _ _ _ _ VI VE) as (Hsp & Hbrk & _).
unfold prog, mo0, ceil_of. cbn [en_brk en_mmap_base en_sp].
apply (mspecL_program LBUDGET (QI [] P0) (prog_with rs (argv_Z (in_argv inp))) (fun _ _ _ => False)).
- apply prog_with_L.
- apply QI_init; [exact Hbrk| exact Hpos| exact Hsp| exact Hceil| exact H40| exact Hlim| exact P0_nonneg| pose proof PHI_P0; lia].
- intros a s' mo' [].
Qed.

Theorem prog_no_enomem : forall segs rs pc ph lim en inp,
0 < reserved_top (segments_reserved segs) ->
reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
reserved_top (segments_reserved segs) + brk_aslr_max + PGSZ <= 2^40 ->
LBUDGET <= lim ->
valid_entry (mkImage segs pc ph) en inp -> valid_input_core inp ->
tsafe nstep no_enomem (prog segs rs (ceil_of en) (in_argv inp)) (mo0 segs lim en inp).
Proof.
intros segs rs pc ph lim [sp brk0 mbase dr] inp Hpos Hceil H40 Hlim VE VI.
pose proof (valid_entry_parts _ _ _ _ _ _ _ _ VI VE) as (Hsp & Hbrk & _).
unfold prog, mo0, ceil_of. cbn [en_brk en_mmap_base en_sp].
apply (mspecL_program_ne LBUDGET (QI [] P0) (prog_with rs (argv_Z (in_argv inp))) (fun _ _ _ => False)).
- apply prog_with_L.
- apply QI_init; [exact Hbrk| exact Hpos| exact Hsp| exact Hceil| exact H40| exact Hlim| exact P0_nonneg| pose proof PHI_P0; lia].
- intros a s' mo' [].
Qed.

Lemma LBUDGET_le_LIM : LBUDGET <= LIM.
Proof. unfold LBUDGET, LIM. lia. Qed.

Theorem LB_plain_proof : forall lim en inp, LBUDGET <= lim ->
valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_core inp ->
tlive LIM (prog psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs lim en inp).
Proof. intros. apply (tlive_mono _ _ LBUDGET LIM LBUDGET_le_LIM). eapply prog_live_bound; [apply reserved_top_psegs| apply ceil_psegs| apply sbk_psegs| eassumption| eassumption| assumption]. Qed.

Theorem LB_ubsan_proof : forall lim en inp, LBUDGET <= lim ->
valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp -> valid_input_core inp ->
tlive LIM (prog usegs RSTAGE_ubsan (ceil_of en) (in_argv inp)) (mo0 usegs lim en inp).
Proof. intros. apply (tlive_mono _ _ LBUDGET LIM LBUDGET_le_LIM). eapply prog_live_bound; [apply reserved_top_usegs| apply ceil_usegs| apply sbk_usegs| eassumption| eassumption| assumption]. Qed.

Lemma LBUDGET_le_source : LBUDGET <= source_alloc_limit. Proof. unfold LBUDGET, source_alloc_limit. lia. Qed.
Lemma LBUDGET_le_target : LBUDGET <= target_alloc_limit. Proof. unfold LBUDGET, target_alloc_limit. lia. Qed.

Theorem prog_no_enomem_plain : forall en inp,
valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_core inp ->
tsafe nstep no_enomem (prog psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs source_alloc_limit en inp).
Proof. intros. eapply prog_no_enomem; [apply reserved_top_psegs| apply ceil_psegs| apply sbk_psegs| apply LBUDGET_le_source| eassumption| assumption]. Qed.

Theorem prog_no_enomem_plain_at : forall lim en inp, LBUDGET <= lim ->
valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_core inp ->
tsafe nstep no_enomem (prog psegs RSTAGE_plain (ceil_of en) (in_argv inp)) (mo0 psegs lim en inp).
Proof. intros lim en inp Hlim VE VI. eapply prog_no_enomem; [apply reserved_top_psegs| apply ceil_psegs| apply sbk_psegs| exact Hlim| exact VE| exact VI]. Qed.

Theorem prog_no_enomem_ubsan : forall en inp,
valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp -> valid_input_core inp ->
tsafe nstep no_enomem (prog usegs RSTAGE_ubsan (ceil_of en) (in_argv inp)) (mo0 usegs target_alloc_limit en inp).
Proof. intros. eapply prog_no_enomem; [apply reserved_top_usegs| apply ceil_usegs| apply sbk_usegs| apply LBUDGET_le_target| eassumption| assumption]. Qed.
