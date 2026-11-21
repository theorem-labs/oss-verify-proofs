(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's segment list with the vDSO/vvar pair; the write-certified stack window; the channel-reader premise; the launch premises). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv FP.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import RsLift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition prog_tree (R : Type) : Type := ProcInput -> ExecEntry -> itree node R.

(* [comment removed for export] *)
Definition ms0 (segs : list Segment) (pc : N) (ph : PhdrInfo)
    (en : ExecEntry) (inp : ProcInput) : machine_state :=
  init_ms segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp.

Lemma ms0_eq : forall segs pc ph en inp,
  ms0 segs pc ph en inp =
  MS (mkR_init (en_sp en)) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem inp (en_mmap_base en) ph (Z_to_bv 64 (Z.of_N pc)) (en_sp en) (en_draw en)) (seg_rom segs).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* At the revision the run's initial model carries the launch's vDSO draw
   ([Run.init_config]'s [with_vdso]); the walks run over that model. *)
Definition mo0 (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Model :=
  with_vdso (vdso_run_init (ed_vdso (en_draw en)))
    (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).

Lemma m_fds_mo0 : forall segs lim en inp,
  m_fds (mo0 segs lim en inp)
  = m_fds (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).
Proof. reflexivity. Qed.

Lemma m_fs_mo0 : forall segs lim en inp,
  m_fs (mo0 segs lim en inp)
  = m_fs (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).
Proof. reflexivity. Qed.

(* The run's initial configuration, over [Run.run_segments]: the machine state
   reads the run's list, the model's reservations are the binary's
   ([RsLift.segments_reserved_run_segments]). *)
Lemma init_config_run : forall segs pc ph lim en inp,
  init_config (run_segments segs inp (en_sp en) (en_mmap_base en)) pc ph
    (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state (run_segments segs inp (en_sp en) (en_mmap_base en)) pc ph
             (en_sp en) (en_mmap_base en) (en_draw en) inp)
          (mo0 segs lim en inp).
Proof.
  intros segs pc ph lim en inp. unfold init_config, mo0.
  rewrite segments_reserved_run_segments. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mo0_alloc_top : forall segs lim en inp,
  alloc_top (m_vmmaps (mo0 segs lim en inp)) = (bv_unsigned (en_sp en) - stack_max_size)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mo0_alloc_top_ceiling : forall segs pc ph lim en inp,
  in_va_size inp = Sv48 ->
  valid_entry (mkImage segs pc ph) en inp ->
  alloc_top (m_vmmaps (mo0 segs lim en inp)) = @alloc_ceiling (ceiling_of_sp (bv_unsigned (en_sp en))).
Proof.
  intros segs pc ph lim en inp Hsv48 Hve. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve.
  destruct en as [sp brk mb rnd]. destruct Hve as (Hsp & _ & _ & _). destruct Hsp as (H1 & H2 & H3).
  rewrite mo0_alloc_top. cbn [en_sp]. unfold sp_window_lo, sp_window_hi, stack_max_size in *.
  rewrite ceiling_of_sp_eq; [reflexivity| lia | exact H3].
Qed.

(* [comment removed for export] *)
Lemma mo0_not_halted : forall segs lim en inp, m_halted (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

Lemma mo0_minv : forall segs lim en inp, in_channel_reader inp = true -> minv (mo0 segs lim en inp).
Proof.
  intros segs lim en inp Hr.
  exact (minv_init (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp Hr).
Qed.

Lemma ms0_svc : forall segs pc ph en inp, ms_svc_pending (ms0 segs pc ph en inp) = None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Remark frm0_init : frm0 (Z_to_bv 32 0).
Proof. reflexivity. Qed.

Lemma ms0_frm0 : forall segs pc ph en inp, frm0 (ms_fcsr (ms0 segs pc ph en inp)).
Proof. intros. exact frm0_init. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tree_ok {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
    (t : prog_tree R) (Q : R -> machine_state -> Prop) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
    impl segs (at_node segs) (t inp en) Q (ms0 segs pc ph en inp)
    /\ leaves_unreachable_m nstep (t inp en) (mo0 segs lim en inp)
    /\ tsafe nstep nsafe (t inp en) (mo0 segs lim en inp).

(* [comment removed for export] *)
Definition tree_traces {R : Type} (t : itree node R) (mo : Model) : list event -> Prop :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

(* [comment removed for export] *)
Definition trees_equiv {RS RT : Type} (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
    (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (tS : prog_tree RS) (tT : prog_tree RT) : Prop :=
  forall enS enT inp,
    valid_entry (mkImage segsS pcS phS) enS inp ->
    valid_entry (mkImage segsT pcT phT) enT inp ->
    valid_input inp ->
    trace_equiv (tree_traces (tS inp enS) (mo0 segsS source_alloc_limit enS inp))
                (tree_traces (tT inp enT) (mo0 segsT target_alloc_limit enT inp)).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [valid_launch] is the fifth conjunct and it is NEW at the revision's shape, not a
   convenience: [StoreOk.stack_window_lo_valid], which P/Impl.v and U/Impl.v reach through
   [valid_input_w_launch], now needs it, and the build names the gap as "The variable
   valid_input_w_launch was not found in the current environment" at P/Impl.v:54 and
   U/Impl.v:54 - a MISSING ACCESSOR, not a missing Require (the name exists nowhere in the
   tree but at those two call sites).
   ADDING A CONJUNCT STRENGTHENS THE HYPOTHESIS AND SO WEAKENS EVERY LEMMA THAT TAKES
   [valid_input_w], SO IT NEEDS BOTH PRODUCERS CHECKED, AND BOTH ARE:
     - [valid_input_w_of] below, from the model's own [Run.valid_input_launch]
       (75d69e00:theories/LinuxProcessSem/Run.v:5219); [valid_launch] is the 13th conjunct
       of [valid_input] at :4594, so nothing is assumed that the model does not give;
     - Top/PlainLane.v:45, the only place in this tree that builds [valid_input_w] by hand,
       which already has the witness: [Top/TopBridge.v:27]'s [image_realizes] carries
       [valid_launch (InpRec.inp ...)] as a hypothesis in its own right, beside
       [entry_launch_ok_va] at :25-26, and [plain_lane_realizes] already intros it.
   So no consumer loses a claim and nothing published moves: the top-level statements
   quantify under the model's [valid_input], which implies the new conjunct. *)
Definition valid_input_w (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ in_va_size inp = Sv48
  /\ in_channel_reader inp = true   (* [Run.valid_input] pins the reader; the channel write arm reads it *)
  /\ valid_launch inp.

Lemma valid_input_w_of : forall inp, valid_input inp -> valid_input_w inp.
Proof.
  intros inp H. pose proof (valid_input_va_size _ H) as Hv. pose proof (valid_input_channel_reader _ H) as Hr.
  pose proof (valid_input_launch _ H) as Hl.
  destruct H as (Ha & He & _). exact (conj Ha (conj He (conj Hv (conj Hr Hl)))).
Qed.

Lemma valid_input_w_va_size : forall inp, valid_input_w inp -> in_va_size inp = Sv48.
Proof. intros inp (_ & _ & H & _). exact H. Qed.

Lemma valid_input_w_reader : forall inp, valid_input_w inp -> in_channel_reader inp = true.
Proof. intros inp (_ & _ & _ & H & _). exact H. Qed.

Lemma valid_input_w_launch : forall inp, valid_input_w inp -> valid_launch inp.
Proof. intros inp (_ & _ & _ & _ & H). exact H. Qed.
