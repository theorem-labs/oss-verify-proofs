(* SPDX-License-Identifier: MIT *)
(* Bridge (B), SECOND half (B2), for coturn's plain [ShapeAlg.realizes].

   (B1) (Common/RunSegTail.v) moves a derivation from the binary's own segment list
   to the run's.  It leaves the CONFIGURATION alone.  This file moves the configuration: the
   run's start state reads its instruction-free bytes out of [seg_rom (run_segments segs ..)],
   which answers everything [seg_rom segs] answers and the vDSO/vvar pair as well.

   WHY THAT IS THE WHOLE DIFFERENCE, read in the model rather than assumed.  [Run.init_config]
   ([c0dd863a:theories/LinuxProcessSem/Run.v:1483-1487]) uses the segment list in exactly two places:
   - [init_machine_state]'s [ms_rom := fun a => match memory_read mi_loaded_segments a 1 with
     Some (b :: _) => Some b | _ => None end] ([c0dd863a:theories/LinuxProcessSem/Run.v:1441-1474]),
     which is this tree's [PropExec.seg_rom] (Common/PropExec.v:260-261) spelled out.  [ms_mem] is
     [entry_stack_image] over the input, the mmap base, the phdrs, the pc, the sp and the draw,
     plus [stack_window_lo]: no segment list.
   - [init_model (segments_reserved mi_loaded_segments) ..].  AND THAT ONE IS NOT A DIFFERENCE:
     [segments_reserved segs = map segment_reservation (filter (fun s => negb (seg_kernel_map s))
     segs)] ([c0dd863a:theories/LinuxProcessSem/Run.v:255-256]), [seg_kernel_map s] is
     [match seg_kind s with SegLoader => false | _ => true end]
     ([c0dd863a:theories/LinuxProcessSem/MemImageType.v:169-170]), and [vdso_segments] builds its
     pair at [SegVdsoVvar] and [SegVdsoText] ([c0dd863a:theories/LinuxProcessSem/Run.v:314-327]).
     [filter] distributes over [++] and kills the tail whole, with no hypothesis on [segs].  The
     model is literally the same term.

   Part 1 is made, statement and proof, from
     projects/bzip2/bzip2_compress_target/proofs/lib/Common/Cfg/RomStable.v
   lines 22-251 (its Part 1), as in the LPS 727298f3 update.  In this file:
   - the step relation is the plain [Run.sstep] (coturn's [ShapeAlg.node_ok]), not
     [sstep_cfg kit_cfg], so no refusal-filter machinery ([spurious_wrom], [nspur_to_wrom],
     [nspur_of_wrom]) is here, and each step lemma below is an [sstep_*] one;
   - [sstep]'s eleven arms are matched in the model's own order, with the three vDSO arms at
     positions 4-6 ([c0dd863a:theories/LinuxProcessSem/Run.v:686-814]) discharged by
     [vdso_entry_fn_none_seg], exactly as Common/RunSegTail.v:215-259 does for (B1);
   - Part 2 is coturn's own: a [realizes_cfg] bridge over [app] is, for this tree, (B1). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.Cfg Require Import RomBase.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** * Part 1: a change of the read-only backing *)

Definition rep_wrom (x : machine_result (access_report machine_state)) (r : word -> option byte)
    : machine_result (access_report machine_state) :=
  match x with
  | MachineOk rep => MachineOk (@mkAccessReport machine_state (wrom (@access_value _ rep) r) (@accessed_ranges _ rep))
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

Section Seg.
Variable segs : list Segment.

Lemma decode_exec_accesses_wrom : forall st w r,
  decode_exec_accesses segs (wrom st r) w = rep_wrom (decode_exec_accesses segs st w) r.
Proof.
  intros st w r. unfold decode_exec_accesses.
  destruct (is_ecall w); [reflexivity|].
  destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); reflexivity].
  assert (E1 : ms_regs (wrom st r) = ms_regs st) by reflexivity.
  assert (E2 : ms_fregs (wrom st r) = ms_fregs st) by reflexivity.
  assert (E3 : ms_pc_val (wrom st r) = ms_pc_val st) by reflexivity.
  assert (E4 : ms_fcsr (wrom st r) = ms_fcsr st) by reflexivity.
  assert (E5 : ms_resv (wrom st r) = ms_resv st) by reflexivity.
  assert (E6 : ms_mem (wrom st r) = ms_mem st) by reflexivity.
  rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6.
  destruct (interp_eff_accesses segs _ (ms_mem st)) as [rep| |]; [|reflexivity|reflexivity].
  destruct rep as [[c m'] acc]. reflexivity.
Qed.

Lemma step_accesses_wrom : forall st r,
  step_accesses segs (wrom st r) = rep_wrom (step_accesses segs st) r.
Proof.
  intros st r. unfold step_accesses.
  assert (Ep : ms_pc (wrom st r) = ms_pc st) by reflexivity.
  assert (Em : ms_mem (wrom st r) = ms_mem st) by reflexivity.
  rewrite ?Ep, ?Em.
  destruct (fetch_word segs (ms_pc st)) as [w|]; [apply decode_exec_accesses_wrom|].
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|]; [apply decode_exec_accesses_wrom|].
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|]; [apply decode_exec_accesses_wrom|].
  destruct (fetch_failure segs (ms_mem st) (ms_pc st)) eqn:Ef; [|reflexivity|reflexivity].
  exfalso. revert Ef. unfold fetch_failure. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    intro Ef; discriminate Ef.
Qed.

Lemma mi_account_step_wrom : forall ms model r,
  mi_account_step segs (wrom ms r) model
  = match mi_account_step segs ms model with
    | MachineOk (ms', m') => MachineOk (wrom ms' r, m')
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof.
  intros ms model r. unfold mi_account_step. rewrite step_accesses_wrom.
  destruct (step_accesses segs ms) as [rep| |]; cbn [rep_wrom access_value accessed_ranges];
    [|reflexivity|reflexivity].
  destruct (materialize_model_accesses model (@accessed_ranges _ rep)); reflexivity.
Qed.

Lemma mi_account_step_rom : forall ms model ms' m',
  mi_account_step segs ms model = MachineOk (ms', m') -> ms_rom ms' = ms_rom ms.
Proof.
  intros ms model ms' m' H.
  pose proof (mi_account_step_wrom ms model (ms_rom ms)) as E.
  rewrite wrom_eta, H in E. injection E as E. rewrite E. reflexivity.
Qed.

Lemma apply_effect_wrom : forall ms eff r,
  advance_past_svc (apply_effect (wrom ms r) eff) = wrom (advance_past_svc (apply_effect ms eff)) r.
Proof. reflexivity. Qed.

Hypothesis Hvi : vdso_image segs = None.

Lemma vdso_entry_fn_none_seg : forall pc, vdso_entry_fn segs pc = None.
Proof. intros pc. unfold vdso_entry_fn. rewrite Hvi. reflexivity. Qed.

Lemma sstep_next_rom : forall c e c',
  sstep segs c e (SNext c') -> ms_rom (cfg_ms c') = ms_rom (cfg_ms c).
Proof.
  intros c e c' H. inversion H; subst; cbn [cfg_ms]; try reflexivity.
  all: first [ eapply mi_account_step_rom; eassumption
             | exfalso; rewrite vdso_entry_fn_none_seg in *; discriminate ].
Qed.

Lemma node_rom : forall c I evs nx, ShapeAlg.node_ok segs c I evs nx ->
  forall i, ms_rom (cfg_ms (nx i)) = ms_rom (cfg_ms c).
Proof. intros c I evs nx [Hc _] i. exact (sstep_next_rom _ _ _ (Hc i)). Qed.

(** Forward: a step from [c] is a step from [c] with a larger backing. *)
Lemma sstep_wrom_fwd : forall c e c' r,
  sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  sstep segs c e (SNext c') -> sstep segs (cwrom c r) e (SNext (cwrom c' r)).
Proof.
  intros [ms model] e c' r Hrob Hr H.
  (* [sys_rob] is quantified over the vDSO layer for bridge (A)'s sake; here the plain form at
     this configuration's own model is what the step relation asks for *)
  pose proof (sys_rob_plain segs _ Hrob) as Hrobp. cbn [cfg_ms cfg_model] in Hrobp.
  unfold cwrom. cbn [cfg_ms cfg_model] in *.
  inversion H; subst; cbn [cfg_ms cfg_model].
  - apply sstep_instr; [assumption | assumption |].
    rewrite mi_account_step_wrom.
    match goal with Hm : mi_account_step _ _ _ = MachineOk _ |- _ => rewrite Hm end. reflexivity.
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - rewrite <- apply_effect_wrom.
    match goal with Hs : ms_svc_pending ms = Some ?x |- _ =>
      assert (Hiff : forall o, syscall_spec (sys_input segs (wrom ms r) x) model o
                               <-> syscall_spec (sys_input segs ms x) model o)
        by (intros o; exact (Hrobp r x Hr Hs o)) end.
    eapply sstep_syscall; [eassumption | eassumption | apply Hiff; eassumption
                          | eassumption | eassumption].
  - match goal with Hs : ms_svc_pending ms = Some ?x |- _ =>
      assert (Hiff : forall o, syscall_spec (sys_input segs (wrom ms r) x) model o
                               <-> syscall_spec (sys_input segs ms x) model o)
        by (intros o; exact (Hrobp r x Hr Hs o)) end.
    eapply sstep_exit; [eassumption | eassumption | apply Hiff; eassumption
                       | eassumption | eassumption].
  - match goal with Hs : ms_svc_pending ms = Some ?x |- _ =>
      assert (Hiff : forall o, syscall_spec (sys_input segs (wrom ms r) x) model o
                               <-> syscall_spec (sys_input segs ms x) model o)
        by (intros o; exact (Hrobp r x Hr Hs o)) end.
    eapply sstep_killed; [eassumption | eassumption | apply Hiff; eassumption | eassumption].
Qed.

(** Backward: every step from the larger backing is one from [c], mapped. *)
Lemma sstep_wrom_back : forall c e st r,
  sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  sstep segs (cwrom c r) e st ->
  exists st0, sstep segs c e st0
         /\ st = match st0 with SNext c0 => SNext (cwrom c0 r) | SError => SError end.
Proof.
  intros [ms model] e st r Hrob Hr H.
  pose proof (sys_rob_plain segs _ Hrob) as Hrobp. cbn [cfg_ms cfg_model] in Hrobp.
  unfold cwrom in H. cbn [cfg_ms cfg_model] in *.
  assert (Hs : forall x8, ms_svc_pending ms = Some x8 ->
            forall o, syscall_spec (sys_input segs (wrom ms r) x8) model o
                      <-> syscall_spec (sys_input segs ms x8) model o)
    by (intros x8 Hx o; exact (Hrobp r x8 Hr Hx o)).
  inversion H; subst.
  - match goal with Hm : mi_account_step _ (wrom ms r) _ = MachineOk (?a, ?b) |- _ =>
      rewrite mi_account_step_wrom in Hm;
      destruct (mi_account_step segs ms model) as [[ms1 m1]| |] eqn:Em; try discriminate Hm;
      injection Hm as <- <- end.
    exists (SNext (mkCfg ms1 m1)). split; [apply sstep_instr; assumption | reflexivity].
  - match goal with Hm : mi_account_step _ (wrom ms r) _ = MachineFault |- _ =>
      rewrite mi_account_step_wrom in Hm;
      destruct (mi_account_step segs ms model) as [[ms1 m1]| |] eqn:Em; try discriminate Hm end.
    exists SError. split; [apply sstep_instr_fault; assumption | reflexivity].
  - (* instr_unmodeled: arm 3 of eleven, and it carries its own [vdso_entry_fn .. = None] *)
    match goal with Hm : mi_account_step _ (wrom ms r) _ = MachineUnmodeled |- _ =>
      rewrite mi_account_step_wrom in Hm;
      destruct (mi_account_step segs ms model) as [[ms1 m1]| |] eqn:Em; try discriminate Hm end.
    exists SError. split; [| reflexivity].
    apply sstep_instr_unmodeled;
      [assumption | assumption | assumption | apply vdso_entry_fn_none_seg].
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - exists (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
    split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_syscall; [eassumption | eassumption | apply Hx; eassumption
                          | eassumption | eassumption].
  - exists SError. split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_syscall_materialization_fault;
      [eassumption | eassumption | apply Hx; eassumption | eassumption | eassumption].
  - exists (SNext (mkCfg ms model')). split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_exit; [eassumption | eassumption | apply Hx; eassumption
                       | eassumption | eassumption].
  - exists (SNext (mkCfg ms model')). split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_killed; [eassumption | eassumption | apply Hx; eassumption | eassumption].
  - exists SError. split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_syscall_unmodeled; [eassumption | eassumption | apply Hx; eassumption].
Qed.

Lemma node_wrom : forall c I evs nx r,
  ShapeAlg.node_ok segs c I evs nx -> sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  ShapeAlg.node_ok segs (cwrom c r) I evs (fun i => cwrom (nx i) r).
Proof.
  intros c I evs nx r [Hc Hb] Hrob Hr. split.
  - intros i. exact (sstep_wrom_fwd c (evs i) (nx i) r Hrob Hr (Hc i)).
  - intros e st Hst.
    destruct (sstep_wrom_back c e st r Hrob Hr Hst) as (st0 & H0 & ->).
    destruct (Hb e st0 H0) as (i & -> & ->). exists i. split; reflexivity.
Qed.

(** The node at the larger backing is robust too: its own extensions are the original's. *)
Lemma sys_rob_wrom : forall c r, sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r -> sys_rob segs (cwrom c r).
Proof.
  intros [ms m] r Hrob Hr r2 x8 Hr2 Hs v o. unfold cwrom in *. cbn [cfg_ms cfg_model] in *.
  change (wrom (wrom ms r) r2) with (wrom ms r2).
  change (ms_svc_pending (wrom ms r)) with (ms_svc_pending ms) in Hs.
  change (ms_rom (wrom ms r)) with r in Hr2.
  cbn [cfg_ms cfg_model] in Hrob.
  rewrite (Hrob r2 x8 (rom_ext_trans _ _ _ Hr Hr2) Hs v o).
  symmetry. exact (Hrob r x8 Hr Hs v o).
Qed.

(** (B2), part 1: a derivation is a derivation at every larger read-only backing. *)
Theorem realizes_wrom : forall c T, realizes segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> realizes segs (cwrom c r) T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hrob Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
  - apply (rz_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (node_wrom c I evs nx r Hn Hrob Hr).
    + exact (sys_rob_wrom c r Hrob Hr).
    + intros i. apply IH. rewrite (node_rom c I evs nx Hn i). exact Hr.
  - apply rz_halt. exact Hh.
  - eapply rz_conseq; [apply IH; exact Hr | exact Heq].
Qed.

End Seg.

(** * Part 2: the run's start state *)

Lemma find_segment_app_rs : forall segs tail addr n,
  find_segment (segs ++ tail) addr n
  = match find_segment segs addr n with
    | Some s => Some s
    | None => find_segment tail addr n
    end.
Proof.
  induction segs as [|seg rest IH]; intros tail addr n; [reflexivity|].
  cbn [find_segment app].
  destruct (Z.leb (Z.of_N (seg_base seg)) addr
            && Z.leb (addr + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool;
    [reflexivity | apply IH].
Qed.

Lemma memory_read_app_some : forall segs tail a n bs,
  memory_read segs a n = Some bs -> memory_read (segs ++ tail) a n = Some bs.
Proof.
  intros segs tail a n bs. unfold memory_read. rewrite find_segment_app_rs.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|];
    [intro H; exact H | intro H; discriminate H].
Qed.

(** The run's backing answers everything the binary's own backing answers. *)
Lemma seg_rom_app_ext : forall segs tail, rom_ext (seg_rom segs) (seg_rom (segs ++ tail)).
Proof.
  intros segs tail a b. unfold seg_rom.
  destruct (memory_read segs a 1) as [[|b0 bs]|] eqn:E; try discriminate.
  rewrite (memory_read_app_some segs tail a 1 (b0 :: bs) E). exact (fun H => H).
Qed.

Lemma seg_rom_run_segments_ext : forall segs inp (sp mb : word),
  rom_ext (seg_rom segs) (seg_rom (run_segments segs inp sp mb)).
Proof. intros segs inp sp mb. unfold run_segments. apply seg_rom_app_ext. Qed.

(** The kernel's pair is not in the LOADER's reservations, so the run's model is the same term.
    [filter] is NOT named here on purpose: this file imports stdpp, whose [filter] is a different
    constant from [List.filter], so a [rewrite List.filter_app] finds no subterm in
    [Run.segments_reserved]'s body.  The cons rule below is proved by reduction
    instead, which is the same fact in whichever [filter] the model's definition uses. *)
Section Reserved.
  Local Transparent vdso_segments.

  Lemma segments_reserved_vdso_only : forall kb (sp mb : word),
    segments_reserved (vdso_segments kb sp mb) = [].
  Proof.
    intros kb sp mb. unfold segments_reserved, vdso_segments. cbv zeta.
    match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
  Qed.
End Reserved.

Lemma segments_reserved_cons : forall s l,
  segments_reserved (s :: l)
  = if seg_kernel_map s then segments_reserved l
    else segment_reservation s :: segments_reserved l.
Proof.
  intros s l. unfold segments_reserved. cbn. destruct (seg_kernel_map s); reflexivity.
Qed.

Lemma segments_reserved_app_vdso : forall segs kb (sp mb : word),
  segments_reserved (segs ++ vdso_segments kb sp mb) = segments_reserved segs.
Proof.
  induction segs as [|x xs IH]; intros kb sp mb.
  - replace ([] ++ vdso_segments kb sp mb) with (vdso_segments kb sp mb) by reflexivity.
    apply segments_reserved_vdso_only.
  - replace ((x :: xs) ++ vdso_segments kb sp mb)
      with (x :: (xs ++ vdso_segments kb sp mb)) by reflexivity.
    rewrite !segments_reserved_cons, IH. reflexivity.
Qed.

Lemma segments_reserved_run_segments : forall segs inp (sp mb : word),
  segments_reserved (run_segments segs inp sp mb) = segments_reserved segs.
Proof.
  intros segs inp sp mb. unfold run_segments. apply segments_reserved_app_vdso.
Qed.

(** (B2): the run's start configuration IS the binary's, at the run's larger backing. *)
Lemma init_config_run_segments : forall segs inp (sp brk mb : word) pc ph rnd lim,
  init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp
  = cwrom (init_config segs pc ph sp brk mb rnd lim inp)
          (seg_rom (run_segments segs inp sp mb)).
Proof.
  intros segs inp sp brk mb pc ph rnd lim.
  unfold init_config, cwrom, wrom, init_machine_state. cbn [cfg_ms cfg_model].
  rewrite segments_reserved_run_segments. reflexivity.
Qed.

(** (B1) and (B2) ask [vdso_image segs = None]; bridge (A) and this tree's own facts are stated
    over [vdso_text_seg segs = None], which is the stronger and more primitive of the two.
   [c0dd863a:theories/LinuxProcessSem/RiscvSemantics.v:500-508] defines [vdso_image] by a match on [vdso_text_seg], so the
    implication is one rewrite -- but the two names are easy to mistake for each other and the
    top needs exactly this step to feed (A)'s premise to (B1) and (B2). *)
Lemma vdso_image_none_of_no_text : forall segs,
  vdso_text_seg segs = None -> vdso_image segs = None.
Proof. intros segs H. unfold vdso_image. rewrite H. reflexivity. Qed.

(** (B2), the form the top consumes: a derivation over the binary's own start state is one over
    the run's.  Compose with (A) (Common/VdsoBridge.realizes_with_vdso_no_text) FIRST, because
    (A)'s premise [vdso_text_seg segs = None] is false over [run_segments], and with (B1)
    (Common/RunSegTail.realizes_run_segments) LAST, which is generic in the configuration. *)
Theorem realizes_run_init : forall segs inp (sp brk mb : word) pc ph rnd lim T,
  vdso_image segs = None ->
  realizes segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  realizes segs (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp brk mb pc ph rnd lim T Hvi H.
  rewrite init_config_run_segments.
  apply (realizes_wrom segs Hvi _ T H).
  cbn [cfg_ms init_config]. apply seg_rom_run_segments_ext.
Qed.
