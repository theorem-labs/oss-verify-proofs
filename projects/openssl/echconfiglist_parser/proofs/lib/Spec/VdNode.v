(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: new for LPS 727298f3: the vDSO step-layer node vdnode, which stands where evt stops at a libc's indirect call into the vDSO, with its post-state vd_npost and the step soundness, completeness and progress theorems; and LPS 20f40762 (vd_npost's frame write bounded to F bytes, as Run.vdso_post's). *)

(* THE vDSO STEP-LAYER NODE.

   At LPS 75d69e00 [__vdsosym] resolves: [Vdso.vdso_images] has exactly one entry
   (Vdso.v:279), [State.vdso_image_of] picks it by [kb_vdso mod length] so the image is a
   CONSTANT (State.v:3784), and [State.vdso_text_pages_pos] (State.v:3831) gives
   [1 <= vdso_text_pages kb] for every kernel build, so there is no vDSO-less launch to
   fall back on.  That image exports [mkVdsoSym VdsoClockGettime 1460] (Vdso.v:298).  A
   libc that reads the clock therefore performs an INDIRECT CALL into the vDSO, and the
   [Lib/Exec.evt] layer cannot follow it:

     - the machine step cannot fetch there.  [Run.vdso_segments] maps both vDSO segments
       [seg_perms := "r--"] (Run.v:301, :305), and [RiscvSemantics.code_read] gates on
       [x /\ ~w] while [code_read_ov]/[code_read_wx] gate on [x /\ w], so every fetch path
       declines; [RiscvSemantics.fetch_failure] then answers [MachineUnmodeled] at a pc in
       the text before any permission is consulted (RiscvSemantics.v:1170).  That is
       deliberate: LPS never executes vDSO instructions.
     - LPS INTERCEPTS instead, with [Run.sstep_cfg_vdso_call] (Run.v:2244), a constructor
       of a DIFFERENT relation from [RiscvSemantics.step].

   This file is the node that stands where [evt] stops.  It is the vDSO counterpart of
   [Spec/CgNode.v]'s [cgnode], and it is written to be LIFTED INTO OTHER TREES: nothing
   below mentions this harness's binary, its addresses or its names.

   THE DRAW, AND WHY THE NODE IS INDEXED ON IT.  [Vdso.VdsoDraw] (Vdso.v:235) maps the
   call's index, the sixteen caller-saved registers of [Vdso.vdso_caller_saved], the bytes
   of [[sp - F, sp)] and the call's result to what the call leaves behind.  It is NOT
   re-chosen at each call: [Vdso.VdsoRun] (Vdso.v:249) carries it in [State.Model] and the
   run quantifies over it ONCE, at [Vdso.vdso_run_init].  So [Run.vdso_post] is a function
   of the state, the MODEL, the frame and the effect -- and [ITree.npost] is a function of
   the node, the state and the response, with no model in sight, because [ITree.impl] is
   model-free by construction.

   The node closes that gap by carrying the draw and the call count in its own INDEX, and
   discharging them in [nsafe].  That is what [nsafe] is for, and it composes: the node's
   step leaves [with_vdso_bump mo], so the continuation's node carries [N.succ calls] and
   [ITree.tsafe]'s own obligation re-establishes it.  The node's post-condition still
   assumes NOTHING about any drawn register or frame byte -- [d] is an arbitrary
   [VdsoDraw], universally quantified wherever a tree is built.

   WHAT THE NODE CARRIES, AND WHY EACH CONJUNCT IS THERE RATHER THAN A PREMISE OF A
   CONSUMER.  [vdso_entry_fn], [vdso_text_at] and [vdso_frame] all read [find_segment] of
   the segment list they are given, and a walk over a BINARY'S OWN segments has no vDSO
   pair in it at all ([Common/Cfg/RomStable]'s [Hvi : vdso_image segs = None], :129/:440,
   is how every other arm of [sstep_cfg] is discharged there).  So these are facts the
   producer establishes on the run's segment list and hands the node, as conjuncts of the
   definition it builds -- not hypotheses the node's consumers carry.  In particular
   [vd_step] is [RiscvSemantics.step segs ms = MachineUnmodeled]: it is what makes the
   node BLOCK [Lib/Exec.mstep] (which demands [MachineOk]), and it is half of
   [sstep_cfg_vdso_call]'s third premise, the other half being
   [Run.mi_account_step_no_lazy] on a lazy-free model. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
(* Vdso is written unqualified below ([VdsoClockGettime], [VdsoDraw], [vdso_fn_sysno],
   [vdso_caller_saved]).  Require is transitive for LOADING but Import is not, so the
   module must be named here or the reference is not in scope -- the failure
   [lib/AsanInit.v:10-15] records against [vdso_run_init]. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time Require Import PosixTimers.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import MmNodes CgNode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg RelSpec SReach SReachTree.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* The ONE node this file defines: a call to the vDSO's clock_gettime entry.  [tp] is the
   caller's [struct timespec *], the same parameter [CgNode.CGRealtime] carries, and
   deliberately so: the two nodes are the same system call reached two ways.  [d] and
   [calls] are the launch's draw and the index of this call, carried for the reason above
   and asserted of the model by [vd_safe]. *)
Inductive vdnode : Type :=
| VDRealtime (tp : Z) (d : VdsoDraw) (calls : N).

(* The resolved entry, named once, generically.  A producer proves this of the run's
   segment list; [Vdso.vdso_fn_at_off] is what [vdso_entry_fn] consults, so the offset
   1460 of [Vdso.v:298] is what makes it hold at [text base + 1460]. *)
Definition vdso_cgt_entry (segs : list Segment) (a : word) : Prop :=
  vdso_entry_fn segs a = Some VdsoClockGettime.

(* [Run.vdso_post] with the node's own draw and count in place of the model's.  Compare
   Run.v:623-635 (LPS 20f40762): the only difference is that [vdr_draw (m_vdso model)] and
   [vdr_calls (m_vdso model)] are replaced by [d] and [calls].  As there, the frame write
   takes at most the first F bytes of the draw's [vl_frame], from [sp - F] up.
   [vd_npost_eq] below is the statement that they agree whenever [vd_safe] holds, and it
   is the whole of what the indexing buys. *)
Definition vd_npost (segs : list Segment) (n : vdnode) (ms : machine_state) (eff : resp)
    : machine_state :=
  match n with
  | VDRealtime _ d calls =>
      let ra := ms_reg ms 1 in
      let f := vdso_frame segs in
      let lo := (ms_sp ms - Z_to_bv 64 (Z.of_N f))%bv in
      let left := d calls (vdso_read_regs ms)
                    (vdso_read_frame (ms_read_byte ms) lo (N.to_nat f))
                    (eff_ret eff) in
      let ms1 := vdso_write_regs ms vdso_caller_saved (vl_regs left) in
      let ms2 := vdso_with_mem ms1
                   (vdso_write_frame segs (ms_mem ms1) lo (firstn (N.to_nat f) (vl_frame left))) in
      vdso_set_pc (apply_effect ms2 eff) ra
  end.

Section AtNode.
Variable segs : list Segment.

Definition vd_at_node (n : vdnode) (ms : machine_state) : Prop :=
  match n with
  | VDRealtime tp _ _ =>
      (* no pending svc: this is a CALL, not a trap; it is the pc that selects the node *)
      ms_svc_pending ms = None /\
      (* the pc is the resolved entry, and the machine declines to run it *)
      vdso_cgt_entry segs (ms_pc ms) /\
      RiscvSemantics.step segs ms = MachineUnmodeled /\
      (* a0 = CLOCK_REALTIME, a1 = the caller's timespec *)
      areg ms 10 = Z_to_bv 64 0 /\ areg ms 11 = Z_to_bv 64 tp /\
      ms_rom ms = seg_rom segs /\ wr_at segs (ms_mem ms) tp 16 /\ tp + 16 <= TASK_SIZE
  end.

(* THE HAND-OFF, generically.  A state the machine declines is a state [Lib/Exec.mstep]
   cannot leave, so the [evt] layer stops exactly where the node layer starts, and the
   two never both apply.  This is the whole of what [Lib/Exec.v] needs for a vDSO call
   and it is a LEMMA, not a second disjunct in [mstep]'s definition: at a pc in the vDSO
   text [RiscvSemantics.fetch_failure] answers [MachineUnmodeled] before any permission
   is consulted (RiscvSemantics.v:1170), and independently every fetch path declines
   there anyway, because [Run.vdso_segments] maps the text [seg_perms := "r--"]
   (Run.v:301, :305) while [code_read] gates on [x /\ ~w] and [code_read_ov] /
   [code_read_wx] gate on [x /\ w].  Two independent routes to the same fact.

   Stated on [step] rather than on [vdso_entry_fn] deliberately.  Going from "the pc is
   an exported entry" to "the machine declines" would need
   [seg_vdso_text seg = true -> seg_executable seg = false], and [seg_kind] and
   [seg_perms] are INDEPENDENT fields of [MemImageType.Segment] -- that implication holds
   of the segments [Run.vdso_segments] builds and of no others, so it belongs to the
   producer, not here.  The node carries the conclusion as a conjunct instead
   (PREMISE-AS-CONJUNCT). *)
Lemma mstep_not_vdso : forall ms ms',
  RiscvSemantics.step segs ms = MachineUnmodeled -> ~ mstep segs ms ms'.
Proof. intros ms ms' MU HM. exact (mstep_not_unmodeled segs ms ms' HM MU). Qed.

(* The node BLOCKS the [evt] layer, which is what lets the two decompose.  [CgNode] gets
   this from [ms_svc_pending <> None]; here [ms_svc_pending] is [None] and the blocker is
   the pc.  No change to [Lib/Exec.mstep] is needed or made. *)
Lemma vd_at_node_blocked : forall n ms ms', vd_at_node n ms -> ~ mstep segs ms ms'.
Proof.
  intros [tp d calls] ms ms' (_ & _ & ST & _). exact (mstep_not_vdso ms ms' ST).
Qed.

Lemma vd_at_node_no_svc : forall n ms, vd_at_node n ms -> ms_svc_pending ms = None.
Proof. intros [tp d calls] ms (H & _); exact H. Qed.

Lemma vd_at_node_entry : forall n ms, vd_at_node n ms -> vdso_cgt_entry segs (ms_pc ms).
Proof. intros [tp d calls] ms (_ & H & _); exact H. Qed.

Lemma vd_at_node_step : forall n ms,
  vd_at_node n ms -> RiscvSemantics.step segs ms = MachineUnmodeled.
Proof. intros [tp d calls] ms (_ & _ & H & _); exact H. Qed.
End AtNode.

(* The system call the entry stands for.  [Vdso.vdso_fn_sysno] (Vdso.v:121-131) is the
   whole of the mapping, and for clock_gettime it is 113 -- the same number
   [CgNode.cg_at_node] keys on, which is why every number-level fact of [Spec/CgNode.v]
   is reused below rather than restated. *)
Lemma vd_sysno : vdso_fn_sysno VdsoClockGettime = Some 113%Z.
Proof. reflexivity. Qed.

(* pc becomes the OLD ra -- read from [ms] before the draw overwrites x1, which is in
   [vdso_caller_saved] (Vdso.v:219-220).  Both by conversion. *)
Lemma vd_npost_pc : forall segs n ms eff, ms_pc (vd_npost segs n ms eff) = ms_reg ms 1.
Proof. intros segs [tp d calls] ms eff. reflexivity. Qed.

Lemma vd_npost_no_svc : forall segs n ms eff, ms_svc_pending (vd_npost segs n ms eff) = None.
Proof. intros segs [tp d calls] ms eff. reflexivity. Qed.

Definition vd_nstep (n : vdnode) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | VDRealtime tp _ _ =>
      evs = [] /\ mo' = with_vdso_bump mo /\
      exists bs, realtime_ok_b bs = true /\ eff = mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] []
  end.

(* The vDSO's entries cannot halt the process: [Run.vdso_call_unmodeled]'s third disjunct
   (Run.v:639-642) sends a halting outcome to the UNMODELED arm rather than to a call, so
   a node that steps at all does not exit. *)
Definition vd_nexit (n : vdnode) (mo : Model) (code : word) (mo' : Model) : Prop := False.

(* The node's index names the launch's draw and this call's number; [vd_safe] is where
   they are tied to the model.  This is the ONLY place the model's vDSO state is read, and
   it is what makes [vd_npost] -- a function with no model argument -- agree with
   [Run.vdso_post], which has one. *)
Definition vd_safe (n : vdnode) (mo : Model) : Prop :=
  match n with
  | VDRealtime _ d calls =>
      vdr_draw (m_vdso mo) = d /\ vdr_calls (m_vdso mo) = calls
  end.

Lemma vd_npost_eq : forall segs n ms mo eff,
  vd_safe n mo -> vd_npost segs n ms eff = vdso_post segs ms mo (vdso_frame segs) eff.
Proof.
  intros segs [tp d calls] ms mo eff (Hd & Hc).
  unfold vd_npost, vdso_post. rewrite Hd, Hc. reflexivity.
Qed.

Section Sound.
Context {SC : StepCfg} {AF : AllocForced SC}.
Variable segs : list Segment.

#[local] Notation SSTEP := (sstep_cfg segs the_scfg).

(* The node's input, characterised exactly as [CgNode.cg_input] does for the trap route.
   The two differ in ONE place -- where the number comes from.  At a trap it is
   [ms_svc_pending]; here it is [vdso_fn_sysno] of the resolved entry, and
   [Run.sstep_cfg_vdso_call]'s sixth premise reads [sys_input segs ms (Z_to_bv 64 n)] with
   that [n].  Everything downstream of the number is [Spec/CgNode.v]'s, reused. *)
Lemma vd_input : forall tp d calls ms mo,
  vd_at_node segs (VDRealtime tp d calls) ms ->
  bv_unsigned (in_sysno (sys_input segs ms (Z_to_bv 64 113))) = 113
  /\ (exists w, copy_bytes_map (in_wmem (sys_input segs ms (Z_to_bv 64 113))) (Z_to_bv 64 tp) 16 = Some w)
  /\ (forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 113)) mo o <->
        exists bs, realtime_ok_b bs = true /\ o = Ok (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] []) mo []).
Proof.
  intros tp d calls ms mo (_ & _ & _ & A0 & A1 & ROM & WR & TS).
  assert (NO : bv_unsigned (in_sysno (sys_input segs ms (Z_to_bv 64 113))) = 113)
    by (rewrite in_sysno_si; reflexivity).
  assert (C0 : clockid32 (in_arg (sys_input segs ms (Z_to_bv 64 113)) 0) = Z_to_bv 64 0)
    by (rewrite in_a0_si, A0; apply clockid32_realtime).
  assert (C1 : in_arg (sys_input segs ms (Z_to_bv 64 113)) 1 = Z_to_bv 64 tp)
    by (rewrite in_a1_si, A1; reflexivity).
  assert (W : exists w, copy_bytes_map (in_wmem (sys_input segs ms (Z_to_bv 64 113))) (Z_to_bv 64 tp) 16 = Some w).
  { rewrite copy_bytes_map_accepted by (apply access_okb_16; [destruct WR as (T0 & _); exact T0| exact TS]).
    rewrite in_wmem_si. unfold ms_writable_byte. rewrite read_bytes_map_eq.
    pose proof (read_bytes_aux_wr_at segs (ms_mem ms) tp 16 16 WR ltac:(cbn; lia)) as X.
    change (wa tp) with (Z_to_bv 64 tp) in X.
    replace (word_to_nat (Z_to_bv 64 16)) with 16%nat by reflexivity.
    destruct (read_bytes_aux (wview segs (ms_mem ms)) (Z_to_bv 64 tp) 16) as [w|];
      [exists w; reflexivity| exfalso; apply X; reflexivity]. }
  split; [exact NO|]. split; [exact W|].
  intros o. rewrite (syscall_spec_113 _ mo o NO), C0, C1.
  destruct W as [w Hw]. apply (clock_realtime_outcome _ _ mo o w Hw).
Qed.

(* Robustness over a larger read-only backing.  [RomBase.sys_rob] quantifies over a
   PENDING svc, which a vDSO node does not have, so it holds for a reason rather than by
   an argument: this node is not a trap.  That is not a weakening -- the node's call reads
   only the WRITABLE view ([CgNode.clock_realtime_outcome] is a statement about
   [in_wmem]), so it is the same over every backing, exactly as [CgNode.cg_rob] argues for
   the trap route. *)
Lemma vd_rob : forall n ms mo, vd_at_node segs n ms -> sys_rob segs (mkCfg ms mo).
Proof.
  intros n ms mo AT r x8 _ SV. exfalso. cbn [cfg_ms] in SV.
  rewrite (vd_at_node_no_svc segs n ms AT) in SV. discriminate SV.
Qed.

(* THE SOUNDNESS HALF: the node's step IS [Run.sstep_cfg_vdso_call], with its draw.
   Every premise of that constructor is discharged here and none is assumed of a consumer:

     1 m_halted mo = None                         -- the caller's, as for every node
     2 ms_svc_pending ms = None                   -- the node's first conjunct
     3 mi_account_step segs ms mo = MachineUnmodeled
                                                  -- the node's [step] conjunct, lifted to
                                                     the accounting wrapper by
                                                     [Run.mi_account_step_no_lazy] on a
                                                     lazy-free model (Run.v:493)
     4 vdso_entry_fn segs (ms_pc ms) = Some fn    -- the node's [vdso_cgt_entry] conjunct
     5 vdso_fn_sysno fn = Some n                  -- [vd_sysno], by conversion
     6 syscall_spec (sys_input ..) mo (Ok eff mo' evs)
                                                  -- [vd_input]'s characterisation
     7 eff_ret eff <> errno_ret EFAULT            -- the realtime arm returns 0
     8 m_halted mo' = None                        -- the arm leaves the model alone
     9 materialize_model_accesses mo' .. = Some mo''
                                                  -- lazy-free, so materialisation is the
                                                     identity

   The post-state is [vd_npost], which [vd_npost_eq] identifies with [Run.vdso_post] at
   [vdso_frame segs] -- the DRAW over the sixteen caller-saved registers and
   [[sp - vdso_frame segs, sp)].  The node asserts nothing about any of them. *)
Theorem vd_step_sound : forall tp d calls ms mo bs,
  vd_at_node segs (VDRealtime tp d calls) ms ->
  vd_safe (VDRealtime tp d calls) mo ->
  m_halted mo = None ->
  m_vm_lazy mo = [] ->
  realtime_ok_b bs = true ->
  SSTEP (mkCfg ms mo) []
        (SNext (mkCfg (vd_npost segs (VDRealtime tp d calls) ms
                        (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] []))
                      (with_vdso_bump mo))).
Proof.
  intros tp d calls ms mo bs AT SF HH HL HB.
  destruct (vd_input tp d calls ms mo AT) as (NO & _ & SP).
  rewrite (vd_npost_eq segs (VDRealtime tp d calls) ms mo _ SF).
  eapply sstep_cfg_vdso_call with (fn := VdsoClockGettime) (n := 113%Z) (model' := mo).
  - exact HH.
  - exact (vd_at_node_no_svc segs _ ms AT).
  - rewrite (mi_account_step_no_lazy segs ms mo HL).
    rewrite (vd_at_node_step segs _ ms AT). reflexivity.
  - exact (vd_at_node_entry segs _ ms AT).
  - exact vd_sysno.
  - apply SP. exists bs. split; [exact HB| reflexivity].
  - cbn [eff_ret]. intro E. vm_compute in E. discriminate E.
  - exact HH.
  - apply materialize_model_accesses_no_lazy. exact HL.
Qed.

(* THE COMPLETENESS HALF: from a node state, every step of [sstep_cfg] is the call above.
   The three vDSO arms share premises 1-4; the other two are refuted here, so the node is
   neither stuck nor ambiguous.

     - [sstep_cfg_vdso_materialization_fault] needs
       [materialize_model_accesses mo' .. = None], which a lazy-free model refutes;
     - [sstep_cfg_vdso_unmodeled] needs [Run.vdso_call_unmodeled], whose three disjuncts
       are refuted by [vd_sysno], by [vd_input] (the specification answers [Ok], not
       [Unmodeled]) and by [m_halted mo = None] with a return of 0;
     - the three INSTRUCTION arms and [sstep_cfg_instr_unmodeled] need either
       [MachineOk]/[MachineFault], which the node's [step] conjunct refutes, or
       [vdso_entry_fn segs (ms_pc ms) = None], which its entry conjunct refutes.  That
       last pairing is the one [reac-repacer/fuzz_uci Reusable/YK0n.v:152-172] discharges
       in the opposite direction, for a unit with no vDSO call at all.
     - the four SYSCALL arms need [ms_svc_pending ms = Some x8]. *)
Theorem vd_step_complete : forall tp d calls ms mo evs X,
  vd_at_node segs (VDRealtime tp d calls) ms ->
  vd_safe (VDRealtime tp d calls) mo ->
  m_halted mo = None ->
  m_vm_lazy mo = [] ->
  SSTEP (mkCfg ms mo) evs X ->
  exists bs, realtime_ok_b bs = true /\ evs = [] /\
    X = SNext (mkCfg (vd_npost segs (VDRealtime tp d calls) ms
                       (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] []))
                     (with_vdso_bump mo)).
Proof.
  intros tp d calls ms mo evs X AT SF HH HL ST.
  (* The step is destructed with [ms]/[mo] reverted, so each constructor's own binders take the
     names [ms]/[model] and the configuration's equation identifies ours with them. *)
  remember (mkCfg ms mo) as c eqn:Ec. revert ms mo Ec AT SF HH HL.
  destruct ST; intros ms1 mo1 Ec AT SF HH HL; injection Ec as E1 E2; subst ms1 mo1; rename model into mo.
  all: pose proof (vd_at_node_no_svc segs _ ms AT) as SV;
       pose proof (vd_at_node_entry segs _ ms AT) as EN;
       pose proof (vd_at_node_step segs _ ms AT) as MS;
       assert (ACC : mi_account_step segs ms mo = MachineUnmodeled)
         by (rewrite (mi_account_step_no_lazy segs ms mo HL), MS; reflexivity);
       destruct (vd_input tp d calls ms mo AT) as (NO & _ & SP).
  (* instruction arms: the accounting step is [MachineUnmodeled].  The [match goal] patterns in
     this proof name no local variable ([ms], [mo]); naming them made the build report "The
     reference ms was not found" at the pattern. *)
  all: try (exfalso;
            match goal with
            | H : mi_account_step _ _ _ = MachineOk _ |- _ => rewrite ACC in H; discriminate H
            | H : mi_account_step _ _ _ = MachineFault |- _ => rewrite ACC in H; discriminate H
            end).
  (* syscall arms: there is no pending svc *)
  all: try (exfalso; match goal with H : ms_svc_pending _ = Some _ |- _ => rewrite SV in H; discriminate H end).
  (* [sstep_cfg_instr_unmodeled]: the pc IS an entry *)
  all: try (exfalso; match goal with H : vdso_entry_fn _ (ms_pc _) = None |- _ =>
              unfold vdso_cgt_entry in EN; rewrite EN in H; discriminate H end).
  - (* the call *)
    match goal with H : vdso_entry_fn _ (ms_pc _) = Some ?f |- _ =>
      unfold vdso_cgt_entry in EN; rewrite EN in H; injection H as <- end.
    match goal with H : vdso_fn_sysno VdsoClockGettime = Some ?k |- _ =>
      rewrite vd_sysno in H; injection H as <- end.
    match goal with H : syscall_spec _ _ (Ok _ _ _) |- _ =>
      apply SP in H as (bs & HB & E); apply Ok_inj in E as (-> & -> & ->) end.
    rewrite (materialize_model_accesses_no_lazy _ _ HL) in *.
    match goal with H : Some _ = Some ?x |- _ => injection H as <- end.
    exists bs. split; [exact HB|]. split; [reflexivity|].
    rewrite (vd_npost_eq segs (VDRealtime tp d calls) ms mo _ SF). reflexivity.
  - (* materialisation fault: impossible on a lazy-free model *)
    exfalso.
    match goal with H : vdso_entry_fn _ (ms_pc _) = Some ?f |- _ =>
      unfold vdso_cgt_entry in EN; rewrite EN in H; injection H as <- end.
    match goal with H : vdso_fn_sysno VdsoClockGettime = Some ?k |- _ =>
      rewrite vd_sysno in H; injection H as <- end.
    match goal with H : syscall_spec _ _ (Ok _ _ _) |- _ =>
      apply SP in H as (bs & HB & E); apply Ok_inj in E as (-> & -> & ->) end.
    match goal with H : materialize_model_accesses _ _ = None |- _ =>
      rewrite (materialize_model_accesses_no_lazy _ _ HL) in H; discriminate H end.
  - (* unmodeled: all three disjuncts refuted *)
    exfalso.
    match goal with H : vdso_entry_fn _ (ms_pc _) = Some ?f |- _ =>
      unfold vdso_cgt_entry in EN; rewrite EN in H; injection H as <- end.
    match goal with H : vdso_call_unmodeled _ _ _ _ |- _ =>
      destruct H as [HN|[(nn & HN & HU)|(nn & eff & mo' & evs0 & HN & HS & HR)]] end.
    + rewrite vd_sysno in HN. discriminate HN.
    + rewrite vd_sysno in HN. injection HN as <-.
      apply SP in HU as (bs & _ & E). discriminate E.
    + rewrite vd_sysno in HN. injection HN as <-.
      apply SP in HS as (bs & _ & E). apply Ok_inj in E as (-> & -> & ->).
      destruct HR as [HR|HR]; [vm_compute in HR; discriminate HR| exact (HR HH)].
Qed.

(* THE NODE IS NOT STUCK: a draw always exists because the specification always answers.
   [CgNode.realtime_ok_zeros] is the witness, and it is the same witness the trap route
   uses -- the two routes are inhabited together. *)
Theorem vd_progress : forall tp d calls mo,
  exists eff mo' evs, vd_nstep (VDRealtime tp d calls) mo eff mo' evs.
Proof.
  intros tp d calls mo.
  exists (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, repeat (Z_to_bv 8 0) 16)] []),
         (with_vdso_bump mo), [].
  cbn. split; [reflexivity|]. split; [reflexivity|].
  exists (repeat (Z_to_bv 8 0) 16). split; [exact realtime_ok_zeros| reflexivity].
Qed.

(* The step leaves the model unhalted and lazy-free, which is what [mminv] asks and what
   lets the node compose.  [State.with_vdso_bump] rebuilds the VM subsystem's vDSO field
   and nothing else (State.v:5035-5038), so every other component is [mo]'s. *)
Lemma vd_bump_halted : forall mo, m_halted (with_vdso_bump mo) = m_halted mo.
Proof. reflexivity. Qed.

Lemma vd_bump_calls : forall mo,
  vdr_calls (m_vdso (with_vdso_bump mo)) = N.succ (vdr_calls (m_vdso mo)).
Proof. reflexivity. Qed.

Lemma vd_bump_draw : forall mo, vdr_draw (m_vdso (with_vdso_bump mo)) = vdr_draw (m_vdso mo).
Proof. reflexivity. Qed.

(* The node emits no event and cannot exit, so it is silent in [SReachTree]'s sense. *)
Lemma vd_silent : forall n, SReachTree.silent_node vd_nstep vd_nexit n.
Proof.
  intros [tp d calls].
  split; [intros mo code mo' H; exact H| intros mo rsp mo' evs (H & _); exact H].
Qed.
End Sound.
