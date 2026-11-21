(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: adapted from Spec/VdNode.v and LazyCgNode.v for LPS 20f40762: the vDSO call node over a model with lazy reservations (sreach_vd_lazy, the step soundness and completeness on the full state, the restriction of Run.vdso_post) and the frame lemmas of State.with_vdso_bump; the restriction lemmas take that the hidden bytes avoid the walk's segments (LazyRestrict.hid_avoids_segs), and sreach_vd_lazy keeps the lazy view over a list of its own, so that a walk over a binary's segments and the vDSO pair can keep the binary's lazy view. *)

(* THE vDSO CALL NODE OVER A MODEL WITH LAZY RESERVATIONS.

   [Spec/VdNode.v] takes the vDSO call ([Run.sstep_cfg_vdso_call], Run.v:2273-2286) on a model
   with no lazy reservation.  Its [vd_step_sound] and [vd_step_complete] read
   [m_vm_lazy mo = []] in three places:

     - premise 3, [mi_account_step segs ms mo = MachineUnmodeled]: [Run.mi_account_step_no_lazy]
       (Run.v:493-512) turns it into the machine step (VdNode.v:300, :345);
     - premise 9, [materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo'']:
       [materialize_model_accesses_no_lazy] makes it [Some mo'] (VdNode.v:307, :367);
     - the arm [sstep_cfg_vdso_materialization_fault] (Run.v:2287-2297) is refuted by the same
       lemma (VdNode.v:380).

   Here the model has lazy reservations and the reach is the restricted one of [LazySR.v]: the
   state a caller knows is [restrict L S msF], and the model steps the full state [msF].  The
   three places become:

     - premise 3 needs no lazy fact: [mi_account_step] (Run.v:439-449) passes the
       [MachineUnmodeled] of [RiscvSemantics.step_accesses] through, whatever the model
       ([vdl_account_unmodeled]).  It reads the FULL state, and the node's [step] conjunct is
       about the restricted one.  That conjunct does not transfer in general: a load whose bytes
       meet a hidden byte and a vvar byte answers [MachineUnmodeled] on the restricted memory
       ([ov_read_bytes] fails at the hidden byte and [range_meets_vvar] holds,
       RiscvSemantics.v:994-1019) and may read on the full one.  So the full state's step is a
       premise of [sreach_vd_lazy]; a caller proves it as it proves the node's conjunct, from the
       machine declining at the entry pc;
     - premise 9: the call's only charged access is the 16-byte timespec
       ([syscall_effect_accesses], State.v:6892-6894).  The node's [wr_at] on the restricted
       memory keeps it clear of the hidden bytes ([LazyCgNode.wr_at_restrictL]), so
       [LazyRestrict.materialize_restrict] answers [Some] and keeps [lazy_inv], as
       [LazyFdNodes.lzok_after_fd_op] does for a system call;
     - the materialisation-fault arm is refuted by the same lemma.

   The post-state.  [Run.vdso_post] (Run.v:623-635) reads the frame [sp - F, sp), F being
   [vdso_frame segs], through [ms_read_byte]; writes at most the draw's first F bytes there through
   [vdso_write_frame] (Run.v:563-573), which skips each byte the writable view does not map and
   charges nothing (only the effect's accesses are materialised, Run.v:2282-2283); then applies
   the effect.  A hidden byte in that frame would read differently in the two states and could be
   written, so the frame being clear of hidden bytes is the second premise of [sreach_vd_lazy].
   Under the two premises the restriction commutes with [vdso_post] ([vdl_post_restrict]) and the
   post-state keeps every hidden byte ([vdl_post_hidden]).

   The bump.  [State.with_vdso_bump] (State.v:5045-5050) rebuilds [m_vm] with a new [vmst_vdso]
   and every other field copied, so every field [lzok] reads is unchanged ([vdl_lzok_bump]).  It
   is not [LazySR.lzok_vm_frame]'s case: [m_vm] itself changes.

   Nothing below names a binary, an address or a symbol of one unit. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time Require Import PosixTimers.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import MmNodes CgNode VdNode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg RelSpec SReach SReachTree.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict LazySR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require LazyCgNode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma vdl_u64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. exact (wa_unsigned z Hz). Qed.

Section VdLazy.
Variable segs : list Segment.
Context {SC : StepCfg} {AF : AllocForced SC}.

#[local] Notation SSTEP := (sstep_cfg segs the_scfg).

(* The call's effect: a0 = 0 and the 16 bytes of the caller's timespec, as [vd_input] answers. *)
Local Notation VEFF tp bs := (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] []).

(* ------------------------------------------------------------------------------------------
   The accounting: [mi_account_step] (Run.v:439-449) passes [MachineUnmodeled] through.
   ------------------------------------------------------------------------------------------ *)

Lemma vdl_account_unmodeled : forall ms mo,
  RiscvSemantics.step segs ms = MachineUnmodeled -> mi_account_step segs ms mo = MachineUnmodeled.
Proof.
  intros ms mo H. rewrite <- RiscvSemantics.drop_step_accesses in H. unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [r| |]; cbn in H;
    [discriminate H | discriminate H | reflexivity].
Qed.

(* ------------------------------------------------------------------------------------------
   The node of the restricted state, read on the full state.  Every conjunct but [step]
   transfers, and the 16 timespec bytes are visible; [step] is the full state's own premise
   (see the head of this file).
   ------------------------------------------------------------------------------------------ *)

(* [LazyCgNode.wr_at_restrictL] with the hidden bytes avoiding the segments in place of
   [lazy_ranges_okb]: the one fact of it the proof reads ([LazyRestrict.lazy_ranges_ok_avoids]). *)
Lemma vdl_wr_at_restrict : forall L S mF a n,
  hid_avoids_segs segs (hiddenb L S) ->
  wr_at segs (restrict_mem L S mF) a n ->
  wr_at segs mF a n /\ (forall i, (0 <= i < n)%Z -> hiddenb L S (wa (a + i)) = false).
Proof.
  intros L S mF a n HL (H0 & Hn & W).
  assert (X : forall i, (0 <= i < n)%Z -> hiddenb L S (wa (a + i)) = false /\ wview segs mF (wa (a + i)) <> None).
  { intros i Hi. specialize (W i Hi). unfold restrict_mem in W.
    rewrite (wview_restrict segs (hiddenb L S) HL) in W.
    destruct (hiddenb L S (wa (a + i))); [exfalso; apply W; reflexivity| auto]. }
  split; [| intros i Hi; apply (X i Hi)].
  split; [exact H0|]. split; [exact Hn|]. intros i Hi. apply (X i Hi).
Qed.

Lemma vd_at_node_restrictL : forall L S msF tp d calls,
  hid_avoids_segs segs (hiddenb L S) ->
  vd_at_node segs (VDRealtime tp d calls) (restrict L S msF) ->
  RiscvSemantics.step segs msF = MachineUnmodeled ->
  vd_at_node segs (VDRealtime tp d calls) msF
  /\ (forall i, (0 <= i < 16)%Z -> hiddenb L S (wa (tp + i)) = false).
Proof.
  intros L S msF tp d calls HL (SV & EN & _ & A0 & A1 & ROM & WR & TS) ST.
  rewrite ms_mem_restrict in WR.
  destruct (vdl_wr_at_restrict L S (ms_mem msF) tp 16 HL WR) as [WRF VIS].
  split; [| exact VIS].
  unfold vd_at_node.
  exact (conj SV (conj EN (conj ST (conj A0 (conj A1 (conj ROM (conj WRF TS))))))).
Qed.

(* ------------------------------------------------------------------------------------------
   The step on the full state.  Soundness: [Run.sstep_cfg_vdso_call] with every premise
   discharged; the materialisation of the timespec is the caller's premise here, and
   [sreach_vd_lazy] proves it from the restriction.
   ------------------------------------------------------------------------------------------ *)

Theorem vd_step_sound_lazy : forall tp d calls ms mo bs mo'',
  vd_at_node segs (VDRealtime tp d calls) ms ->
  m_halted mo = None ->
  realtime_ok_b bs = true ->
  materialize_model_accesses mo (syscall_effect_accesses (VEFF tp bs)) = Some mo'' ->
  SSTEP (mkCfg ms mo) []
        (SNext (mkCfg (vdso_post segs ms mo (vdso_frame segs) (VEFF tp bs)) (with_vdso_bump mo''))).
Proof.
  intros tp d calls ms mo bs mo'' AT HH HB HM.
  destruct (vd_input segs tp d calls ms mo AT) as (_ & _ & SP).
  eapply sstep_cfg_vdso_call with (fn := VdsoClockGettime) (n := 113%Z) (model' := mo).
  - exact HH.
  - exact (vd_at_node_no_svc segs _ ms AT).
  - exact (vdl_account_unmodeled ms mo (vd_at_node_step segs _ ms AT)).
  - exact (vd_at_node_entry segs _ ms AT).
  - exact vd_sysno.
  - apply SP. exists bs. split; [exact HB| reflexivity].
  - cbn [eff_ret]. intro E. vm_compute in E. discriminate E.
  - exact HH.
  - exact HM.
Qed.

(* Completeness: from a node state whose timespec materialises, every step is the call.  The
   arms are refuted as in [VdNode.vd_step_complete] (VdNode.v:310-393), except the
   materialisation fault, which the materialisation premise refutes in place of
   [m_vm_lazy mo = []]. *)
Theorem vd_step_complete_lazy : forall tp d calls ms mo evs X,
  vd_at_node segs (VDRealtime tp d calls) ms ->
  m_halted mo = None ->
  (forall bs, realtime_ok_b bs = true ->
     materialize_model_accesses mo (syscall_effect_accesses (VEFF tp bs)) <> None) ->
  SSTEP (mkCfg ms mo) evs X ->
  exists bs mo'', realtime_ok_b bs = true /\ evs = [] /\
    materialize_model_accesses mo (syscall_effect_accesses (VEFF tp bs)) = Some mo'' /\
    X = SNext (mkCfg (vdso_post segs ms mo (vdso_frame segs) (VEFF tp bs)) (with_vdso_bump mo'')).
Proof.
  intros tp d calls ms mo evs X AT HH HM ST.
  remember (mkCfg ms mo) as c eqn:Ec. revert ms mo Ec AT HH HM.
  destruct ST; intros ms1 mo1 Ec AT HH HM; injection Ec as E1 E2; subst ms1 mo1; rename model into mo.
  all: pose proof (vd_at_node_no_svc segs _ ms AT) as SV;
       pose proof (vd_at_node_entry segs _ ms AT) as EN;
       pose proof (vdl_account_unmodeled ms mo (vd_at_node_step segs _ ms AT)) as ACC;
       destruct (vd_input segs tp d calls ms mo AT) as (_ & _ & SP).
  (* instruction arms: the accounting step is [MachineUnmodeled] *)
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
    match goal with H : materialize_model_accesses _ _ = Some ?x |- _ =>
      exists bs, x; split; [exact HB|]; split; [reflexivity|]; split; [exact H | reflexivity] end.
  - (* materialisation fault: the timespec materialises *)
    exfalso.
    match goal with H : vdso_entry_fn _ (ms_pc _) = Some ?f |- _ =>
      unfold vdso_cgt_entry in EN; rewrite EN in H; injection H as <- end.
    match goal with H : vdso_fn_sysno VdsoClockGettime = Some ?k |- _ =>
      rewrite vd_sysno in H; injection H as <- end.
    match goal with H : syscall_spec _ _ (Ok _ _ _) |- _ =>
      apply SP in H as (bs & HB & E); apply Ok_inj in E as (-> & -> & ->) end.
    match goal with H : materialize_model_accesses _ _ = None |- _ => exact (HM bs HB H) end.
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

(* ------------------------------------------------------------------------------------------
   The pieces of [Run.vdso_post] (Run.v:525-635) under the restriction.
   ------------------------------------------------------------------------------------------ *)

Lemma vdl_mem_vis : forall L S ms a,
  hiddenb L S a = false -> ms_mem (restrict L S ms) a = ms_mem ms a.
Proof.
  intros L S ms a Ha. rewrite ms_mem_restrict. unfold restrict_mem, restrict_mem_by.
  rewrite Ha. reflexivity.
Qed.

Lemma vdl_wview_vis : forall L S, hid_avoids_segs segs (hiddenb L S) ->
  forall m a, hiddenb L S a = false -> wview segs (restrict_mem L S m) a = wview segs m a.
Proof.
  intros L S HL m a Ha. unfold restrict_mem.
  rewrite (wview_restrict segs (hiddenb L S) HL).
  rewrite Ha. reflexivity.
Qed.

Lemma vdl_rv_mono : forall (h : word -> bool) a n k,
  (k <= n)%nat -> range_visible h a n -> range_visible h a k.
Proof. intros h a n k Hle H. unfold range_visible in *. intros i Hi. apply H. lia. Qed.

(* The frame read, Run.v:547-554. *)
Lemma vdl_vrf_S : forall (m : word -> option byte) (a : word) (n : nat),
  vdso_read_frame m a (S n)
  = (match m a with Some b => b | None => Z_to_bv 8 0 end) :: vdso_read_frame m (a + 1)%bv n.
Proof. intros m a n. reflexivity. Qed.

Lemma vdl_vrf_restrict : forall L S ms n a,
  range_visible (hiddenb L S) a n ->
  vdso_read_frame (ms_read_byte (restrict L S ms)) a n = vdso_read_frame (ms_read_byte ms) a n.
Proof.
  intros L S ms n. induction n as [|n IH]; intros a Hv; [reflexivity|].
  apply range_visible_S in Hv. destruct Hv as [Ha Hv].
  rewrite !vdl_vrf_S. rewrite (IH (a + 1)%bv Hv).
  assert (E : ms_read_byte (restrict L S ms) a = ms_read_byte ms a).
  { unfold ms_read_byte. rewrite (vdl_mem_vis L S ms a Ha). reflexivity. }
  rewrite E. reflexivity.
Qed.

(* The register write, Run.v:533-539. *)
Lemma vdl_vwr_cons : forall ms r rs v vs,
  vdso_write_regs ms (r :: rs) (v :: vs) = vdso_write_regs (set_reg ms (Z_to_bv 5 r) v) rs vs.
Proof. intros ms r rs v vs. reflexivity. Qed.

Lemma vdl_vwr_restrict : forall L S ms rs vs,
  restrict L S (vdso_write_regs ms rs vs) = vdso_write_regs (restrict L S ms) rs vs.
Proof.
  intros L S ms rs. revert ms. induction rs as [|r rs IH]; intros ms vs; [reflexivity|].
  destruct vs as [|v vs]; [reflexivity|].
  rewrite !vdl_vwr_cons. rewrite IH. f_equal.
  unfold set_reg. match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma vdl_vwr_mem : forall ms rs vs, ms_mem (vdso_write_regs ms rs vs) = ms_mem ms.
Proof.
  intros ms rs. revert ms. induction rs as [|r rs IH]; intros ms vs; [reflexivity|].
  destruct vs as [|v vs]; [reflexivity|].
  rewrite vdl_vwr_cons, IH.
  unfold set_reg. match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

(* The frame write, Run.v:563-573. *)
Lemma vdl_vwf_cons : forall m a b rest,
  vdso_write_frame segs m a (b :: rest)
  = vdso_write_frame segs
      (match wview segs m a with
       | Some _ => fun x => if bv_eqb x a then Some b else m x
       | None => m
       end) (a + 1)%bv rest.
Proof. intros m a b rest. reflexivity. Qed.

Lemma vdl_vwf_cons_some : forall m a b rest b0,
  wview segs m a = Some b0 ->
  vdso_write_frame segs m a (b :: rest)
  = vdso_write_frame segs (fun x => if bv_eqb x a then Some b else m x) (a + 1)%bv rest.
Proof. intros m a b rest b0 H. rewrite vdl_vwf_cons, H. reflexivity. Qed.

Lemma vdl_vwf_cons_none : forall m a b rest,
  wview segs m a = None ->
  vdso_write_frame segs m a (b :: rest) = vdso_write_frame segs m (a + 1)%bv rest.
Proof. intros m a b rest H. rewrite vdl_vwf_cons, H. reflexivity. Qed.

Lemma vdl_vwf_restrict : forall L S, hid_avoids_segs segs (hiddenb L S) ->
  forall bs m a, range_visible (hiddenb L S) a (length bs) ->
  vdso_write_frame segs (restrict_mem L S m) a bs = restrict_mem L S (vdso_write_frame segs m a bs).
Proof.
  intros L S HL bs. induction bs as [|b rest IH]; intros m a Hv; [reflexivity|].
  cbn [length] in Hv. apply range_visible_S in Hv. destruct Hv as [Ha Hv].
  destruct (wview segs m a) as [b0|] eqn:Ew.
  - rewrite (vdl_vwf_cons_some (restrict_mem L S m) a b rest b0)
      by (rewrite (vdl_wview_vis L S HL m a Ha); exact Ew).
    rewrite (vdl_vwf_cons_some m a b rest b0 Ew).
    rewrite <- (IH (fun x => if bv_eqb x a then Some b else m x) (a + 1)%bv Hv).
    f_equal. apply functional_extensionality. intros x.
    unfold restrict_mem, restrict_mem_by. cbv beta.
    destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
    unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x. rewrite Ha. reflexivity.
  - rewrite (vdl_vwf_cons_none (restrict_mem L S m) a b rest)
      by (rewrite (vdl_wview_vis L S HL m a Ha); exact Ew).
    rewrite (vdl_vwf_cons_none m a b rest Ew).
    exact (IH m (a + 1)%bv Hv).
Qed.

Lemma vdl_vwf_hidden : forall L S bs m a x,
  range_visible (hiddenb L S) a (length bs) -> hiddenb L S x = true ->
  vdso_write_frame segs m a bs x = m x.
Proof.
  intros L S bs. induction bs as [|b rest IH]; intros m a x Hv Hx; [reflexivity|].
  cbn [length] in Hv. apply range_visible_S in Hv. destruct Hv as [Ha Hv].
  destruct (wview segs m a) as [b0|] eqn:Ew.
  - rewrite (vdl_vwf_cons_some m a b rest b0 Ew).
    rewrite (IH _ (a + 1)%bv x Hv Hx). cbv beta.
    destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
    unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x. congruence.
  - rewrite (vdl_vwf_cons_none m a b rest Ew). exact (IH m (a + 1)%bv x Hv Hx).
Qed.

Lemma vdl_vwf_hidden_firstn : forall L S k (l : list byte) m a x,
  range_visible (hiddenb L S) a k -> hiddenb L S x = true ->
  vdso_write_frame segs m a (firstn k l) x = m x.
Proof.
  intros L S k l m a x Hv Hx. apply (vdl_vwf_hidden L S); [| exact Hx].
  eapply vdl_rv_mono; [apply firstn_le_length | exact Hv].
Qed.

(* The effect, Run.v:176-189, and the two record rebuilds, Run.v:575-588. *)
Lemma vdl_ms_ext : forall X Y : machine_state,
  ms_regs X = ms_regs Y -> ms_fregs X = ms_fregs Y -> ms_pc_val X = ms_pc_val Y ->
  ms_svc_pending X = ms_svc_pending Y -> ms_resv X = ms_resv Y -> ms_fcsr X = ms_fcsr Y ->
  ms_mem X = ms_mem Y -> ms_rom X = ms_rom Y -> X = Y.
Proof.
  intros [r1 f1 p1 s1 v1 c1 m1 o1] [r2 f2 p2 s2 v2 c2 m2 o2]; cbn.
  intros E1 E2 E3 E4 E5 E6 E7 E8. subst. reflexivity.
Qed.

Lemma vdl_apply_mem : forall ms tp bs,
  ms_mem (apply_effect ms (VEFF tp bs)) = write_to_mem (ms_mem ms) (Z_to_bv 64 tp) bs.
Proof. intros ms tp bs. destruct ms; reflexivity. Qed.

Lemma vdl_apply_restrict : forall L S X tp bs,
  range_visible (hiddenb L S) (Z_to_bv 64 tp) (length bs) ->
  restrict L S (apply_effect X (VEFF tp bs)) = apply_effect (restrict L S X) (VEFF tp bs).
Proof.
  intros L S X tp bs Hv.
  apply vdl_ms_ext;
    [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity].
  rewrite ms_mem_restrict, !vdl_apply_mem, ms_mem_restrict. unfold restrict_mem.
  rewrite (write_to_mem_restrict (hiddenb L S) bs (ms_mem X) (Z_to_bv 64 tp) Hv). reflexivity.
Qed.

Lemma vdl_set_pc_restrict : forall L S ms pc,
  restrict L S (vdso_set_pc ms pc) = vdso_set_pc (restrict L S ms) pc.
Proof. intros L S ms pc. destruct ms; reflexivity. Qed.

Lemma vdl_set_pc_mem : forall ms pc, ms_mem (vdso_set_pc ms pc) = ms_mem ms.
Proof. intros ms pc. reflexivity. Qed.

Lemma vdl_with_mem_mem : forall ms m, ms_mem (vdso_with_mem ms m) = m.
Proof. intros ms m. reflexivity. Qed.

(* [Run.vdso_post] with the draw's answer [lv] given: everything after the two reads. *)
Definition vdl_body (ms : machine_state) (f : N) (lv : VdsoLeftovers) (eff : SyscallEffect)
    : machine_state :=
  vdso_set_pc
    (apply_effect
       (vdso_with_mem (vdso_write_regs ms vdso_caller_saved (vl_regs lv))
          (vdso_write_frame segs (ms_mem (vdso_write_regs ms vdso_caller_saved (vl_regs lv)))
             (ms_sp ms - Z_to_bv 64 (Z.of_N f))%bv (firstn (N.to_nat f) (vl_frame lv))))
       eff)
    (ms_reg ms 1).

Lemma vdl_post_body : forall ms mo f eff,
  vdso_post segs ms mo f eff
  = vdl_body ms f
      (vdr_draw (m_vdso mo) (vdr_calls (m_vdso mo)) (vdso_read_regs ms)
         (vdso_read_frame (ms_read_byte ms) (ms_sp ms - Z_to_bv 64 (Z.of_N f))%bv (N.to_nat f))
         (eff_ret eff))
      eff.
Proof. intros ms mo f eff. reflexivity. Qed.

Lemma vdl_body_restrict : forall L S ms f lv tp bs,
  hid_avoids_segs segs (hiddenb L S) ->
  range_visible (hiddenb L S) (ms_sp ms - Z_to_bv 64 (Z.of_N f))%bv
                (length (firstn (N.to_nat f) (vl_frame lv))) ->
  range_visible (hiddenb L S) (Z_to_bv 64 tp) (length bs) ->
  restrict L S (vdl_body ms f lv (VEFF tp bs)) = vdl_body (restrict L S ms) f lv (VEFF tp bs).
Proof.
  intros L S ms f lv tp bs HL Hfr Htp. unfold vdl_body.
  change (ms_sp (restrict L S ms)) with (ms_sp ms).
  change (ms_reg (restrict L S ms) 1) with (ms_reg ms 1).
  rewrite <- (vdl_vwr_restrict L S ms vdso_caller_saved (vl_regs lv)).
  rewrite vdl_set_pc_restrict. f_equal.
  rewrite (vdl_apply_restrict L S _ tp bs Htp). f_equal.
  rewrite ms_mem_restrict.
  rewrite (vdl_vwf_restrict L S HL (firstn (N.to_nat f) (vl_frame lv))
             (ms_mem (vdso_write_regs ms vdso_caller_saved (vl_regs lv)))
             (ms_sp ms - Z_to_bv 64 (Z.of_N f))%bv Hfr).
  reflexivity.
Qed.

(* The restriction commutes with the post-state when the frame and the timespec are visible. *)
Lemma vdl_post_restrict : forall L S msF mo tp bs,
  hid_avoids_segs segs (hiddenb L S) ->
  range_visible (hiddenb L S) (ms_sp msF - Z_to_bv 64 (Z.of_N (vdso_frame segs)))%bv
                (N.to_nat (vdso_frame segs)) ->
  range_visible (hiddenb L S) (Z_to_bv 64 tp) (length bs) ->
  restrict L S (vdso_post segs msF mo (vdso_frame segs) (VEFF tp bs))
  = vdso_post segs (restrict L S msF) mo (vdso_frame segs) (VEFF tp bs).
Proof.
  intros L S msF mo tp bs HL VF VT.
  rewrite !vdl_post_body.
  change (ms_sp (restrict L S msF)) with (ms_sp msF).
  change (vdso_read_regs (restrict L S msF)) with (vdso_read_regs msF).
  rewrite (vdl_vrf_restrict L S msF (N.to_nat (vdso_frame segs))
             (ms_sp msF - Z_to_bv 64 (Z.of_N (vdso_frame segs)))%bv VF).
  apply vdl_body_restrict; [exact HL | | exact VT].
  eapply vdl_rv_mono; [apply firstn_le_length | exact VF].
Qed.

(* The post-state keeps every hidden byte. *)
Lemma vdl_post_hidden : forall L S ms mo tp bs x,
  range_visible (hiddenb L S) (ms_sp ms - Z_to_bv 64 (Z.of_N (vdso_frame segs)))%bv
                (N.to_nat (vdso_frame segs)) ->
  range_visible (hiddenb L S) (Z_to_bv 64 tp) (length bs) ->
  hiddenb L S x = true ->
  ms_mem (vdso_post segs ms mo (vdso_frame segs) (VEFF tp bs)) x = ms_mem ms x.
Proof.
  intros L S ms mo tp bs x VF VT Hx.
  rewrite vdl_post_body. unfold vdl_body.
  rewrite vdl_set_pc_mem, vdl_apply_mem.
  rewrite (write_to_mem_hidden (hiddenb L S) bs _ (Z_to_bv 64 tp) x VT Hx).
  rewrite vdl_with_mem_mem.
  rewrite (vdl_vwf_hidden_firstn L S _ _ _ _ x VF Hx).
  rewrite vdl_vwr_mem. reflexivity.
Qed.

(* ------------------------------------------------------------------------------------------
   The bump.  [State.with_vdso_bump] (State.v:5045-5050) rebuilds [m_vm] from the model's own
   [m_vmmaps], [m_vm_lazy], [m_vm_materialized] and [m_kernel] and a new [vmst_vdso], and keeps
   every other subsystem: each field below is unchanged by conversion.
   ------------------------------------------------------------------------------------------ *)

Lemma vdl_bump_lazy : forall m, m_vm_lazy (with_vdso_bump m) = m_vm_lazy m.
Proof. intros m. reflexivity. Qed.
Lemma vdl_bump_vmmaps : forall m, m_vmmaps (with_vdso_bump m) = m_vmmaps m.
Proof. intros m. reflexivity. Qed.
Lemma vdl_bump_kernel : forall m, m_kernel (with_vdso_bump m) = m_kernel m.
Proof. intros m. reflexivity. Qed.
Lemma vdl_bump_fds : forall m, m_fds (with_vdso_bump m) = m_fds m.
Proof. intros m. reflexivity. Qed.
Lemma vdl_bump_fs : forall m, m_fs (with_vdso_bump m) = m_fs m.
Proof. intros m. reflexivity. Qed.
Lemma vdl_bump_reader : forall m, m_channel_reader (with_vdso_bump m) = m_channel_reader m.
Proof. intros m. reflexivity. Qed.
Lemma vdl_bump_halted : forall m, m_halted (with_vdso_bump m) = m_halted m.
Proof. intros m. reflexivity. Qed.
Lemma vdl_bump_materialized : forall m, m_vm_materialized (with_vdso_bump m) = m_vm_materialized m.
Proof. intros m. reflexivity. Qed.
Lemma vdl_bump_eager : forall m, eager_used (with_vdso_bump m) = eager_used m.
Proof. intros m. reflexivity. Qed.

Lemma vdl_lazy_inv_bump : forall L S m, lazy_inv L S m -> lazy_inv L S (with_vdso_bump m).
Proof.
  intros L S m [Hl Hnd Hincl Hb]. split; [exact Hl | exact Hnd | exact Hincl | exact Hb].
Qed.

Lemma vdl_lzok_bump : forall (sg : list Segment) L S Zr ms m,
  lzok sg L S Zr (mkCfg ms m) -> lzok sg L S Zr (mkCfg ms (with_vdso_bump m)).
Proof.
  intros sg L S Zr ms m [HL Hinv Hh HZ HSZ HZL HLM]. split.
  - exact HL.
  - exact (vdl_lazy_inv_bump L S m Hinv).
  - exact Hh.
  - exact HZ.
  - exact HSZ.
  - exact HZL.
  - exact HLM.
Qed.

Lemma vdl_sbm_bump : forall m m',
  same_but_materialized m m' -> same_but_materialized (with_vdso_bump m) (with_vdso_bump m').
Proof.
  intros m m' H. unfold same_but_materialized in *.
  transitivity (with_vdso_bump (with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m)).
  - exact (f_equal with_vdso_bump H).
  - reflexivity.
Qed.

(* The next call's index: a model the continuation of [sreach_vd_lazy] receives is safe for a
   node with the same draw and the next count. *)
Lemma vd_safe_bump_lazy : forall tp tp' d calls mo mo',
  vd_safe (VDRealtime tp d calls) mo ->
  same_but_materialized (with_vdso_bump mo) mo' ->
  vd_safe (VDRealtime tp' d (N.succ calls)) mo'.
Proof.
  intros tp tp' d calls mo mo' (Hd & Hc) E.
  unfold same_but_materialized in E. rewrite E. subst d calls.
  unfold vd_safe. split; reflexivity.
Qed.

(* ------------------------------------------------------------------------------------------
   THE NODE IN THE RESTRICTED FRAMEWORK, in the shape of [LazyCgNode.sreach_cg_lazy]
   (LazyCgNode.v:57-114).  The two premises beyond the spec's are the full state's step
   (premise 3 of the call reads it) and the frame [sp - F, sp) clear of hidden bytes (the
   frame read and write of [Run.vdso_post] see it); see the head of this file.
   ------------------------------------------------------------------------------------------ *)

(* The lazy view [lzok] is over [segs0], the walk over [segs]; [HL] (the hidden bytes avoid
   [segs]) is what the restriction lemmas read of the walk's list.  With [segs0 = segs] it is
   [lzok_ranges] through [LazyRestrict.lazy_ranges_ok_avoids]. *)
Theorem sreach_vd_lazy : forall (segs0 : list Segment) L S Zr msF1 mo ms tp d calls (Q : config -> Prop),
  hid_avoids_segs segs (hiddenb L S) ->
  lzok segs0 L S Zr (mkCfg msF1 mo) ->
  restrict L S msF1 = ms ->
  vd_at_node segs (VDRealtime tp d calls) ms ->
  vd_safe (VDRealtime tp d calls) mo ->
  RiscvSemantics.step segs msF1 = MachineUnmodeled ->
  range_visible (hiddenb L S) (ms_sp ms - Z_to_bv 64 (Z.of_N (vdso_frame segs)))%bv
                (N.to_nat (vdso_frame segs)) ->
  (forall bs msF' mo', realtime_ok_b bs = true -> length bs = 16%nat ->
      lzok segs0 L S Zr (mkCfg msF' mo') ->
      same_but_materialized (with_vdso_bump mo) mo' ->
      restrict L S msF' = vd_npost segs (VDRealtime tp d calls) ms
                            (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] []) ->
      hid_same L S msF1 msF' ->
      sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF1 mo).
Proof.
  intros segs0 L S Zr msF1 mo ms tp d calls Q HL Hok Hr AT SF STF VF Hk.
  subst ms.
  assert (HH : m_halted mo = None) by exact (lzok_halted Hok).
  destruct (vd_at_node_restrictL L S msF1 tp d calls HL AT STF) as [ATF VIS16].
  pose proof ATF as (_ & _ & _ & _ & _ & _ & WR & _). destruct WR as (T0 & T16 & _).
  assert (VISb : forall bs : list byte, length bs = 16%nat ->
            range_visible (hiddenb L S) (Z_to_bv 64 tp) (length bs)).
  { intros bs Lb i Hi. rewrite Lb in Hi. rewrite wa_add_nat. rewrite (vdl_u64 tp) by lia.
    apply VIS16. lia. }
  assert (RV : forall bs : list byte, length bs = 16%nat ->
            ranges_visible (hiddenb L S) (syscall_effect_accesses (VEFF tp bs))).
  { intros bs Lb. change (syscall_effect_accesses (VEFF tp bs)) with [(Z_to_bv 64 tp, length bs)].
    intros a n Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. exact (VISb bs Lb). }
  assert (MAT : forall bs, realtime_ok_b bs = true -> exists pages,
            materialize_model_accesses mo (syscall_effect_accesses (VEFF tp bs))
              = Some (with_vm_backing (m_vm_lazy mo) pages mo)
            /\ lazy_inv L S (with_vm_backing (m_vm_lazy mo) pages mo)).
  { intros bs Hbs.
    exact (materialize_restrict L S mo _ (lzok_inv Hok) (RV bs (realtime_ok_length bs Hbs))). }
  assert (HNN : forall bs, realtime_ok_b bs = true ->
            materialize_model_accesses mo (syscall_effect_accesses (VEFF tp bs)) <> None).
  { intros bs Hbs E. destruct (MAT bs Hbs) as (pages & Hm & _). rewrite Hm in E. discriminate E. }
  apply sr_step.
  - exact (vd_rob segs _ msF1 mo ATF).
  - destruct (MAT _ realtime_ok_zeros) as (pages0 & Hm0 & _).
    eexists. exact (vd_step_sound_lazy tp d calls msF1 mo _ _ ATF HH realtime_ok_zeros Hm0).
  - intros evs X Hss.
    destruct (vd_step_complete_lazy tp d calls msF1 mo evs X ATF HH HNN Hss)
      as (bs & mo'' & _ & E1 & _ & E2).
    subst evs X. split; [reflexivity | eexists; reflexivity].
  - intros evs c' Hss.
    destruct (vd_step_complete_lazy tp d calls msF1 mo evs (SNext c') ATF HH HNN Hss)
      as (bs & mo'' & Hbs & _ & Hm & E2).
    injection E2 as E3. subst c'.
    destruct (MAT bs Hbs) as (pages & Hm' & Hinv').
    rewrite Hm in Hm'. injection Hm' as Emo. subst mo''.
    pose proof (realtime_ok_length bs Hbs) as Lb.
    assert (HS : hid_same L S msF1 (vdso_post segs msF1 mo (vdso_frame segs) (VEFF tp bs))).
    { intros a Ha. exact (vdl_post_hidden L S msF1 mo tp bs a VF (VISb bs Lb) Ha). }
    apply (Hk bs _ _ Hbs Lb).
    + apply vdl_lzok_bump.
      exact (lzok_lifted segs0 L S Zr msF1 mo _ _ Hok Hinv'
               (same_but_materialized_with_vm_backing mo pages) HS).
    + apply vdl_sbm_bump. apply same_but_materialized_with_vm_backing.
    + rewrite (vdl_post_restrict L S msF1 mo tp bs HL VF (VISb bs Lb)).
      exact (eq_sym (vd_npost_eq segs (VDRealtime tp d calls) (restrict L S msF1) mo _ SF)).
    + exact HS.
Qed.

End VdLazy.
