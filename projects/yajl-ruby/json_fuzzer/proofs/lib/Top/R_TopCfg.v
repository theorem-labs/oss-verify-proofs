(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Exec Step ITree ITreeCfg Nodes NodesCfg Decode RegsEquiv RegsEquivCfg InitMem RunInit Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg TrzNodesCfg TrzStdioCfg SpecT GlueCfg RunInitCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Malloc RawAlloc KArena MSuccIface MSuccRaw.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocKown.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import R_StartupLib R_Startup RMallocRep RMalloc_iface RMalloc_ifaceP RAlloc_rz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rc_of (en : ExecEntry) : RunCeiling :=
  {| rc_sp := bv_unsigned (en_sp en);
     rc_guard := guard_of (at_random_bytes (ed_random (en_draw en)));
     rc_secret := bv_unsigned (secret_of (at_random_bytes (ed_random (en_draw en))));
     rc_secret_range := bv_unsigned_in_range 64 _ |}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma t_die_nil : forall msg fs, t_die msg fs []. Proof. intros. apply t_emit_has_nil. Qed.
Lemma t_alt2_nil_l : forall A B, A [] -> t_alt2 A B []. Proof. intros A B H. left. exact H. Qed.

Lemma spec_nil : forall argv fs, spec argv fs [].
Proof.
  intros argv fs. unfold spec.
  destruct argv as [|a0 [|path [|x l]]]; try apply t_die_nil.
  destruct (4096 <=? length path)%nat; [apply t_die_nil|].
  destruct (list_byte_eqb path []); [apply t_die_nil|].
  destruct (list_byte_eqb path dot_path); [apply t_alt2_nil_l, t_die_nil|].
  destruct (fs_lookup fs path); [apply t_alt2_nil_l, t_die_nil | apply t_die_nil].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithRC.
Context {RC__ : RunCeiling}.

Local Notation leafC := (ImplRzCfg.leaf (nstep_cfg acfg)).

(* [comment removed for export] *)
Lemma mo0_set_tid_leaf_cfg : forall lim en inp (r : exc Z) mo',
  bv_unsigned (en_sp en) = rc_sp -> valid_sp (en_sp en) ->
  leafC (enode NSetTid dec_set_tid) (mo0 rsegs lim en inp) r mo' ->
  exists t, 0 < t < PID_MAX_ENVELOPE /\ r = Ok t /\ mo' = with_tid (Z_to_bv 64 t) (mo0 rsegs lim en inp).
Proof.
  intros lim en inp r mo' Hsp Vsp H. unfold enode in H. inversion H; subst.
  match goal with Hn : nstep_cfg _ _ _ ?rsp _ _, Hl : ImplRzCfg.leaf _ _ _ _ _ |- _ =>
    destruct (nstep_dec_set_tid _ _ _ _ (mo0_minv rsegs lim en inp Hsp Vsp) (nstep_cfg_sub _ _ _ _ _ _ Hn)) as (_ & t & D & Ht & Hmo);
    rewrite D in Hl; apply ImplRzCfg.leaf_ret_inv in Hl as [-> ->]; exists t end.
  rewrite mo0_tid in Hmo. destruct Hmo as [[? _] | [_ ->]]; [discriminate|]. auto.
Qed.

Lemma trz_startup_set_tid_cfg : forall lim en inp (T : TSet),
  bv_unsigned (en_sp en) = rc_sp -> valid_sp (en_sp en) -> T [] ->
  trz node (nstep_cfg acfg) nexit minv nsafe (enode NSetTid dec_set_tid) (mo0 rsegs lim en inp) (fun (_ : exc Z) _ => T) T.
Proof.
  intros lim en inp T Hsp Vsp HT. unfold enode.
  apply (trz_vis_silent node (nstep_cfg acfg) nexit minv nsafe NSetTid _ (mo0 rsegs lim en inp) (fun _ _ => T) T (mo0_minv _ _ _ _ Hsp Vsp) I).
  - exists (eff0 (Z_to_bv 64 1)), (with_tid (Z_to_bv 64 1) (mo0 rsegs lim en inp)), []. cbn [nstep_cfg node_off alloc_only_cfg sc_alloc sc_fs negb nstep].
    split; [reflexivity|]. exists (Z_to_bv 64 1). split; [reflexivity|]. rewrite mo0_tid.
    split; [| reflexivity]. unfold PID_MAX_ENVELOPE. rewrite unsigned_lit by lia. lia.
  - intros rsp mo' evs H. destruct (nstep_dec_set_tid _ _ _ _ (mo0_minv rsegs lim en inp Hsp Vsp) (nstep_cfg_sub _ _ _ _ _ _ H)) as (-> & t & D & _ & _).
    rewrite D. split; [reflexivity | apply trz_ret].
  - intros code mo' H. exact H.
  - exact HT.
Qed.
End WithRC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithRC2.
Context {RC__ : RunCeiling}.
Lemma rsegs_rcost : rcost (segments_reserved rsegs) <= RCMAXc.
Proof. vm_compute. discriminate. Qed.
Lemma rsegs_top_pos : 0 < reserved_top (segments_reserved rsegs).
Proof. vm_compute. reflexivity. Qed.
Lemma rsegs_top_ceiling : reserved_top (segments_reserved rsegs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling.
Proof.
  pose proof alloc_ceiling_ge_min as G. unfold sp_window_lo, stack_max_size in G.
  assert (reserved_top (segments_reserved rsegs) + brk_aslr_max + 4 * PGSZ <= 0x7fff7f800000) by (vm_compute; discriminate). lia.
Qed.
End WithRC2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition G_fs (FS : Fs.Fs) : PState -> Model -> Prop := fun _ mo => m_fs mo = FS.
Section WithRC3.
Context {RC__ : RunCeiling}.
Definition ps0 : PState := ps_init (reservedZ rsegs).
End WithRC3.

Section R_TopCfg.

  (* [comment removed for export] *)
  Variable DRV : Model -> Fs.Fs -> list (list byte) -> TSet.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis DRV_SPEC : forall (fs : Fs.Fs) (MO : Model) (argv : list (list byte)),
    m_fs MO = fs -> valid_argv argv -> t_eq (DRV MO fs argv) (spec argv fs).

  (* [comment removed for export] *)
  Hypothesis RZ_MAIN_DRV : forall (RC__ : RunCeiling) (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw),
    valid_sp sp0 -> rc_sp = bv_unsigned sp0 -> rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))) ->
    entry_stack_fits sp0 argv envp -> valid_argv argv -> valid_envp envp ->
    forall (FS0 : Fs.Fs) (MO : Model),
    m_fs MO = FS0 -> alloc_fd (m_fds MO) = Z_to_bv 64 3 -> fd_lookup (m_fds MO) (Z_to_bv 64 3) = None ->
    m_halted MO = None -> m_vm_lazy MO = [] ->
    (forall m : mem,
      (forall a : word, 0x55040 <= bv_unsigned a < 0x553f0 -> m a = None) ->
      rw_cells rsegs m 0x54fd0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] ->
      rw_cells rsegs m 0x54fd8 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
      rw_cells rsegs m 0x23928 [C8 (Z_to_bv 64 0x54fb0)] ->
      rw_cells rsegs m 0x54fb0 [C8 rc_guard] ->
      mem_inv rsegs m ->
      RHKG (G_fs FS0) ps0 [] m MO /\ rw_cells rsegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))]) ->
    forall ms, rat_main sp0 argv envp uid hw rnd ms -> realizes_cfg acfg rsegs (mkCfg ms MO) (DRV MO FS0 argv).

  (* [comment removed for export] *)
  Lemma main_rz : forall (lim : Z), VMINc <= lim -> forall (en : ExecEntry) (inp : ProcInput) (tw : word) (ms : machine_state),
    let RC := rc_of en in
    valid_entry (mkImage rsegs r_init_pc r_phdrs) en inp -> valid_input inp ->
    0 < bv_unsigned tw < PID_MAX_ENVELOPE ->
    rat_main (RC__:=RC) (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) ms ->
    realizes_cfg acfg rsegs (mkCfg ms (with_tid tw (mo0 rsegs lim en inp)))
                 (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros lim HLIM en inp tw ms RC VE VI Ht AM.
    destruct (valid_entry_unpack _ _ _ _ _ VE VI) as (VSP & VBRK & _ & EFIT).
    destruct (valid_input_unpack _ VI) as (VA & VEN & _ & _).
    assert (Hsp : bv_unsigned (en_sp en) = rc_sp) by reflexivity.
    assert (Hspw : sp_window_lo <= rc_sp <= sp_window_hi) by (destruct VSP as (L & H & _); cbn; split; assumption).
    set (MO := with_tid tw (mo0 rsegs lim en inp)).
    assert (MOFS : m_fs MO = in_fs inp) by reflexivity.
    eapply rz_conseq_cfg; [| apply (DRV_SPEC (in_fs inp) MO (in_argv inp) MOFS VA)].
    apply (RZ_MAIN_DRV RC (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) VSP (eq_sym Hsp) eq_refl EFIT VA VEN (in_fs inp) MO MOFS);
      [reflexivity| reflexivity| reflexivity| reflexivity| | exact AM].
    intros m NONE LC LC2 GOT GUARD MI.
    destruct (RHEAP_init_proof m _ NONE LC LC2 GOT GUARD MI) as [HR AUXC]. split; [| exact AUXC].
    split; [exact HR|]. split.
    - (* [comment removed for export] *)
      unfold MO, mo0. apply (KOWN_with_tid GTrue (G_fs (in_fs inp))); [exact Ht| | intros _; reflexivity].
      apply KOWN_init; [exact Hsp| exact Hspw| exact VBRK| apply rsegs_top_pos| apply rsegs_top_ceiling| exact I].
    - (* [comment removed for export] *)
      unfold MO, mo0. change (map sigb []) with (@nil (bptr * Z)).
      apply HEADc_init_lim; [exact Hsp| exact Hspw| exact VBRK| apply rsegs_top_pos| apply rsegs_top_ceiling| exact HLIM| apply rsegs_rcost| exact Ht].
  Qed.

  Theorem R_realizes_cfg_lim : forall (lim : Z), VMINc <= lim -> forall en inp,
    valid_entry (mkImage rsegs r_init_pc r_phdrs) en inp -> valid_input inp ->
    realizes_cfg acfg rsegs (mkCfg (ms0 rsegs r_init_pc r_phdrs en inp) (mo0 rsegs lim en inp))
                 (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros lim HLIM en inp VE VI.
    pose (RC := rc_of en).
    destruct (valid_entry_unpack _ _ _ _ _ VE VI) as (VSP & _ & _ & _).
    destruct (valid_input_unpack _ VI) as (VA & VEN & _ & _).
    assert (Hsp : bv_unsigned (en_sp en) = rc_sp) by reflexivity.
    assert (RCG : rc_guard = guard_of (at_random_bytes (ed_random (en_draw en)))) by reflexivity.
    change (ms0 rsegs r_init_pc r_phdrs en inp)
      with (init_ms rsegs r_init_pc r_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)).
    apply (impl_trz_realizes_leaf_cfg acfg node rsegs (at_node rsegs) (nstep_cfg acfg) nexit minv nsafe (nodes_sound_cfg acfg rsegs)
             (enode NSetTid dec_set_tid)
             (epost (fun _ => rat_main (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)))
             _ (mo0 rsegs lim en inp) (fun _ _ => spec (in_argv inp) (in_fs inp)) _
             (rstartup_spec (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) VSP VA VEN RCG)
             (trz_startup_set_tid_cfg _ _ _ _ Hsp VSP (spec_nil _ _)) (mo0_not_halted _ _ _ _) (mo0_minv _ _ _ _ Hsp VSP)).
    intros [|t] ms' mo' HQ L Hh Hmi.
    - destruct (mo0_set_tid_leaf_cfg _ _ _ _ _ Hsp VSP L) as (t & _ & E & _). discriminate.
    - destruct (mo0_set_tid_leaf_cfg _ _ _ _ _ Hsp VSP L) as (t' & Ht & E & ->). cbn in HQ.
      apply (main_rz lim HLIM en inp (Z_to_bv 64 t') ms' VE VI); [rewrite unsigned_lit; unfold PID_MAX_ENVELOPE in *; lia | exact HQ].
  Qed.

  (* [comment removed for export] *)
  Theorem R_realizes_cfg : forall en inp,
    valid_entry (mkImage rsegs r_init_pc r_phdrs) en inp -> valid_input inp ->
    realizes_cfg acfg rsegs (mkCfg (ms0 rsegs r_init_pc r_phdrs en inp) (mo0 rsegs source_alloc_limit en inp))
                 (spec (in_argv inp) (in_fs inp)).
  Proof. exact (R_realizes_cfg_lim source_alloc_limit VMINc_le_source). Qed.

  Theorem R_realizes_spec_cfg_lim : forall (lim : Z), VMINc <= lim ->
    realizes_spec_cfg acfg rsegs r_init_pc r_phdrs lim (fun inp => spec (in_argv inp) (in_fs inp)).
  Proof. intros lim HLIM. apply realizes_spec_cfg_of_ms0. exact (R_realizes_cfg_lim lim HLIM). Qed.

  Theorem R_realizes_spec_cfg :
    realizes_spec_cfg acfg rsegs r_init_pc r_phdrs source_alloc_limit (fun inp => spec (in_argv inp) (in_fs inp)).
  Proof. exact (R_realizes_spec_cfg_lim source_alloc_limit VMINc_le_source). Qed.

End R_TopCfg.
