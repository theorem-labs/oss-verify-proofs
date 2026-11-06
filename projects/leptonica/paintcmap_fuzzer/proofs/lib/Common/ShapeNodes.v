(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  SimInv ExitSim CatSim MmapSim AllocSim PropExec CatExec SeqExec StreamExec StreamSim
  FileSim StoreOk ShapeAlg CfgStep.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From Stdlib Require Finite.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bv_modulus_64 : bv_modulus 64 = 18446744073709551616%Z.
Proof. reflexivity. Qed.
Lemma bv_half_modulus_64 : bv_half_modulus 64 = 9223372036854775808%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma errno_ret_signed_neg : forall e, (1 <= e <= 4095)%Z ->
  (bv_signed (errno_ret e) = - e)%Z.
Proof.
  intros e He. unfold errno_ret.
  rewrite Z_to_bv_signed. apply bv_swrap_small.
  rewrite bv_half_modulus_64. lia.
Qed.

(* [comment removed for export] *)
Lemma errno_ret_unsigned_ge : forall e, (1 <= e <= 4095)%Z ->
  (bv_unsigned (errno_ret e) = 2^64 - e)%Z.
Proof.
  intros e He. rewrite (errno_ret_unsigned e) by lia.
  unfold two_pow_64. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma small_signed_nonneg : forall (w : word) (z : Z),
  w = Z_to_bv 64 z -> (0 <= z < 2^63)%Z -> (bv_signed w = z)%Z.
Proof.
  intros w z -> Hz. rewrite Z_to_bv_signed. apply bv_swrap_small.
  rewrite bv_half_modulus_64. lia.
Qed.

Lemma Z_to_bv_small_unsigned : forall z, (0 <= z < 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. rewrite bv_modulus_64. lia. Qed.

(* [comment removed for export] *)
Lemma len_word_unsigned : forall {A} (l : list A),
  (Z.of_nat (length l) < 2^64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof. intros A l H. unfold len_word. apply Z_to_bv_small_unsigned. lia. Qed.

Lemma len_word_signed : forall {A} (l : list A),
  (Z.of_nat (length l) < 2^63)%Z ->
  bv_signed (len_word l) = Z.of_nat (length l).
Proof. intros A l H. apply (small_signed_nonneg _ _ eq_refl). lia. Qed.

Lemma word_to_nat_len_word : forall {A} (l : list A),
  (Z.of_nat (length l) < 2^64)%Z ->
  word_to_nat (len_word l) = length l.
Proof. intros A l H. unfold word_to_nat. rewrite len_word_unsigned by lia. lia. Qed.

(* [comment removed for export] *)
Lemma fd32_small : forall fd : word, (bv_unsigned fd < 2^32)%Z -> fd32 fd = fd.
Proof. exact fd32_id. Qed.

Lemma fd32_AT_FDCWD : fd32 AT_FDCWD = AT_FDCWD32.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fd32_is_AT_FDCWD32 : forall w : word,
  (bv_unsigned w mod 2^32 = 2^32 - 100)%Z -> fd32 w = AT_FDCWD32.
Proof.
  intros w Hw. unfold AT_FDCWD32, fd32, abi_low32. rewrite Hw.
  apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.

Lemma AT_FDCWD_low32 : (bv_unsigned AT_FDCWD mod 2^32 = 2^32 - 100)%Z.
Proof. unfold AT_FDCWD. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)

Section Generic.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma sstep_sys_inv : forall ms model x8 e st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
                      m_halted m' = None) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
                      m_vm_lazy m' = []) ->
  sstep segs (mkCfg ms model) e st ->
  exists eff m', syscall_spec (sys_input segs ms x8) model (Ok eff m' e)
                 /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m').
Proof.
  intros ms model x8 e st Hh Hsvc Hnu Hnh Hnl Hss.
  inversion Hss; subst;
    match goal with
    | H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1
    | H1 : ms_svc_pending ms = Some ?y |- _ =>
        rewrite Hsvc in H1; injection H1; intro; subst y
    end.
  - (* [comment removed for export] *)
    match goal with
    | Hs : syscall_spec _ _ (Ok _ ?m1 _),
      Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
        rewrite (materialize_model_accesses_no_lazy m1 _ (Hnl _ _ _ Hs)) in Hm;
        injection Hm; intro; subst m2
    end.
    eexists _, _. split; [eassumption | reflexivity].
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | Hs : syscall_spec _ _ (Ok _ ?m1 _),
      Hm : materialize_model_accesses ?m1 _ = None |- _ =>
        rewrite (materialize_model_accesses_no_lazy m1 _ (Hnl _ _ _ Hs)) in Hm;
        discriminate Hm
    end.
  - (* [comment removed for export] *) exfalso.
    match goal with
    | Hs : syscall_spec _ _ (Ok ?eff ?m' ?evs), Hc : m_halted ?m' = Some _ |- _ =>
        rewrite (Hnh _ _ _ Hs) in Hc; discriminate Hc
    end.
  - (* [comment removed for export] *) exfalso.
    match goal with
    | Hs : syscall_spec _ _ (Ok ?eff ?m' ?evs), Hk : m_killed ?m' = Some _ |- _ =>
        rewrite (m_killed_of_m_halted_none _ (Hnh _ _ _ Hs)) in Hk; discriminate Hk
    end.
  - (* [comment removed for export] *) exfalso. apply Hnu. assumption.
Qed.

(* [comment removed for export] *)
Lemma node_sys_u : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) (EV i))) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall i, m_halted (M i) = None) ->
  (forall i, m_vm_lazy (M i) = []) ->
  node_ok_u segs (mkCfg ms model) I EV
          (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)).
Proof.
  intros ms model x8 I E M EV Hh Hsvc Hcomp Hsound Hnu Hnh Hnl. split.
  - intro i. apply (sstep_syscall segs ms model x8 (E i) (M i) (M i) (EV i));
      [exact Hh | exact Hsvc | apply Hcomp | apply Hnh
       | apply materialize_model_accesses_no_lazy; apply Hnl].
  - intros e st Hss.
    assert (Hnh' : forall eff m' evs,
              syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_halted m' = None).
    { intros eff m' evs Hs. destruct (Hsound eff m' evs Hs) as (i & _ & -> & _). apply Hnh. }
    assert (Hnl' : forall eff m' evs,
              syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_vm_lazy m' = []).
    { intros eff m' evs Hs. destruct (Hsound eff m' evs Hs) as (i & _ & -> & _). apply Hnl. }
    destruct (sstep_sys_inv ms model x8 e st Hh Hsvc Hnu Hnh' Hnl' Hss) as (eff & m' & Hs & ->).
    destruct (Hsound eff m' e Hs) as (i & -> & -> & ->).
    exists i. split; reflexivity.
Qed.

Lemma node_sys : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  pending_on segs kit_cfg (mkCfg ms model) ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) (EV i))) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall i, m_halted (M i) = None) ->
  (forall i, m_vm_lazy (M i) = []) ->
  node_ok segs (mkCfg ms model) I EV
          (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)).
Proof.
  intros ms model x8 I E M EV Hh Hsvc Hon Hcomp Hsound Hnu Hnh Hnl.
  apply node_ok_of_u; [exact Hon |].
  exact (node_sys_u ms model x8 I E M EV Hh Hsvc Hcomp Hsound Hnu Hnh Hnl).
Qed.

(* [comment removed for export] *)
Lemma node_sys_chk : forall ms model x8 (chk : SyscallEffect -> check_result) (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  pending_on segs kit_cfg (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall i, chk (E i) = CheckOk (M i) (EV i)) ->
  (forall eff m' evs, chk eff = CheckOk m' evs -> exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall i, m_halted (M i) = None) ->
  (forall i, m_vm_lazy (M i) = []) ->
  node_ok segs (mkCfg ms model) I EV
          (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)).
Proof.
  intros ms model x8 chk I E M EV Hh Hsvc Hon Hchk Hok Hinv Hnu Hnh Hnl.
  apply (node_sys ms model x8 I E M EV Hh Hsvc Hon).
  - intro i. apply check_syscall_ok_iff. rewrite Hchk. apply Hok.
  - intros eff m' evs Hs. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply Hinv. exact Hs.
  - intro Hs.
    pose proof (proj2 (check_syscall_err_iff (sys_input segs ms x8)
                         (mkEffect (Z_to_bv 64 0) [] []) model) Hs) as Hs'.
    rewrite Hchk in Hs'. exact (Hnu _ Hs').
  - exact Hnh.
  - exact Hnl.
Qed.

(* [comment removed for export] *)
Lemma rz_sys_chk : forall ms model x8 (chk : SyscallEffect -> check_result) (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event) (T : I -> TSet) (i0 : I),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  pending_on segs kit_cfg (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall i, chk (E i) = CheckOk (M i) (EV i)) ->
  (forall eff m' evs, chk eff = CheckOk m' evs -> exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall i, m_halted (M i) = None) ->
  (forall i, m_vm_lazy (M i) = []) ->
  (forall i, realizes segs (mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)) (T i)) ->
  realizes segs (mkCfg ms model) (t_alt (fun i => t_emit (EV i) (T i))).
Proof.
  intros ms model x8 chk I E M EV T i0 Hh Hsvc Hon Hchk Hok Hinv Hnu Hnh Hnl Hcont.
  apply (rz_node segs (mkCfg ms model) I EV
           (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)) T i0).
  - eapply node_sys_chk; eassumption.
  - exact Hcont.
Qed.

(* [comment removed for export] *)
Lemma rz_sys_chk_const : forall ms model x8 (chk : SyscallEffect -> check_result) (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (T : TSet) (i0 : I),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  pending_on segs kit_cfg (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall i, chk (E i) = CheckOk (M i) []) ->
  (forall eff m' evs, chk eff = CheckOk m' evs -> exists i, eff = E i /\ m' = M i /\ evs = []) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall i, m_halted (M i) = None) ->
  (forall i, m_vm_lazy (M i) = []) ->
  (forall i, realizes segs (mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)) T) ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 chk I E M T i0 Hh Hsvc Hon Hchk Hok Hinv Hnu Hnh Hnl Hcont.
  eapply rz_conseq.
  - apply (rz_sys_chk ms model x8 chk I E M (fun _ => []) (fun _ => T) i0);
      try eassumption.
  - assert (HT : T []) by (eapply realizes_nonempty; apply (Hcont i0)).
    intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT tr) Hi).
    + intro Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT tr) Htr).
Qed.

(* [comment removed for export] *)
Lemma rz_ret_chk : forall ms model x8 r m' evs T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect r [] []))) m') T ->
  realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
  intros ms model x8 r m' evs T Hh Hsvc Hchk Hh' Hnl' Hcont.
  assert (Hu : node_ok_u segs (mkCfg ms model) unit (fun _ => evs)
                 (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect r [] []))) m')).
  { apply (node_sys_u ms model x8 unit (fun _ => mkEffect r [] []) (fun _ => m') (fun _ => evs) Hh Hsvc).
    - intros []. apply check_syscall_ok_iff. rewrite Hchk. apply check_ret_only_ok_iff. auto.
    - intros eff m2 evs2 Hs. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
      apply check_ret_only_ok_iff in Hs. destruct Hs as (-> & -> & ->). exists tt. auto.
    - intro Hs.
      pose proof (proj2 (check_syscall_err_iff (sys_input segs ms x8)
                           (mkEffect (Z_to_bv 64 0) [] []) model) Hs) as Hs'.
      rewrite Hchk in Hs'. exact (check_ret_only_no_unmodeled _ _ _ _ Hs').
    - intros []. exact Hh'.
    - intros []. exact Hnl'. }
  assert (Hn : node_ok segs (mkCfg ms model) unit (fun _ => evs)
                 (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect r [] []))) m')).
  { refine (node_ok_gen segs (mkCfg ms model) unit unit _ _ (fun x => x) Hu _ _).
    - intros [] (_ & Hr & (y8 & eff' & m2 & evs2 & Hy & Hspec & Hnr)).
      cbn [cfg_ms cfg_model] in *. rewrite Hsvc in Hy. injection Hy as <-.
      apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
      apply check_ret_only_ok_iff in Hspec. destruct Hspec as (-> & _ & _).
      rewrite (child_refusal_b_syscall segs ms model x8 _ m' Hsvc Hh') in Hr.
      rewrite Hr in Hnr. discriminate Hnr.
    - intros [] _. exists tt. split; reflexivity. }
  eapply rz_conseq.
  - apply (rz_node segs (mkCfg ms model) unit (fun _ => evs) _ (fun _ => T) tt Hn).
    intros []. exact Hcont.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
Lemma rz_ret_chk_silent : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect r [] []))) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hnl' Hcont.
  eapply rz_conseq; [eapply rz_ret_chk; eassumption|].
  apply t_emit_nil_eq. eapply realizes_nonempty. exact Hcont.
Qed.

End Generic.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma arg_reg_3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg).
Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg).
Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg).
Proof. apply bv_eq. reflexivity. Qed.

Section EcallState.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition ecall_st (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := Some (getr regs 17);
     ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.

Lemma step_ecall_st : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (ecall_st regs pc mem rom).
Proof. intros. eapply step_ecall; eassumption. Qed.

Lemma ecall_st_svc : forall regs pc mem rom,
  ms_svc_pending (ecall_st regs pc mem rom) = Some (getr regs 17).
Proof. reflexivity. Qed.
Lemma ecall_st_mem : forall regs pc mem rom, ms_mem (ecall_st regs pc mem rom) = mem.
Proof. reflexivity. Qed.
Lemma ecall_st_rom : forall regs pc mem rom, ms_rom (ecall_st regs pc mem rom) = rom.
Proof. reflexivity. Qed.
Lemma ecall_st_pc : forall regs pc mem rom, ms_pc (ecall_st regs pc mem rom) = pc.
Proof. reflexivity. Qed.

Lemma ecall_st_gpr0 : forall regs pc mem rom, ms_gpr (ecall_st regs pc mem rom) 0 = getr regs 10.
Proof. intros. unfold ecall_st. rewrite record_gpr, arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ecall_st_gpr1 : forall regs pc mem rom, ms_gpr (ecall_st regs pc mem rom) 1 = getr regs 11.
Proof. intros. unfold ecall_st. rewrite record_gpr, arg_reg_1. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ecall_st_gpr2 : forall regs pc mem rom, ms_gpr (ecall_st regs pc mem rom) 2 = getr regs 12.
Proof. intros. unfold ecall_st. rewrite record_gpr, arg_reg_2. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ecall_st_gpr3 : forall regs pc mem rom, ms_gpr (ecall_st regs pc mem rom) 3 = getr regs 13.
Proof. intros. unfold ecall_st. rewrite record_gpr, arg_reg_3. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ecall_st_gpr4 : forall regs pc mem rom, ms_gpr (ecall_st regs pc mem rom) 4 = getr regs 14.
Proof. intros. unfold ecall_st. rewrite record_gpr, arg_reg_4. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ecall_st_gpr5 : forall regs pc mem rom, ms_gpr (ecall_st regs pc mem rom) 5 = getr regs 15.
Proof. intros. unfold ecall_st. rewrite record_gpr, arg_reg_5. symmetry. apply getr_nz. reg_neq_tac. Qed.

(* [comment removed for export] *)
Lemma ecall_st_read_byte : forall segs regs pc mem,
  ms_read_byte (ecall_st regs pc mem (seg_rom segs)) = mrb segs mem.
Proof. reflexivity. Qed.

Lemma ecall_st_read_bytes : forall segs regs pc mem a n,
  ms_read_bytes (ecall_st regs pc mem (seg_rom segs)) a n = rdn segs mem a (word_to_nat n).
Proof. intros. apply ms_read_bytes_rdn. reflexivity. Qed.

Lemma ecall_st_writable : forall segs regs pc mem rom,
  ms_writable_byte segs (ecall_st regs pc mem rom) = wview segs mem.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma adv_ret_st : forall regs pc mem rom r,
  advance_past_svc (apply_effect (ecall_st regs pc mem rom) (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold ecall_st. apply adv_eff_ret. Qed.

Lemma adv_setgpr0_st : forall regs pc mem rom r,
  advance_past_svc (set_gpr0 (ecall_st regs pc mem rom) r)
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold ecall_st. apply adv_set. Qed.

Lemma adv_write_st : forall regs pc mem rom r buf data,
  advance_past_svc (apply_effect (ecall_st regs pc mem rom) (mkEffect r [(buf, data)] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof. intros. unfold ecall_st. apply adv_apply_write. Qed.

Lemma adv_delivered_st : forall regs pc mem rom r buf data,
  advance_past_svc (apply_effect (ecall_st regs pc mem rom)
                      (mkEffect r (delivered_writes buf data) []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof. intros. unfold ecall_st. apply adv_apply_delivered. Qed.

Lemma adv_grant_st : forall regs pc mem rom a n,
  advance_past_svc (apply_effect (ecall_st regs pc mem rom) (mkEffect a [] [(a, n)]))
  = mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom.
Proof. intros. unfold ecall_st. apply adv_mmap_grant. Qed.

(* [comment removed for export] *)
Lemma write_to_mem_wbytes : forall data mem a,
  write_to_mem mem a data = wbytes mem a data.
Proof. induction data as [|b data IH]; intros mem a; [reflexivity|]. cbn. apply IH. Qed.

(* [comment removed for export] *)
Lemma rz_ecall : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (ecall_st regs pc mem rom) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs regs pc mem rom model w T Hh Hlazy Hf He Hc.
  eapply rz_step; [exact Hh | exact Hlazy | reflexivity
                  | eapply step_ecall_st; eassumption | exact Hc].
Qed.

End EcallState.
