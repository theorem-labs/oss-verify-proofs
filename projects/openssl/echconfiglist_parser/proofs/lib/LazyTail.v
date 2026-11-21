(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (RomBase.sys_rob robustness premises on the fd, openat, ioctl and writev nodes; the channel-reader premise on writev; C-string path reads bounded below TASK_SIZE; copy_iovecs_accesses now lists each iovec entry's own access). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/LazyFdNodes.v; 242 of its 396 lines of code are new or changed and 987 lines of the source are left out; taken from projects/openssl/echconfiglist_parser/proofs/lib/LazyFdNodes.v, lines 7-25, 41-85, 117-167, 205-266, 360-417, 960-961 and 1231-1262, as in the LPS 727298f3 update. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the lazy-reservation walk lemmas of LazyRestrictAlg.v,
   As/AsLazyRun.v, As/AsPrintfFirst.v and LazyFdNodes.v, restated for a walk over a binary's
   segment list [segs] followed by a [tail] that is neither executable nor writable (the launch's
   vDSO pair).  The lazy view [lzok] stays over [segs]; the walk is over [segs ++ tail]; the
   restricted states of the system-call lemmas carry the read-only backing [seg_rom (segs ++ tail)];
   a step invariant [I] is carried from the start configuration to every continuation. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  Scfg SimInv ExitSim PropExec CatExec CatSim MmapSim AllocSim FileSim RelSpec
  ShapeAlg Nodes AgentLib AgentNodes Gap04 RefNodes RefNodesDir Hoare LibWritev SReach
  SymExec SymExec2 SymExec2Sound SymRun
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazyLedger LazySR LazyNodes LazyFdNodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require RomBase RomWrite RomStable RunTail.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* The read-only backing is not part of the lazy view: [lzok] reads only the overlay. *)
Lemma lzok_wrom : forall segs L S Zr ms mo r,
  lzok segs L S Zr (mkCfg ms mo) -> lzok segs L S Zr (mkCfg (RomBase.wrom ms r) mo).
Proof.
  intros segs L S Zr ms mo r Hok. destruct Hok as [HL Hinv Hh HZ HSZ HZL HLM].
  constructor; [exact HL | exact Hinv | exact Hh | | exact HSZ | exact HZL | exact HLM].
  intros a Ha Hz. exact (HZ a Ha Hz).
Qed.

Lemma restrict_wrom : forall L S ms r, restrict L S (RomBase.wrom ms r) = RomBase.wrom (restrict L S ms) r.
Proof. intros L S ms r. destruct ms; reflexivity. Qed.

Lemma ms_rom_restrict : forall L S ms, ms_rom (restrict L S ms) = ms_rom ms.
Proof. intros L S ms. reflexivity. Qed.

(* no machine step reads the backing (Common/Cfg/RunTail.v:38, [step_wrom]) *)
Lemma msteps_wrom : forall segs ms ms' r,
  CatSim.msteps segs ms ms' -> CatSim.msteps segs (RomBase.wrom ms r) (RomBase.wrom ms' r).
Proof.
  intros segs ms ms' r H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH].
  - apply mst_refl.
  - eapply mst_step; [exact Hsvc | exact (RunTail.step_wrom segs ms ms1 r Hstep) | exact IH].
Qed.

(* LazyFdNodes.v:194, restated here for any backing *)
Lemma ltl_gpr_of_restrict_epend : forall L S msF1 regs pc mem rom x8 k,
  restrict L S msF1 = epend regs pc mem rom x8 -> ms_gpr msF1 k = ms_gpr (epend regs pc mem rom x8) k.
Proof.
  intros L S msF1 regs pc mem rom x8 k Hr. unfold ms_gpr.
  replace (ms_regs msF1) with (ms_regs (restrict L S msF1)) by reflexivity. rewrite Hr. reflexivity.
Qed.

Section LazyTail.
Variables segs tail : list Segment.
Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
Context {SC : StepCfg}.
Variable I : config -> Prop.
Hypothesis HI : forall c evs c', I c -> sstep_cfg (segs ++ tail) the_scfg c evs (SNext c') -> I c'.
(* every lemma below: `Proof using Hnx Hnw HI.`, so its arguments are exactly
   segs tail Hnx Hnw {SC} I HI, then its own binders *)

(* the tail is not executable, so an instruction fetch reads the same (Common/Cfg/RomStable.v:306) *)
Lemma ltl_fetch : forall a, fetch_word (segs ++ tail) a = fetch_word segs a.
Proof using Hnx Hnw HI.
  intros a. apply RomStable.fetch_word_app_nx; first [exact Hnx | exact Hnw].
Qed.

(* the tail is not writable, so a system call's input is the same (Common/Cfg/RomStable.v:433) *)
Lemma ltl_sys_input : forall ms x8, sys_input (segs ++ tail) ms x8 = sys_input segs ms x8.
Proof using Hnx Hnw HI.
  intros ms x8. apply RomStable.sys_input_app_nw; first [exact Hnw | exact Hnx].
Qed.

(* Common/Cfg/RomStable.v:503 [sys_rob_app_tail], by [ltl_sys_input] *)
Lemma ltl_sys_rob : forall c, RomBase.sys_rob segs c -> RomBase.sys_rob (segs ++ tail) c.
Proof using Hnx Hnw HI.
  intros c H r x8 Hr Hs o. rewrite !ltl_sys_input. exact (H r x8 Hr Hs o).
Qed.

Lemma dsteps_app_tail : forall c c', dsteps segs c c' -> dsteps (segs ++ tail) c c'.
Proof using Hnx Hnw HI.
  intros c c' H. induction H as [c | ms model ms' model' c3 Hh Hsvc Hacc H IH].
  - apply ds_refl.
  - eapply ds_step; [exact Hh | exact Hsvc | | exact IH].
    eapply RomStable.mi_account_step_app_nx; first [exact Hnx | exact Hnw | exact Hacc].
Qed.

(* each silent step is a node over the joined list (LazyRestrictAlg.v:20, [node_account]) *)
Lemma dsteps_inv : forall c c', dsteps (segs ++ tail) c c' -> I c -> I c'.
Proof using Hnx Hnw HI.
  intros c c' H. induction H as [c | ms model ms' model' c3 Hh Hsvc Hacc H IH]; intros Hc; [exact Hc|].
  apply IH. apply (HI (mkCfg ms model) [] (mkCfg ms' model') Hc).
  exact (proj1 (node_account (segs ++ tail) ms model ms' model' Hh Hsvc Hacc) tt).
Qed.

(* As/AsLazyRun.v:19, with the walk over the joined list *)
Theorem rz_msteps_lazy_tail : forall L S Zr msF ms1 mo T,
  lzok segs L S Zr (mkCfg msF mo) -> I (mkCfg msF mo) ->
  msteps segs (restrict L S msF) ms1 ->
  (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = ms1 -> I (mkCfg msF' mo') -> realizes (segs ++ tail) (mkCfg msF' mo') T) ->
  realizes (segs ++ tail) (mkCfg msF mo) T.
Proof using Hnx Hnw HI.
  intros L S Zr msF ms1 mo T Hok HIc Hms Hk.
  destruct (msteps_restrict segs L S (lzok_ranges Hok) msF ms1 mo (lzok_inv Hok) (lzok_halted Hok) Hms)
    as (mo' & Hd & Hinv' & Hsame & Hh' & Hrestr).
  pose proof (dsteps_app_tail _ _ Hd) as Hd'.
  eapply rz_dsteps; [exact Hd'|].
  apply Hk; [| exact Hsame | apply hid_same_unrestrict | exact Hrestr | exact (dsteps_inv _ _ Hd' HIc)].
  eapply lzok_lifted; [exact Hok | exact Hinv' | exact Hsame | apply hid_same_unrestrict].
Qed.

(* As/AsLazyRun.v:39, with the walk over the joined list *)
Corollary rz_msteps_lazy_mkst_tail : forall L S Zr msF regs pc mem rom regs' pc' mem' mo T,
  lzok segs L S Zr (mkCfg msF mo) -> I (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem rom ->
  msteps segs (mkst regs pc mem rom) (mkst regs' pc' mem' rom) ->
  (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst regs' pc' mem' rom -> I (mkCfg msF' mo') -> realizes (segs ++ tail) (mkCfg msF' mo') T) ->
  realizes (segs ++ tail) (mkCfg msF mo) T.
Proof using Hnx Hnw HI.
  intros L S Zr msF regs pc mem rom regs' pc' mem' mo T Hok HIc Hr Hms Hcont.
  eapply rz_msteps_lazy_tail; [exact Hok | exact HIc | rewrite Hr; exact Hms | exact Hcont].
Qed.

(* As/AsPrintfFirst.v:138, with the walk over the joined list; the symbolic run stays over [segs] *)
Theorem rz_run_lf_lazy_tail : forall L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R msF mo T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  lzok segs L S Zr (mkCfg msF mo) ->
  I (mkCfg msF mo) ->
  restrict L S msF = mkst R (Z_to_bv 64 pc) M rom ->
  (forall R' M' msF' mo', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
     lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (s_pc ss')) M' rom ->
     I (mkCfg msF' mo') ->
     realizes (segs ++ tail) (mkCfg msF' mo') T) ->
  realizes (segs ++ tail) (mkCfg msF mo) T.
Proof using Hnx Hnw HI.
  intros L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R msF mo T
         Hex Hc HR HK Hsc Hsc2 Hok HIc Hr Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply (rz_msteps_lazy_mkst_tail L S Zr); [exact Hok | exact HIc | exact Hr | exact Hms |].
  intros msF' mo' Hok' Hsb Hhs Hr' HIc'.
  apply (Hcont R' (mem_denot E M (s_log ss')) msF' mo' HR');
    [| reflexivity | exact Hlf | exact Hok' | exact Hsb | exact Hhs | exact Hr' | exact HIc'].
  eapply carry_after; eassumption.
Qed.

(* LazyFdNodes.v:53: the ecall step, over the joined list *)
Lemma rz_sys_lazy_tail : forall L S Zr msF regs pc mem mo w T,
  lzok segs L S Zr (mkCfg msF mo) ->
  I (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom (segs ++ tail)) ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  (forall msF1, lzok segs L S Zr (mkCfg msF1 mo) ->
     restrict L S msF1 = epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17) ->
     ms_svc_pending msF1 = Some (getr regs 17) ->
     hid_same L S msF msF1 ->
     I (mkCfg msF1 mo) ->
     realizes (segs ++ tail) (mkCfg msF1 mo) T) ->
  realizes (segs ++ tail) (mkCfg msF mo) T.
Proof using Hnx Hnw HI.
  intros L S Zr msF regs pc mem mo w T Hok HIc Hr HF HE Hk.
  assert (HF' : fetch_word (segs ++ tail) pc = Some w) by (rewrite ltl_fetch; exact HF).
  destruct msF as [rg fr pcv svc rv fc mm rom].
  unfold restrict, restrict_by, with_mem in Hr. cbn in Hr. unfold mkst in Hr.
  injection Hr as Erg Efr Epc Esvc Erv Efc Emm Erom. subst rg fr pcv svc rv fc rom.
  set (msF := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := None;
                 ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mm; ms_rom := seg_rom (segs ++ tail) |}) in *.
  set (msF1 := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mm; ms_rom := seg_rom (segs ++ tail) |}).
  assert (Hacc : mi_account_step (segs ++ tail) msF mo = MachineOk (msF1, mo)).
  { unfold mi_account_step. rewrite (step_accesses_ecall_gen (segs ++ tail) msF w HF' HE).
    cbn [accessed_ranges access_value]. rewrite materialize_model_accesses_nil. reflexivity. }
  assert (Hnode : node_ok (segs ++ tail) (mkCfg msF mo) unit (fun _ => []) (fun _ => mkCfg msF1 mo)).
  { apply node_account; [exact (lzok_halted Hok) | reflexivity | exact Hacc]. }
  eapply rz_silent1; [exact Hnode | apply RomBase.sys_rob_instr; reflexivity |].
  apply Hk.
  - destruct Hok as [HL Hinv Hh HZ HSZ HZL HLM]. split; cbn in *; assumption.
  - unfold msF1, epend, restrict, restrict_by, with_mem. cbn. rewrite Emm. reflexivity.
  - reflexivity.
  - intros a Ha. reflexivity.
  - apply (HI (mkCfg msF mo) [] (mkCfg msF1 mo) HIc). exact (proj1 Hnode tt).
Qed.

(* LazyFdNodes.v:115: a deterministic fd system call, over the joined list *)
Lemma rz_fd_det_lazy_tail : forall L S Zr msF1 mo x8 eff mo1 T,
  lzok segs L S Zr (mkCfg msF1 mo) ->
  I (mkCfg msF1 mo) ->
  ms_svc_pending msF1 = Some x8 ->
  RomBase.sys_rob segs (mkCfg msF1 mo) ->
  (forall o, syscall_spec (sys_input segs msF1 x8) mo o <-> o = Ok eff mo1 []) ->
  m_vm mo1 = m_vm mo -> m_halted mo1 = None ->
  ranges_visible (hiddenb L S) (syscall_effect_accesses eff) ->
  (forall a, hiddenb L S a = true -> ms_mem (apply_effect msF1 eff) a = ms_mem msF1 a) ->
  (forall mo', lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect msF1 eff)) mo') ->
              same_but_materialized mo1 mo' ->
              hid_same L S msF1 (advance_past_svc (apply_effect msF1 eff)) ->
              I (mkCfg (advance_past_svc (apply_effect msF1 eff)) mo') ->
              realizes (segs ++ tail) (mkCfg (advance_past_svc (apply_effect msF1 eff)) mo') T) ->
  realizes (segs ++ tail) (mkCfg msF1 mo) T.
Proof using Hnx Hnw HI.
  intros L S Zr msF1 mo x8 eff mo1 T Hok HIc Hsvc Hrob Hspec Evm Hh1 Hvis Hmem Hk.
  destruct (lzok_after_fd_op segs L S Zr msF1 mo mo1 eff Hok Evm Hh1 Hvis Hmem) as (mo' & Hmat & Hsame & Hok' & Hhs).
  assert (Hspec' : forall o, syscall_spec (sys_input (segs ++ tail) msF1 x8) mo o <-> o = Ok eff mo1 []).
  { intros o. rewrite ltl_sys_input. exact (Hspec o). }
  assert (Hnode : node_ok (segs ++ tail) (mkCfg msF1 mo) unit (fun _ => [])
                    (fun _ => mkCfg (advance_past_svc (apply_effect msF1 eff)) mo')).
  { apply (node_family_mat (segs ++ tail) msF1 mo x8 unit (fun _ => eff) (fun _ => mo1) (fun _ => mo') (fun _ => []) _
             (lzok_halted Hok) Hsvc Hspec').
    - intros []. reflexivity.
    - intros []. exact (not_spurious_det (segs ++ tail) msF1 mo x8 eff mo1 [] Hspec').
    - intros o ->. exists tt. reflexivity.
    - intros []. exact Hh1.
    - intros []. exact Hmat. }
  eapply rz_silent1; [exact Hnode | exact (ltl_sys_rob _ Hrob) |].
  apply (Hk mo' Hok' Hsame Hhs).
  apply (HI (mkCfg msF1 mo) [] _ HIc). exact (proj1 Hnode tt).
Qed.

(* LazyFdNodes.v:142: the same with no memory access, over the joined list *)
Lemma rz_fd_det_noacc_lazy_tail : forall L S Zr msF1 mo x8 eff mo1 T,
  lzok segs L S Zr (mkCfg msF1 mo) ->
  I (mkCfg msF1 mo) ->
  ms_svc_pending msF1 = Some x8 ->
  RomBase.sys_rob segs (mkCfg msF1 mo) ->
  (forall o, syscall_spec (sys_input segs msF1 x8) mo o <-> o = Ok eff mo1 []) ->
  m_vm mo1 = m_vm mo -> m_halted mo1 = None ->
  syscall_effect_accesses eff = [] ->
  (forall a, hiddenb L S a = true -> ms_mem (apply_effect msF1 eff) a = ms_mem msF1 a) ->
  (lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect msF1 eff)) mo1) ->
   hid_same L S msF1 (advance_past_svc (apply_effect msF1 eff)) ->
   I (mkCfg (advance_past_svc (apply_effect msF1 eff)) mo1) ->
   realizes (segs ++ tail) (mkCfg (advance_past_svc (apply_effect msF1 eff)) mo1) T) ->
  realizes (segs ++ tail) (mkCfg msF1 mo) T.
Proof using Hnx Hnw HI.
  intros L S Zr msF1 mo x8 eff mo1 T Hok HIc Hsvc Hrob Hspec Evm Hh1 Hacc Hmem Hk.
  assert (Hhs : hid_same L S msF1 (advance_past_svc (apply_effect msF1 eff))).
  { intros a Ha. cbn [ms_mem advance_past_svc]. apply Hmem. exact Ha. }
  assert (Hspec' : forall o, syscall_spec (sys_input (segs ++ tail) msF1 x8) mo o <-> o = Ok eff mo1 []).
  { intros o. rewrite ltl_sys_input. exact (Hspec o). }
  assert (Hnode : node_ok (segs ++ tail) (mkCfg msF1 mo) unit (fun _ => [])
                    (fun _ => mkCfg (advance_past_svc (apply_effect msF1 eff)) mo1)).
  { apply (node_family_noacc (segs ++ tail) msF1 mo x8 unit (fun _ => eff) (fun _ => mo1) (fun _ => []) _
             (lzok_halted Hok) Hsvc Hspec').
    - intros []. reflexivity.
    - intros []. exact (not_spurious_det (segs ++ tail) msF1 mo x8 eff mo1 [] Hspec').
    - intros o ->. exists tt. reflexivity.
    - intros []. exact Hh1.
    - intros []. exact Hacc. }
  eapply rz_silent1; [exact Hnode | exact (ltl_sys_rob _ Hrob) |].
  apply Hk; [| exact Hhs |].
  - eapply lzok_vm_frame; [exact Hok | exact Evm | exact Hh1 | exact Hhs].
  - apply (HI (mkCfg msF1 mo) [] _ HIc). exact (proj1 Hnode tt).
Qed.

(* LazyFdNodes.v:204: close *)
Theorem rz_close_lazy_tail : forall L S Zr msF regs (pc : word) mem mo w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  I (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom (segs ++ tail)) ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds mo) fd = Some e ->
  (forall msF', lzok segs L S Zr (mkCfg msF' (with_fds (fd_remove (m_fds mo) fd) mo)) ->
     restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom (segs ++ tail)) ->
     hid_same L S msF msF' ->
     I (mkCfg msF' (with_fds (fd_remove (m_fds mo) fd) mo)) ->
     realizes (segs ++ tail) (mkCfg msF' (with_fds (fd_remove (m_fds mo) fd) mo)) K) ->
  realizes (segs ++ tail) (mkCfg msF mo) K.
Proof using Hnx Hnw HI.
  intros L S Zr msF regs pc mem mo w fd e K HF HE Hok HIc Hr H17 Hfd Hfd32 Hlk Hc.
  eapply rz_sys_lazy_tail; [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
  pose proof (ltl_gpr_of_restrict_epend L S msF1 regs pc mem (seg_rom (segs ++ tail)) (getr regs 17)) as Hg.
  eapply (rz_fd_det_noacc_lazy_tail L S Zr msF1 mo (getr regs 17) (mkEffect (Z_to_bv 64 0) [] [])
            (with_fds (fd_remove (m_fds mo) fd) mo));
    [exact Hok1 | exact HI1 | exact Hsvc1 | rob_mf H17 | | reflexivity | | reflexivity | |].
  - intros o. rewrite (syscall_spec_57 _ mo o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
    rewrite in_arg0_si, (Hg 0%nat Hr1), ms_gpr_epend0, Hfd, (fd32_id fd Hfd32). exact (close_outcome fd _ mo e o Hlk).
  - rewrite with_fds_halted'. exact (lzok_halted Hok).
  - intros a Ha. rewrite apply_effect_ret_mem. reflexivity.
  - intros Hok' Hhs HI'.
    apply Hc; [exact Hok' | | eapply hid_same_trans; [exact Hhs1 | exact Hhs] | exact HI'].
    rewrite <- (restrict_adv_ret (segs ++ tail) L S msF1 regs pc mem (getr regs 17) (Z_to_bv 64 0) [] Hr1).
    reflexivity.
Qed.

(* LazyFdNodes.v:232: the terminal-size ioctl on /dev/null *)
Theorem rz_ioctl_winsz_lazy_tail : forall L S Zr msF regs (pc : word) mem mo w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  I (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom (segs ++ tail)) ->
  getr regs 17 = Z_to_bv 64 29 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds mo) fd = Some (nodevnull e) ->
  getr regs 11 = Z_to_bv 64 0x5413 ->
  (forall msF', lzok segs L S Zr (mkCfg msF' mo) ->
     restrict L S msF' = mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom (segs ++ tail)) ->
     hid_same L S msF msF' ->
     I (mkCfg msF' mo) ->
     realizes (segs ++ tail) (mkCfg msF' mo) K) ->
  realizes (segs ++ tail) (mkCfg msF mo) K.
Proof using Hnx Hnw HI.
  intros L S Zr msF regs pc mem mo w fd e K HF HE Hok HIc Hr H17 Hfd Hfd32 Hlk H11 Hc.
  eapply rz_sys_lazy_tail; [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
  pose proof (ltl_gpr_of_restrict_epend L S msF1 regs pc mem (seg_rom (segs ++ tail)) (getr regs 17)) as Hg.
  eapply (rz_fd_det_noacc_lazy_tail L S Zr msF1 mo (getr regs 17) (mkEffect (errno_ret ENOTTY) [] []) mo);
    [exact Hok1 | exact HI1 | exact Hsvc1
    | eapply (RomWrite.ioctl_tty_rob segs msF1 mo (getr regs 17) Hsvc1);
        [rewrite H17; apply u64_lit; lia | rewrite (Hg 1%nat Hr1), ms_gpr_epend1, H11; reflexivity]
    | | reflexivity | exact (lzok_halted Hok) | reflexivity | |].
  - intros o. rewrite (syscall_spec_29 _ mo o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
    rewrite in_arg0_si, in_arg1_si, !(Hg _ Hr1), ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), H11.
    apply (ioctl_tty_outcome fd _ _ mo e o Hlk). reflexivity.
  - intros a Ha. rewrite apply_effect_ret_mem. reflexivity.
  - intros Hok' Hhs HI'.
    apply Hc; [exact Hok' | | eapply hid_same_trans; [exact Hhs1 | exact Hhs] | exact HI'].
    rewrite <- (restrict_adv_ret (segs ++ tail) L S msF1 regs pc mem (getr regs 17) (errno_ret ENOTTY) [] Hr1).
    reflexivity.
Qed.

(* LazyFdNodes.v:356: read from a regular file *)
Theorem rz_read_file_lazy_tail : forall L S Zr msF regs (pc : word) mem mo w fd p off data (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  I (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom (segs ++ tail)) ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds mo) fd = Some (FdFile p off) ->
  fs_lookup (m_fs mo) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= MAX_RW_COUNT)%Z -> (cnt < 2 ^ 64)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  let bs := file_read data off (getr regs 12) in
  let mo1 := with_fds (fd_insert (m_fds mo) fd (FdFile p (off + len_word bs))) mo in
  (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') ->
     same_but_materialized mo1 mo' ->
     restrict L S msF' = mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) (wbytes mem (getr regs 11) bs) (seg_rom (segs ++ tail)) ->
     hid_same L S msF msF' ->
     I (mkCfg msF' mo') ->
     realizes (segs ++ tail) (mkCfg msF' mo') K) ->
  realizes (segs ++ tail) (mkCfg msF mo) K.
Proof using Hnx Hnw HI.
  intros L S Zr msF regs pc mem mo w fd p off data cnt K HF HE Hok HIc Hr H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hover Hst bs mo1 Hc.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply rz_sys_lazy_tail; [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
  pose proof (ltl_gpr_of_restrict_epend L S msF1 regs pc mem (seg_rom (segs ++ tail)) (getr regs 17)) as Hg.
  (* the store target is visible and writable in the full memory (LazyFdNodes.v:43) *)
  assert (Emem : restrict_mem L S (ms_mem msF1) = mem).
  { transitivity (ms_mem (restrict L S msF1)); [reflexivity|]. rewrite Hr1. reflexivity. }
  destruct (store_ok_restrictL segs L S (ms_mem msF1) (getr regs 11) (Z.to_nat cnt) (lzok_ranges Hok)
              ltac:(rewrite Emem; exact Hst)) as [HstF Hvis].
  destruct (read_bytes_map_of_store_ok segs (ms_mem msF1) (getr regs 11) (Z.to_nat cnt) HstF ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  assert (Hu2 : bv_unsigned (ms_gpr msF1 2) = cnt).
  { rewrite (Hg 2%nat Hr1), ms_gpr_epend2, H12. apply u64_lit. lia. }
  pose proof (read_file_outcome_si segs msF1 (getr regs 17) mo fd p off data wv Hno
              ltac:(rewrite (Hg 0%nat Hr1), ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms_writable_byte; rewrite (Hg 1%nat Hr1), (Hg 2%nat Hr1), ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(rewrite Hu2, (Hg 1%nat Hr1), ms_gpr_epend1; exact Hover)) as Hchk.
  rewrite (Hg 1%nat Hr1), (Hg 2%nat Hr1), ms_gpr_epend1, ms_gpr_epend2 in Hchk. fold bs in Hchk. fold mo1 in Hchk.
  assert (Hlen : (length bs <= Z.to_nat cnt)%nat).
  { unfold bs. rewrite length_file_read, H12. unfold word_to_nat. rewrite u64_lit by lia. lia. }
  assert (HvisW : range_visible (hiddenb L S) (getr regs 11) (length bs)).
  { intros i Hi. apply Hvis. lia. }
  eapply (rz_fd_det_lazy_tail L S Zr msF1 mo (getr regs 17) (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) []) mo1);
    [exact Hok1 | exact HI1 | exact Hsvc1 | rob_mf H17 | exact Hchk | reflexivity | | | |].
  - unfold mo1. rewrite with_fds_halted'. exact (lzok_halted Hok).
  - unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
    destruct bs as [|b bsr]; cbn [delivered_writes write_accesses]; intros a n Hin; [destruct Hin|].
    destruct Hin as [Hin|[]]. injection Hin as <- <-. exact HvisW.
  - intros a Ha. destruct bs as [|b bsr]; cbn [delivered_writes].
    + rewrite apply_effect_ret_mem. reflexivity.
    + rewrite apply_effect_write1_mem.
      apply (write_to_mem_hidden (hiddenb L S)); [exact HvisW | exact Ha].
  - intros mo' Hok' Hsame Hhs HI'.
    apply (Hc _ mo' Hok' Hsame); [| eapply hid_same_trans; [exact Hhs1 | exact Hhs] | exact HI'].
    rewrite (restrict_sysret L S L S msF1), Hr1, sysret_epend. cbn [eff_ret]. f_equal.
    destruct bs as [|b bsr]; cbn [delivered_writes].
    + rewrite apply_effect_ret_mem. cbn [wbytes]. exact Emem.
    + rewrite apply_effect_write1_mem, <- (write_to_mem_wbytes (b :: bsr) mem (getr regs 11)), <- Emem.
      unfold restrict_mem. symmetry. apply (write_to_mem_restrict (hiddenb L S)). exact HvisW.
Qed.

(* LazyFdNodes.v:1227: read from a directory (EISDIR) *)
Theorem rz_read_dir_mapped_lazy_tail : forall L S Zr msF regs (pc : word) mem mo w fd (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  I (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom (segs ++ tail)) ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds mo) fd = Some FdDir ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= 2 ^ 24)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  (forall msF', lzok segs L S Zr (mkCfg msF' mo) ->
     restrict L S msF' = mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom (segs ++ tail)) ->
     hid_same L S msF msF' ->
     I (mkCfg msF' mo) ->
     realizes (segs ++ tail) (mkCfg msF' mo) K) ->
  realizes (segs ++ tail) (mkCfg msF mo) K.
Proof using Hnx Hnw HI.
  intros L S Zr msF regs pc mem mo w fd cnt K HF HE Hok HIc Hr H17 Hfd Hfd32 Hlk H12 Hc1 H64 Hover Hst Hc.
  eapply rz_sys_lazy_tail; [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
  pose proof (ltl_gpr_of_restrict_epend L S msF1 regs pc mem (seg_rom (segs ++ tail)) (getr regs 17)) as Hg.
  assert (Emem : restrict_mem L S (ms_mem msF1) = mem).
  { transitivity (ms_mem (restrict L S msF1)); [reflexivity|]. rewrite Hr1. reflexivity. }
  destruct (store_ok_restrictL segs L S (ms_mem msF1) (getr regs 11) (Z.to_nat cnt) (lzok_ranges Hok)
              ltac:(rewrite Emem; exact Hst)) as [HstF _].
  eapply (rz_fd_det_noacc_lazy_tail L S Zr msF1 mo (getr regs 17) (mkEffect (errno_ret EISDIR) [] []) mo);
    [exact Hok1 | exact HI1 | exact Hsvc1 | rob_mf H17 | | reflexivity | exact (lzok_halted Hok) | reflexivity | |].
  - intros o. rewrite (syscall_spec_63 _ mo o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si, !(Hg _ Hr1), ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32).
    apply (read_dir_outcome fd _ _ _ mo o Hlk).
    (* the buffer lies below TASK_SIZE *)
    apply access_okb_intro. rewrite H12, u64_lit by lia. exact Hover.
  - intros a Ha. rewrite apply_effect_ret_mem. reflexivity.
  - intros Hok' Hhs HI'.
    apply Hc; [exact Hok' | | eapply hid_same_trans; [exact Hhs1 | exact Hhs] | exact HI'].
    rewrite <- (restrict_adv_ret (segs ++ tail) L S msF1 regs pc mem (getr regs 17) (errno_ret EISDIR) [] Hr1).
    reflexivity.
Qed.

End LazyTail.
