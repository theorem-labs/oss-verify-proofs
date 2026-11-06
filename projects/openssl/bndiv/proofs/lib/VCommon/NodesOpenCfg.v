(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import
  PropExec SimInv CatSim CatExec SeqExec FileSim ShapeAlg ShapeAlgCfg AgentLib AgentNodes Nodes NodesCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Lemma openat_enoent_check : forall {fx : PropExec.FPState} segs ms x8 model p,
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  (path_eqb p [] = true \/ (openat_plain_name p = true /\ fs_lookup (m_fs model) p = None)) ->
  forall eff, check_syscall (sys_input segs ms x8) eff model
              = check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model [].
Proof.
  intros fx segs ms x8 model p Hno Hdirfd Hpath Hfl Hcase eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno).
  unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  destruct (path_eqb p []) eqn:Hpe; cbv beta iota.
  - apply check_copyins_after_ret_only.
  - destruct Hcase as [Hc | (Hdot & Hfs)]; [discriminate Hc|].
    pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
    apply openat_plain_name_nodirref in Hdot.
    rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
    unfold Open.check_openat_resolved.
    rewrite Hunw. cbv beta iota.
    rewrite Hfl, Z.eqb_refl. cbv beta iota.
    unfold Open.check_openat_read. rewrite Hdot, Hfs.
    apply check_copyins_after_ret_only.
Qed.

(* [comment removed for export] *)
Lemma openat_dot_check : forall {fx : PropExec.FPState} segs ms x8 model,
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk dot_path ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_open_result_copyins (open_copyins ms) eff model
        (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model).
Proof.
  intros fx segs ms x8 model Hno Hdirfd Hpath Hfl eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  change (path_eqb dot_path []) with false. cbv beta iota.
  rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved.
  change (path_has_slash dot_path) with false. cbv beta iota.
  rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read.
  change (path_is_dirref dot_path) with true. cbv beta iota.
  unfold check_open_result_copyins, open_copyins.
  destruct (check_open_result (clear_copyins eff) model
    (fun fd : word => with_fds (fd_insert (m_fds model) fd FdDir) model)) eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

(* [comment removed for export] *)
Lemma read_dir_check : forall {fx : PropExec.FPState} segs ms x8 model,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some FdDir ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff (errno_ret EISDIR) model [].
Proof.
  intros fx segs ms x8 model Hno Hfd Hfd32 Haok eff.
  rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
  rewrite Hfd32, Hfd. cbv beta iota.
  rewrite Haok. cbn [negb]. reflexivity.
Qed.

Section OpenCfg.
Context {fx : PropExec.FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hcfg : cfg_nonalloc_on cfg.

Lemma transparent_56 : forall ms model x8,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 56%Z -> cfg_transparent segs cfg (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc H56. destruct Hcfg as (H1 & H2 & H3 & H4 & H5).
  apply (transparent_nonalloc segs cfg ms model x8 H1 H2 H3 H4 H5 Hsvc).
  apply (not_alloc_sysno x8 56 H56). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rzc_ret_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  cfg_transparent segs cfg (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes_cfg segs cfg (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Ht Hchk Hh' Hlazy Hc.
  eapply rzc_silent1; [|exact Hc].
  apply node_ok_cfg_of_transparent; [|exact Ht].
  eapply node_ret_only_copyins; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rzc_open : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  cfg_transparent segs cfg (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  realizes_cfg segs cfg (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                       (mk (alloc_fd (m_fds model)))) B ->
  realizes_cfg segs cfg (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hlazy Hsvc Ht Hchk Hmk Hmklazy Hfree HA HB.
  apply (rzc_alt2 segs cfg (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - apply node_ok_cfg_of_transparent; [|exact Ht]. eapply node_open; eassumption.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

(* [comment removed for export] *)
Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  (* [comment removed for export] *)
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma Hno56 : bv_unsigned (getr regs 17) = 56%Z.
  Proof. rewrite H17. reflexivity. Qed.

  Lemma ms_t : cfg_transparent segs cfg (mkCfg ms model).
  Proof. apply (transparent_56 ms model (getr regs 17)); [reflexivity | exact Hno56]. Qed.

  Lemma ms_a0 : ms_gpr ms 0 = AT_FDCWD.
  Proof. cbv delta [ms]. rewrite ms_gpr_epend0. exact H10. Qed.
  Lemma ms_fl : Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z.
  Proof. cbv delta [ms]. rewrite ms_gpr_epend2. exact Hfl. Qed.
  Lemma ms_cstr : forall a, ms_gpr ms 1 = a -> read_cstr (ms_read_byte ms) a = read_cstr (mrb segs mem) a.
  Proof. intros a _. cbv delta [ms]. rewrite ms_read_byte_epend. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition path_at (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
    /\ rdn segs mem (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

  Lemma path_at_cstr : forall p, path_at p -> read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p.
  Proof.
    intros p (H1 & H2 & H3). cbv delta [ms]. rewrite ms_read_byte_epend, ms_gpr_epend1.
    apply read_cstr_of_rdn; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rzc_openat_toolong : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    realizes_cfg segs cfg (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
    realizes_cfg segs cfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros bs K Hrd Hnz Hc.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
    eapply rzc_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply (rzc_ret_copyins_silent ms model (getr regs 17) (open_copyins ms) (errno_ret ENAMETOOLONG) model K
              Hh eq_refl ms_t); [ | exact Hh | exact Hlazy | ].
    - apply (openat_toolong_check segs ms (getr regs 17) model Hno56).
      + cbv delta [ms]. rewrite ms_gpr_epend2. exact (modeled_open_flags_rd _ Hfl).
      + cbv delta [ms]. rewrite ms_read_byte_epend, ms_gpr_epend1. exact Hp.
    - cbv delta [ms]. rewrite adv_set_epend. exact Hc.
  Qed.

  (* [comment removed for export] *)
  Lemma rzc_openat_enoent : forall p K,
    path_at p ->
    (p = [] \/ (openat_plain_name p = true /\ fs_lookup (m_fs model) p = None)) ->
    realizes_cfg segs cfg (mkCfg (post (errno_ret ENOENT)) model) K ->
    realizes_cfg segs cfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros p K Hp Hcase Hc.
    eapply rzc_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply (rzc_ret_copyins_silent ms model (getr regs 17) (open_copyins ms) (errno_ret ENOENT) model K
              Hh eq_refl ms_t); [ | exact Hh | exact Hlazy | ].
    - apply (openat_enoent_check segs ms (getr regs 17) model p Hno56 ms_a0 (path_at_cstr p Hp) ms_fl).
      destruct Hcase as [-> | Hpl]; [left; reflexivity | right; exact Hpl].
    - cbv delta [ms]. rewrite adv_set_epend. exact Hc.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  (* [comment removed for export] *)
  Lemma rzc_openat_file : forall p d KA KB,
    path_at p -> path_eqb p [] = false -> openat_plain_name p = true -> fs_lookup (m_fs model) p = Some d ->
    (forall e, In e openat_errnos -> realizes_cfg segs cfg (mkCfg (post (errno_ret e)) model) KA) ->
    realizes_cfg segs cfg (mkCfg (post (alloc_fd fds))
                             (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
    realizes_cfg segs cfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hpe Hpl Hfs HA HB.
    eapply rzc_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply (rzc_open ms model (getr regs 17) (open_copyins ms)); [exact Hh | exact Hlazy | reflexivity | exact ms_t | | | | exact Hfree | |].
    - exact (openat_rd_check segs ms (getr regs 17) model p d Hno56 ms_a0 (path_at_cstr p Hp) Hpe ms_fl Hpl Hfs).
    - intros fd. exact Hh.
    - intros fd. exact Hlazy.
    - intros e He. cbv delta [ms]. rewrite adv_set_epend. exact (HA e He).
    - cbv delta [ms]. rewrite adv_set_epend. exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma rzc_openat_dot : forall KA KB,
    path_at dot_path ->
    (forall e, In e openat_errnos -> realizes_cfg segs cfg (mkCfg (post (errno_ret e)) model) KA) ->
    realizes_cfg segs cfg (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    realizes_cfg segs cfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros KA KB Hp HA HB.
    eapply rzc_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply (rzc_open ms model (getr regs 17) (open_copyins ms)); [exact Hh | exact Hlazy | reflexivity | exact ms_t | | | | exact Hfree | |].
    - exact (openat_dot_check segs ms (getr regs 17) model Hno56 ms_a0 (path_at_cstr dot_path Hp) ms_fl).
    - intros fd. exact Hh.
    - intros fd. exact Hlazy.
    - intros e He. cbv delta [ms]. rewrite adv_set_epend. exact (HA e He).
    - cbv delta [ms]. rewrite adv_set_epend. exact HB.
  Qed.

End Openat.

(* [comment removed for export] *)
Lemma rzc_read_dir : forall regs pc mem model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  fd_lookup (m_fds model) (getr regs 10) = Some FdDir ->
  fd32 (getr regs 10) = getr regs 10 ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  realizes_cfg segs cfg (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  realizes_cfg segs cfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w K HF HE Hh Hlazy H17 Hfd Hfd32 Haok Hc.
  eapply rzc_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  assert (H63 : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; reflexivity).
  eapply rzc_conseq; [| apply t_emit_nil_eq; eapply realizes_cfg_nonempty; exact Hc].
  eapply (rzc_ret_chk segs cfg (epend regs pc mem (seg_rom segs) (getr regs 17)) model (getr regs 17)
            (errno_ret EISDIR) model [] K Hh eq_refl).
  - apply (read_dir_check segs _ (getr regs 17) model H63);
      rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2; assumption.
  - destruct Hcfg as (H1 & H2 & H3 & H4 & H5).
    apply (nospur_nonalloc segs cfg _ (getr regs 17) model _ (conj H1 (conj H2 (conj H3 (conj H4 H5))))).
    apply (not_alloc_sysno (getr regs 17) 63 H63). reflexivity.
  - exact Hh.
  - exact Hlazy.
  - rewrite adv_eff_ret_epend. exact Hc.
Qed.

End OpenCfg.
