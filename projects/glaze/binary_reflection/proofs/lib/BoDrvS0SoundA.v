(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvNodesSoundA4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.ShapeNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma openat_dir_check : forall segs ms x8 model q,
  u x8 = 56%Z -> ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk q -> path_eqb q [] = false ->
  Z.ldiff (u (ms_gpr ms 2)) open_ignored_flags = 0%Z -> path_is_dirref q = true ->
  forall eff, check_syscall (sys_input segs ms x8) eff model
              = check_open_result_copyins (open_copyins ms) eff model (fun fd => with_fds (fd_insert (m_fds model) fd State.FdDir) model).
Proof.
  intros segs ms x8 model q Hno Hdirfd Hpath Hpe Hfl Hdir eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hpe. cbv beta iota.
  rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved. rewrite (path_is_dirref_no_slash _ Hdir). cbv beta iota. rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read. rewrite Hdir.
  unfold check_open_result_copyins, open_copyins.
  destruct (check_open_result (clear_copyins eff) model (fun fd : word => with_fds (fd_insert (m_fds model) fd State.FdDir) model)) eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

Section NodesSoundA4.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
#[local] Notation RZ := (realizes BSEGS).
Lemma RZ_silent1_rz : GPS.RZ_SILENT1 BSEGS RZ.
Proof. exact (GPS.RZ_SILENT1_realizes BSEGS). Qed.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GBOTH SHC AINVH.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
#[local] Notation AINVc := (AINV_f SWIN GBOTH AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation cs_okA := (GPS.cs_ok BSEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV).
#[local] Notation Mr := (GPS.Mr SHC VSHc).
#[local] Notation A2 := (fun nd Ta Tb => forall cs csa csb E fx R M model,
    cs_okA E cs fx R M model -> nd cs = Some (csa, csb) -> Ta [] -> Tb [] ->
    (forall E' fx' R' M' model',
        env_agree NXD E E' /\ env_agree (nxt cs) E E' -> cs_okA E' csa fx' R' M' model' -> m_fs model' = m_fs model -> RZ (cfgF BSEGS fx' R' (pc csa) M' model') Ta) ->
    (forall E' fx' R' M' model',
        env_agree NXD E E' /\ env_agree (nxt cs) E E' -> cs_okA E' csb fx' R' M' model' -> m_fs model' = m_fs model -> RZ (cfgF BSEGS fx' R' (pc csb) M' model') Tb) ->
    RZ (cfgF BSEGS fx R (pc cs) M model) (t_alt2 Ta Tb)).

Hypothesis NONUL2 : forall E, UINV E -> ~ In (Z_to_bv 8 0) (eb E 2%nat).
(* [comment removed for export] *)
Variable data : list byte.
Hypothesis FILE2 : forall E, UINV E -> u (ev E 4%nat) <= DNA.FCAP ->        (* [comment removed for export] *)
  eb E 2%nat <> [] /\ openat_plain_name (eb E 2%nat) = true /\ fs_lookup FS0 (eb E 2%nat) = Some data
  /\ uE E (EVar 4) = flen data /\ (forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (3 + j)%nat = chunk j data).

#[local] Notation at_sys_soundI := (at_sys_sound SHC KCAP AINVH SWIN PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV).
#[local] Notation openat_ok_soundI := (openat_ok_sound SHC KCAP AINVH SWIN HP PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV).
#[local] Notation pages_above_ceil_not_lazyI := (pages_above_ceil_not_lazy SHC AINVH SWIN HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c).

(* [comment removed for export] *)
Lemma cs_ok_ret_with : forall E cs fx R M model r v k' nx' f model',
  cs_okA E cs fx R M model ->
  edenot E r = v ->
  m_vm model' = m_vm model -> m_halted model' = m_halted model -> m_fs model' = m_fs model ->
  APS.fds_ok E f model' ->
  know_ok BSEGS E (Mr E cs model M) k' ->
  cs_okA E (DNA.ret_with cs r k' nx' f) fx (regupd R 10 v) M model'.
Proof.
  intros E cs fx R M model r v k' nx' f model' HC Hr Hvm Hh Hfs Hfd HK.
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL].
  constructor; cbn [DNA.ret_with a_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_meter a_fake a_fbud mk_ss nxt pc];
    try assumption.
  - replace (10%bv : Prelude.reg) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
    apply APS.regs_ok_set_n; [exact CR | lia | exact Hr].
  - reflexivity.
  - rewrite (Mr_ret_with SHC HIDc HIDFc E cs r k' nx' f model model' M Hvm). exact HK.
  - rewrite Hh. exact CH.
  - rewrite Hfs. exact CF.
  - eapply (AINV_f_vm SWIN GBOTH SHC AINVH HP); [exact CA | exact Hvm].
Qed.

Lemma alloc_fd_std : alloc_fd APS.fds_std = Z_to_bv 64 3.
Proof. vm_compute. reflexivity. Qed.


(* [comment removed for export] *)
Lemma rz_openat_pair : forall args L cs E fx R M model (mk : word -> Model) (f : afd) Ta Tb,
  cs_okA E cs fx R M model -> DNA.openat_ok BSEGS args cs = Some L -> fresh_ok NXD cs = true ->
  (forall path rest bs, args = path :: rest -> cstring_at E M (u (edenot E path)) bs -> Z.of_nat (length bs) = u (edenot E L) ->
     forall ms, ms_gpr ms 0 = AT_FDCWD -> ms_gpr ms 1 = edenot E path -> ms_gpr ms 2 = Z_to_bv 64 DNA.O_FLAGS -> ms_read_byte ms = mrb BSEGS M ->
     forall ef, check_syscall (sys_input BSEGS ms (Z_to_bv 64 56)) ef model = check_open_result_copyins (open_copyins ms) ef model mk) ->
  m_vm (mk (Z_to_bv 64 3)) = m_vm model -> m_halted (mk (Z_to_bv 64 3)) = m_halted model -> m_fs (mk (Z_to_bv 64 3)) = m_fs model ->
  APS.fds_ok E f (mk (Z_to_bv 64 3)) ->
  Ta [] -> Tb [] ->
  (forall E' fx' R' M' model',
      env_agree NXD E E' /\ env_agree (nxt cs) E E' -> cs_okA E' (DNA.openat_err_child cs) fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfgF BSEGS fx' R' (pc (DNA.openat_err_child cs)) M' model') Ta) ->
  (forall E' fx' R' M' model',
      env_agree NXD E E' /\ env_agree (nxt cs) E E' -> cs_okA E' (DNA.ret_with cs (ELit 3) (kn cs) (nxt cs) f) fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfgF BSEGS fx' R' (pc (DNA.ret_with cs (ELit 3) (kn cs) (nxt cs) f)) M' model') Tb) ->
  RZ (cfgF BSEGS fx R (pc cs) M model) (t_alt2 Ta Tb).
Proof.
  intros args L cs E fx R M model mk f Ta Tb HC Hok Hfresh Hspec Hvm Hh Hfsm Hfd HTa HTb Hka Hkb.
  destruct (openat_ok_soundI E cs fx R M model args L HC Hok) as (path & rest & bs & Hargs & Hec & G17 & G10 & G11 & G12 & Hafd & Hlen & Hceil & Hnw & Hstr).
  destruct (GPS.is_ecall_at_sound BSEGS cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  assert (E17 : Z_to_bv 5 17 = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11. rewrite E12 in G12.
  pose proof (u64_range (edenot E path)) as Rp. pose proof (u64_range (edenot E L)) as Rl.
  assert (Hfds : m_fds model = APS.fds_std) by (pose proof (co_fds HC) as X; rewrite Hafd in X; exact X).
  unfold cfgF.
  eapply (GPS.rz_step_ecall BSEGS RZ RZ_silent1_rz); [exact (co_halt HC) | eapply GPS.step_ecallF; eassumption | reflexivity | cbn; discriminate |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc cs)) M (seg_rom BSEGS) (getr R 17))
    with (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom BSEGS) (getr R 17)).
  rewrite G17.
  set (ms := @epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom BSEGS) (Z_to_bv 64 56)).
  assert (Hchk : forall ef, check_syscall (sys_input BSEGS ms (Z_to_bv 64 56)) ef model = check_open_result_copyins (open_copyins ms) ef model mk).
  { assert (Hrb : ms_read_byte ms = mrb BSEGS M) by (subst ms; apply ms_read_byte_ependA).
    assert (Ha1 : ms_gpr ms 1 = edenot E path) by (subst ms; rewrite ms_gpr_epend1; exact G11).
    assert (Ha0 : ms_gpr ms 0 = AT_FDCWD) by (subst ms; rewrite ms_gpr_epend0, G10; exact (ATFDCWD_eq)).
    assert (Ha2 : ms_gpr ms 2 = Z_to_bv 64 DNA.O_FLAGS) by (subst ms; rewrite ms_gpr_epend2; exact G12).
    clearbody ms. exact (Hspec path rest bs Hargs Hstr Hlen ms Ha0 Ha1 Ha2 Hrb). }
  set (effA := fun e : Z => with_copyins (open_copyins ms) (mkEffect (errno_ret e) [] [])).
  set (effB := with_copyins (open_copyins ms) (mkEffect (Z_to_bv 64 3) [] [])).
  set (IA := { e : Z | In e openat_errnos }).
  set (effs := fun i : IA + unit => match i with inl a => effA (proj1_sig a) | inr _ => effB end).
  set (mdls := fun i : IA + unit => match i with inl _ => model | inr _ => mk (Z_to_bv 64 3) end).
  apply (rz_alt2 BSEGS (mkCfg ms model) IA unit (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (mdls i)) Ta Tb
           (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - apply (node_chk_ev_nl ms model (Z_to_bv 64 56) (IA + unit) effs mdls (fun _ => [])).
    + reflexivity.
    + exact (co_halt HC).
    + reflexivity.
    + intros [[e He]|[]]; rewrite Hchk; apply (proj2 (check_open_result_copyins_ok_iff _ _ _ _ _ _)).
      * left. exists e. subst effs effA. cbn [proj1_sig]. auto.
      * right. exists (Z_to_bv 64 3). rewrite Hfds, alloc_fd_std. subst effs effB mdls. repeat split; reflexivity.
    + intros ef m' ev Hs. rewrite Hchk in Hs. apply (proj1 (check_open_result_copyins_ok_iff _ _ _ _ _ _)) in Hs.
      destruct Hs as [(e & HIn & -> & -> & ->) | (fd & Hlk & Hfd3 & -> & -> & ->)].
      * exists (inl (exist _ e HIn)). subst effs mdls effA. cbn [proj1_sig]. auto.
      * rewrite Hfds, alloc_fd_std in Hfd3. subst fd. exists (inr tt). subst effs mdls effB. auto.
    + intros ef Hs. rewrite Hchk in Hs. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hs).
    + intros [[e He]|[]]; subst mdls; cbn beta iota; [exact (co_halt HC) | rewrite Hh; exact (co_halt HC)].
    + intros i p Hp.
      assert (Hacc : syscall_effect_accesses (effs i) = open_copyins ms) by (destruct i as [[e He]|[]]; subst effs effA effB; cbn [proj1_sig]; apply sea_copyins_ret).
      rewrite Hacc in Hp.
      assert (Hlz : m_vm_lazy (mdls i) = m_vm_lazy model) by (destruct i as [[e He]|[]]; subst mdls; cbn beta iota; [reflexivity | unfold m_vm_lazy; rewrite Hvm; reflexivity]).
      rewrite Hlz.
      eapply (pages_above_ceil_not_lazyI _ _ _ _ _ M model _ (co_ainv HC)); [|exact Hp].
      intros a n Hin. unfold open_copyins in Hin. destruct Hin as [Hin|[]].
      pose proof (f_equal fst Hin) as Ea. cbn [fst] in Ea. pose proof (proj2 (proj1 (pair_equal_spec _ _ _ _) Hin)) as En.   (* [comment removed for export] *)
      assert (Hn : (n <= 4096)%nat) by (rewrite <- En; apply (cstr_access_len_le _ 4096%nat)).
      subst a ms. rewrite ms_gpr_epend1, G11. split; [exact Hceil |]. clear - Hn Hnw Rp Rl. unfold two64 in *. lia.
  - (* [comment removed for export] *)
    intros [e He]. subst effs mdls effA. cbn [proj1_sig]. subst ms. rewrite adv_eff_ret_copyins_ependA, (v_addi_pc (pc cs) Hpc0 Hpc4).
    set (v := nxt cs). set (E' := ext1 E v (errno_ret e)).
    assert (Hag : env_agree v E E') by apply ext1_agree.
    pose proof (APS.fresh_ok_parts NXD cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    pose proof (GPS.cs_ok_agree BSEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
    refine (Hka E' fx (regupd R 10 (errno_ret e)) M model (conj (env_agree_le _ _ _ _ Hag Fle) Hag) _ eq_refl).
    unfold DNA.openat_err_child. fold v.
    apply (cs_ok_ret_with E' cs fx R M model (EVar v) (errno_ret e) _ (S v) FdStd model HC').
    + cbn [edenot]. subst E'. apply ext1_at.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + cbn [APS.fds_ok]. exact Hfds.
    + constructor; [|exact (co_know HC')].
      cbn [kentry_ok edenot]. subst E'. rewrite ext1_at.
      pose proof (openat_errno_range e He) as Re. rewrite (errno_lit e) by lia.
      change DNA.two64 with two64. unfold two64. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *)
    intros []. subst effs mdls effB. cbn beta iota. subst ms. rewrite adv_eff_ret_copyins_ependA, (v_addi_pc (pc cs) Hpc0 Hpc4).
    refine (Hkb E fx (regupd R 10 (Z_to_bv 64 3)) M (mk (Z_to_bv 64 3)) (conj (env_agree_refl _ _) (env_agree_refl _ _)) _ Hfsm).
    apply (cs_ok_ret_with E cs fx R M model (ELit 3) (Z_to_bv 64 3) (kn cs) (nxt cs) f (mk (Z_to_bv 64 3)) HC).
    + cbn [edenot]. reflexivity.
    + exact Hvm.
    + exact Hh.
    + exact Hfsm.
    + exact Hfd.
    + exact (co_know HC).
Qed.

(* [comment removed for export] *)
Lemma read_cstr_ok : forall E cs fx R M model args L path rest bs,
  cs_okA E cs fx R M model -> DNA.openat_ok BSEGS args cs = Some L -> args = path :: rest ->
  cstring_at E M (u (edenot E path)) bs -> Z.of_nat (length bs) = u (edenot E L) -> (length bs <= 4095)%nat ->
  read_cstr (mrb BSEGS M) (edenot E path) = CstrOk bs.
Proof.
  intros E cs fx R M model args L path rest bs HC Hok Hargs Hstr Hlen Hl.
  destruct (openat_ok_soundI E cs fx R M model args L HC Hok) as (path' & rest' & bs' & Hargs' & _ & _ & _ & _ & _ & _ & Hlen' & _ & Hnw' & _).
  rewrite Hargs in Hargs'. injection Hargs' as <- <-.
  pose proof (u64_range (edenot E path)) as Rp. pose proof Hstr as (Sb & Sn & Sbs).
  rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E path)).
  apply (read_cstr_of_rdn BSEGS M _ bs).
  - exact Hl.
  - destruct Sbs as [-> | ->]; [intros [] | exact (NONUL2 E (co_uinv HC))].
  - apply (cstring_rdn E M _ bs Hstr); [lia|]. unfold two64 in *. lia.
Qed.

Theorem node_openat_file2_sound : forall args Ta Tb, A2 (DNA.node_openat_file2 BSEGS NXD args) Ta Tb.
Proof.
  intros args Ta Tb cs csa csb E fx R M model HC Hn HTa HTb Hka Hkb.
  unfold DNA.node_openat_file2 in Hn.
  destruct args as [|path [|lenE rest]]; [discriminate Hn | destruct (DNA.openat_ok BSEGS [path] cs); discriminate Hn |].
  destruct (DNA.openat_ok BSEGS (path :: lenE :: rest) cs) as [L|] eqn:Hok; [|discriminate Hn].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate Hn] end.
  injection Hn as <- <-.
  apply andb_prop in Hg as [Hg Hrng]. apply andb_prop in Hg as [Hg Hvl]. apply andb_prop in Hg as [Hg Hlen4]. apply andb_prop in Hg as [Hpl Hfresh].
  apply expr_eqb_eq in Hlen4. subst lenE.
  unfold DNA.path_len_ok in Hpl.
  destruct (xlo (kn cs) L) as [lo|] eqn:Hlo; [|discriminate Hpl]. destruct (xhi (kn cs) L) as [hi|] eqn:Hhi; [|discriminate Hpl].
  apply andb_prop in Hpl as [Hlo1 Hhi1]. apply Z.leb_le in Hlo1. apply Z.leb_le in Hhi1.
  pose proof (xlo_sound BSEGS E _ (kn cs) L lo (co_know HC) Hlo) as BL. pose proof (xhi_sound BSEGS E _ (kn cs) L hi (co_know HC) Hhi) as BH.
  assert (Hcls : u (ev E 4%nat) <= DNA.FCAP).
  { destruct (xlo (kn cs) (EVar 4)) as [l4|]; [|discriminate Hrng]. destruct (xhi (kn cs) (EVar 4)) as [h4|] eqn:Hh4; [|discriminate Hrng].
    apply andb_prop in Hrng as [_ Hr2]. apply Z.leb_le in Hr2.
    pose proof (xhi_sound BSEGS E _ (kn cs) _ _ (co_know HC) Hh4) as X. cbn [edenot] in X. lia. }
  destruct (FILE2 E (co_uinv HC) Hcls) as (Hne & Hplain & Hfs & Hflen & Hch).
  destruct (openat_ok_soundI E cs fx R M model _ L HC Hok) as (path' & rest' & bs0 & Hargs' & _ & _ & _ & _ & _ & Hafd & _).
  injection Hargs' as E1 E2.
  assert (Hfds : m_fds model = APS.fds_std) by (pose proof (co_fds HC) as X; rewrite Hafd in X; exact X).
  apply (rz_openat_pair (path :: EVar 4 :: rest) L cs E fx R M model
           (fun fd => with_fds (fd_insert (m_fds model) fd (State.FdFile (eb E 2%nat) (Z_to_bv 64 0))) model)
           (FdFile DNA.CHUNKB (EVar 4) (ELit 0)) Ta Tb HC Hok Hfresh); try assumption.
  - intros path1 rest1 bs Hargs Hstr Hlen ms Ha0 Ha1 Ha2 Hrb ef. injection Hargs as E3 E4. subst path1 rest1.
    pose proof Hstr as (Sb & Sn & Sbs).
    assert (Hbs : bs = eb E 2%nat) by (destruct Sbs as [-> | ->]; [cbn in Hlen; lia | reflexivity]). subst bs.
    apply (openat_rd_check BSEGS ms (Z_to_bv 64 56) model (eb E 2%nat) data).
    + apply u64_lit. lia.
    + exact Ha0.
    + rewrite Hrb, Ha1. eapply (read_cstr_ok E cs fx R M model _ L path _ (eb E 2%nat) HC Hok eq_refl Hstr Hlen). lia.
    + destruct (eb E 2%nat); [exfalso; exact (Hne eq_refl) | reflexivity].
    + rewrite Ha2. exact O_FLAGS_rd.
    + exact Hplain.
    + rewrite (co_fs HC). exact Hfs.
  - reflexivity.
  - apply with_fds_halted.
  - apply with_fds_fs.
  - cbn [APS.fds_ok]. exists (eb E 2%nat), data.
    rewrite with_fds_fds, with_fds_fs, Hfds, (co_fs HC). cbn [edenot].
    split; [reflexivity|]. split; [exact Hfs|]. split; [exact Hflen|]. split; [|exact Hch].
    unfold GPS.uE, APS.uE in *. rewrite Hflen. cbn [edenot]. rewrite u64_lit by (unfold two64; lia). unfold flen. lia.
Qed.

(* [comment removed for export] *)
Hypothesis DIR2 : forall E, UINV E -> u (ev E 4%nat) = DNA.CLS_DIR -> path_is_dirref (eb E 2%nat) = true.

Theorem node_openat_dir2_sound : forall args Ta Tb, A2 (DNA.node_openat_dir2 BSEGS NXD args) Ta Tb.
Proof.
  intros args Ta Tb cs csa csb E fx R M model HC Hn HTa HTb Hka Hkb.
  unfold DNA.node_openat_dir2 in Hn.
  destruct (DNA.openat_ok BSEGS args cs) as [L|] eqn:Hok; [|discriminate Hn].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate Hn] end.
  injection Hn as <- <-.
  apply andb_prop in Hg as [Hg Hcls]. apply andb_prop in Hg as [Hpl Hfresh].
  unfold DNA.path_len_ok in Hpl.
  destruct (xlo (kn cs) L) as [lo|] eqn:Hlo; [|discriminate Hpl]. destruct (xhi (kn cs) L) as [hi|] eqn:Hhi; [|discriminate Hpl].
  apply andb_prop in Hpl as [Hlo1 Hhi1]. apply Z.leb_le in Hlo1. apply Z.leb_le in Hhi1.
  pose proof (xlo_sound BSEGS E _ (kn cs) L lo (co_know HC) Hlo) as BL. pose proof (xhi_sound BSEGS E _ (kn cs) L hi (co_know HC) Hhi) as BH.
  pose proof (DIR2 E (co_uinv HC) (cls_is_sound E _ (kn cs) _ (co_know HC) Hcls)) as Hdir.
  destruct (openat_ok_soundI E cs fx R M model _ L HC Hok) as (path & rest & bs0 & Hargs' & _ & _ & _ & _ & _ & Hafd & _).
  assert (Hfds : m_fds model = APS.fds_std) by (pose proof (co_fds HC) as X; rewrite Hafd in X; exact X).
  apply (rz_openat_pair args L cs E fx R M model
           (fun fd => with_fds (fd_insert (m_fds model) fd State.FdDir) model)
           FdDir Ta Tb HC Hok Hfresh); try assumption.
  - intros path1 rest1 bs Hargs Hstr Hlen ms Ha0 Ha1 Ha2 Hrb ef.
    pose proof Hstr as (Sb & Sn & Sbs).
    assert (Hbs : bs = eb E 2%nat) by (destruct Sbs as [-> | ->]; [cbn in Hlen; lia | reflexivity]).
    apply (openat_dir_check BSEGS ms (Z_to_bv 64 56) model bs).
    + apply u64_lit. lia.
    + exact Ha0.
    + rewrite Hrb, Ha1. eapply (read_cstr_ok E cs fx R M model _ L path1 _ bs HC Hok Hargs Hstr Hlen). lia.
    + rewrite Hbs. destruct (eb E 2%nat) eqn:He; [|reflexivity]. exfalso. revert Hdir. rewrite ?He. cbn. discriminate.
    + rewrite Ha2. exact O_FLAGS_rd.
    + rewrite Hbs. exact Hdir.
  - reflexivity.
  - apply with_fds_halted.
  - apply with_fds_fs.
  - cbn [APS.fds_ok]. rewrite with_fds_fds, Hfds. reflexivity.
Qed.
End NodesSoundA4.
End BoDrvNodesSoundA4.
Module BoDrvUinvA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Definition U_drv (a0 p : list byte) (fs : Fs.Fs) (data : list byte) (E : env) : Prop :=
  eb E 1%nat = a0 /\ eb E 2%nat = p
  /\ ~ In (Z_to_bv 8 0) a0 /\ ~ In (Z_to_bv 8 0) p
  /\ (bv_unsigned (ev E 4%nat) = DNA.CLS_ABSENT -> p <> [] -> openat_plain_name p = true /\ fs_lookup fs p = None)
  /\ (bv_unsigned (ev E 4%nat) <= DNA.FCAP ->
        p <> [] /\ openat_plain_name p = true /\ fs_lookup fs p = Some data
        /\ uE E (EVar 4) = flen data /\ (forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (3 + j)%nat = chunk j data))
  /\ (bv_unsigned (ev E 4%nat) = DNA.CLS_DIR -> path_is_dirref p = true).

Section Facts.
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).
#[local] Notation UINV := (U_drv a0 p fs data).

Lemma U_drv_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
Proof.
  intros E E' [Hev Heb] (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  assert (E4 : ev E' 4%nat = ev E 4%nat) by (symmetry; apply Hev; unfold NXD; lia).
  unfold U_drv, uE. cbn [edenot]. rewrite <- Heb, E4. unfold uE in H6. cbn [edenot] in H6.
  repeat split; try assumption; try (apply H5; assumption); try (apply H6; assumption); try (apply H7; assumption).
Qed.
Lemma U_drv_NONUL12 : forall E, UINV E -> forall j, (j = 1 \/ j = 2)%nat -> ~ In (Z_to_bv 8 0) (eb E j).
Proof. intros E (H1 & H2 & H3 & H4 & _) j [-> | ->]; [rewrite H1; exact H3 | rewrite H2; exact H4]. Qed.
Lemma U_drv_ABSENT2 : forall E, UINV E -> bv_unsigned (ev E 4%nat) = DNA.CLS_ABSENT ->
  eb E 2%nat <> [] -> openat_plain_name (eb E 2%nat) = true /\ fs_lookup fs (eb E 2%nat) = None.
Proof. intros E (H1 & H2 & H3 & H4 & H5 & _) Hc. rewrite H2. exact (H5 Hc). Qed.
Lemma U_drv_FILE2 : forall E, UINV E -> bv_unsigned (ev E 4%nat) <= DNA.FCAP ->
  eb E 2%nat <> [] /\ openat_plain_name (eb E 2%nat) = true /\ fs_lookup fs (eb E 2%nat) = Some data
  /\ uE E (EVar 4) = flen data /\ (forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (3 + j)%nat = chunk j data).
Proof. intros E (H1 & H2 & H3 & H4 & H5 & H6 & _) Hc. rewrite H2. exact (H6 Hc). Qed.
Lemma U_drv_DIR2 : forall E, UINV E -> bv_unsigned (ev E 4%nat) = DNA.CLS_DIR -> path_is_dirref (eb E 2%nat) = true.
Proof. intros E (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hc. rewrite H2. exact (H7 Hc). Qed.
End Facts.
End BoDrvUinvA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtChkTail OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtChkTailI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvNodesSoundA6.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtChkTail OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtChkTailI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoDrvQcSlow OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma regs_ok_havoc_to : forall rs E sr R R' nx,
  regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> Forall (fun r => 0 < r < 32)%nat rs ->
  (forall r : Prelude.reg, ~ In (ridx r) rs -> getr R' r = getr R r) ->
  regs_ok (ext_list E nx (map (fun r => getr R' (Z_to_bv 5 (Z.of_nat r))) rs)) (sr_fresh sr rs nx) R'.
Proof.
  induction rs as [|r rest IH]; intros E sr R R' nx HR Hsr Hrs Hagree; cbn [sr_fresh map ext_list].
  - intros x. rewrite (Hagree x ltac:(intros [])). apply HR.
  - apply Forall_cons_iff in Hrs as [Hr Hrest].
    assert (Hrx : ridx (Z_to_bv 5 (Z.of_nat r)) = r) by (apply ridx_lit; lia).
    assert (Hnz' : bv_eqb (Z_to_bv 5 (Z.of_nat r)) 0%bv = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32%Z.
      rewrite Z.mod_small by lia. replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
    apply (IH (ext1 E nx (getr R' (Z_to_bv 5 (Z.of_nat r)))) (sr_upd sr r (EVar nx)) (regupd R (Z_to_bv 5 (Z.of_nat r)) (getr R' (Z_to_bv 5 (Z.of_nat r)))) R' (S nx)).
    + pose proof (regs_ok_agree' nx E (ext1 E nx (getr R' (Z_to_bv 5 (Z.of_nat r)))) sr R (ext1_agree _ _ _) Hsr HR) as HR1.
      pose proof (regs_ok_upd _ sr R (Z_to_bv 5 (Z.of_nat r)) (getr R' (Z_to_bv 5 (Z.of_nat r))) (EVar nx) HR1 ltac:(cbn [edenot]; apply ext1_at)) as HR2.
      rewrite Hnz', Hrx in HR2. exact HR2.
    + apply sr_vars_lt_upd; [eapply sr_vars_lt_mono; [exact Hsr | lia] |]. cbn [AP.expr_vars_lt]. apply Nat.ltb_lt. lia.
    + exact Hrest.
    + intros x Hx. destruct (bv_eq_dec _ x (Z_to_bv 5 (Z.of_nat r))) as [->|Hne].
      * unfold getr. rewrite Hnz'. symmetry. apply regupd_same.
      * transitivity (getr R x).
        { apply Hagree. intros [Hin|Hin]; [|exact (Hx Hin)].
          apply Hne. rewrite Hin. unfold ridx. rewrite Z2Nat.id by (pose proof (bv_unsigned_in_range _ x); lia).
          symmetry. apply Z_to_bv_bv_unsigned. }
        unfold getr. destruct (bv_eqb x 0); [reflexivity|]. symmetry. apply regupd_other. exact Hne.
Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_mod64 : forall a, Z_to_bv 64 (a mod two64) = Z_to_bv 64 a.
Proof. intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, two64. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. Qed.
Lemma kreadZ_lit0_sound : forall E M k a (w : nat) z,
  know_ok BSEGS E M k -> kreadZ BSEGS k (ELit 0) a w = Some z ->
  (1 <= w <= 8)%nat -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  rdn BSEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 z)) /\ 0 <= z < two64.
Proof.
  intros E M k a w z HK H Hw Ha0 Ha8. unfold kreadZ in H.
  destruct (know_lookup BSEGS k (ELit 0) a w false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v as [zl| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  assert (Hfl : flat E (SA (ELit 0) a) (Z.of_nat w)) by (unfold flat; rewrite estart_lit0; lia).
  destruct (GCL.lookup_piece BSEGS E M k (ELit 0) a w (ELit zl) hs HK ltac:(lia) HL Hfl) as (bs & Hrd & Hlen & Hbs).
  rewrite estart_lit0 in Hrd. split; [| unfold two64; apply Z.mod_pos_bound; lia].
  rewrite Hrd, <- Hbs. cbn [edenot]. do 2 f_equal. symmetry. apply Z_to_bv_mod64.
Qed.

(* [comment removed for export] *)
Lemma m2s_ok_sound : forall E M k,
  know_ok BSEGS E M k -> DNA.m2s_ok BSEGS k = true ->
  rdn BSEGS M (Z_to_bv 64 0x105f18) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10e1b8))
  /\ rdn BSEGS M (Z_to_bv 64 0x105f20) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10eea8))
  /\ rdn BSEGS M (Z_to_bv 64 0x105f28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10eeb0))
  /\ rdn BSEGS M (Z_to_bv 64 0x105f30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10eea0))
  /\ rdn BSEGS M (Z_to_bv 64 0x10e1b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000)).
Proof.
  intros E M k HK H. unfold DNA.m2s_ok in H. cbn [forallb DNA.M2S_CELLS fst snd] in H.
  apply andb_prop in H as [H1 H]. apply andb_prop in H as [H2 H]. apply andb_prop in H as [H3 H]. apply andb_prop in H as [H4 H]. apply andb_prop in H as [H5 _].
  assert (G : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < two64 ->
             match kreadZ BSEGS k (ELit 0) a 8 with Some z => Z.eqb z v | None => false end = true ->
             rdn BSEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v))).
  { intros a v Ha0 Ha8 Hv Hc. destruct (kreadZ BSEGS k (ELit 0) a 8) as [z|] eqn:Hz; [|discriminate Hc]. apply Z.eqb_eq in Hc. subst z.
    exact (proj1 (kreadZ_lit0_sound E M k a 8 v HK Hz ltac:(lia) Ha0 Ha8)). }
  unfold two64 in G.
  repeat split; (apply G; [lia | lia | lia | assumption]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kshok_sem : forall E M hb hk ne,
  kentry_ok BSEGS E M (KShOk (SA hb hk) ne) ->
  shok_sem M (estart E (SA hb hk)) (elenZ E ne) /\ 0 <= estart E (SA hb hk) /\ estart E (SA hb hk) + elenZ E ne <= 2 ^ 47.
Proof.
  intros E M hb hk ne (Hfl & Hhi & Hs). destruct Hfl as (F0 & F1 & F2 & F3).
  split; [|split; [exact F0 | exact Hhi]]. intros z Hz. exact (Hs z Hz).
Qed.


(* [comment removed for export] *)
Lemma shok_word0_gen : forall M (A N q : Z),
  shok_sem M A N -> 0 <= A -> A <= q / 64 * 64 -> q / 64 * 64 + 64 <= A + N -> SB + (A + N) / 8 + 8 <= 2 ^ 64 ->
  rdn BSEGS M (Z_to_bv 64 ((SB + q / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros M A N q HS HA Hlo Hhi Hnw.
  assert (Hq : 0 <= q) by (Z.div_mod_to_equations; lia).
  pose proof (div8_mul8_le (SB + q / 8) ltac:(unfold SB; pose proof (Z.div_pos q 8); lia)) as [D1 D2].
  pose proof (div8_mul8_le q ltac:(lia)) as [Q1 Q2].
  set (w0 := (SB + q / 8) / 8 * 8) in *.
  change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8).
  apply (rdn_of_mem M (repeat (Z_to_bv 8 0) 8) w0). rewrite repeat_length.
  intros i Hi. rewrite nth_repeat.
  unfold mrb. replace (w0 + Z.of_nat i) with (SB + (w0 - SB + Z.of_nat i)) by lia.
  change SB with QSB. rewrite (shok_granule0 M A N (w0 - QSB + Z.of_nat i) HS); [reflexivity | |].
  - clear - D1 D2 Q1 Q2 Hi Hlo Hhi HA Hq. unfold SB, QSB in *. subst w0. Z.div_mod_to_equations. lia.
  - clear - D1 D2 Q1 Q2 Hi Hlo Hhi HA Hq. unfold SB, QSB in *. subst w0. Z.div_mod_to_equations. lia.
Qed.

Lemma eaddz_mod0 : forall E e z, u (edenot E (eaddz e z)) = (u (edenot E e) + z) mod 2 ^ 64.
Proof.
  intros E e z. unfold eaddz. rewrite mkAlu_denot. cbn [Sem.alu64 Sem.alu edenot]. rewrite bv_add_unsigned, bv_wrap64_mod.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma kshok_al_sound : forall E M k beg n,
  know_ok BSEGS E M k -> DNA.kshok_al k beg n = true -> u (edenot E n) + 64 < 2 ^ 64 ->
  exists A N, shok_sem M A N /\ 0 <= A /\ A + N <= 2 ^ 47 /\ (A + N) mod 64 = 0
              /\ 63 <= u (edenot E beg) /\ A <= u (edenot E beg) - 63 /\ u (edenot E beg) + u (edenot E n) + 1 <= A + N.
Proof.
  intros E M k beg n HK H Hn. unfold DNA.kshok_al in H.
  destruct (split_lit (eaddz beg (-63))) as [hb hk] eqn:Hsplit.
  apply existsb_exists in H as (F & HF & H).
  destruct F as [| | | | | | | | | | [fb fo] fl |]; try discriminate H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hal; [|discriminate H] end.
  apply existsb_exists in Hal as (KA & HKA & Hal).
  destruct KA as [| | | | e m | | | | | | |]; try discriminate Hal.
  assert (Hm : m = 64 /\ expr_eqb e (eadd (eaddz fb fo) fl) = true).
  { destruct m as [|p|p]; try discriminate Hal. do 7 (destruct p as [p|p|]; try discriminate Hal). split; [reflexivity | exact Hal]. }
  destruct Hm as [-> Hal']. apply expr_eqb_eq in Hal'. subst e.
  pose proof (proj1 (Forall_forall _ _) HK _ HF) as KF. pose proof (proj1 (Forall_forall _ _) HK _ HKA) as [_ KAl].
  pose proof KF as (Hfl & _). apply kshok_sem in KF as (KS & KS0 & KS47).
  destruct Hfl as (F0 & F1 & F2 & F3).
  set (A := estart E (SA fb fo)) in *. set (N := elenZ E fl) in *.
  assert (Hend : u (edenot E (eadd (eaddz fb fo) fl)) = A + N).
  { unfold eadd. rewrite mkAlu_denot. cbn [Sem.alu64 Sem.alu]. rewrite bv_add_unsigned, bv_wrap64_mod, eaddz_mod0.
    unfold A, N, estart, elenZ in *. cbn [a_base a_off] in *. rewrite (Z.mod_small (u (edenot E fb) + fo)) by lia.
    rewrite Z.mod_small by lia. reflexivity. }
  rewrite Hend in KAl.
  destruct (xinside_sound BSEGS E M k hb hk (eaddz n 64) fb fo fl HK H) as [X1 X2]. fold A in X1, X2. fold N in X2.
  assert (Hlen : elenZ E (eaddz n 64) = u (edenot E n) + 64) by (unfold elenZ; rewrite eaddz_mod0; apply Z.mod_small; pose proof (u64_range (edenot E n)); lia).
  rewrite Hlen in X2.
  pose proof (split_lit_denot E _ hb hk Hsplit) as X. apply (f_equal bv_unsigned) in X. rewrite eaddz_mod0 in X.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod in X. unfold estart in X1, X2. cbn [a_base a_off] in X1, X2.
  pose proof (u64_range (edenot E n)) as Rn. pose proof (u64_range (edenot E beg)) as Rb.
  rewrite (Z.mod_small (u (edenot E hb) + hk)) in X by lia.
  assert (Hb63 : 63 <= u (edenot E beg)).
  { destruct (Z_lt_ge_dec (u (edenot E beg)) 63) as [Hlt|Hge]; [|lia]. exfalso.
    rewrite <- (Z.mod_add _ 1) in X by lia. rewrite Z.mod_small in X by lia. lia. }
  rewrite Z.mod_small in X by lia.
  exists A, N. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
#[local] Notation r5 n := (Z_to_bv 5 (Z.of_nat n)).
#[local] Notation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).
(* [comment removed for export] *)
Definition QC_FAST_stmt (from to : Z) (rb rn : nat) (Cf : Prelude.reg -> Prop) : Prop :=
  forall (fx : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte) (b : word) (n : Z),
    getr regs (r5 rb) = b -> getr regs (r5 rn) = Z_to_bv 64 n -> 1 <= n <= 64 -> u b + n <= 2 ^ 47 ->
    rdn BSEGS mem (Z_to_bv 64 0x105f18) 8 = Some (LE8 0x10e1b8) ->
    rdn BSEGS mem (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 2147450880) ->
    rdn BSEGS mem (Z_to_bv 64 ((2147450880 + u b / 8) / 8 * 8)) 8 = Some (LE8 0) ->
    rdn BSEGS mem (Z_to_bv 64 ((2147450880 + (u b + n - 1) / 8) / 8 * 8)) 8 = Some (LE8 0) ->
    exists r, msteps BSEGS (@mkst fx regs (Z_to_bv 64 from) mem rom) (@mkst fx r (Z_to_bv 64 to) mem rom) /\ regs_agree Cf regs r.
(* [comment removed for export] *)
Definition QC_SLOW_stmt (from to : Z) (rb rn : nat) (Cs : Prelude.reg -> Prop) : Prop :=
  forall (fx : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte) (b : word) (A N n sp : Z),
    getr regs (r5 rb) = b -> getr regs (r5 rn) = Z_to_bv 64 n -> getr regs (r5 2) = Z_to_bv 64 sp ->
    65 <= n <= 2 ^ 43 -> 0 <= A <= u b -> u b + n + 1 <= A + N -> A + N <= 2 ^ 47 -> shok_sem mem A N ->
    (DNA.KHIMEM <= u b \/ u b + n <= 0x7fff7fff) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f18) 8 = Some (LE8 0x10e1b8) -> rdn BSEGS mem (Z_to_bv 64 0x105f20) 8 = Some (LE8 0x10eea8) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f28) 8 = Some (LE8 0x10eeb0) -> rdn BSEGS mem (Z_to_bv 64 0x105f30) 8 = Some (LE8 0x10eea0) ->
    rdn BSEGS mem (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 0x7fff8000) -> rdn BSEGS mem (Z_to_bv 64 0x10eea8) 8 = Some (LE8 0) ->
    rdn BSEGS mem (Z_to_bv 64 0x10eea0) 8 = Some (LE8 0x7fffffffffff) ->
    (exists me : Z, rdn BSEGS mem (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 me)) ->
    DNA.KHIMEM + 80 <= sp -> sp + 16 <= 2 ^ 47 -> store_ok BSEGS mem (Z_to_bv 64 (sp - 80)) 80 = true ->
    exists r mem', msteps BSEGS (@mkst fx regs (Z_to_bv 64 from) mem rom) (@mkst fx r (Z_to_bv 64 to) mem' rom)
      /\ regs_agree Cs regs r
      /\ (forall x : word, u x < sp - 80 \/ sp <= u x -> mem' x = mem x) /\ mem_grows mem mem'.


(* [comment removed for export] *)
Ltac in_clob := intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [vm_compute; repeat (first [left; reflexivity | right]) |]); destruct Hr.
Lemma r5_lit : forall k (l : Prelude.reg), Z.of_nat k = bv_unsigned l -> (Z_to_bv 5 (Z.of_nat k) : Prelude.reg) = l.
Proof. intros k l H. rewrite H. apply Z_to_bv_bv_unsigned. Qed.
Lemma w_lit : forall z (l : word), z = bv_unsigned l -> Z_to_bv 64 z = l.
Proof. intros z l H. rewrite H. apply Z_to_bv_bv_unsigned. Qed.

Lemma qc_fast_printf : QC_FAST_stmt 0x5fe1c 0x5fd70 22 23 (fun x => In x [10; 11; 12; 13; 14]%bv).
Proof.
  intros fx regs mem rom b n Hb Hn Hn64 H47 G P W0 W1.
  rewrite (r5_lit 22 22%bv eq_refl) in Hb. rewrite (r5_lit 23 23%bv eq_refl) in Hn.
  destruct (@both_chk_tail_printf fx regs mem rom b n Hb Hn Hn64 H47 ltac:(lia) ltac:(lia) G P W0 W1) as (r & Hms & Hag).
  exists r. split; [|exact Hag].
  rewrite (w_lit 0x5fe1c (Hoare.at_ (0x5fe1c : word) 0) eq_refl), (w_lit 0x5fd70 (0x5fd70 : word) eq_refl). exact Hms.
Qed.
Lemma qc_fast_strnlen : QC_FAST_stmt 0x5d2fc 0x5d344 18 9 (fun x => In x [11; 12; 13; 14; 15]%bv).
Proof.
  intros fx regs mem rom b n Hb Hn Hn64 H47 G P W0 W1.
  rewrite (r5_lit 18 18%bv eq_refl) in Hb. rewrite (r5_lit 9 9%bv eq_refl) in Hn.
  destruct (@both_chk_tail_strnlen fx regs mem rom b n Hb Hn Hn64 H47 ltac:(lia) ltac:(lia) G P W0 W1) as (r & Hms & Hag).
  exists r. split; [|exact Hag].
  rewrite (w_lit 0x5d2fc (Hoare.at_ (0x5d2fc : word) 0) eq_refl), (w_lit 0x5d344 (Hoare.at_ (0x5d2fc : word) 72) eq_refl). exact Hms.
Qed.
Lemma qc_fast_memchr : QC_FAST_stmt 0x5e7ac 0x5e7f4 18 9 (fun x => In x [11; 12; 13; 14; 15]%bv).
Proof.
  intros fx regs mem rom b n Hb Hn Hn64 H47 G P W0 W1.
  rewrite (r5_lit 18 18%bv eq_refl) in Hb. rewrite (r5_lit 9 9%bv eq_refl) in Hn.
  destruct (@both_chk_tail_memchr fx regs mem rom b n Hb Hn Hn64 H47 ltac:(lia) ltac:(lia) G P W0 W1) as (r & Hms & Hag).
  exists r. split; [|exact Hag].
  rewrite (w_lit 0x5e7ac (Hoare.at_ (0x5e7ac : word) 0) eq_refl), (w_lit 0x5e7f4 (Hoare.at_ (0x5e7ac : word) 72) eq_refl). exact Hms.
Qed.

Ltac slow_pre k1 k2 l1 l2 :=
  intros fx regs mem rom b A N n sp Hb Hn Hsp Hn65 HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk;
  rewrite (r5_lit k1 l1 eq_refl) in Hb; rewrite (r5_lit k2 l2 eq_refl) in Hn; rewrite (r5_lit 2 2%bv eq_refl) in Hsp.
Ltac slow_post zfrom zto lfrom lto :=
  lazymatch goal with
  | X : exists r mem', msteps _ _ _ /\ _ |- _ =>
      destruct X as (r & mem' & Hms & Hag & Hout & Hgr);
      exists r, mem'; split; [|split; [exact Hag | split; [exact Hout | exact Hgr]]];
      rewrite (w_lit zfrom lfrom eq_refl), (w_lit zto lto eq_refl); exact Hms
  end.
Lemma qc_slow_printf' : QC_SLOW_stmt 0x5fe1c 0x5fd70 22 23 (fun x => In x [1; 5; 10; 11; 12; 13; 14; 15; 16; 17]%bv).
Proof.
  slow_pre 22%nat 23%nat (22%bv : Prelude.reg) (23%bv : Prelude.reg).
  pose proof (@qc_slow_printf fx regs mem rom b A N n sp Hb Hn Hsp Hn65 HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk) as X.
  slow_post 0x5fe1c 0x5fd70 (0x5fe1c%bv : word) (0x5fd70%bv : word).
Qed.
Lemma qc_slow_strnlen' : QC_SLOW_stmt 0x5d2fc 0x5d344 18 9 (fun x => In x [1; 5; 11; 12; 13; 14; 15; 16; 17; 18; 22]%bv).
Proof.
  slow_pre 18%nat 9%nat (18%bv : Prelude.reg) (9%bv : Prelude.reg).
  pose proof (@qc_slow_strnlen fx regs mem rom b A N n sp Hb Hn Hsp Hn65 HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk) as X.
  slow_post 0x5d2fc 0x5d344 (0x5d2fc%bv : word) (0x5d344%bv : word).
Qed.
Lemma qc_slow_memchr' : QC_SLOW_stmt 0x5e7ac 0x5e7f4 18 9 (fun x => In x [1; 5; 11; 12; 13; 14; 15; 16; 17; 18; 21]%bv).
Proof.
  slow_pre 18%nat 9%nat (18%bv : Prelude.reg) (9%bv : Prelude.reg).
  pose proof (@qc_slow_memchr fx regs mem rom b A N n sp Hb Hn Hsp Hn65 HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk) as X.
  slow_post 0x5e7ac 0x5e7f4 (0x5e7ac%bv : word) (0x5e7f4%bv : word).
Qed.

Lemma rip_clob_ridx : forall x : Prelude.reg, In x AsRtRegion.rip_clob -> x = Z_to_bv 5 (Z.of_nat 10) \/ In (ridx x) DNA.RIP_CLOB.
Proof.
  intros x H. unfold AsRtRegion.rip_clob in H. cbn [In] in H.
  destruct H as [<-|[<-|H]]; [right; vm_compute; auto 10 | left; symmetry; apply r5_lit; reflexivity |].
  repeat (destruct H as [<-|H]; [right; vm_compute; auto 10|]). destruct H.
Qed.

Section NodesSoundA6.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 BSEGS RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GBOTH SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH /\ (forall plo phi, In (plo, phi) (g_priv GBOTH) -> hi <= plo \/ phi <= lo).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Hypothesis M2S_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (LE8 0) /\ rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (LE8 0x7fffffffffff)
  /\ exists me : Z, rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 me).
#[local] Notation AINVc := (AINV_f SWIN GBOTH AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation cs_okA := (GPS.cs_ok BSEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV).
#[local] Notation N1 := (fun nd => GPS.node1_stmtN BSEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ always nd).
#[local] Notation Mr := (GPS.Mr SHC VSHc).
#[local] Notation AF := (AINV_f_frame SWIN GBOTH SHC AINVH HP both_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation ALZ := (AINV_f_lazy SWIN GBOTH SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation AFACTS := (AINV_f_facts SWIN GBOTH SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation GCORE := (GCL.gcall_core BSEGS NXD SWIN PERMc SPTOPc FS0 AINVc AF fx_ok UINV UINV_agree RZ RZ_silent1 ABOTH SHC VSHc KCAP FTOPc
                              ALZ AFACTS both_in_hull both_segs_wx).

(* [comment removed for export] *)
Lemma hid_image_false' : forall E cs B C K M mdl (a : word),
  AINVc (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  g_img_lo GBOTH <= u a -> u a < g_img_hi GBOTH -> GPS.hid SHC VSHc E cs mdl a = false.
Proof.
  intros E cs B C K M mdl a HA Hlo Hhi. unfold GPS.hid, GPS.lz.
  destruct (page_in_ranges (page_base a) (m_vm_lazy mdl)) eqn:Hp; [|reflexivity]. exfalso.
  unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hiv Hc]].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) (AFACTS _ _ _ _ _ _ _ HA) iv Hiv) as (L0 & L1 & L2).
  pose proof (GPS.page_base_le' a) as (P1 & P2 & P3).
  cbn [g_img_lo g_img_hi GBOTH] in Hlo, Hhi, L2.
  unfold page_size in *. clear - H1 H2 P1 P2 P3 L2 Hlo Hhi. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_Mr_image8 : forall E cs B C K M mdl (a : Z),
  AINVc (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  g_img_lo GBOTH <= a -> a + 8 <= g_img_hi GBOTH ->
  rdn BSEGS (Mr E cs mdl M) (Z_to_bv 64 a) 8 = rdn BSEGS M (Z_to_bv 64 a) 8.
Proof.
  intros E cs B C K M mdl a HA Hlo Hhi. unfold GPS.Mr. apply rdn_mrestrict_eq.
  intros k Hk. unfold woff. cbn [g_img_lo g_img_hi GBOTH] in Hlo, Hhi. rewrite u64_lit by lia.
  apply (hid_image_false' E cs B C K M mdl _ HA); cbn [g_img_lo g_img_hi GBOTH]; rewrite u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma eaddz_mod : forall E e z, u (edenot E (eaddz e z)) = (u (edenot E e) + z) mod 2 ^ 64.
Proof.
  intros E e z. unfold eaddz. rewrite mkAlu_denot. cbn [Sem.alu64 Sem.alu edenot]. rewrite bv_add_unsigned, bv_wrap64_mod.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.


(* [comment removed for export] *)
Theorem node_qctail_sound_gen : forall (from to : Z) (rb rn : nat) (xclob : list nat) (keep : bool) (Cf Cs : Prelude.reg -> Prop),
  (0 < rb < 32)%nat -> (0 < rn < 32)%nat ->
  QC_FAST_stmt from to rb rn Cf -> QC_SLOW_stmt from to rb rn Cs ->
  (forall r, Cf r -> In (ridx r) ((if keep then [] else [10%nat]) ++ DNA.CLOB ++ xclob)) ->
  (forall r, Cs r -> In (ridx r) ((if keep then [] else [10%nat]) ++ DNA.CLOB ++ xclob)) ->
  N1 (DNA.node_qctail BSEGS NXD (from, to, rb, rn, xclob) keep).
Proof.
  intros from to rb rn xclob keep Cf Cs Hrb Hrn FAST SLOW HCf HCs cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DNA.node_qctail in Hn.
  destruct (Z.eqb (pc cs) from && fresh_ok NXD cs)%bool eqn:Hg0; [|discriminate Hn]. cbn [negb] in Hn.
  apply andb_prop in Hg0 as [Hpc Hfresh]. apply Z.eqb_eq in Hpc.
  destruct (split_lit (eaddz (reg cs rb) (-63))) as [hb hk] eqn:Hsplit.
  destruct (xlo (kn cs) (reg cs rn)) as [nlo|] eqn:Hnlo; [|discriminate Hn].
  destruct (xhi (kn cs) (reg cs rn)) as [nhi|] eqn:Hnhi; [|discriminate Hn].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate Hn] end.
  apply andb_prop in Hg as [Hg Harm]. apply andb_prop in Hg as [Hg Hm2s]. apply andb_prop in Hg as [Hn1 Hks]. apply Z.leb_le in Hn1.
  set (rs := ((if keep then [] else [10%nat]) ++ DNA.CLOB ++ xclob)) in *.
  (* [comment removed for export] *)
  unfold node_havoc in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hhv; [|discriminate Hn] end.
  apply andb_prop in Hhv as [_ Hrs]. injection Hn as Ecs'.
  assert (Hrs' : Forall (fun r => 0 < r < 32)%nat rs).
  { apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as X.
    apply andb_prop in X as [X1 X2]. apply Nat.ltb_lt in X1. apply Nat.ltb_lt in X2. lia. }
  (* [comment removed for export] *)
  pose proof (co_know HC) as HK. pose proof (co_ainv HC) as HA.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model rb HC Hrb) as Grb.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model rn HC Hrn) as Grn.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 2 HC ltac:(lia)) as G2.
  set (b := edenot E (reg cs rb)) in *. set (nw := edenot E (reg cs rn)) in *. set (n := u nw).
  pose proof (u64_range nw) as Rn. pose proof (u64_range b) as Rb.
  pose proof (xlo_sound BSEGS E _ (kn cs) _ _ HK Hnlo) as L1. pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hnhi) as L2.
  fold nw in L1, L2. fold n in L1, L2.
  assert (Hnw : nw = Z_to_bv 64 n) by (subst n; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  assert (Hnhi43 : nhi <= 2 ^ 43).
  { apply orb_prop in Harm as [H64|Hsl]; [apply Z.leb_le in H64; lia|].
    apply andb_prop in Hsl as [Hrr _]. unfold DNA.rip_range_ok in Hrr.
    rewrite Hnlo, Hnhi in Hrr. destruct (xlo (kn cs) (reg cs rb)); [|discriminate Hrr]. destruct (xhi (kn cs) (reg cs rb)); [|discriminate Hrr].
    apply andb_prop in Hrr as [Hrr _]. apply andb_prop in Hrr as [_ H43]. apply Z.leb_le in H43. exact H43. }
  (* [comment removed for export] *)
  assert (HULL : exists A N, shok_sem (Mr E cs model M) A N /\ 0 <= A /\ A + N <= 2 ^ 47 /\ 63 <= u b /\ A <= u b - 63 /\ u b + n + 1 <= A + N
                              /\ (forall q, u b <= q <= u b + n - 1 -> q / 64 * 64 + 64 <= A + N)).
  { destruct (kshok_x (kn cs) hb hk (eaddz (reg cs rn) 126)) eqn:Hkx.
    - pose proof (kshok_x_sound BSEGS ABOTH GBOTH both_A_img_hi both_A_img_lo both_in_hull drvA_G_img_shlo E _ (kn cs) hb hk _ HK Hkx) as KS.
      apply kshok_sem in KS as (KS & KS0 & KS47).
      assert (Hlen : elenZ E (eaddz (reg cs rn) 126) = (n + 126) mod 2 ^ 64) by (unfold elenZ; rewrite eaddz_mod; reflexivity).
      assert (Hest : estart E (SA hb hk) = (u b - 63) mod 2 ^ 64).
      { pose proof (split_lit_denot E _ hb hk Hsplit) as X. apply (f_equal bv_unsigned) in X.
        rewrite eaddz_mod in X. fold b in X. unfold estart in KS0, KS47 |- *. cbn [a_base a_off] in KS0, KS47 |- *.
        pose proof (u64_range (edenot E hb)) as Rh. rewrite Z_to_bv_unsigned, bv_wrap64_mod in X.
        rewrite Hlen in KS47. pose proof (Z.mod_pos_bound (n + 126) (2 ^ 64) ltac:(lia)) as M1.
        rewrite (Z.mod_small (u (edenot E hb) + hk)) in X by lia. symmetry. exact X. }
      rewrite Hest in KS, KS0, KS47. rewrite Hlen in KS, KS47.
      rewrite (Z.mod_small (n + 126)) in KS, KS47 by lia.
      assert (Hb63 : 63 <= u b).
      { destruct (Z_lt_ge_dec (u b) 63) as [Hlt|Hge]; [|lia]. exfalso.
        rewrite <- (Z.mod_add _ 1) in KS47 by lia. rewrite Z.mod_small in KS47 by lia. lia. }
      rewrite (Z.mod_small (u b - 63)) in KS, KS47 by lia.
      exists (u b - 63), (n + 126). repeat split; try assumption; try lia.
      intros q Hq. clear - Hq Hb63. Z.div_mod_to_equations. lia.
    - destruct (kshok_al_sound E _ (kn cs) (reg cs rb) (reg cs rn) HK Hks ltac:(fold nw; fold n; lia)) as (A & N & KS & KS0 & KS47 & Hal & Hb63 & HA1 & HA2).
      fold b in Hb63, HA1, HA2. fold nw in HA2. fold n in HA2.
      exists A, N. repeat split; try assumption.
      intros q Hq. clear - Hal HA2 Hq KS0 Hb63. Z.div_mod_to_equations. lia. }
  destruct HULL as (A & N & KS & KS0 & KS47 & Hb63 & HA1 & HA2 & HBLK).
  (* [comment removed for export] *)
  destruct (m2s_ok_sound E _ (kn cs) HK Hm2s) as (C1 & C2 & C3 & C4 & C5).
  (* [comment removed for export] *)
  destruct (fresh_ok_parts NXD cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp2.
  assert (Hspv : AP.expr_vars_lt (nxt cs) spb = true).
  { eapply GCL.split_lit_vars; [exact Hsp2|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
  assert (POST : forall (C : Prelude.reg -> Prop) (r' : bvmap 5 word) (Mr' : word -> option byte),
            (forall r, C r -> In (ridx r) rs) -> regs_agree C R r' ->
            (forall x : word, u x < estart E (SA spb (spk - DNA.FR_RIP)) \/ estart E (SA spb (spk - DNA.FR_RIP)) + DNA.FR_RIP <= u x ->
                              Mr' x = Mr E cs model M x) ->
            mem_grows (Mr E cs model M) Mr' ->
            (forall x : word, Mr' x <> Mr E cs model M x ->
               gowned SWIN PERMc SPTOPc SB (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) x /\ Mr' x <> None) ->
            msteps BSEGS (@mkst fx R (Z_to_bv 64 from) (Mr E cs model M) (seg_rom BSEGS)) (@mkst fx r' (Z_to_bv 64 to) Mr' (seg_rom BSEGS)) ->
            RZ (cfgF BSEGS fx R (pc cs) M model) T).
  { intros C r' Mr' HCr Hagr Hout Hgr Hown Hms.
    set (E' := ext_list E (nxt cs) (map (fun r => getr r' (r5 r)) rs)).
    assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
    apply (GCORE cs E E' fx fx R M model T to (sr_fresh (s_regs (a_ss cs)) rs (nxt cs)) (DNA.havoc_scratch (kn cs) (reg cs 2) DNA.FR_RIP)
             (nxt cs + length rs)%nat r' Mr' HC Hfresh Hag).
    - rewrite Hpc. cbn [restrict mkstF mkst ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom]. exact Hms.
    - exact (co_fx HC).
    - exact Hown.
    - apply (regs_ok_havoc_to rs E _ R r' (nxt cs) (co_regs HC) Fsr Hrs').
      intros x Hx. apply Hagr. intros HCx. exact (Hx (HCr x HCx)).
    - (* [comment removed for export] *)
      unfold DNA.havoc_scratch. rewrite Hsp2.
      assert (HK' : know_ok BSEGS E' (Mr E cs model M) (kn cs)) by (eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK]).
      eapply APS.know_ok_havoc; [exact HK' | | exact Hgr].
      intros x Hx. apply Hout. unfold estart, elenZ in Hx |- *. cbn [a_base a_off edenot] in Hx |- *.
      rewrite <- (edenot_agree' (nxt cs) E E' spb Hag Hspv) in Hx. rewrite u64_lit in Hx by (unfold DNA.FR_RIP; lia). exact Hx.
    - intros fx'' R' M'' model' HC' Hfs'. rewrite <- Ecs' in Hk.
      exact (Hk E' fx'' R' M'' model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag) HC' Hfs'). }
  (* [comment removed for export] *)
  destruct (Z_le_gt_dec n 64) as [Hsmall|Hbig].
  - (* [comment removed for export] *)
    assert (W47 : SB + (A + N) / 8 + 8 <= 2 ^ 64).
    { pose proof (Z.div_le_upper_bound (A + N) 8 (2 ^ 47) ltac:(lia) ltac:(lia)) as X. unfold SB. lia. }
    assert (HAb : forall q, u b <= q -> A <= q / 64 * 64) by (intros q Hq; clear - Hq HA1 Hb63; Z.div_mod_to_equations; lia).
    destruct (FAST fx R (Mr E cs model M) (seg_rom BSEGS) b n Grb ltac:(rewrite Grn; exact Hnw) ltac:(lia) ltac:(lia) C1 C5
                (shok_word0_gen (Mr E cs model M) A N (u b) KS KS0 (HAb (u b) ltac:(lia)) (HBLK (u b) ltac:(lia)) W47)
                (shok_word0_gen (Mr E cs model M) A N (u b + n - 1) KS KS0 (HAb (u b + n - 1) ltac:(lia)) (HBLK (u b + n - 1) ltac:(lia)) W47)) as (r' & Hms & Hagr).
    apply (POST Cf r' (Mr E cs model M) HCf Hagr); [intros; reflexivity | apply mem_grows_refl | intros x Hx; exfalso; exact (Hx eq_refl) | exact Hms].
  - (* [comment removed for export] *)
    apply orb_prop in Harm as [H64|Hsl]; [apply Z.leb_le in H64; lia|].
    apply andb_prop in Hsl as [Hrr Hstk].
    (* [comment removed for export] *)
    unfold DNA.rip_range_ok in Hrr. rewrite Hnlo, Hnhi in Hrr.
    destruct (xlo (kn cs) (reg cs rb)) as [blo|] eqn:Hblo; [|discriminate Hrr].
    destruct (xhi (kn cs) (reg cs rb)) as [bhi|] eqn:Hbhi; [|discriminate Hrr].
    apply andb_prop in Hrr as [_ Hloc].
    pose proof (xlo_sound BSEGS E _ (kn cs) _ _ HK Hblo) as B1. pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hbhi) as B2. fold b in B1, B2.
    assert (Hrng : DNA.KHIMEM <= u b \/ u b + n <= 0x7fff7fff).
    { apply orb_prop in Hloc as [Hh|Hl]; [left | right].
      - apply andb_prop in Hh as [Hh _]. apply Z.leb_le in Hh. lia.
      - apply Z.leb_le in Hl. lia. }
    (* [comment removed for export] *)
    unfold DNA.rip_stack_ok in Hstk. rewrite Hsp2 in Hstk.
    apply andb_prop in Hstk as [Hstk Hsphi]. apply andb_prop in Hstk as [Hstk Hsplo]. apply andb_prop in Hstk as [Hkw Hfl].
    destruct (xlo (kn cs) (reg cs 2)) as [slo|] eqn:Hslo; [|discriminate Hsplo]. apply Z.leb_le in Hsplo.
    destruct (xhi (kn cs) (reg cs 2)) as [shi|] eqn:Hshi; [|discriminate Hsphi]. apply Z.leb_le in Hsphi.
    pose proof (xlo_sound BSEGS E _ (kn cs) _ _ HK Hslo) as S1. pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hshi) as S2.
    set (spw := edenot E (reg cs 2)) in *. set (spz := u spw) in *.
    destruct (GCL.kwritable_x_sound BSEGS E _ (kn cs) (kn cs) spb (spk - DNA.FR_RIP) (ELit DNA.FR_RIP) HK HK Hkw) as (Hst & Hs0 & Hs1).
    assert (Hl80 : elenZ E (ELit DNA.FR_RIP) = 80) by (unfold elenZ; cbn [edenot]; apply u64_lit; unfold DNA.FR_RIP; lia).
    rewrite Hl80 in Hs1.
    assert (Hest2 : estart E (SA spb (spk - DNA.FR_RIP)) = spz - 80).
    { pose proof (split_lit_denot E _ spb spk Hsp2) as X. apply (f_equal bv_unsigned) in X. fold spw in X. fold spz in X.
      rewrite Z_to_bv_unsigned, bv_wrap64_mod in X. unfold estart in Hs0, Hs1 |- *. cbn [a_base a_off] in Hs0, Hs1 |- *.
      unfold DNA.FR_RIP in *. unfold DNA.KHIMEM in Hsplo.
      destruct (Z.eq_dec (u (edenot E spb) + spk) (2 ^ 64)) as [E64|N64].
      - rewrite E64, Z.mod_same in X by lia. lia.
      - rewrite Z.mod_small in X by lia. lia. }
    rewrite Hest2 in Hst, Hs0, Hs1.
    destruct (M2S_H _ _ _ _ _ _ _ (proj1 HA)) as (P1 & P2 & me & P3).
    assert (IMG : forall a, g_img_lo GBOTH <= a -> a + 8 <= g_img_hi GBOTH ->
                  rdn BSEGS (Mr E cs model M) (Z_to_bv 64 a) 8 = rdn BSEGS M (Z_to_bv 64 a) 8)
      by (intros a Ha1 Ha2; exact (rdn_Mr_image8 E cs _ _ _ M model a HA Ha1 Ha2)).
    destruct (SLOW fx R (Mr E cs model M) (seg_rom BSEGS) b A N n spz Grb ltac:(rewrite Grn; exact Hnw)
                ltac:(rewrite G2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) HA2 KS47 KS Hrng C1 C2 C3 C4 C5
                ltac:(rewrite IMG by (cbn [g_img_lo g_img_hi GBOTH]; lia); exact P1)
                ltac:(rewrite IMG by (cbn [g_img_lo g_img_hi GBOTH]; lia); exact P2)
                ltac:(exists me; rewrite IMG by (cbn [g_img_lo g_img_hi GBOTH]; lia); exact P3)
                ltac:(lia) ltac:(unfold two47 in Hsphi; lia) (Hst 80%nat ltac:(lia))) as (r' & Mr' & Hms & Hagr & Hout & Hgr).
    apply (POST Cs r' Mr' HCs Hagr).
    + intros x Hx. apply Hout. rewrite Hest2 in Hx. unfold DNA.FR_RIP in Hx. lia.
    + exact Hgr.
    + intros x Hx. split.
      * left. right. right. left.
        assert (Hin : spz - 80 <= u x < spz).
        { destruct (Z_lt_ge_dec (u x) (spz - 80)) as [Hlt|Hge]; [exfalso; apply Hx; apply Hout; lia|].
          destruct (Z_lt_ge_dec (u x) spz) as [Hlt2|Hge2]; [lia|]. exfalso. apply Hx. apply Hout. lia. }
        pose proof (in_floor_sound BSEGS E _ (kn cs) _ _ _ spb (spk - DNA.FR_RIP) (ELit DNA.FR_RIP) x HK Hfl (co_floor HC)
                      ltac:(rewrite Hest2, Hl80; lia)) as [F1 F2].
        rewrite (co_top HC) in F1. exact F1.
      * intros Hnone. destruct (Mr E cs model M x) eqn:Hm.
        -- apply (Hgr x); [rewrite Hm; discriminate | exact Hnone].
        -- apply Hx. exact Hnone.
    + exact Hms.
Qed.

(* [comment removed for export] *)
Theorem node_qctail_printf_sound : N1 (DNA.node_qctail BSEGS NXD DNA.QC_PRINTF false).
Proof.
  apply (node_qctail_sound_gen 0x5fe1c 0x5fd70 22 23 [1%nat] false _ _ ltac:(lia) ltac:(lia) qc_fast_printf qc_slow_printf'); in_clob.
Qed.
Theorem node_qctail_strnlen_sound : N1 (DNA.node_qctail BSEGS NXD DNA.QC_STRNLEN true).
Proof.
  apply (node_qctail_sound_gen 0x5d2fc 0x5d344 18 9 [1; 18; 22]%nat true _ _ ltac:(lia) ltac:(lia) qc_fast_strnlen qc_slow_strnlen'); in_clob.
Qed.
Theorem node_qctail_memchr_sound : N1 (DNA.node_qctail BSEGS NXD DNA.QC_MEMCHR true).
Proof.
  apply (node_qctail_sound_gen 0x5e7ac 0x5e7f4 18 9 [1; 18; 21]%nat true _ _ ltac:(lia) ltac:(lia) qc_fast_memchr qc_slow_memchr'); in_clob.
Qed.

(* [comment removed for export] *)
Theorem node_region_sound : N1 (DNA.node_region BSEGS NXD GBOTH).
Proof.
  intros cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DNA.node_region in Hn.
  destruct (call_ok_stk NXD GBOTH DNA.FR_RIP DNA.X_REGION cs) as [ra|] eqn:Hcall; [|discriminate Hn].
  destruct (split_lit (reg cs 10)) as [pb pk] eqn:Hsplit.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate Hn] end.
  apply andb_prop in Hg as [Hg Hm2s]. apply andb_prop in Hg as [Hg Hstk]. apply andb_prop in Hg as [Hks Hrr].
  pose proof (AzNodesAlloc.call_ok_stk_sound BSEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV GBOTH DNA.FR_RIP DNA.X_REGION
                cs ra E fx R M model ltac:(unfold DNA.FR_RIP; lia) HC Hcall) as CS.
  cbv zeta in CS. destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp2.
  destruct CS as (Hpc & Hfresh & Hlen & G1 & Hra & Hraev & _ & G2 & _).
  set (rs := DNA.RIP_CLOB) in *.
  unfold node_havoc in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hhv; [|discriminate Hn] end.
  apply andb_prop in Hhv as [_ Hrs]. injection Hn as Ecs'.
  assert (Hrs' : Forall (fun r => 0 < r < 32)%nat rs).
  { apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as X.
    apply andb_prop in X as [X1 X2]. apply Nat.ltb_lt in X1. apply Nat.ltb_lt in X2. lia. }
  pose proof (co_know HC) as HK. pose proof (co_ainv HC) as HA.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 10 HC ltac:(lia)) as G10.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 11 HC ltac:(lia)) as G11.
  set (b := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 11)) in *. set (n := u nw).
  pose proof (u64_range nw) as Rn. pose proof (u64_range b) as Rb.
  assert (Hnw : nw = Z_to_bv 64 n) by (subst n; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (kshok_x_sound BSEGS ABOTH GBOTH both_A_img_hi both_A_img_lo both_in_hull drvA_G_img_shlo E _ (kn cs) pb pk _ HK Hks) as KS.
  apply kshok_sem in KS as (KS & KS0 & KS47).
  assert (Hlen11 : elenZ E (reg cs 11) = n) by reflexivity. rewrite Hlen11 in KS, KS47.
  assert (Hest : estart E (SA pb pk) = u b).
  { pose proof (split_lit_denot E _ pb pk Hsplit) as X. apply (f_equal bv_unsigned) in X. fold b in X.
    unfold estart in KS0, KS47 |- *. cbn [a_base a_off] in KS0, KS47 |- *.
    rewrite Z_to_bv_unsigned, bv_wrap64_mod in X. rewrite Z.mod_small in X by lia. symmetry. exact X. }
  rewrite Hest in KS, KS0, KS47.
  (* [comment removed for export] *)
  unfold DNA.rip_range_ok in Hrr.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate Hrr].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate Hrr].
  destruct (xlo (kn cs) (reg cs 10)) as [blo|] eqn:Hblo; [|discriminate Hrr].
  destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate Hrr].
  apply andb_prop in Hrr as [Hrr Hloc]. apply andb_prop in Hrr as [Hn8 Hn43]. apply Z.leb_le in Hn8. apply Z.leb_le in Hn43.
  pose proof (xlo_sound BSEGS E _ (kn cs) _ _ HK Hnlo) as L1. pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hnhi) as L2.
  pose proof (xlo_sound BSEGS E _ (kn cs) _ _ HK Hblo) as B1. pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hbhi) as B2.
  fold nw in L1, L2. fold n in L1, L2. fold b in B1, B2.
  assert (Hrng : (DNA.KHIMEM <= u b /\ u b + n + 1 <= 2 ^ 47) \/ u b + n <= 0x7fff7fff).
  { apply orb_prop in Hloc as [Hh|Hl]; [left | right].
    - apply andb_prop in Hh as [Hh1 Hh2]. apply Z.leb_le in Hh1. cbn [Z.leb orb] in Hh2. apply Z.ltb_lt in Hh2. unfold two47 in Hh2. lia.
    - apply Z.leb_le in Hl. lia. }
  destruct (m2s_ok_sound E _ (kn cs) HK Hm2s) as (C1 & C2 & C3 & C4 & C5).
  (* [comment removed for export] *)
  unfold DNA.rip_stack_ok in Hstk. rewrite Hsp2 in Hstk.
  apply andb_prop in Hstk as [Hstk Hsphi]. apply andb_prop in Hstk as [Hstk Hsplo]. apply andb_prop in Hstk as [Hkw Hfl].
  destruct (xlo (kn cs) (reg cs 2)) as [slo|] eqn:Hslo; [|discriminate Hsplo]. apply Z.leb_le in Hsplo.
  destruct (xhi (kn cs) (reg cs 2)) as [shi|] eqn:Hshi; [|discriminate Hsphi]. apply Z.leb_le in Hsphi.
  pose proof (xlo_sound BSEGS E _ (kn cs) _ _ HK Hslo) as S1. pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hshi) as S2.
  set (spw := edenot E (reg cs 2)) in *. set (spz := u spw) in *.
  destruct (GCL.kwritable_x_sound BSEGS E _ (kn cs) (kn cs) spb (spk - DNA.FR_RIP) (ELit DNA.FR_RIP) HK HK Hkw) as (Hst & Hs0 & Hs1).
  assert (Hl80 : elenZ E (ELit DNA.FR_RIP) = 80) by (unfold elenZ; cbn [edenot]; apply u64_lit; unfold DNA.FR_RIP; lia).
  rewrite Hl80 in Hs1.
  assert (Hest2 : estart E (SA spb (spk - DNA.FR_RIP)) = spz - 80).
  { pose proof (split_lit_denot E _ spb spk Hsp2) as X. apply (f_equal bv_unsigned) in X. fold spw in X. fold spz in X.
    rewrite Z_to_bv_unsigned, bv_wrap64_mod in X. unfold estart in Hs0, Hs1 |- *. cbn [a_base a_off] in Hs0, Hs1 |- *.
    unfold DNA.FR_RIP in *. unfold DNA.KHIMEM in Hsplo.
    destruct (Z.eq_dec (u (edenot E spb) + spk) (2 ^ 64)) as [E64|N64].
    - rewrite E64, Z.mod_same in X by lia. lia.
    - rewrite Z.mod_small in X by lia. lia. }
  rewrite Hest2 in Hst, Hs0, Hs1.
  destruct (M2S_H _ _ _ _ _ _ _ (proj1 HA)) as (P1 & P2 & me & P3).
  assert (IMG : forall a, g_img_lo GBOTH <= a -> a + 8 <= g_img_hi GBOTH ->
                rdn BSEGS (Mr E cs model M) (Z_to_bv 64 a) 8 = rdn BSEGS M (Z_to_bv 64 a) 8)
    by (intros a Ha1 Ha2; exact (rdn_Mr_image8 E cs _ _ _ M model a HA Ha1 Ha2)).
  assert (RA : Hoare.ret_ok (Z_to_bv 64 ra)) by (apply Hoare.ret_ok_even; rewrite u64_lit by lia; exact Hraev).
  destruct (@region_call_clear fx R (Mr E cs model M) (seg_rom BSEGS) b (Z_to_bv 64 ra) n spz
              ltac:(rewrite <- G1; f_equal; apply bv_eq; reflexivity) RA
              ltac:(rewrite <- G10; f_equal; apply bv_eq; reflexivity)
              ltac:(rewrite <- Hnw, <- G11; f_equal; apply bv_eq; reflexivity)
              ltac:(transitivity spw; [rewrite <- G2; f_equal; apply bv_eq; reflexivity | symmetry; apply Z_to_bv_bv_unsigned])
              ltac:(lia) KS Hrng C1 C2 C3 C4 C5
              ltac:(rewrite IMG by (cbn [g_img_lo g_img_hi GBOTH]; lia); exact P1)
              ltac:(rewrite IMG by (cbn [g_img_lo g_img_hi GBOTH]; lia); exact P2)
              ltac:(exists me; rewrite IMG by (cbn [g_img_lo g_img_hi GBOTH]; lia); exact P3)
              ltac:(unfold QKHIMEM; unfold DNA.KHIMEM in Hsplo; lia) ltac:(unfold two47 in Hsphi; lia) (Hst 80%nat ltac:(lia))) as (r' & Mr' & Hms & A10 & Hagr & Hout & Hgr).
  (* [comment removed for export] *)
  destruct (fresh_ok_parts NXD cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  assert (Hspv : AP.expr_vars_lt (nxt cs) spb = true).
  { eapply GCL.split_lit_vars; [exact Hsp2|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
  set (E' := ext_list E (nxt cs) (map (fun r => getr r' (r5 r)) rs)).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  apply (GCORE cs E E' fx fx R M model T ra (sr_fresh (sr_upd (s_regs (a_ss cs)) 10 (ELit 0)) rs (nxt cs))
           (DNA.havoc_scratch (kn cs) (reg cs 2) DNA.FR_RIP) (nxt cs + length rs)%nat r' Mr' HC Hfresh Hag).
  - rewrite Hpc. cbn [restrict mkstF mkst ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
    rewrite (w_lit DNA.X_REGION (0x70a08%bv : word) eq_refl). exact Hms.
  - exact (co_fx HC).
  - intros x Hx. split.
    + left. right. right. left.
      assert (Hin : spz - 80 <= u x < spz).
      { destruct (Z_lt_ge_dec (u x) (spz - 80)) as [Hlt|Hge]; [exfalso; apply Hx; apply Hout; lia|].
        destruct (Z_lt_ge_dec (u x) spz) as [Hlt2|Hge2]; [lia|]. exfalso. apply Hx. apply Hout. lia. }
      pose proof (in_floor_sound BSEGS E _ (kn cs) _ _ _ spb (spk - DNA.FR_RIP) (ELit DNA.FR_RIP) x HK Hfl (co_floor HC)
                    ltac:(rewrite Hest2, Hl80; lia)) as [F1 F2].
      rewrite (co_top HC) in F1. exact F1.
    + intros Hnone. destruct (Mr E cs model M x) eqn:Hm.
      * apply (Hgr x); [rewrite Hm; discriminate | exact Hnone].
      * apply Hx. exact Hnone.
  - (* [comment removed for export] *)
    assert (Hnz10 : bv_eqb (Z_to_bv 5 (Z.of_nat 10)) 0%bv = false) by reflexivity.
    assert (Hrx10 : ridx (Z_to_bv 5 (Z.of_nat 10)) = 10%nat) by (apply ridx_lit; lia).
    pose proof (regs_ok_upd E (s_regs (a_ss cs)) R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0) (ELit 0) (co_regs HC) ltac:(reflexivity)) as HR2.
    rewrite Hnz10, Hrx10 in HR2.
    apply (regs_ok_havoc_to rs E _ _ r' (nxt cs) HR2); [apply sr_vars_lt_upd; [exact Fsr | reflexivity] | exact Hrs' |].
    intros x Hx. destruct (bv_eq_dec _ x (Z_to_bv 5 (Z.of_nat 10))) as [->|Hne].
    + rewrite (r5_lit 10 10%bv eq_refl) at 1. rewrite A10. unfold getr. rewrite Hnz10. symmetry. apply regupd_same.
    + transitivity (getr R x).
      * apply Hagr. intros Hc. destruct (rip_clob_ridx x Hc) as [->|Hc']; [apply Hne; reflexivity | exact (Hx Hc')].
      * unfold getr. destruct (bv_eqb x 0); [reflexivity|]. symmetry. apply regupd_other. exact Hne.
  - unfold DNA.havoc_scratch. rewrite Hsp2.
    assert (HK' : know_ok BSEGS E' (Mr E cs model M) (kn cs)) by (eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK]).
    eapply APS.know_ok_havoc; [exact HK' | | exact Hgr].
    intros x Hx. apply Hout. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx.
    rewrite <- (edenot_agree' (nxt cs) E E' spb Hag Hspv) in Hx. rewrite u64_lit in Hx by (unfold DNA.FR_RIP; lia).
    unfold estart in Hest2. cbn [a_base a_off] in Hest2. unfold DNA.FR_RIP in *. lia.
  - intros fx'' R' M'' model' HC' Hfs'. rewrite <- Ecs' in Hk.
    exact (Hk E' fx'' R' M'' model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag) HC' Hfs').
Qed.
End NodesSoundA6.
End BoDrvNodesSoundA6.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvNodesSoundA7.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoDrvQcSlow OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA3 BoDrvNodesSoundA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u := bv_unsigned.
#[local] Notation r5 n := (Z_to_bv 5 (Z.of_nat n)).

(* [comment removed for export] *)
Lemma Z_to_bv64_succ : forall a, (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1).
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1%bv : word)) with 1. change (bv_modulus 64) with (2 ^ 64).
  rewrite ?Z.mod_mod by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rdn_defined : forall (Mm : word -> option byte) (n : nat) (a : Z),
  (forall i, (i < n)%nat -> Mm (Z_to_bv 64 (a + Z.of_nat i)) <> None) ->
  exists buf, rdn BSEGS Mm (Z_to_bv 64 a) n = Some buf /\ length buf = n
    /\ forall i, (i < n)%nat -> Mm (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i buf (Z_to_bv 8 0)).
Proof.
  intros Mm n. induction n as [|n IH]; intros a Hd.
  - exists []. split; [reflexivity|]. split; [reflexivity|]. intros i Hi. lia.
  - pose proof (Hd 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
    destruct (Mm (Z_to_bv 64 a)) as [b0|] eqn:Hb0; [|exfalso; exact (H0 eq_refl)].
    destruct (IH (a + 1)) as (buf & Hrd & Hlen & Hnth).
    { intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. apply Hd. lia. }
    exists (b0 :: buf). split; [|split].
    + cbn [rdn]. rewrite Hb0. rewrite Z_to_bv64_succ, Hrd. reflexivity.
    + cbn [length]. rewrite Hlen. reflexivity.
    + intros i Hi. destruct i as [|i]; [rewrite Z.add_0_r; exact Hb0|].
      cbn [nth]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply Hnth. lia.
Qed.
(* [comment removed for export] *)
Lemma rdn1_overlay : forall (Mm : word -> option byte) (a : word) (b c : byte),
  Mm a = Some b -> rdn BSEGS Mm a 1 = Some [c] -> b = c.
Proof. intros Mm a b c H R. cbn [rdn] in R. rewrite H in R. injection R as ->. reflexivity. Qed.

Lemma kimg_cov_sound : forall E M k lo hi,
  know_ok BSEGS E M k -> DNA.kimg_cov k lo hi = true -> forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M k lo hi Hk. induction k as [|K rest IH]; intros Hc i Hi; [discriminate|].
  apply Forall_cons_iff in Hk as [HK Hrest]. cbn [DNA.kimg_cov] in Hc.
  destruct K; try exact (IH Hrest Hc i Hi).
  apply orb_prop in Hc as [Hc|Hc]; [|exact (IH Hrest Hc i Hi)].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [kentry_ok] in HK. destruct HK as (_ & _ & HI). apply HI. lia.
Qed.

(* [comment removed for export] *)
Lemma blob_at_sound : forall E (Mm : word -> option byte) k s L j,
  know_ok BSEGS E Mm k -> DNA.blob_at k s = Some (L, j) ->
  u (edenot E s) + u (edenot E L) + 1 < two64 ->
  exists bs, Z.of_nat (length bs) = u (edenot E L)
    /\ (forall i, (i < length bs)%nat -> Mm (Z_to_bv 64 (u (edenot E s) + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)))
    /\ rdn BSEGS Mm (Z_to_bv 64 (u (edenot E s) + Z.of_nat (length bs))) 1 = Some [Z_to_bv 8 0]
    /\ (bs = [] \/ ((j = 1 \/ j = 2)%nat /\ bs = eb E j)).
Proof.
  intros E Mm k s L j HKn Hba Hnw. unfold two64 in Hnw.
  pose proof (u64_range (edenot E s)) as Rs. pose proof (u64_range (edenot E L)) as Rl.
  unfold DNA.blob_at in Hba. destruct (split_lit s) as [sb sk] eqn:Hsl.
  pose proof (APS.split_lit_denot E s sb sk Hsl) as SD.
  match type of Hba with (match ?f with _ => _ end) = _ => destruct f as [K|] eqn:Hfind end.
  - apply List.find_some in Hfind as [Hin HK].
    destruct K as [ | |[b o] L2 j2| | | | | | | | | ]; try discriminate HK.
    apply andb_prop in HK as [HKb HKo]. apply expr_eqb_eq in HKb. apply Z.eqb_eq in HKo. subst b o.
    match type of Hba with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate Hba] end.
    injection Hba as E1 E2. subst L2 j2.
    apply andb_prop in Hc as [Hab Hnul].
    assert (Hj : (j = 1 \/ j = 2)%nat).
    { unfold DNA.argv_blob in Hab. apply orb_prop in Hab. destruct Hab as [H1|H2]; [left; apply Nat.eqb_eq in H1 | right; apply Nat.eqb_eq in H2]; assumption. }
    pose proof (proj1 (Forall_forall _ _) HKn _ Hin) as KB. cbn [kentry_ok] in KB. destruct KB as (Hflat & Hlen & Hbytes).
    unfold flat, elenZ, estart in Hflat, Hlen, Hbytes. cbn [a_base a_off] in Hflat, Hlen, Hbytes. destruct Hflat as (F1 & F2 & F3 & F4).
    assert (Hpa : u (edenot E s) = u (edenot E sb) + sk) by (rewrite SD; rewrite u64_lit by lia; reflexivity).
    destruct (split_lit (eadd s L)) as [b' o'] eqn:Hsl'.
    pose proof (has_fact_sound E _ k _ HKn Hnul) as KW. cbn [kentry_ok] in KW. destruct KW as (_ & Hflat1 & Hrd1).
    pose proof (flat_u E (SA b' o') 1 Hflat1) as U1. unfold flat, estart in U1, Hflat1. cbn [a_base a_off] in U1, Hflat1.
    pose proof (APS.split_lit_denot E (eadd s L) b' o' Hsl') as SD'.
    assert (EADD : u (edenot E (eadd s L)) = u (edenot E s) + u (edenot E L)).
    { unfold eadd. rewrite mkAlu_denot. unfold Sem.alu64, Sem.alu. rewrite bv_add_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity. }
    assert (Hnuladdr : u (adenot E (SA b' o')) = u (edenot E s) + u (edenot E L)).
    { rewrite U1, <- EADD, SD'. destruct Hflat1 as (G1 & G2 & _). rewrite u64_lit by lia. reflexivity. }
    exists (eb E j). split; [exact Hlen|]. split; [|split].
    + intros i Hi. rewrite Hpa. specialize (Hbytes (Z.of_nat i) ltac:(apply Nat2Z.inj_lt in Hi; lia)). rewrite Nat2Z.id in Hbytes. exact Hbytes.
    + replace (Z_to_bv 64 (u (edenot E s) + Z.of_nat (length (eb E j)))) with (adenot E (SA b' o')) by (apply bv_eq; rewrite Hnuladdr, u64_lit; lia).
      etransitivity; [exact Hrd1 | reflexivity].
    + right. split; [exact Hj | reflexivity].
  - match type of Hba with (if ?c then _ else _) = _ => destruct c eqn:Hnul; [|discriminate Hba] end.
    injection Hba as E1 E2. subst L j.
    pose proof (has_fact_sound E _ k _ HKn Hnul) as KW. cbn [kentry_ok] in KW. destruct KW as (_ & Hflat1 & Hrd1).
    pose proof (flat_u E (SA sb sk) 1 Hflat1) as U1. unfold flat, estart in U1, Hflat1. cbn [a_base a_off] in U1, Hflat1.
    destruct Hflat1 as (G1 & G2 & _).
    exists (@nil byte). split; [cbn [edenot length]; rewrite u64_lit; [reflexivity | lia]|]. split; [|split].
    + intros i Hi. cbn in Hi. lia.
    + cbn [length]. rewrite Z.add_0_r.
      assert (Hpa : u (edenot E s) = u (edenot E sb) + sk) by (rewrite SD; rewrite u64_lit by lia; reflexivity).
      replace (Z_to_bv 64 (u (edenot E s))) with (adenot E (SA sb sk)) by (apply bv_eq; rewrite U1, Hpa; rewrite u64_lit by lia; reflexivity).
      etransitivity; [exact Hrd1 | reflexivity].
    + left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma byte_of_lit : forall z, 0 <= z < two64 -> word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold word_to_le_bytes. rewrite u64_lit by (unfold two64 in Hz; lia). reflexivity. Qed.
Lemma lit_strlen_sound : forall E (Mm : word -> option byte) k fuel a n0 n,
  know_ok BSEGS E Mm k -> 0 <= a -> 0 <= n0 -> a + n0 + Z.of_nat fuel < 2 ^ 64 ->
  DNA.lit_strlen BSEGS fuel k a n0 = Some n ->
  n0 <= n
  /\ (forall j, n0 <= j < n -> exists b : byte, rdn BSEGS Mm (Z_to_bv 64 (a + j)) 1 = Some [b] /\ u b <> 0)
  /\ rdn BSEGS Mm (Z_to_bv 64 (a + n)) 1 = Some [Z_to_bv 8 0]
  /\ a + n + 1 < 2 ^ 64.
Proof.
  intros E Mm k fuel. induction fuel as [|f IH]; intros a n0 n HK Ha Hn0 Hb H; [discriminate H|].
  cbn [DNA.lit_strlen] in H.
  destruct (kreadZ BSEGS k (ELit 0) (a + n0) 1) as [z|] eqn:Hz; [|discriminate H].
  destruct (kreadZ_lit0_sound E Mm k (a + n0) 1 z HK Hz ltac:(lia) ltac:(lia) ltac:(lia)) as [Hrd Hzr].
  rewrite (byte_of_lit z Hzr) in Hrd.
  destruct (Z.eqb (z mod 256) 0) eqn:Hz0.
  - injection H as <-. apply Z.eqb_eq in Hz0. split; [lia|]. split; [intros j Hj; lia|]. split; [|lia].
    rewrite Hrd. do 2 f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Hz0. reflexivity.
  - apply Z.eqb_neq in Hz0.
    destruct (IH a (n0 + 1) n HK Ha ltac:(lia) ltac:(lia) H) as (I1 & I2 & I3 & I4).
    split; [lia|]. split; [|split; [exact I3 | exact I4]].
    intros j Hj. destruct (Z.eq_dec j n0) as [->|Hne]; [|apply I2; lia].
    exists (Z_to_bv 8 z). split; [exact Hrd|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact Hz0.
Qed.

(* [comment removed for export] *)
Lemma ridx_inj : forall x y : Prelude.reg, ridx x = ridx y -> x = y.
Proof.
  intros x y H. unfold ridx in H. apply bv_eq.
  pose proof (bv_unsigned_in_range _ x). pose proof (bv_unsigned_in_range _ y). apply Z2Nat.inj; lia.
Qed.
Definition clob_cls (k : nat) : bool :=
  (Nat.eqb k 10 || existsb (Nat.eqb k) DNA.CLOB || existsb (Nat.eqb k) (map ridx MemsetLibF.RefMemcpyLib.callee_saved) || Nat.eqb k 0)%bool.
Lemma clob_cls_all : forallb clob_cls (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma clob_complement : forall x : Prelude.reg,
  x <> Z_to_bv 5 (Z.of_nat 10) -> ~ In (ridx x) DNA.CLOB -> In x MemsetLibF.RefMemcpyLib.callee_saved \/ ridx x = 0%nat.
Proof.
  intros x H10 Hc.
  assert (Hk : (ridx x < 32)%nat).
  { unfold ridx. pose proof (bv_unsigned_in_range _ x) as Rx. change (bv_modulus 5) with 32 in Rx. lia. }
  pose proof (proj1 (forallb_forall _ _) clob_cls_all (ridx x) ltac:(apply in_seq; lia)) as Hcls.
  unfold clob_cls in Hcls. apply orb_prop in Hcls as [Hcls|H0]; [|right; apply Nat.eqb_eq; exact H0].
  apply orb_prop in Hcls as [Hcls|Hcs].
  - exfalso. apply orb_prop in Hcls as [Ha0|Hcl].
    + apply H10. apply Nat.eqb_eq in Ha0. apply ridx_inj. rewrite Ha0. symmetry. apply ridx_lit. lia.
    + apply existsb_exists in Hcl as (k & Hin & Hek). apply Nat.eqb_eq in Hek. subst k. exact (Hc Hin).
  - left. apply existsb_exists in Hcs as (k & Hin & Hek). apply Nat.eqb_eq in Hek. subst k.
    apply in_map_iff in Hin as (y & Hy & Hiny). apply ridx_inj in Hy. subst y. exact Hiny.
Qed.

Section NodesSoundA7.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 BSEGS RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GBOTH SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH /\ (forall plo phi, In (plo, phi) (g_priv GBOTH) -> hi <= plo \/ phi <= lo).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Hypothesis NONUL12 : forall E, UINV E -> forall j, (j = 1 \/ j = 2)%nat -> ~ In (Z_to_bv 8 0) (eb E j).
#[local] Notation AINVc := (AINV_f SWIN GBOTH AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation cs_okA := (GPS.cs_ok BSEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV).
#[local] Notation N1 := (fun nd => GPS.node1_stmtN BSEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ always nd).
#[local] Notation Mr := (GPS.Mr SHC VSHc).
#[local] Notation AF := (AINV_f_frame SWIN GBOTH SHC AINVH HP both_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation ALZ := (AINV_f_lazy SWIN GBOTH SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation AFACTS := (AINV_f_facts SWIN GBOTH SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation GCORE := (GCL.gcall_core BSEGS NXD SWIN PERMc SPTOPc FS0 AINVc AF fx_ok UINV UINV_agree RZ RZ_silent1 ABOTH SHC VSHc KCAP FTOPc
                              ALZ AFACTS both_in_hull both_segs_wx).

(* [comment removed for export] *)
Lemma leaf_kit : forall cs cs' E fx R M model (T : StoreOk.ShapeAlg.TSet) (ra : Z) (rv : expr) (cl : list nat) (r' : bvmap 5 word),
  cs_okA E cs fx R M model -> fresh_ok NXD cs = true ->
  DNA.leaf_ret NXD cs (kn cs) rv ra cl = Some cs' ->
  msteps BSEGS (@mkst fx R (Z_to_bv 64 (pc cs)) (Mr E cs model M) (seg_rom BSEGS)) (@mkst fx r' (Z_to_bv 64 ra) (Mr E cs model M) (seg_rom BSEGS)) ->
  getr r' (r5 10) = edenot E rv ->
  (forall x : Prelude.reg, x <> r5 10 -> ~ In (ridx x) cl -> getr r' x = getr R x) ->
  (forall E' fx' R' M' model',
      env_agree NXD E E' /\ env_agree (nxt cs) E E' -> cs_okA E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfgF BSEGS fx' R' (pc cs') M' model') T) ->
  RZ (cfgF BSEGS fx R (pc cs) M model) T.
Proof.
  intros cs cs' E fx R M model T ra rv cl r' HC Hfresh Hret Hms H10 Hagr Hk.
  unfold DNA.leaf_ret, node_havoc in Hret.
  match type of Hret with (if ?c then _ else _) = _ => destruct c eqn:Hhv; [|discriminate Hret] end.
  apply andb_prop in Hhv as [Hfr1 Hrs]. injection Hret as Ecs'.
  assert (Hrs' : Forall (fun r => 0 < r < 32)%nat cl).
  { apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as X.
    apply andb_prop in X as [X1 X2]. apply Nat.ltb_lt in X1. apply Nat.ltb_lt in X2. lia. }
  destruct (fresh_ok_parts NXD cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (fresh_ok_parts NXD _ Hfr1) as (Fsr1 & _).
  set (E' := ext_list E (nxt cs) (map (fun r => getr r' (r5 r)) cl)).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  apply (GCORE cs E E' fx fx R M model T ra (sr_fresh (sr_upd (s_regs (a_ss cs)) 10 rv) cl (nxt cs)) (kn cs)
           (nxt cs + length cl)%nat r' (Mr E cs model M) HC Hfresh Hag).
  - cbn [restrict mkstF mkst ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom]. exact Hms.
  - exact (co_fx HC).
  - intros x Hx. exfalso. exact (Hx eq_refl).
  - assert (Hnz10 : bv_eqb (Z_to_bv 5 (Z.of_nat 10)) 0%bv = false) by reflexivity.
    assert (Hrx10 : ridx (Z_to_bv 5 (Z.of_nat 10)) = 10%nat) by (apply ridx_lit; lia).
    pose proof (regs_ok_upd E (s_regs (a_ss cs)) R (Z_to_bv 5 (Z.of_nat 10)) (edenot E rv) rv (co_regs HC) eq_refl) as HR2.
    rewrite Hnz10, Hrx10 in HR2.
    apply (regs_ok_havoc_to cl E _ _ r' (nxt cs) HR2); [exact Fsr1 | exact Hrs' |].
    intros x Hx. destruct (bv_eq_dec _ x (Z_to_bv 5 (Z.of_nat 10))) as [->|Hne].
    + rewrite H10. unfold getr. rewrite Hnz10. symmetry. apply regupd_same.
    + rewrite (Hagr x Hne Hx). unfold getr. destruct (bv_eqb x 0); [reflexivity|]. symmetry. apply regupd_other. exact Hne.
  - eapply know_ok_agree'; [exact Hag | exact Fkn | exact (co_know HC)].
  - intros fx'' R' M'' model' HC' Hfs'. rewrite <- Ecs' in Hk.
    exact (Hk E' fx'' R' M'' model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag) HC' Hfs').
Qed.


Theorem node_blobstrlen_sound : N1 (DNA.node_blobstrlen BSEGS NXD).
Proof.
  intros cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DNA.node_blobstrlen in Hn.
  destruct (DNA.leaf_ok NXD DNA.X_ISTRLEN cs) as [ra|] eqn:Hleaf; [|discriminate Hn].
  unfold DNA.leaf_ok in Hleaf.
  destruct (negb (Z.eqb (pc cs) DNA.X_ISTRLEN)) eqn:Hpc; [discriminate Hleaf|]. apply negb_false_iff in Hpc. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ra'|] eqn:Hret; [|discriminate Hleaf].
  destruct (fresh_ok NXD cs) eqn:Hfresh; [|discriminate Hleaf]. injection Hleaf as ->.
  destruct (GCL.ret_lit_sound E cs R ra (co_regs HC) Hret) as (G1 & RA & Hra & Hraev).
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 10 HC ltac:(lia)) as G10.
  pose proof (co_know HC) as HK.
  set (s := edenot E (reg cs 10)) in *. pose proof (u64_range s) as Rs.
  (* [comment removed for export] *)
  assert (RUN : forall (K : Z) (rv : expr),
            0 <= K -> u s + K + 1 < 2 ^ 64 ->
            (forall j, 0 <= j < K -> exists b : byte, rdn BSEGS (Mr E cs model M) (Z_to_bv 64 (u s + j)) 1 = Some [b] /\ u b <> 0) ->
            rdn BSEGS (Mr E cs model M) (Z_to_bv 64 (u s + K)) 1 = Some [Z_to_bv 8 0] ->
            edenot E rv = Z_to_bv 64 K ->
            DNA.leaf_ret NXD cs (kn cs) rv ra [11; 12]%nat = Some cs' -> RZ (cfgF BSEGS fx R (pc cs) M model) T).
  { intros K rv HK0 HKw Hnz Hz Hrv Hret'.
    destruct (@istrlen_run fx BSEGS (0x80afc%bv : word) (Mr E cs model M) s K (seg_rom BSEGS) both_istrlen_code (conj HK0 HKw) Hnz Hz
                R (Z_to_bv 64 ra) RA ltac:(rewrite <- G1; f_equal; apply bv_eq; reflexivity) ltac:(rewrite <- G10; f_equal; apply bv_eq; reflexivity))
      as (r' & Hms & Hag & A10 & _).
    apply (leaf_kit cs cs' E fx R M model T ra rv [11; 12]%nat r' HC Hfresh Hret').
    - rewrite Hpc. rewrite (w_lit DNA.X_ISTRLEN (Hoare.at_ (0x80afc%bv : word) 0) eq_refl). exact Hms.
    - rewrite Hrv, <- A10. first [reflexivity | f_equal; apply bv_eq; reflexivity].
    - intros x Hx10 Hx. apply Hag. unfold istrlen_clob. cbn [In]. intros [Hc|[Hc|[Hc|[]]]].
      + apply Hx10. rewrite <- Hc. symmetry. apply r5_lit. reflexivity.
      + apply Hx. left. rewrite <- Hc. reflexivity.
      + apply Hx. right. left. rewrite <- Hc. reflexivity.
    - exact Hk. }
  (* [comment removed for export] *)
  assert (BLOB : match DNA.blob_at (kn cs) (reg cs 10) with
                 | Some (L, _) => if DNA.str_nowrap (kn cs) (reg cs 10) L 1 then DNA.leaf_ret NXD cs (kn cs) L ra [11; 12]%nat else None
                 | None => None
                 end = Some cs' -> RZ (cfgF BSEGS fx R (pc cs) M model) T).
  { intros Hb. destruct (DNA.blob_at (kn cs) (reg cs 10)) as [[L j]|] eqn:Hba; [|discriminate Hb].
    destruct (DNA.str_nowrap (kn cs) (reg cs 10) L 1) eqn:Hnw; [|discriminate Hb].
    unfold DNA.str_nowrap in Hnw.
    destruct (xhi (kn cs) (reg cs 10)) as [sh|] eqn:Hsh; [|discriminate Hnw]. destruct (xhi (kn cs) L) as [lh|] eqn:Hlh; [|discriminate Hnw].
    apply Z.ltb_lt in Hnw. change DNA.two64 with (2 ^ 64) in Hnw.
    pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hsh) as B1. pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hlh) as B2. fold s in B1.
    destruct (blob_at_sound E _ (kn cs) (reg cs 10) L j HK Hba ltac:(fold s; unfold two64; lia)) as (bs & Hlen & Hbytes & Hnul & Hbs).
    fold s in Hbytes, Hnul.
    apply (RUN (Z.of_nat (length bs)) L ltac:(lia) ltac:(lia)); [| exact Hnul | rewrite Hlen; symmetry; apply Z_to_bv_bv_unsigned | exact Hb].
    intros i Hi. exists (nth (Z.to_nat i) bs (Z_to_bv 8 0)). split.
    - apply rdn1_of_mem. rewrite <- (Hbytes (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id by lia. reflexivity.
    - destruct Hbs as [->|[Hj ->]]; [cbn [length] in Hi; lia|].
      intros Hu. apply (NONUL12 E (co_uinv HC) j Hj).
      replace (Z_to_bv 8 0) with (nth (Z.to_nat i) (eb E j) (Z_to_bv 8 0)) by (apply bv_eq; rewrite Hu; reflexivity).
      apply nth_In. lia. }
  destruct (reg cs 10) as [a| | | | | | |] eqn:H10e; try exact (BLOB Hn).
  (* [comment removed for export] *)
  destruct (DNA.lit_strlen BSEGS 80 (kn cs) (a mod DNA.two64) 0) as [n|] eqn:Hls; [|discriminate Hn].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate Hn] end.
  apply Z.ltb_lt in Hg. change DNA.two64 with (2 ^ 64) in *.
  assert (Hus : u s = a mod 2 ^ 64) by (subst s; cbn [edenot]; rewrite Z_to_bv_unsigned; apply bv_wrap64_mod).
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ra.
  destruct (lit_strlen_sound E _ (kn cs) 80 (a mod 2 ^ 64) 0 n HK ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Hls) as (L0 & Lnz & Lz & Lw).
  rewrite <- Hus in Lnz, Lz, Lw.
  apply (RUN n (ELit n) L0 Lw); [intros j Hj; apply Lnz; lia | exact Lz | reflexivity | exact Hn].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kn_readable_al_sound : forall E (Mm : word -> option byte) k s L,
  know_ok BSEGS E Mm k -> DNA.kn_readable_al k s L = true -> u (edenot E L) + 1 < 2 ^ 64 ->
  exists A N, (forall i, 0 <= i < N -> Mm (Z_to_bv 64 (A + i)) <> None) /\ 0 <= A /\ A + N < 2 ^ 64 /\ (A + N) mod 8 = 0
              /\ A <= u (edenot E s) /\ u (edenot E s) + u (edenot E L) + 1 <= A + N.
Proof.
  intros E Mm k s L HK H HL. unfold DNA.kn_readable_al in H.
  destruct (split_lit s) as [sb sk] eqn:Hsl.
  apply existsb_exists in H as (F & HF & H).
  destruct F as [| | | | | | | | | [fb fo] fl | |]; try discriminate H. cbv zeta in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hal; [|discriminate H] end.
  apply existsb_exists in Hal as (KA & HKA & Hal).
  destruct KA as [| | | | e m | | | | | | |]; try discriminate Hal.
  assert (Hm : m = 8 /\ expr_eqb e (eadd (eaddz fb fo) fl) = true).
  { destruct m as [|p|p]; try discriminate Hal. do 4 (destruct p as [p|p|]; try discriminate Hal). split; [reflexivity | exact Hal]. }
  destruct Hm as [-> Hal']. apply expr_eqb_eq in Hal'. subst e.
  destruct (xlo k (eadd (eaddz fb fo) fl)) as [lo|] eqn:Hlo; [|discriminate H].
  destruct (Z.leb 1 lo) eqn:Hlo1; [|discriminate H]. apply Z.leb_le in Hlo1.
  pose proof (xlo_sound BSEGS E _ k _ _ HK Hlo) as Xlo.
  pose proof (proj1 (Forall_forall _ _) HK _ HF) as [Hfl KU]. pose proof (proj1 (Forall_forall _ _) HK _ HKA) as [_ KAl].
  destruct Hfl as (F0 & F1 & F2 & F3).
  set (A := estart E (SA fb fo)) in *. set (N := elenZ E fl) in *.
  assert (Hend : u (edenot E (eadd (eaddz fb fo) fl)) = (A + N) mod 2 ^ 64).
  { unfold eadd. rewrite mkAlu_denot. cbn [Sem.alu64 Sem.alu]. rewrite bv_add_unsigned, bv_wrap64_mod, eaddz_mod.
    unfold A, N, estart, elenZ in *. cbn [a_base a_off] in *. rewrite (Z.mod_small (u (edenot E fb) + fo)) by lia. reflexivity. }
  assert (HAN : A + N < 2 ^ 64).
  { destruct (Z_lt_ge_dec (A + N) (2 ^ 64)) as [Hlt|Hge]; [exact Hlt|]. exfalso.
    assert (A + N = 2 ^ 64) by lia. rewrite Hend in Xlo. rewrite H0, Z.mod_same in Xlo by lia. lia. }
  rewrite Hend in KAl. rewrite (Z.mod_small (A + N)) in KAl by lia.
  destruct (xinside_sound BSEGS E Mm k sb sk (eaddz L 1) fb fo fl HK H) as [X1 X2]. fold A in X1, X2. fold N in X2.
  assert (Hlen : elenZ E (eaddz L 1) = u (edenot E L) + 1) by (unfold elenZ; rewrite eaddz_mod; apply Z.mod_small; pose proof (u64_range (edenot E L)); lia).
  rewrite Hlen in X2.
  pose proof (APS.split_lit_denot E _ sb sk Hsl) as X. apply (f_equal bv_unsigned) in X.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod in X. unfold estart in X1, X2. cbn [a_base a_off] in X1, X2.
  pose proof (u64_range (edenot E L)) as Rl.
  rewrite Z.mod_small in X by lia.
  exists A, N. repeat split; try assumption; try lia.
Qed.

Theorem node_blobmemchr_sound : N1 (DNA.node_blobmemchr NXD).
Proof.
  intros cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DNA.node_blobmemchr in Hn.
  destruct (DNA.leaf_ok NXD DNA.X_MEMCHR cs) as [ra|] eqn:Hleaf; [|discriminate Hn].
  unfold DNA.leaf_ok in Hleaf.
  destruct (negb (Z.eqb (pc cs) DNA.X_MEMCHR)) eqn:Hpc; [discriminate Hleaf|]. apply negb_false_iff in Hpc. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ra'|] eqn:Hret; [|discriminate Hleaf].
  destruct (fresh_ok NXD cs) eqn:Hfresh; [|discriminate Hleaf]. injection Hleaf as ->.
  destruct (GCL.ret_lit_sound E cs R ra (co_regs HC) Hret) as (G1 & RA & Hra & Hraev).
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 10 HC ltac:(lia)) as G10.
  pose proof (co_know HC) as HK.
  destruct (reg_lit cs 11) as [c|] eqn:H11; [|discriminate Hn].
  destruct c as [|pc0|pc0]; try discriminate Hn.
  destruct (reg_lit cs 12) as [n|] eqn:H12; [|discriminate Hn].
  destruct (DNA.blob_at (kn cs) (reg cs 10)) as [[L j]|] eqn:Hba; [|discriminate Hn].
  destruct (xhi (kn cs) L) as [lh|] eqn:Hlh; [|discriminate Hn].
  destruct (split_lit (reg cs 10)) as [sb sk] eqn:Hsl.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate Hn] end.
  apply andb_prop in Hg as [Hg Hc2]. apply andb_prop in Hg as [Hg Hc1]. apply andb_prop in Hg as [Hg Hnw]. apply andb_prop in Hg as [Hg Hrd].
  apply andb_prop in Hg as [Hn8 Hn64]. apply Z.leb_le in Hn8. apply Z.ltb_lt in Hn64. change DNA.two64 with (2 ^ 64) in Hn64.
  destruct (GCL.reg_lit_sound E cs R 11 0 (co_regs HC) ltac:(lia) H11) as [G11 _].
  destruct (GCL.reg_lit_sound E cs R 12 n (co_regs HC) ltac:(lia) H12) as [G12 Hn0].
  set (s := edenot E (reg cs 10)) in *. pose proof (u64_range s) as Rs.
  unfold DNA.str_nowrap in Hnw. destruct (xhi (kn cs) (reg cs 10)) as [sh|] eqn:Hsh; [|discriminate Hnw]. rewrite Hlh in Hnw.
  apply Z.ltb_lt in Hnw. change DNA.two64 with (2 ^ 64) in Hnw.
  pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hsh) as B1. pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hlh) as B2. fold s in B1.
  pose proof (u64_range (edenot E L)) as Rl.
  destruct (blob_at_sound E _ (kn cs) (reg cs 10) L j HK Hba ltac:(fold s; unfold two64; lia)) as (bs & Hlen & Hbytes & Hnul & Hbs).
  fold s in Hbytes, Hnul.
  set (K := Z.of_nat (length bs)) in *.
  (* [comment removed for export] *)
  assert (WIN : exists Wn : Z, K + 1 <= Wn /\ (u s + K) / 8 * 8 + 8 <= u s + Wn /\ u s + Wn < 2 ^ 64
                 /\ forall i, 0 <= i < Wn -> Mr E cs model M (Z_to_bv 64 (u s + i)) <> None).
  { destruct (kn_readable_x (kn cs) sb sk (eaddz L 8)) eqn:Hrx.
    - destruct (kn_readable_x_sound BSEGS E _ (kn cs) sb sk (eaddz L 8) HK Hrx) as (W0 & W1 & Wd).
      assert (Hpa : estart E (SA sb sk) = u s).
      { pose proof (APS.split_lit_denot E _ sb sk Hsl) as SD. fold s in SD. apply (f_equal bv_unsigned) in SD.
        rewrite Z_to_bv_unsigned, bv_wrap64_mod in SD. unfold estart in W0, W1 |- *. cbn [a_base a_off] in W0, W1 |- *.
        assert (Hel : 8 <= elenZ E (eaddz L 8)).
        { unfold elenZ. rewrite eaddz_mod. rewrite Z.mod_small by lia. lia. }
        rewrite Z.mod_small in SD by lia. symmetry. exact SD. }
      assert (Hel : elenZ E (eaddz L 8) = K + 8) by (unfold elenZ; rewrite eaddz_mod; rewrite Z.mod_small by lia; lia).
      rewrite Hpa, Hel in Wd.
      exists (K + 8). split; [lia|]. split; [pose proof (div8_mul8_le (u s + K) ltac:(lia)) as [D1 D2]; lia|]. split; [lia|]. exact Wd.
    - destruct (kn_readable_al_sound E (Mr E cs model M) (kn cs) (reg cs 10) L HK Hrd ltac:(lia)) as (A & N & KU & A0 & AN & Aal & A1 & A2).
      fold s in A1, A2. rewrite <- Hlen in A2. fold K in A2.
      exists (A + N - u s). split; [lia|]. split; [clear - Aal A2 Rs; Z.div_mod_to_equations; lia|]. split; [lia|].
      intros i Hi. replace (u s + i) with (A + (u s - A + i)) by lia. apply KU. lia. }
  destruct WIN as (Wn & Wn1 & Wn2 & Wn3 & Wd).
  destruct (rdn_defined (Mr E cs model M) (Z.to_nat Wn) (u s)) as (buf & Hbuf & Hblen & Hbnth).
  { intros i Hi. apply Wd. lia. }
  assert (MH : mchrH (Mr E cs model M) s buf K n).
  { split.
    - rewrite Hblen. rewrite <- Hbuf. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    - rewrite Hblen, Z2Nat.id by lia. exact Wn2.
    - rewrite Hblen, Z2Nat.id by lia. exact Wn3.
    - lia.
    - pose proof (Hbnth (Z.to_nat K) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
      rewrite (rdn1_overlay _ _ _ _ X Hnul). reflexivity.
    - intros i Hi. pose proof (Hbnth i ltac:(lia)) as X. rewrite (Hbytes i ltac:(lia)) in X. injection X as X. rewrite <- X.
      destruct Hbs as [->|[Hj ->]]; [cbn [length] in K; lia|].
      intros Hu. apply (NONUL12 E (co_uinv HC) j Hj).
      replace (Z_to_bv 8 0) with (nth i (eb E j) (Z_to_bv 8 0)) by (apply bv_eq; rewrite Hu; reflexivity).
      apply nth_In. lia.
    - lia.
    - exact Hn64.
    - intros i Hi. destruct Hi as [Hi|Hi].
      + exact (kimg_cov_sound E _ (kn cs) _ _ HK Hc1 i ltac:(unfold DNA.MEMCHR_C1; lia)).
      + exact (kimg_cov_sound E _ (kn cs) _ _ HK Hc2 i ltac:(unfold DNA.MEMCHR_C2; lia)). }
  destruct (@ref_memchr0 fx (Mr E cs model M) s buf K n (seg_rom BSEGS) R (Z_to_bv 64 ra) MH RA
              ltac:(rewrite <- G1; f_equal; apply bv_eq; reflexivity) ltac:(rewrite <- G10; f_equal; apply bv_eq; reflexivity)
              ltac:(rewrite <- G11; f_equal; apply bv_eq; reflexivity) ltac:(rewrite <- G12; f_equal; apply bv_eq; reflexivity))
    as (r' & Hms & Hkeep & A10).
  apply (leaf_kit cs cs' E fx R M model T ra (eadd (reg cs 10) L) DNA.CLOB r' HC Hfresh Hn).
  - rewrite Hpc. rewrite (w_lit DNA.X_MEMCHR (0xfbe8c%bv : word) eq_refl). exact Hms.
  - transitivity (getr r' 10%bv); [f_equal; apply r5_lit; reflexivity|]. rewrite A10.
    apply bv_eq. unfold eadd. rewrite mkAlu_denot. unfold Sem.alu64, Sem.alu. rewrite bv_add_unsigned. fold s. rewrite <- Hlen. fold K.
    rewrite Z_to_bv_unsigned. reflexivity.
  - intros x Hx10 Hx.
    (* [comment removed for export] *)
    destruct (clob_complement x Hx10 Hx) as [Hcs|H0]; [exact (Hkeep x Hcs)|].
    assert (x = 0%bv) by (apply ridx_inj; rewrite H0; reflexivity). subst x. reflexivity.
  - exact Hk.
Qed.

End NodesSoundA7.
End BoDrvNodesSoundA7.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnreg OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnregI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvDtor.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvNodesSoundA10.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnreg OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnregI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvDtor OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA3 BoDrvNodesSoundA6 BoDrvNodesSoundA7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u := bv_unsigned.
#[local] Notation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Definition cell_ok_b (c : Z * nat * Z) : bool :=
  (Nat.leb 1 (snd (fst c)) && Nat.leb (snd (fst c)) 8 && Z.leb 0 (fst (fst c)) && Z.leb (fst (fst c) + Z.of_nat (snd (fst c))) (2 ^ 64))%bool.
Lemma DTOR_CELLS_wf : forallb cell_ok_b DNA.DTOR_CELLS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dtor_cell_sound : forall E M k a w v,
  know_ok BSEGS E M k -> DNA.dtor_cells_ok BSEGS k = true -> In (a, w, v) DNA.DTOR_CELLS ->
  rdn BSEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
Proof.
  intros E M k a w v HK H Hin. unfold DNA.dtor_cells_ok in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  pose proof (proj1 (forallb_forall _ _) H _ Hin) as Hc. cbn [fst snd] in Hc.
  pose proof (proj1 (forallb_forall _ _) DTOR_CELLS_wf _ Hin) as Hw. unfold cell_ok_b in Hw. cbn [fst snd] in Hw.
  apply andb_prop in Hw as [Hw W4]. apply andb_prop in Hw as [Hw W3]. apply andb_prop in Hw as [W1 W2].
  apply Nat.leb_le in W1. apply Nat.leb_le in W2. apply Z.leb_le in W3. apply Z.leb_le in W4.
  destruct (kreadZ BSEGS k (ELit 0) a w) as [z|] eqn:Hz; [|discriminate Hc]. apply Z.eqb_eq in Hc. subst z.
  exact (proj1 (kreadZ_lit0_sound E M k a w v HK Hz ltac:(lia) W3 W4)).
Qed.

(* [comment removed for export] *)
Definition cell_eqb (c d : Z * nat * Z) : bool :=
  (Z.eqb (fst (fst c)) (fst (fst d)) && Nat.eqb (snd (fst c)) (snd (fst d)) && Z.eqb (snd c) (snd d))%bool.
Lemma cell_mem : forall c, existsb (cell_eqb c) DNA.DTOR_CELLS = true -> In c DNA.DTOR_CELLS.
Proof.
  intros [[a w] v] H. apply existsb_exists in H as ([[a' w'] v'] & Hin & He). unfold cell_eqb in He. cbn [fst snd] in He.
  apply andb_prop in He as [He E3]. apply andb_prop in He as [E1 E2].
  apply Z.eqb_eq in E1. apply Nat.eqb_eq in E2. apply Z.eqb_eq in E3. subst. exact Hin.
Qed.

Lemma wseg_mu : wseg_ok BSEGS (Z_to_bv 64 0x10ba70) 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_flag : wseg_ok BSEGS (Z_to_bv 64 0x10ab00) 8 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Section DtorGate.
Context {fx : FPState}.

Lemma readable_store_ok : forall E (M : word -> option byte) k (a n : Z),
  know_ok BSEGS E M k -> kn_readable_x k (ELit 0) a (ELit n) = true -> 1 <= n < 2 ^ 64 ->
  store_ok BSEGS M (Z_to_bv 64 a) (Z.to_nat n) = true.
Proof.
  intros E M k a n HK H Hn.
  destruct (kn_readable_x_sound BSEGS E M k (ELit 0) a (ELit n) HK H) as (R0 & R1 & Rd).
  assert (Un : u (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  rewrite estart_lit0 in R0, R1, Rd. unfold elenZ in R1, Rd. cbn [edenot] in R1, Rd. rewrite Un in R1, Rd.
  assert (Ua : u (Z_to_bv 64 a) = a) by (apply u64_lit; lia).
  apply store_ok_of_all; [rewrite Ua, Z2Nat.id by lia; lia|].
  intros x Hx. rewrite Ua, Z2Nat.id in Hx by lia. unfold wview.
  specialize (Rd (u x - a) ltac:(lia)). replace (a + (u x - a)) with (u x) in Rd by lia. rewrite Z_to_bv_bv_unsigned in Rd.
  destruct (M x); [discriminate | exfalso; exact (Rd eq_refl)].
Qed.

Lemma dtor_unregH : forall E (M : word -> option byte) k (sp ra : word) (me : Z) (cpm : byte),
  know_ok BSEGS E M k -> DNA.dtor_cells_ok BSEGS k = true ->
  0x10007fff8000 + 512 <= u sp -> u sp + 16 <= 2 ^ 47 ->
  store_ok BSEGS M (Z_to_bv 64 (u sp - 512)) 512 = true ->
  Hoare.ret_ok ra ->
  rdn BSEGS M (Z_to_bv 64 0x10ba70) 8 = Some (LE8 0) ->
  rdn BSEGS M (Z_to_bv 64 0x10da1c) 1 = Some [cpm] -> u cpm <> 0 ->
  rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (LE8 0) ->
  rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (LE8 0x7fffffffffff) ->
  rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 me) ->
  exists pg ro : word, unregH BSEGS drv_unreg_tab M sp ra (Z_to_bv 64 1) cpm (Z_to_bv 64 me) (2 ^ 64 - 1) pg ro.
Proof.
  intros E M k sp ra me cpm HK Hg Hsp1 Hsp2 Hstk Hra Pmu Pcpm Pcpmnz Pmb Phe Pme.
  pose proof Hg as Hg0. unfold DNA.dtor_cells_ok in Hg0.
  apply andb_prop in Hg0 as [Hg0 Hsh]. apply andb_prop in Hg0 as [_ Hany].
  destruct (kreadZ BSEGS k (ELit 0) 0x105ef8 8) as [zpg|] eqn:Hpg; [|discriminate Hany].
  destruct (kreadZ BSEGS k (ELit 0) 0x10468 8) as [zro|] eqn:Hro; [|discriminate Hany].
  pose proof (proj1 (kreadZ_lit0_sound E M k _ _ _ HK Hpg ltac:(lia) ltac:(lia) ltac:(lia))) as Rpg.
  pose proof (proj1 (kreadZ_lit0_sound E M k _ _ _ HK Hro ltac:(lia) ltac:(lia) ltac:(lia))) as Rro.
  assert (CELL : forall a w v, existsb (cell_eqb (a, w, v)) DNA.DTOR_CELLS = true ->
            rdn BSEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)))
    by (intros a w v Hm; exact (dtor_cell_sound E M k a w v HK Hg (cell_mem _ Hm))).
  assert (SHD : forall b s, In (b, s) ((DNA.DTOR_P_START, 64 * 9) :: DNA.DTOR_GLOBS) -> 1 <= s / 8 < 2 ^ 64 ->
            store_ok BSEGS M (Z_to_bv 64 (zshad b)) (Z.to_nat (s / 8)) = true).
  { intros b s Hin Hs. pose proof (proj1 (forallb_forall _ _) Hsh _ Hin) as Hr. cbn [fst snd] in Hr.
    unfold zshad. replace (b / 8 + 2147450880) with (0x7fff8000 + b / 8) by lia.
    exact (readable_store_ok E M k _ _ HK Hr Hs). }
  exists (Z_to_bv 64 zpg), (Z_to_bv 64 zro).
  constructor.
  all: cbn [drv_unreg_tab both_unreg_tab both_poison_tab ut_dtor ut_base ut_pt ut_g_start ut_g_stop ut_p_start ut_globs ut_p_flag ut_g_aflags
            ut_p_aflags ut_p_mu ut_g_pgsz ut_c_inited ut_c_ro ut_str pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend
            pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm].
  all: try (first [exact Pmu | exact Pcpm | exact Pcpmnz | exact Pmb | exact Phe | exact Pme | exact Hra | exact Rpg | exact Rro]).
  all: try (apply CELL; vm_compute; reflexivity).
  - lia.
  - rewrite u64_lit by lia. lia.
  - exact (CELL 0x10ee98 1%nat 1 eq_refl).
  - exact (CELL 0x107e58 8%nat 0xfc38c eq_refl).
  - lia.
  - unfold poison_cells. cbn [both_poison_tab pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm].
    repeat (apply Forall_cons; [lia|]). apply Forall_nil.
  - unfold poison_cells. cbn [both_poison_tab pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm].
    repeat (apply Forall_cons; [lia|]). apply Forall_nil.
  - repeat split; first [lia | reflexivity].
  - cbn. lia.
  - change (Z.of_nat (length drv_unreg_globs)) with 9. repeat split; first [lia | reflexivity].
  - cbn. lia.
  - (* [comment removed for export] *)
    intros i b s Hnth.
    assert (SH : forall b' s', In (b', s') DNA.DTOR_GLOBS -> 1 <= s' / 8 < 2 ^ 64 ->
              store_ok BSEGS M (Z_to_bv 64 (zshad b')) (Z.to_nat (s' / 8)) = true)
      by (intros b' s' Hin Hs; apply SHD; [right; exact Hin | exact Hs]).
    do 9 (destruct i as [|i]; [cbn [nth_error drv_unreg_globs] in Hnth; injection Hnth as <- <-;
                                 split; [apply CELL; vm_compute; reflexivity|]; split; [apply CELL; vm_compute; reflexivity|]; split; [apply CELL; vm_compute; reflexivity|];
                                 split; [lia|]; split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [vm_compute; reflexivity|];
                                 apply SH; [vm_compute; tauto | vm_compute; split; [intro X; discriminate X | reflexivity]] |]).
    cbn in Hnth. destruct i; discriminate Hnth.
  - replace (at_ sp (-272)) with (Z_to_bv 64 (u sp - 272)) by reflexivity.
    apply (store_ok_sub BSEGS M (Z_to_bv 64 (u sp - 512)) _ 512 272); [rewrite u64_lit by lia; lia | exact Hstk | rewrite !u64_lit by lia; lia | rewrite !u64_lit by lia; lia].
  - exact (store_ok_wseg BSEGS M _ _ wseg_mu).
  - exact (store_ok_wseg BSEGS M _ _ wseg_flag).
  - exact (SHD DNA.DTOR_P_START (64 * 9) (or_introl eq_refl) ltac:(vm_compute; split; [intro X; discriminate X | reflexivity])).
  - apply Hoare.ret_ok_even. reflexivity.
  - vm_compute. discriminate.
Qed.
End DtorGate.
End BoDrvNodesSoundA10.
Require Stdlib.Logic.FunctionalExtensionality OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvNodesSoundA11.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnreg OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnregI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvDtor OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA3 BoDrvNodesSoundA6 BoDrvNodesSoundA10.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AzImageBoth.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u := bv_unsigned.
#[local] Notation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).
#[local] Notation r5 n := (Z_to_bv 5 (Z.of_nat n)).

Lemma gplan_tailF : gplan_ok tailF = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_tailN : gplan_ok tailN = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma XT70_cases : forall chk0 id args cs fd ps code,
  XT70g chk0 id args cs = Some (fd, ps, code) ->
  exists cs1, DNA.node_module_dtor BSEGS NXD cs = Some cs1
    /\ (chk0 cs1 tailF = COk (SEmitP fd ps (SExit code))
        \/ (chk0 cs1 tailN = COk (SExit code) /\ fd = 1 /\ ps = [])).
Proof.
  intros chk0 id args cs fd ps code H. unfold XT70g in H.
  destruct (negb (Nat.eqb id 70)); [discriminate H|].
  destruct (DNA.node_module_dtor BSEGS NXD cs) as [cs1|]; [|discriminate H].
  exists cs1. split; [reflexivity|].
  assert (TN : match chk0 cs1 tailN with COk (SExit c) => Some (1, @nil spiece, c) | _ => None end = Some (fd, ps, code) ->
               chk0 cs1 tailN = COk (SExit code) /\ fd = 1 /\ ps = []).
  { destruct (chk0 cs1 tailN) as [[ |c'| | | | | ]|]; intros X; try discriminate X. injection X as <- <- <-. auto. }
  destruct (chk0 cs1 tailF) as [s|n0 p0 c0] eqn:HF; [|right; exact (TN H)].
  destruct s as [ |c1|fd1 ps1 s1| | | | ]; try (right; exact (TN H)).
  destruct s1 as [ |c2| | | | | ]; try (right; exact (TN H)).
  injection H as <- <- <-. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Wp_agree_eb : forall E E' fd ps, eb E = eb E' -> GPS.Wp E fd ps = GPS.Wp E' fd ps.
Proof.
  intros E E' fd ps He. unfold GPS.Wp. f_equal. induction ps as [|q r IH]; [reflexivity|]. cbn [flat_map]. rewrite IH. f_equal.
  destruct q; cbn [GPS.piece_den]; [reflexivity | rewrite He; reflexivity].
Qed.

Lemma unreg_clob_ridx : forall x : Prelude.reg, In x unreg_clob -> In (ridx x) (10%nat :: DNA.CLOB).
Proof.
  intros x H. unfold unreg_clob in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [vm_compute; auto 20|]). destruct H.
Qed.

(* [comment removed for export] *)
Definition in_lsb (z : Z) : bool := (Z.leb DNA.LOWSH_LO z && Z.ltb z DNA.LOWSH_HI)%bool.
Definition in_mub (z : Z) : bool := (Z.leb DNA.DTOR_MU z && Z.ltb z (DNA.DTOR_MU + 8))%bool.
Definition in_flb (z : Z) : bool := (Z.leb DNA.DTOR_FLAG z && Z.ltb z (DNA.DTOR_FLAG + 8))%bool.

Lemma glob_shadow_in_lowsh :
  Forall (fun bs : Z * Z => DNA.LOWSH_LO <= zshad (fst bs) /\ zshad (fst bs) + snd bs / 8 <= DNA.LOWSH_HI) ((0x10a8c0, 64 * 9) :: drv_unreg_globs).
Proof. repeat (apply Forall_cons; [vm_compute; split; intro X; discriminate X|]). apply Forall_nil. Qed.

Lemma know_havoc_lit : forall E (Ma Mb : word -> option byte) k lo n,
  know_ok BSEGS E Ma k -> 0 <= n < 2 ^ 64 ->
  (forall x : word, u x < lo \/ lo + n <= u x -> Mb x = Ma x) -> mem_grows Ma Mb ->
  know_ok BSEGS E Mb (kn_havoc k (ELit 0) lo (ELit n)).
Proof.
  intros E Ma Mb k lo n HK Hn Hout Hg. eapply APS.know_ok_havoc; [exact HK | | exact Hg].
  intros x Hx. apply Hout. rewrite estart_lit0 in Hx. unfold elenZ in Hx. cbn [edenot] in Hx. rewrite u64_lit in Hx by lia. exact Hx.
Qed.

Section NodesSoundA11.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 BSEGS RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GBOTH SHC AINVH.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Hypothesis M2S_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (LE8 0) /\ rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (LE8 0x7fffffffffff)
  /\ exists me : Z, rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 me).
Hypothesis DTOR_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (LE8 0)
  /\ exists cpm : byte, rdn BSEGS M (Z_to_bv 64 0x10da1c) 1 = Some [cpm] /\ u cpm <> 0.
(* [comment removed for export] *)
Hypothesis DTOR_FRAME : forall L LF B C K M M' mdl, AINVH L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (u a) = true \/ in_mub (u a) = true) /\ M' a <> None) ->
  rdn BSEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (LE8 0) ->
  AINVH L LF B C K M' mdl.
(* [comment removed for export] *)
Hypothesis PERM_flag : forall a, DNA.DTOR_FLAG <= a < DNA.DTOR_FLAG + 8 -> in_wins PERMc a.

#[local] Notation AINVat M0 := (AINV_f SWIN GBOTH AINVH PERMc SPTOPc HIDc HIDFc M0 B0c C0c).
#[local] Notation AINVc := (AINVat M0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation cs_okat M0 := (GPS.cs_ok BSEGS PERMc SPTOPc FS0 SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINV).
#[local] Notation cs_okA := (cs_okat M0c).
#[local] Notation Mr := (GPS.Mr SHC VSHc).
#[local] Notation AF := (AINV_f_frame SWIN GBOTH SHC AINVH HP both_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation ALZ := (AINV_f_lazy SWIN GBOTH SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation AFACTS := (AINV_f_facts SWIN GBOTH SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c).

(* [comment removed for export] *)
Variable chk0 : acs -> plan -> cres.
Hypothesis TAIL_sound : forall (M0' : word -> option byte) pl cs s,
  gplan_ok pl = true -> chk0 cs pl = COk s ->
  forall E fx R M model, cs_okat M0' E cs fx R M model ->
  RZ (cfgF BSEGS fx R (pc cs) M model) (GPS.sd (fun _ _ _ => t_nil) t_nil E (m_fs model) s).

Lemma hid_image_false11 : forall E cs B C K M mdl (a : word),
  AINVc (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  g_img_lo GBOTH <= u a -> u a < g_img_hi GBOTH -> GPS.hid SHC VSHc E cs mdl a = false.
Proof.
  intros E cs B C K M mdl a HA Hlo Hhi. unfold GPS.hid, GPS.lz.
  destruct (page_in_ranges (page_base a) (m_vm_lazy mdl)) eqn:Hp; [|reflexivity]. exfalso.
  unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hiv Hc]].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) (AFACTS _ _ _ _ _ _ _ HA) iv Hiv) as (L0 & L1 & L2).
  pose proof (GPS.page_base_le' a) as (P1 & P2 & P3).
  cbn [g_img_lo g_img_hi GBOTH] in Hlo, Hhi, L2.
  unfold page_size in *. clear - H1 H2 P1 P2 P3 L2 Hlo Hhi. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_Mr_image : forall E cs B C K M mdl (a : Z) (n : nat),
  AINVc (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  g_img_lo GBOTH <= a -> a + Z.of_nat n <= g_img_hi GBOTH ->
  rdn BSEGS (Mr E cs mdl M) (Z_to_bv 64 a) n = rdn BSEGS M (Z_to_bv 64 a) n.
Proof.
  intros E cs B C K M mdl a n HA Hlo Hhi. cbn [g_img_lo g_img_hi GBOTH] in Hlo, Hhi.
  apply rdn_ext; [rewrite u64_lit by lia; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia. unfold GPS.Mr, mrestrict.
  rewrite (hid_image_false11 E cs B C K M mdl x HA) by (cbn [g_img_lo g_img_hi GBOTH]; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma dtor_core : forall cs E E' fx R M model T (ret : Z) sr2 k' nx2 regs' Mr',
  cs_okA E cs fx R M model ->
  fresh_ok NXD cs = true ->
  env_agree (nxt cs) E E' ->
  msteps BSEGS (restrict (GPS.hid SHC VSHc E cs model) (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom BSEGS)))
               (mkstF fx regs' (Z_to_bv 64 ret) Mr' (seg_rom BSEGS)) ->
  (forall a, Mr' a <> Mr E cs model M a ->
     (gowned SWIN PERMc SPTOPc SB (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) a \/ in_lsb (u a) = true \/ in_mub (u a) = true)
     /\ Mr' a <> None) ->
  rdn BSEGS Mr' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (LE8 0) ->
  regs_ok E' sr2 regs' ->
  know_ok BSEGS E' Mr' k' ->
  (forall M0' fx'' R' M'' model',
      cs_okat M0' E' (with_ss cs (mk_ss ret sr2 k' nx2)) fx'' R' M'' model' -> m_fs model' = m_fs model ->
      RZ (cfgF BSEGS fx'' R' ret M'' model') T) ->
  RZ (cfgF BSEGS fx R (pc cs) M model) T.
Proof.
  intros cs E E' fx R M model T ret sr2 k' nx2 regs' Mr' HC Hfresh Hag Hms Hown Hmu HR' HK' Hk.
  destruct (fresh_ok_parts NXD cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (GPS.fresh_ok_parts2 NXD cs Hfresh) as [Ffk Fmt].
  eapply (GPS.restricted_run_sound BSEGS ABOTH PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc ALZ AFACTS fx_ok UINV RZ RZ_silent1 both_in_hull both_segs_wx);
    [exact HC | exact Hms |].
  intros model' Hsame Hhid Hhalt' Hfs' Hfds' HA' Hclean.
  unfold unrestrict. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom mkstF mkst].
  set (M'' := munrestrict (GPS.hid SHC VSHc E cs model) M Mr').
  apply (Hk M'' fx regs' M'' model'); [|exact Hfs'].
  pose proof (GPS.cs_ok_agree BSEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC1.
  (* [comment removed for export] *)
  assert (CH : forall a, M'' a <> M a ->
            (gowned SWIN PERMc SPTOPc SB (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) a \/ in_lsb (u a) = true \/ in_mub (u a) = true)
            /\ M'' a <> None).
  { intros a Ha. unfold M'', munrestrict in Ha |- *.
    destruct (GPS.hid SHC VSHc E cs model a) eqn:EH; [exfalso; apply Ha; reflexivity|].
    apply Hown. unfold GPS.Mr, mrestrict. rewrite EH. exact Ha. }
  assert (HAE : AINVat M'' (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) M'' model').
  { set (M1 := fun a : word => if (in_lsb (u a) || in_mub (u a))%bool then M a else M'' a).
    assert (H1 : AINVc (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) M1 model').
    { apply (AF _ _ _ _ _ M M1 model' HA'). intros a Ha. unfold M1 in Ha |- *.
      destruct (in_lsb (u a) || in_mub (u a))%bool eqn:Hs; [exfalso; apply Ha; reflexivity|].
      apply orb_false_iff in Hs as [Hs1 Hs2].
      destruct (CH a Ha) as [[Ho|[Hl|Hm]] Hd]; [split; [exact Ho | exact Hd] | rewrite Hs1 in Hl; discriminate Hl | rewrite Hs2 in Hm; discriminate Hm]. }
    destruct H1 as (HAH & HPo & HT & HF & HD).
    assert (H2 : AINVH (blocks_den E (a_vis cs) ++ HIDc) (blocks_den E (a_fake cs) ++ HIDFc) (B0c + bcost E (a_vis cs)) (C0c + bcount (a_vis cs))
                   (uE E (a_meter cs)) M'' model').
    { apply (DTOR_FRAME _ _ _ _ _ M1 M'' model' HAH).
      - intros a Ha. unfold M1 in Ha. destruct (in_lsb (u a) || in_mub (u a))%bool eqn:Hs; [|exfalso; apply Ha; reflexivity].
        split; [apply orb_prop in Hs; exact Hs | exact (proj2 (CH a Ha))].
      - rewrite <- Hmu. apply rdn_ext; [rewrite u64_lit by (unfold DNA.DTOR_MU; lia); unfold DNA.DTOR_MU; lia|].
        intros x Hx. rewrite u64_lit in Hx by (unfold DNA.DTOR_MU; lia). unfold M'', munrestrict.
        rewrite <- Hhid. rewrite (hid_image_false11 E cs _ _ _ M model' x HA') by (cbn [g_img_lo g_img_hi GBOTH]; unfold DNA.DTOR_MU in Hx; lia).
        reflexivity. }
    split; [exact H2|]. split; [exact HPo|]. split; [exact HT|]. split; [intros a _; reflexivity | intros a _ X; exact X]. }
  pose proof (same_but_materialized_frame model model' Hsame) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfds & _ & _ & Hfs & Hhalt & _).
  destruct HC1 as [CR CL CK CH0 CF CD CA CU CX CP CT CK2 CFB CFL]; constructor;
    cbn [with_ss a_ss a_vis a_fake a_meter a_totsz a_eager kn mk_ss s_regs s_log s_know]; try assumption; try reflexivity.
  - (* [comment removed for export] *)
    change (Mr E' (with_ss cs (mk_ss ret sr2 k' nx2)) model' M'') with (Mr E' cs model' M'').
    rewrite (GPS.Mr_agreeE NXD SHC VSHc E E' cs model' _ Hag Hfresh).
    unfold GPS.Mr. rewrite Hhid. unfold M''. rewrite mrestrict_munrestrict.
    replace (mrestrict (GPS.hid SHC VSHc E cs model) Mr') with Mr'; [exact HK'|].
    apply functional_extensionality. intros a. unfold mrestrict. destruct (GPS.hid SHC VSHc E cs model a) eqn:EH; [|reflexivity].
    pose proof (Hclean a EH) as HX. cbn [ms_mem mkstF mkst] in HX. rewrite HX. reflexivity.
  - rewrite Hfs'. exact CF.
  - eapply GPS.fds_ok_model; [exact Hfds | exact Hfs | exact CD].
  - rewrite (blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
    rewrite (blocks_den_agree (nxt cs) E E' (a_fake cs) Hag Ffk).
    rewrite (bcost_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
    rewrite (GPS.uE_agree (nxt cs) E E' (a_meter cs) Hag Fmt). exact HAE.
Qed.

(* [comment removed for export] *)
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.

Theorem XT70_sound : GPS.term_stmt BSEGS (XT70g chk0) PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  intros id args cs fd ps code E fx R M model HC HX.
  destruct (XT70_cases chk0 id args cs fd ps code HX) as (cs1 & Hn & Hcase).
  unfold DNA.node_module_dtor in Hn.
  destruct (negb (Z.eqb (pc cs) DNA.X_MODULE_DTOR)) eqn:Hpcb; [discriminate Hn|].
  apply negb_false_iff in Hpcb. apply Z.eqb_eq in Hpcb.
  destruct (ret_lit cs) as [ra|] eqn:Hret; [|discriminate Hn].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate Hn] end. cbn [negb] in Hn.
  apply andb_prop in Hg as [Hg Hcells]. apply andb_prop in Hg as [Hspok Hfresh].
  set (rs := (10%nat :: DNA.CLOB)) in *.
  unfold node_havoc in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hhv; [|discriminate Hn] end.
  apply andb_prop in Hhv as [_ Hrs]. injection Hn as Ecs1.
  assert (Hrs' : Forall (fun r => 0 < r < 32)%nat rs).
  { apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as X.
    apply andb_prop in X as [X1 X2]. apply Nat.ltb_lt in X1. apply Nat.ltb_lt in X2. lia. }
  pose proof (co_know HC) as HK. pose proof (co_ainv HC) as HA.
  destruct (GCL.ret_lit_sound E cs R ra (co_regs HC) Hret) as (G1 & RA & Hra & Hraev).
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 2 HC ltac:(lia)) as G2.
  (* [comment removed for export] *)
  unfold DNA.dtor_sp_ok in Hspok. cbv zeta in Hspok. destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp2.
  apply andb_prop in Hspok as [Hspok Hsplohi]. apply andb_prop in Hspok as [Hkw Hfl].
  destruct (xlo (kn cs) (reg cs 2)) as [slo|] eqn:Hslo; [|discriminate Hsplohi].
  destruct (xhi (kn cs) (reg cs 2)) as [shi|] eqn:Hshi; [|discriminate Hsplohi].
  apply andb_prop in Hsplohi as [Hsplo Hsphi]. apply Z.leb_le in Hsplo. apply Z.leb_le in Hsphi.
  pose proof (xlo_sound BSEGS E _ (kn cs) _ _ HK Hslo) as S1. pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hshi) as S2.
  set (spw := edenot E (reg cs 2)) in *. set (spz := u spw) in *.
  destruct (GCL.kwritable_x_sound BSEGS E _ (kn cs) (kn cs) spb (spk - 512) (ELit 512) HK HK Hkw) as (Hst & Hs0 & Hs1).
  assert (Hl512 : elenZ E (ELit 512) = 512) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  rewrite Hl512 in Hs1.
  assert (Hest2 : estart E (SA spb (spk - 512)) = spz - 512).
  { pose proof (split_lit_denot E _ spb spk Hsp2) as X. apply (f_equal bv_unsigned) in X. fold spw in X. fold spz in X.
    rewrite Z_to_bv_unsigned, bv_wrap64_mod in X. unfold estart in Hs0, Hs1 |- *. cbn [a_base a_off] in Hs0, Hs1 |- *.
    unfold DNA.KHIMEM in Hsplo.
    destruct (Z.eq_dec (u (edenot E spb) + spk) (2 ^ 64)) as [E64|N64].
    - rewrite E64, Z.mod_same in X by lia. lia.
    - rewrite Z.mod_small in X by lia. lia. }
  rewrite Hest2 in Hst, Hs0, Hs1.
  unfold DNA.KHIMEM in Hsplo. unfold two47 in Hsphi.
  (* [comment removed for export] *)
  destruct (M2S_H _ _ _ _ _ _ _ (proj1 HA)) as (P1 & P2 & me & P3).
  destruct (DTOR_H _ _ _ _ _ _ _ (proj1 HA)) as (Pmu & cpm & Pcpm & Pcpmnz).
  assert (IMG : forall a n, g_img_lo GBOTH <= a -> a + Z.of_nat n <= g_img_hi GBOTH ->
                rdn BSEGS (Mr E cs model M) (Z_to_bv 64 a) n = rdn BSEGS M (Z_to_bv 64 a) n)
    by (intros a n Ha1 Ha2; exact (rdn_Mr_image E cs _ _ _ M model a n HA Ha1 Ha2)).
  assert (IMGL : forall a n, 0x10000 <= a -> a + Z.of_nat n <= 0x63b000 ->
                rdn BSEGS (Mr E cs model M) (Z_to_bv 64 a) n = rdn BSEGS M (Z_to_bv 64 a) n)
    by (intros a n Ha1 Ha2; apply IMG; cbn [g_img_lo g_img_hi GBOTH]; lia).
  pose proof (eq_trans (IMGL 0x10ba70 8%nat ltac:(lia) ltac:(lia)) Pmu) as Qmu.
  pose proof (eq_trans (IMGL 0x10da1c 1%nat ltac:(lia) ltac:(lia)) Pcpm) as Qcpm.
  pose proof (eq_trans (IMGL 0x10eea8 8%nat ltac:(lia) ltac:(lia)) P1) as Q1.
  pose proof (eq_trans (IMGL 0x10eea0 8%nat ltac:(lia) ltac:(lia)) P2) as Q2.
  pose proof (eq_trans (IMGL 0x10eeb0 8%nat ltac:(lia) ltac:(lia)) P3) as Q3.
  destruct (dtor_unregH E (Mr E cs model M) (kn cs) spw (Z_to_bv 64 ra) me cpm HK Hcells ltac:(fold spz; lia) ltac:(fold spz; lia)
              (Hst 512%nat ltac:(lia)) RA Qmu Qcpm Pcpmnz Q1 Q2 Q3) as (pg & ro & UH).
  destruct (@drv_dtor_run fx (Mr E cs model M) (seg_rom BSEGS) spw (Z_to_bv 64 ra) (Z_to_bv 64 1) cpm (Z_to_bv 64 me) (2 ^ 64 - 1) pg ro R UH
              ltac:(rewrite <- G1; f_equal; apply bv_eq; reflexivity)
              ltac:(transitivity (getr R (r5 2)); [f_equal; apply bv_eq; reflexivity | exact G2]))
    as (r' & Mr' & Hms & Hagr & Hout & Hsh & Hmu' & Hflag' & Hgr).
  fold spz in Hout.
  (* [comment removed for export] *)
  assert (UNCH : forall x : word, ~ (spz - 272 <= u x < spz) -> in_lsb (u x) = false -> in_flb (u x) = false -> in_mub (u x) = false ->
            Mr' x = Mr E cs model M x).
  { intros x Hfr Hl Hf Hm. unfold in_lsb, in_flb, in_mub, DNA.DTOR_FLAG, DNA.DTOR_MU in Hl, Hf, Hm.
    apply andb_false_iff in Hf. apply andb_false_iff in Hm. rewrite Z.leb_gt, Z.ltb_ge in Hf, Hm.
    destruct (Z_lt_ge_dec (u x) 0x7fff8000) as [Hb|Hb]; [apply Hout; lia|].
    destruct (Z_lt_ge_dec (u x) 0x8fff8000) as [Hb2|Hb2]; [|apply Hout; lia].
    apply Hsh; [lia|]. apply andb_false_iff in Hl. rewrite Z.leb_gt, Z.ltb_ge in Hl.
    eapply Forall_impl; [|exact glob_shadow_in_lowsh]. intros bs [B1 B2]. cbv beta. lia. }
  assert (DEFD : forall x : word, Mr' x <> Mr E cs model M x -> Mr' x <> None).
  { intros x Hx Hnone. destruct (Mr E cs model M x) eqn:Hm.
    - apply (Hgr x); [rewrite Hm; discriminate | exact Hnone].
    - apply Hx. exact Hnone. }
  destruct (fresh_ok_parts NXD cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  assert (Hspv : AP.expr_vars_lt (nxt cs) spb = true).
  { eapply GCL.split_lit_vars; [exact Hsp2|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
  set (E' := ext_list E (nxt cs) (map (fun r => getr r' (r5 r)) rs)).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  set (k0 := kn_havoc (kn_havoc (kn_havoc (kn cs) (ELit 0) DNA.LOWSH_LO (ELit (DNA.LOWSH_HI - DNA.LOWSH_LO))) (ELit 0) DNA.DTOR_FLAG (ELit 8))
                      (ELit 0) DNA.DTOR_MU (ELit 8)) in *.
  apply (dtor_core cs E E' fx R M model _ ra (sr_fresh (s_regs (a_ss cs)) rs (nxt cs))
           (DNA.havoc_scratch k0 (reg cs 2) 512) (nxt cs + length rs)%nat r' Mr' HC Hfresh Hag).
  - rewrite Hpcb. cbn [restrict mkstF mkst ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
    rewrite (w_lit DNA.X_MODULE_DTOR (0xc5cd0%bv : word) eq_refl). exact Hms.
  - (* [comment removed for export] *)
    intros x Hx. split; [|exact (DEFD x Hx)].
    destruct (in_lsb (u x)) eqn:Hl; [right; left; reflexivity|].
    destruct (in_mub (u x)) eqn:Hm; [right; right; reflexivity|]. left.
    destruct (in_flb (u x)) eqn:Hf.
    + left. right. left. apply PERM_flag. unfold in_flb in Hf. apply andb_prop in Hf as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. lia.
    + left. right. right. left.
      assert (Hin : spz - 272 <= u x < spz).
      { destruct (Z_lt_ge_dec (u x) (spz - 272)) as [Hlt|Hge]; [exfalso; apply Hx; apply UNCH; [lia | exact Hl | exact Hf | exact Hm]|].
        destruct (Z_lt_ge_dec (u x) spz) as [Hlt2|Hge2]; [lia|]. exfalso. apply Hx. apply UNCH; [lia | exact Hl | exact Hf | exact Hm]. }
      pose proof (in_floor_sound BSEGS E _ (kn cs) _ _ _ spb (spk - 512) (ELit 512) x HK Hfl (co_floor HC)
                    ltac:(rewrite Hest2, Hl512; lia)) as [F1 F2].
      rewrite (co_top HC) in F1. exact F1.
  - exact Hmu'.
  - (* [comment removed for export] *)
    apply (regs_ok_havoc_to rs E _ _ r' (nxt cs) (co_regs HC) Fsr Hrs').
    intros x Hx. apply Hagr. intros Hc. exact (Hx (unreg_clob_ridx x Hc)).
  - (* [comment removed for export] *)
    assert (HK' : know_ok BSEGS E' (Mr E cs model M) (kn cs)) by (eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK]).
    set (Mq := Mr E cs model M) in *.
    set (M_1 := fun x : word => if in_lsb (u x) then Mr' x else Mq x).
    set (M_2 := fun x : word => if (in_lsb (u x) || in_flb (u x))%bool then Mr' x else Mq x).
    set (M_3 := fun x : word => if (in_lsb (u x) || in_flb (u x) || in_mub (u x))%bool then Mr' x else Mq x).
    assert (K1 : know_ok BSEGS E' M_1 (kn_havoc (kn cs) (ELit 0) DNA.LOWSH_LO (ELit (DNA.LOWSH_HI - DNA.LOWSH_LO)))).
    { apply (know_havoc_lit E' Mq M_1 _ _ _ HK'); [vm_compute; split; [intro X; discriminate X | reflexivity] | |].
      - intros x Hx. unfold M_1. replace (in_lsb (u x)) with false; [reflexivity|]. symmetry. unfold in_lsb. apply andb_false_iff. rewrite Z.leb_gt, Z.ltb_ge. lia.
      - intros x Hx. unfold M_1. destruct (in_lsb (u x)); [apply (Hgr x Hx) | exact Hx]. }
    assert (K2 : know_ok BSEGS E' M_2 (kn_havoc (kn_havoc (kn cs) (ELit 0) DNA.LOWSH_LO (ELit (DNA.LOWSH_HI - DNA.LOWSH_LO))) (ELit 0) DNA.DTOR_FLAG (ELit 8))).
    { apply (know_havoc_lit E' M_1 M_2 _ _ _ K1); [lia | |].
      - intros x Hx. unfold M_1, M_2. replace (in_flb (u x)) with false; [rewrite orb_false_r; reflexivity|]. symmetry. unfold in_flb. apply andb_false_iff. rewrite Z.leb_gt, Z.ltb_ge. lia.
      - intros x Hx. unfold M_1, M_2 in *. destruct (in_lsb (u x)); cbn [orb]; [exact Hx|]. destruct (in_flb (u x)); [apply (Hgr x Hx) | exact Hx]. }
    assert (K3 : know_ok BSEGS E' M_3 k0).
    { apply (know_havoc_lit E' M_2 M_3 _ _ _ K2); [lia | |].
      - intros x Hx. unfold M_2, M_3. replace (in_mub (u x)) with false; [rewrite orb_false_r; reflexivity|]. symmetry. unfold in_mub. apply andb_false_iff. rewrite Z.leb_gt, Z.ltb_ge. lia.
      - intros x Hx. unfold M_2, M_3 in *. destruct (in_lsb (u x) || in_flb (u x))%bool; cbn [orb]; [exact Hx|]. destruct (in_mub (u x)); [apply (Hgr x Hx) | exact Hx]. }
    unfold DNA.havoc_scratch. rewrite Hsp2.
    eapply APS.know_ok_havoc; [exact K3 | |].
    + intros x Hx. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx.
      rewrite <- (edenot_agree' (nxt cs) E E' spb Hag Hspv) in Hx. rewrite u64_lit in Hx by lia.
      unfold estart in Hest2. cbn [a_base a_off] in Hest2.
      unfold M_3. destruct (in_lsb (u x)) eqn:Hl; cbn [orb]; [reflexivity|]. destruct (in_flb (u x)) eqn:Hf; cbn [orb]; [reflexivity|].
      destruct (in_mub (u x)) eqn:Hm; [reflexivity|]. apply UNCH; [lia | exact Hl | exact Hf | exact Hm].
    + intros x Hx. unfold M_3 in Hx. destruct (in_lsb (u x) || in_flb (u x) || in_mub (u x))%bool; [exact Hx | apply (Hgr x Hx)].
  - (* [comment removed for export] *)
    intros M0' fx'' R' M'' model' HC' Hfs'. rewrite <- Ecs1 in Hcase.
    assert (HW : GPS.Wp E' fd ps = GPS.Wp E fd ps) by (symmetry; apply Wp_agree_eb; exact (proj2 Hag)).
    destruct Hcase as [HF|(HN & -> & ->)].
    + pose proof (TAIL_sound M0' tailF _ _ gplan_tailF HF E' fx'' R' M'' model' HC') as HT.
      cbn [GPS.sd] in HT. rewrite HW, Hfs' in HT. exact HT.
    + pose proof (TAIL_sound M0' tailN _ _ gplan_tailN HN E' fx'' R' M'' model' HC') as HT.
      cbn [GPS.sd] in HT. rewrite Hfs' in HT.
      eapply RZ_conseq; [exact HT|]. intros tr. symmetry. apply t_emit_nil_eq. apply t_exit_has_nil.
Qed.
End NodesSoundA11.
End BoDrvNodesSoundA11.
Module BoDrvNodesSoundA8.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA3 BoDrvNodesSoundA6 BoDrvNodesSoundA7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Definition pbytes (E : env) (ps : list spiece) : list byte := flat_map (GPS.piece_den E) ps.
Lemma pbytes_app : forall E p q, pbytes E (p ++ q) = pbytes E p ++ pbytes E q.
Proof. intros. unfold pbytes. rewrite flat_map_app. reflexivity. Qed.
Lemma pbytes_flush : forall E acc ps, pbytes E (DNA.flush_lit acc ps) = pbytes E ps ++ map (Z_to_bv 8) (rev acc).
Proof.
  intros E acc ps. unfold DNA.flush_lit. destruct acc as [|z r]; [cbn; rewrite app_nil_r; reflexivity|].
  rewrite pbytes_app. cbn [pbytes flat_map GPS.piece_den]. rewrite app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_app_Z : forall (M : word -> option byte) bs1 (a : Z) bs2,
  rdn BSEGS M (Z_to_bv 64 a) (length bs1) = Some bs1 ->
  rdn BSEGS M (Z_to_bv 64 (a + Z.of_nat (length bs1))) (length bs2) = Some bs2 ->
  rdn BSEGS M (Z_to_bv 64 a) (length (bs1 ++ bs2)) = Some (bs1 ++ bs2).
Proof.
  intros M bs1. induction bs1 as [|b1 r IH]; intros a bs2 H1 H2.
  - cbn [length app Z.of_nat] in *. rewrite Z.add_0_r in H2. exact H2.
  - cbn [length app] in *. cbn [rdn] in H1 |- *.
    destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom BSEGS (Z_to_bv 64 a) end) as [b|]; [|discriminate].
    rewrite Z_to_bv64_succ in H1 |- *.
    destruct (rdn BSEGS M (Z_to_bv 64 (a + 1)) (length r)) as [rest|] eqn:Hr; [|discriminate].
    injection H1 as -> ->.
    rewrite (IH (a + 1) bs2 Hr); [reflexivity|].
    replace (a + 1 + Z.of_nat (length r)) with (a + Z.of_nat (S (length r))) by lia. exact H2.
Qed.

(* [comment removed for export] *)
Lemma kreadZ1_sound : forall E M k b o z,
  know_ok BSEGS E M k -> kreadZ BSEGS k b o 1 = Some z -> flat E (SA b o) 1 ->
  rdn BSEGS M (Z_to_bv 64 (estart E (SA b o))) 1 = Some [Z_to_bv 8 z].
Proof.
  intros E M k b o z HK H Hfl. unfold kreadZ in H.
  destruct (know_lookup BSEGS k b o 1 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v as [zl| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  destruct (GCL.lookup_piece BSEGS E M k b o 1 (ELit zl) hs HK ltac:(lia) HL Hfl) as (bs & Hrd & Hlen & Hbs).
  rewrite Hrd, <- Hbs. cbn [edenot]. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma blob_litlen_sound : forall E M k j n,
  know_ok BSEGS E M k -> DNA.blob_litlen k j = Some n -> Z.of_nat (length (eb E j)) = n.
Proof.
  intros E M k j n HK H. unfold DNA.blob_litlen in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate H].
  apply List.find_some in Hf as [Hin HKp].
  destruct K as [ | |a L j'| | | | | | | | | ]; try discriminate H.
  apply Nat.eqb_eq in HKp. subst j'.
  destruct (xlo k L) as [lo|] eqn:Hlo; [|discriminate H]. destruct (xhi k L) as [hi|] eqn:Hhi; [|discriminate H].
  destruct (Z.eqb lo hi) eqn:He; [|discriminate H]. injection H as <-. apply Z.eqb_eq in He.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as KB. cbn [kentry_ok] in KB. destruct KB as (_ & Hlen & _). unfold elenZ in Hlen.
  pose proof (xlo_sound BSEGS E M k _ _ HK Hlo). pose proof (xhi_sound BSEGS E M k _ _ HK Hhi). lia.
Qed.

Lemma skipn_firstn_cons : forall (w : nat) (l : list byte) (i : nat),
  (i + w <= length l)%nat -> skipn i l = firstn w (skipn i l) ++ skipn (i + w) l.
Proof. intros w l i H. rewrite <- (firstn_skipn w (skipn i l)) at 1. rewrite skipn_skipn. f_equal. f_equal. lia. Qed.

Lemma eblob_run_sound : forall E M k b j n fuel o i o',
  know_ok BSEGS E M k -> Z.of_nat (length (eb E j)) = n ->
  DNA.eblob_run fuel k b o j i n = Some o' -> 0 <= i ->
  i <= n /\ o' = o + (n - i)
  /\ rdn BSEGS M (Z_to_bv 64 (estart E (SA b o))) (length (skipn (Z.to_nat i) (eb E j))) = Some (skipn (Z.to_nat i) (eb E j)).
Proof.
  intros E M k b j n fuel. induction fuel as [|f IH]; intros o i o' HK Hn H Hi; [discriminate H|].
  cbn [DNA.eblob_run] in H.
  destruct (Z.leb n i) eqn:Hni.
  - destruct (Z.eqb n i) eqn:He; [|discriminate H]. injection H as <-. apply Z.eqb_eq in He. subst i.
    split; [lia|]. split; [lia|]. rewrite skipn_all2 by lia. reflexivity.
  - apply Z.leb_gt in Hni.
    destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate H].
    apply List.find_some in Hf as [Hin HKp].
    destruct K as [[kb ko] w v| | | | | | | | | | | ]; try discriminate HKp.
    destruct v as [ | | | | | | |sx j' i' w']; try discriminate HKp. destruct sx; [discriminate HKp|].
    apply andb_prop in HKp as [HKp Hw]. apply andb_prop in HKp as [HKp Hi']. apply andb_prop in HKp as [HKp Hj]. apply andb_prop in HKp as [Hb Ho].
    apply expr_eqb_eq in Hb. apply Z.eqb_eq in Ho. apply Nat.eqb_eq in Hj. apply Z.eqb_eq in Hi'. apply Nat.eqb_eq in Hw. subst kb ko j' i' w'.
    destruct (IH _ _ _ HK Hn H ltac:(lia)) as (I1 & I2 & I3).
    split; [lia|]. split; [lia|].
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as KW. cbn [kentry_ok] in KW. destruct KW as (Hw8 & Hfl & Hrd).
    pose proof (flat_u E (SA b o) _ Hfl) as U1.
    assert (Hcov : (Z.to_nat i + w <= length (eb E j))%nat) by lia.
    assert (Hpl : length (firstn w (skipn (Z.to_nat i) (eb E j))) = w) by (rewrite firstn_length, skipn_length; lia).
    rewrite (skipn_firstn_cons w (eb E j) (Z.to_nat i) Hcov).
    apply rdn_app_Z.
    + rewrite Hpl. replace (Z_to_bv 64 (estart E (SA b o))) with (adenot E (SA b o)) by (apply bv_eq; rewrite U1; destruct Hfl as (F1 & F2 & _); rewrite u64_lit by lia; reflexivity).
      rewrite Hrd. f_equal. cbn [edenot]. unfold blob_val, blob_bytes.
      apply GCL.word_to_le_bytes_of_bytes_n; [exact Hpl | exact Hw8].
    + rewrite Hpl. replace (estart E (SA b o) + Z.of_nat w) with (estart E (SA b (o + Z.of_nat w))) by (unfold estart; cbn [a_base a_off]; lia).
      replace (Z.to_nat i + w)%nat with (Z.to_nat (i + Z.of_nat w)) by lia. exact I3.
Qed.

(* [comment removed for export] *)
Lemma eadd_u : forall E a c, u (edenot E (eadd a c)) = (u (edenot E a) + u (edenot E c)) mod 2 ^ 64.
Proof. intros E a c. unfold eadd. rewrite mkAlu_denot. unfold Sem.alu64, Sem.alu. rewrite bv_add_unsigned, bv_wrap64_mod. reflexivity. Qed.

Lemma pos_eq_sound : forall E M k b o sb so,
  know_ok BSEGS E M k -> DNA.pos_eq k b o sb so = true -> estart E (SA b o) = estart E (SA sb so).
Proof.
  intros E M k b o sb so HK H. unfold DNA.pos_eq in H. apply orb_prop in H as [H|H].
  - apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
  - apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound BSEGS E M k _ _ HK H1) as X1. pose proof (lin_ge0_sound BSEGS E M k _ _ HK H2) as X2.
    cbn [xt_den] in X1, X2. unfold estart. cbn [a_base a_off]. lia.
Qed.

Lemma pieces_walk_sound : forall E M k sb so fuel b o acc ps out,
  know_ok BSEGS E M k ->
  DNA.pieces_walk BSEGS fuel k b o sb so acc ps = Some out ->
  exists rem, pbytes E out = pbytes E (DNA.flush_lit acc ps) ++ rem
    /\ forall H, Z.of_nat (length rem) <= H -> 0 <= estart E (SA b o) -> estart E (SA b o) + H < 2 ^ 64 ->
         rdn BSEGS M (Z_to_bv 64 (estart E (SA b o))) (length rem) = Some rem
         /\ estart E (SA b o) + Z.of_nat (length rem) = estart E (SA sb so).
Proof.
  intros E M k sb so fuel. induction fuel as [|f IH]; intros b o acc ps out HK H; [discriminate H|].
  cbn [DNA.pieces_walk] in H.
  destruct (DNA.pos_eq k b o sb so) eqn:Hpe.
  { injection H as <-. exists []. split; [rewrite app_nil_r; reflexivity|]. intros H0 _ _ _. split; [reflexivity|].
    cbn [length Z.of_nat]. rewrite Z.add_0_r. exact (pos_eq_sound E M k b o sb so HK Hpe). }
  (* [comment removed for export] *)
  assert (REST : match kreadZ BSEGS k b o 1 with
                 | Some z => DNA.pieces_walk BSEGS f k b (o + 1) sb so (z :: acc) ps
                 | None =>
                     match List.find (fun K => match K with KWord (SA kb ko) _ (EBlob false _ 0 _) => expr_eqb kb b && Z.eqb ko o | _ => false end) k with
                     | Some (KWord _ _ (EBlob _ j _ _)) =>
                         match DNA.blob_litlen k j with
                         | Some n => match DNA.eblob_run 600 k b o j 0 n with
                                     | Some o' => DNA.pieces_walk BSEGS f k b o' sb so [] (DNA.flush_lit acc ps ++ [SPBlob j])
                                     | None => None
                                     end
                         | None => None
                         end
                     | _ => None
                     end
                 end = Some out ->
          exists rem, pbytes E out = pbytes E (DNA.flush_lit acc ps) ++ rem
            /\ forall H, Z.of_nat (length rem) <= H -> 0 <= estart E (SA b o) -> estart E (SA b o) + H < 2 ^ 64 ->
                 rdn BSEGS M (Z_to_bv 64 (estart E (SA b o))) (length rem) = Some rem
                 /\ estart E (SA b o) + Z.of_nat (length rem) = estart E (SA sb so)).
  { intros HR. destruct (kreadZ BSEGS k b o 1) as [z|] eqn:Hz.
    - destruct (IH _ _ _ _ _ HK HR) as (rem' & Hout & Hrd).
      exists (Z_to_bv 8 z :: rem'). split.
      + rewrite Hout, !pbytes_flush. cbn [rev map]. rewrite map_app, <- !app_assoc. reflexivity.
      + intros H0 Hlen Hs0 Hs1. cbn [length] in Hlen.
        assert (Hfl : flat E (SA b o) 1) by (unfold flat; lia).
        pose proof (kreadZ1_sound E M k b o z HK Hz Hfl) as R1.
        destruct (Hrd (H0 - 1) ltac:(lia)) as [R2 R3]; [unfold estart in *; cbn [a_base a_off] in *; lia | unfold estart in *; cbn [a_base a_off] in *; lia |].
        split; [|cbn [length]; unfold estart in *; cbn [a_base a_off] in *; lia].
        change (Z_to_bv 8 z :: rem') with ([Z_to_bv 8 z] ++ rem'). apply rdn_app_Z; [exact R1|].
        replace (estart E (SA b o) + Z.of_nat (length [Z_to_bv 8 z])) with (estart E (SA b (o + 1))) by (unfold estart; cbn [a_base a_off length]; lia).
        exact R2.
    - match type of HR with context [List.find ?p k] => destruct (List.find p k) as [K|] eqn:Hf end; [|discriminate HR].
      destruct K as [[kb ko] w v| | | | | | | | | | | ]; try (cbv beta iota in HR; discriminate HR).
      destruct v as [ | | | | | | |sx j i' w']; try (cbv beta iota in HR; discriminate HR).
      destruct (DNA.blob_litlen k j) as [n|] eqn:Hbl; [|discriminate HR].
      destruct (DNA.eblob_run 600 k b o j 0 n) as [o'|] eqn:Her; [|discriminate HR].
      pose proof (blob_litlen_sound E M k j n HK Hbl) as Hn.
      destruct (eblob_run_sound E M k b j n 600 o 0 o' HK Hn Her ltac:(lia)) as (_ & Ho' & Rb). cbn [Z.to_nat skipn] in Rb.
      destruct (IH _ _ _ _ _ HK HR) as (rem' & Hout & Hrd).
      exists (eb E j ++ rem'). split.
      + rewrite Hout. cbn [DNA.flush_lit]. rewrite pbytes_app. cbn [pbytes flat_map GPS.piece_den]. rewrite app_nil_r, <- app_assoc. reflexivity.
      + intros H0 Hlen Hs0 Hs1. rewrite length_app in Hlen |- *. rewrite Nat2Z.inj_add in Hlen |- *.
        assert (Es : estart E (SA b o') = estart E (SA b o) + n) by (unfold estart; cbn [a_base a_off]; lia).
        destruct (Hrd (H0 - n) ltac:(lia)) as [R2 R3]; [lia | lia |].
        split; [|lia]. rewrite <- length_app. apply rdn_app_Z; [exact Rb|]. rewrite Hn, <- Es. exact R2. }
  destruct (List.find (fun K => match K with KBlob (SA kb ko) _ _ => expr_eqb kb b && Z.eqb ko o | _ => false end) k) as [K|] eqn:Hf; [|exact (REST H)].
  destruct K as [ | |[kb ko] ne j| | | | | | | | | ]; try exact (REST H).
  apply List.find_some in Hf as [Hin HKp]. apply andb_prop in HKp as [Hb Ho]. apply expr_eqb_eq in Hb. apply Z.eqb_eq in Ho. subst kb ko.
  destruct (split_lit (eadd (eaddz b o) ne)) as [b' o'] eqn:Hsl.
  destruct (bflat_x k b' o' (ELit 0)) eqn:Hbf; [|discriminate H].
  destruct (IH _ _ _ _ _ HK H) as (rem' & Hout & Hrd).
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as KB. cbn [kentry_ok] in KB. destruct KB as (Hflat & Hlen & Hbytes).
  exists (eb E j ++ rem'). split.
  - rewrite Hout. cbn [DNA.flush_lit]. rewrite pbytes_app. cbn [pbytes flat_map GPS.piece_den]. rewrite app_nil_r, <- app_assoc. reflexivity.
  - intros H0 Hl Hs0 Hs1. rewrite length_app in Hl |- *. rewrite Nat2Z.inj_add in Hl |- *.
    destruct (bflat_x_sound BSEGS E M k b' o' (ELit 0) HK Hbf) as (F0 & _ & F1).
    assert (Es : estart E (SA b' o') = estart E (SA b o) + elenZ E ne).
    { pose proof (APS.split_lit_denot E _ b' o' Hsl) as SD. apply (f_equal bv_unsigned) in SD.
      rewrite eadd_u, eaddz_mod in SD. rewrite Z_to_bv_unsigned, bv_wrap64_mod in SD.
      unfold estart, elenZ in *. cbn [a_base a_off] in *.
      rewrite (Z.mod_small (u (edenot E b) + o)) in SD by lia. rewrite Z.mod_small in SD by lia. rewrite Z.mod_small in SD by lia. lia. }
    destruct (Hrd (H0 - elenZ E ne) ltac:(lia)) as [R2 R3]; [lia | lia |].
    split; [|lia]. rewrite <- length_app. apply rdn_app_Z.
    + apply rdn_of_mem. intros i Hi. apply mrb_of_mem.
      specialize (Hbytes (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id in Hbytes. exact Hbytes.
    + rewrite Hlen, <- Es. exact R2.
Qed.

(* [comment removed for export] *)
Lemma pieces_len_hi_sound : forall E M k ps h,
  know_ok BSEGS E M k -> DNA.pieces_len_hi k ps = Some h -> Z.of_nat (length (pbytes E ps)) <= h.
Proof.
  intros E M k ps. induction ps as [|p r IH]; intros h HK H.
  - injection H as <-. cbn. lia.
  - cbn [DNA.pieces_len_hi] in H. destruct p as [zs|j].
    + destruct (DNA.pieces_len_hi k r) as [h'|] eqn:Hr; [|discriminate H]. injection H as <-.
      specialize (IH h' HK eq_refl). change (pbytes E (SPLit zs :: r)) with (map (Z_to_bv 8) zs ++ pbytes E r).
      rewrite length_app, length_map. lia.
    + destruct (DNA.blob_len_hi k j) as [a|] eqn:Hb; [|discriminate H].
      destruct (DNA.pieces_len_hi k r) as [h'|] eqn:Hr; [|discriminate H]. injection H as <-.
      specialize (IH h' HK eq_refl). change (pbytes E (SPBlob j :: r)) with (eb E j ++ pbytes E r). rewrite length_app.
      unfold DNA.blob_len_hi in Hb. destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate Hb].
      apply List.find_some in Hf as [Hin HKp].
      destruct K as [ | |a0 L j'| | | | | | | | | ]; try discriminate Hb. apply Nat.eqb_eq in HKp. subst j'.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as KB. cbn [kentry_ok] in KB. destruct KB as (_ & Hlen & _). unfold elenZ in Hlen.
      pose proof (xhi_sound BSEGS E M k _ _ HK Hb). lia.
Qed.

Lemma range_pieces_sound : forall E M k from to ps H,
  know_ok BSEGS E M k -> DNA.range_pieces BSEGS k from to = Some ps ->
  Z.of_nat (length (pbytes E ps)) <= H -> u (edenot E from) + H < 2 ^ 64 ->
  rdn BSEGS M (edenot E from) (length (pbytes E ps)) = Some (pbytes E ps)
  /\ u (edenot E from) + Z.of_nat (length (pbytes E ps)) = u (edenot E to).
Proof.
  intros E M k from to ps H HK Hrp Hlen Hnw. unfold DNA.range_pieces in Hrp.
  destruct (split_lit from) as [fb fo] eqn:Hsf. destruct (split_lit to) as [tb tk] eqn:Hst.
  destruct (bflat_x k fb fo (ELit 0)) eqn:Hbf; [|discriminate Hrp].
  destruct (bflat_x_sound BSEGS E M k fb fo (ELit 0) HK Hbf) as (F0 & _ & F1).
  assert (Ef : estart E (SA fb fo) = u (edenot E from)).
  { pose proof (APS.split_lit_denot E _ fb fo Hsf) as SD. rewrite SD. unfold estart in *. cbn [a_base a_off] in *. rewrite u64_lit by lia. reflexivity. }
  destruct (pieces_walk_sound E M k tb tk 600 fb fo [] [] ps HK Hrp) as (rem & Hout & Hrd).
  cbn [DNA.flush_lit pbytes flat_map app] in Hout. fold (pbytes E ps) in Hout. subst rem.
  destruct (Hrd H Hlen F0 ltac:(lia)) as [R1 R2].
  split.
  - rewrite <- R1. f_equal. rewrite Ef. symmetry. apply Z_to_bv_bv_unsigned.
  - pose proof (APS.split_lit_denot E _ tb tk Hst) as SD. rewrite SD, Z_to_bv_unsigned, bv_wrap64_mod.
    unfold estart in R2, Ef. cbn [a_base a_off] in R2, Ef. rewrite <- R2, Ef. rewrite Z.mod_small by (pose proof (u64_range (edenot E from)); lia). reflexivity.
Qed.
End BoDrvNodesSoundA8.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvWritevR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvNodesSoundA9.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2.BoStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvWritevR OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA3 BoDrvNodesSoundA6 BoDrvNodesSoundA7 BoDrvNodesSoundA8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u := bv_unsigned.
#[local] Notation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Lemma kread8e_lit0_sound : forall E M k a v,
  know_ok BSEGS E M k -> kread8e BSEGS k (ELit 0) a = Some v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdn BSEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (edenot E v)).
Proof.
  intros E M k a v HK H Ha0 Ha8. unfold kread8e in H.
  destruct (know_lookup BSEGS k (ELit 0) a 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate]. injection H as <-.
  assert (Hfl : flat E (SA (ELit 0) a) 8) by (unfold flat; rewrite estart_lit0; lia).
  destruct (GCL.lookup_piece BSEGS E M k (ELit 0) a 8 v' hs HK ltac:(lia) HL Hfl) as (bs & Hrd & Hlen & Hbs).
  rewrite estart_lit0 in Hrd. rewrite Hrd, <- Hbs. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_pristine : forall (M : word -> option byte) n (a : Z) bs,
  (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) = None) ->
  rdn BSEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> rdn BSEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M n. induction n as [|n IH]; intros a bs HM H; [exact H|].
  cbn [rdn] in H |- *. rewrite (HM a ltac:(lia)).
  destruct (seg_rom BSEGS (Z_to_bv 64 a)) as [b|]; [|discriminate H].
  rewrite Z_to_bv64_succ in H |- *.
  destruct (rdn BSEGS (fun _ => None) (Z_to_bv 64 (a + 1)) n) as [r|] eqn:Hr; [|discriminate H].
  rewrite (IH (a + 1) r); [exact H | intros i Hi; apply HM; lia | exact Hr].
Qed.
Lemma img_ssp_got : rdn BSEGS (fun _ => None) (Z_to_bv 64 DNA.SSP_GOT) 8 = Some (LE8 DNA.SSP_CELL).
Proof. vm_refl_bv. Qed.

Lemma ssp_ok_sound : forall {fx : FPState} E M k,
  know_ok BSEGS E M k -> DNA.ssp_ok BSEGS k = true -> exists can : word, ssp_cells M can.
Proof.
  intros fx E M k HK H. unfold DNA.ssp_ok in H. apply andb_prop in H as [Hc Hr].
  destruct (kread8e BSEGS k (ELit 0) DNA.SSP_CELL) as [v|] eqn:Hv; [|discriminate Hr].
  exists (edenot E v). split.
  - apply rdn_pristine; [|exact img_ssp_got]. intros i Hi. change (Z.of_nat 8) with 8 in Hi. exact (kimg_cov_sound E M k _ _ HK Hc i Hi).
  - exact (kread8e_lit0_sound E M k DNA.SSP_CELL v HK Hv ltac:(unfold DNA.SSP_CELL; lia) ltac:(unfold DNA.SSP_CELL; lia)).
Qed.

(* [comment removed for export] *)
Lemma fds_ok_chan12 : forall E f model fd,
  APS.fds_ok E f model -> fd = 1 \/ fd = 2 -> fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
Proof.
  intros E f model fd H Hfd. destruct f as [|k len off|]; cbn [APS.fds_ok] in H.
  - rewrite H. destruct Hfd as [-> | ->]; reflexivity.
  - destruct H as (p & c & H & _). rewrite H. destruct Hfd as [-> | ->]; reflexivity.
  - rewrite H. destruct Hfd as [-> | ->]; reflexivity.
Qed.

(* [comment removed for export] *)
Definition hrange : Type := (expr * Z * expr)%type.
Definition hv (k : list kentry) (r : hrange) : list kentry := kn_havoc k (fst (fst r)) (snd (fst r)) (snd r).
Definition off_r (E : env) (r : hrange) (x : word) : Prop :=
  u x < estart E (SA (fst (fst r)) (snd (fst r))) \/ estart E (SA (fst (fst r)) (snd (fst r))) + elenZ E (snd r) <= u x.
Lemma off_r_dec : forall E r x, {off_r E r x} + {~ off_r E r x}.
Proof.
  intros E r x. unfold off_r.
  destruct (Z_lt_dec (u x) (estart E (SA (fst (fst r)) (snd (fst r))))); [left; left; assumption|].
  destruct (Z_le_dec (estart E (SA (fst (fst r)) (snd (fst r))) + elenZ E (snd r)) (u x)); [left; right; assumption | right; intros [X|X]; contradiction].
Qed.
Lemma know_ok_havocs : forall E rs (M M' : word -> option byte) k,
  know_ok BSEGS E M k -> mem_grows M M' ->
  (forall x, Forall (fun r => off_r E r x) rs -> M' x = M x) ->
  know_ok BSEGS E M' (fold_left hv rs k).
Proof.
  intros E rs. induction rs as [|r rs IH]; intros M M' k HK HG HO; cbn [fold_left].
  - replace M' with M; [exact HK|]. apply FunctionalExtensionality.functional_extensionality. intros x. symmetry. apply HO. constructor.
  - set (M1 := fun x : word => if off_r_dec E r x then M x else M' x).
    apply (IH M1 M').
    + unfold hv. apply (APS.know_ok_havoc BSEGS E M M1 k); [exact HK | |].
      * intros x Hx. unfold M1. destruct (off_r_dec E r x) as [_|N]; [reflexivity | exfalso; exact (N Hx)].
      * intros x Hx. unfold M1. destruct (off_r_dec E r x); [exact Hx | exact (HG x Hx)].
    + intros x Hx. unfold M1 in Hx. destruct (off_r_dec E r x); [exact (HG x Hx) | exact Hx].
    + intros x Hx. unfold M1. destruct (off_r_dec E r x) as [Y|N]; [|reflexivity]. apply HO. constructor; assumption.
Qed.

(* [comment removed for export] *)
Lemma sw_range_ok_sound : forall E M k from to ps spb spk,
  know_ok BSEGS E M k -> DNA.sw_range_ok k from to ps spb spk = true -> DNA.range_pieces BSEGS k from to = Some ps ->
  rdn BSEGS M (edenot E from) (length (pbytes E ps)) = Some (pbytes E ps)
  /\ u (edenot E from) + Z.of_nat (length (pbytes E ps)) = u (edenot E to)
  /\ Z.of_nat (length (pbytes E ps)) <= 2 ^ 29 /\ u (edenot E to) <= 2 ^ 47
  /\ (u (edenot E to) <= estart E (SA spb (spk - DNA.FR_SW)) \/ estart E (SA spb (spk - DNA.FR_SW)) + 112 <= u (edenot E from)).
Proof.
  intros E M k from to ps spb spk HK H Hrp. unfold DNA.sw_range_ok in H.
  destruct (DNA.pieces_len_hi k ps) as [h|] eqn:Hh; [|discriminate H].
  destruct (xhi k from) as [fh|] eqn:Hfh; [|discriminate H].
  destruct (xhi2 k to) as [th|] eqn:Hth; [|discriminate H].
  destruct (split_lit from) as [fb fo] eqn:Hsf.
  apply andb_prop in H as [H Hdj]. apply andb_prop in H as [H H47]. apply andb_prop in H as [H29 H64].
  apply Z.leb_le in H29. apply Z.ltb_lt in H64. apply Z.leb_le in H47. change DNA.two64 with (2 ^ 64) in H64. unfold two47 in H47.
  pose proof (pieces_len_hi_sound E M k ps h HK Hh) as Lh.
  pose proof (xhi_sound BSEGS E M k _ _ HK Hfh) as Bf.
  pose proof (APS.xhi2_sound BSEGS E M k _ _ HK Hth) as Bt.
  destruct (range_pieces_sound E M k from to ps (2 ^ 29) HK Hrp ltac:(clear - Lh H29; lia) ltac:(clear - Bf H64; lia)) as [R1 R2].
  split; [exact R1|]. split; [exact R2|]. split; [clear - Lh H29; lia|]. split; [clear - Bt H47; lia|].
  pose proof (APS.disj_x_sound BSEGS E M k fb fo (ELit h) spb (spk - DNA.FR_SW) (ELit DNA.FR_SW) HK Hdj) as DJ.
  unfold elenZ in DJ. cbn [edenot] in DJ. rewrite !u64_lit in DJ by (unfold DNA.FR_SW; pose proof (Zle_0_nat (length (pbytes E ps))); clear - Lh H29 H; lia).
  (* [comment removed for export] *)
  unfold DNA.range_pieces in Hrp. rewrite Hsf in Hrp. destruct (split_lit to) as [tb tk]. 
  destruct (bflat_x k fb fo (ELit 0)) eqn:Hbf; [|discriminate Hrp].
  destruct (bflat_x_sound BSEGS E M k fb fo (ELit 0) HK Hbf) as (F0 & _ & F1).
  assert (Ef : estart E (SA fb fo) = u (edenot E from)).
  { pose proof (APS.split_lit_denot E _ fb fo Hsf) as SD. rewrite SD. unfold estart in *. cbn [a_base a_off] in *. rewrite u64_lit by lia. reflexivity. }
  rewrite Ef in DJ. unfold DNA.FR_SW in DJ |- *. clear - DJ R2 Lh. lia.
Qed.

Section NodesSoundA9.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable SR : shape_rel BSEGS.
#[local] Notation RZ := (sr_rel BSEGS SR).
(* [comment removed for export] *)
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GBOTH SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH /\ (forall plo phi, In (plo, phi) (g_priv GBOTH) -> hi <= plo \/ phi <= lo).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Hypothesis PERM_files : forall a, (DNA.STDOUT_F <= a < DNA.STDOUT_F + 232 \/ DNA.STDERR_F <= a < DNA.STDERR_F + 232) -> in_wins PERMc a.
#[local] Notation AINVc := (AINV_f SWIN GBOTH AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation cs_okA := (GPS.cs_ok BSEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV).
#[local] Notation Mr := (GPS.Mr SHC VSHc).
#[local] Notation hid := (GPS.hid SHC VSHc).
#[local] Notation AF := (AINV_f_frame SWIN GBOTH SHC AINVH HP both_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation ALZ := (AINV_f_lazy SWIN GBOTH SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation AFACTS := (AINV_f_facts SWIN GBOTH SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c).

(* [comment removed for export] *)
Lemma hid_ceil_false : forall E cs B C K M mdl (a : word),
  AINVc (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl -> CEIL_run <= u a -> hid E cs mdl a = false.
Proof.
  intros E cs B C K M mdl a HA Ha. unfold GPS.hid, GPS.lz.
  destruct (page_in_ranges (page_base a) (m_vm_lazy mdl)) eqn:Hp; [|reflexivity]. exfalso.
  unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hiv Hc]].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) (AFACTS _ _ _ _ _ _ _ HA) iv Hiv) as (L0 & L1 & L2).
  pose proof (GPS.page_base_le' a) as (P1 & P2 & P3). unfold page_size in *. lia.
Qed.
(* [comment removed for export] *)
Lemma rdn1_visible : forall E cs B C K M mdl (a : word) (b : byte),
  AINVc (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  rdn BSEGS (Mr E cs mdl M) a 1 = Some [b] -> hid E cs mdl a = false.
Proof.
  intros E cs B C K M mdl a b HA H. destruct (hid E cs mdl a) eqn:Hh; [|reflexivity].
  cbn [rdn] in H. unfold GPS.Mr, mrestrict in H. rewrite Hh in H.
  destruct (APS.in_hull ABOTH (u a)) eqn:Hull.
  - rewrite <- Hh. apply (hid_image_false' SHC AINVH SWIN HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c E cs B C K M mdl a HA).
    + unfold APS.in_hull in Hull. apply andb_prop in Hull as [X _]. apply Z.leb_le in X. rewrite both_A_img_lo in X. exact X.
    + unfold APS.in_hull in Hull. apply andb_prop in Hull as [_ X]. apply Z.ltb_lt in X. rewrite both_A_img_hi in X. exact X.
  - rewrite (APS.seg_rom_off_hull BSEGS ABOTH both_in_hull a Hull) in H. discriminate H.
Qed.
Lemma rdn_visible : forall E cs B C K M mdl n (a : Z) bs,
  AINVc (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  rdn BSEGS (Mr E cs mdl M) (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  hid_off (hid E cs mdl) a (Z.of_nat n).
Proof.
  intros E cs B C K M mdl n. induction n as [|n IH]; intros a bs HA H Ha0 Ha1 x Hx; [lia|].
  cbn [rdn] in H.
  destruct (match Mr E cs mdl M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom BSEGS (Z_to_bv 64 a) end) as [b0|] eqn:Hb0; [|discriminate H].
  rewrite Z_to_bv64_succ in H.
  destruct (rdn BSEGS (Mr E cs mdl M) (Z_to_bv 64 (a + 1)) n) as [r|] eqn:Hr; [|discriminate H].
  destruct (Z.eq_dec (u x) a) as [Hxa|Hne].
  - apply (rdn1_visible E cs B C K M mdl x b0 HA). cbn [rdn].
    replace x with (Z_to_bv 64 a) by (rewrite <- Hxa; apply Z_to_bv_bv_unsigned). rewrite Hb0. reflexivity.
  - apply (IH (a + 1) r HA Hr ltac:(lia) ltac:(lia) x). lia.
Qed.

(* [comment removed for export] *)
Lemma eaddz_vadd : forall E e z, edenot E (eaddz e z) = v_add (edenot E e) (Z_to_bv 64 z).
Proof. intros E e z. unfold eaddz. rewrite mkAlu_denot. reflexivity. Qed.

(* [comment removed for export] *)
Theorem node_stdio_write_sound : forall cs fd ps cs' E fx R M model (T : TSet),
  cs_okA E cs fx R M model -> DNA.node_stdio_write BSEGS NXD cs = Some (fd, ps, cs') -> T [] ->
  (forall E' fx' R' M' model',
      env_agree NXD E E' /\ env_agree (nxt cs) E E' -> cs_okA E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfgF BSEGS fx' R' (pc cs') M' model') T) ->
  RZ (cfgF BSEGS fx R (pc cs) M model) (t_emit (Wp E fd ps) T).
Proof.
  intros cs fd ps cs' E fx R M model T HC Hn HT Hk. unfold DNA.node_stdio_write in Hn.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg1; [|discriminate Hn] end. cbn [negb] in Hn.
  apply andb_prop in Hg1 as [Hg1 Hssp]. apply andb_prop in Hg1 as [Hg1 Hspok]. apply andb_prop in Hg1 as [Hpc Hfresh]. apply Z.eqb_eq in Hpc.
  destruct (reg_lit cs 10) as [f|] eqn:R10; [|discriminate Hn].
  destruct (ret_lit cs) as [ra|] eqn:Rret; [|discriminate Hn].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hf12; [|discriminate Hn] end. cbn [negb] in Hn.
  destruct (kreadZ BSEGS (kn cs) (ELit 0) (f + 120) 4) as [fdv|] eqn:Hfd; [|discriminate Hn].
  destruct (kread8e BSEGS (kn cs) (ELit 0) (f + 88)) as [bufe|] eqn:Hbuf; [|discriminate Hn].
  destruct (kreadZ BSEGS (kn cs) (ELit 0) (f + 96) 8) as [bsz|] eqn:Hbsz; [|discriminate Hn].
  destruct (kread8e BSEGS (kn cs) (ELit 0) (f + 56)) as [wbe|] eqn:Hwb; [|discriminate Hn].
  destruct (kread8e BSEGS (kn cs) (ELit 0) (f + 40)) as [wpe|] eqn:Hwp; [|discriminate Hn].
  destruct (DNA.range_pieces BSEGS (kn cs) wbe wpe) as [pend|] eqn:Hpend; [|discriminate Hn].
  destruct (DNA.range_pieces BSEGS (kn cs) (reg cs 11) (eadd (reg cs 11) (reg cs 12))) as [ext|] eqn:Hext; [|discriminate Hn].
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsq.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg2; [|discriminate Hn] end. cbn [negb] in Hn.
  match type of Hn with context [node_havoc ?a ?b ?c] => destruct (node_havoc a b c) as [cs1|] eqn:Hnh; [|discriminate Hn] end.
  injection Hn as <- <- <-.
  (* [comment removed for export] *)
  apply andb_prop in Hg2 as [Hg2 Hrext]. apply andb_prop in Hg2 as [Hfdm Hrpend].
  assert (Hfdv : (fdv = 1 \/ fdv = 2) /\ (f = DNA.STDOUT_F \/ f = DNA.STDERR_F)).
  { apply orb_prop in Hfdm as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.eqb_eq in H1; apply Z.eqb_eq in H2; tauto. }
  destruct Hfdv as [Hfdv Hf].
  assert (Hfb : 0x10a5c8 <= f /\ f + 232 <= 0x10a7a0) by (unfold DNA.STDOUT_F, DNA.STDERR_F in Hf; lia).
  pose proof (co_know HC) as HK. pose proof (co_ainv HC) as HA.
  destruct (GCL.reg_lit_sound E cs R 10 f (co_regs HC) ltac:(lia) R10) as [G10 _].
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 11 HC ltac:(lia)) as G11.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 12 HC ltac:(lia)) as G12.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 2 HC ltac:(lia)) as G2.
  destruct (GCL.ret_lit_sound E cs R ra (co_regs HC) Rret) as (G1 & RA & Hra & Hraev).
  (* [comment removed for export] *)
  unfold DNA.sw_sp_ok in Hspok. rewrite Hsq in Hspok.
  apply andb_prop in Hspok as [Hspok Hsprng]. apply andb_prop in Hspok as [Hkw Hfl].
  destruct (xlo (kn cs) (reg cs 2)) as [slo|] eqn:Hslo; [|discriminate Hsprng].
  destruct (xhi (kn cs) (reg cs 2)) as [shi|] eqn:Hshi; [|discriminate Hsprng].
  apply andb_prop in Hsprng as [Hsplo Hsphi]. apply Z.leb_le in Hsplo. apply Z.leb_le in Hsphi. unfold two47 in Hsphi. unfold DNA.FR_SW in Hsplo.
  pose proof (xlo_sound BSEGS E _ (kn cs) _ _ HK Hslo) as S1. pose proof (xhi_sound BSEGS E _ (kn cs) _ _ HK Hshi) as S2.
  set (spw := edenot E (reg cs 2)) in *. set (su := u spw) in *.
  destruct (GCL.kwritable_x_sound BSEGS E _ (kn cs) (kn cs) spb (spk - DNA.FR_SW) (ELit DNA.FR_SW) HK HK Hkw) as (Hst & Hs0 & Hs1).
  assert (Hl112 : elenZ E (ELit DNA.FR_SW) = 112) by (unfold elenZ; cbn [edenot]; apply u64_lit; unfold DNA.FR_SW; lia).
  rewrite Hl112 in Hs1.
  assert (Hest2 : estart E (SA spb (spk - DNA.FR_SW)) = su - 112).
  { pose proof (APS.split_lit_denot E _ spb spk Hsq) as X. apply (f_equal bv_unsigned) in X. fold spw in X. fold su in X.
    rewrite Z_to_bv_unsigned, bv_wrap64_mod in X. unfold estart in Hs0, Hs1 |- *. cbn [a_base a_off] in Hs0, Hs1 |- *.
    unfold DNA.FR_SW in *.
    destruct (Z.eq_dec (u (edenot E spb) + spk) (2 ^ 64)) as [E64|N64].
    - rewrite E64, Z.mod_same in X by lia. lia.
    - rewrite Z.mod_small in X by lia. lia. }
  rewrite Hest2 in Hst, Hs0, Hs1.
  (* [comment removed for export] *)
  destruct (kreadZ_lit0_sound E _ (kn cs) _ _ _ HK Hfd ltac:(lia) ltac:(lia) ltac:(lia)) as [Rfd Bfd].
  destruct (kreadZ_lit0_sound E _ (kn cs) _ _ _ HK Hbsz ltac:(lia) ltac:(lia) ltac:(lia)) as [Rbsz Bbsz].
  pose proof (kread8e_lit0_sound E _ (kn cs) _ _ HK Hbuf ltac:(lia) ltac:(lia)) as Rbuf.
  pose proof (kread8e_lit0_sound E _ (kn cs) _ _ HK Hwb ltac:(lia) ltac:(lia)) as Rwb.
  pose proof (kread8e_lit0_sound E _ (kn cs) _ _ HK Hwp ltac:(lia) ltac:(lia)) as Rwp.
  destruct (@ssp_ok_sound fx E _ (kn cs) HK Hssp) as [can Hcan].
  (* [comment removed for export] *)
  destruct (sw_range_ok_sound E _ (kn cs) wbe wpe pend spb spk HK Hrpend Hpend) as (Rpend & Lpend & Bpend & Bwp47 & Dpend).
  destruct (sw_range_ok_sound E _ (kn cs) _ _ ext spb spk HK Hrext Hext) as (Rext & Lext & Bext & Bs47 & Dext).
  rewrite Hest2 in Dpend, Dext.
  set (pending := pbytes E pend) in *. set (extra := pbytes E ext) in *.
  set (s := edenot E (reg cs 11)) in *. set (l := edenot E (reg cs 12)) in *.
  pose proof (u64_range s) as Rs. pose proof (u64_range l) as Rl. pose proof (u64_range (edenot E wbe)) as Rwbr.
  assert (Hul : u l = Z.of_nat (length extra)).
  { rewrite eadd_u in Lext. fold s l in Lext. rewrite eadd_u in Bs47. fold s l in Bs47.
    destruct (Z_lt_ge_dec (u s + u l) (2 ^ 64)) as [Hlt|Hge].
    - rewrite Z.mod_small in Lext by lia. lia.
    - exfalso. assert (Hm : (u s + u l) mod 2 ^ 64 = u s + u l - 2 ^ 64) by (symmetry; apply Z.mod_unique with (q := 1); lia). lia. }
  (* [comment removed for export] *)
  destruct (ALZ _ _ _ _ _ _ _ HA) as (AA & Hwf & Hminv & Hshc & Hshv & Hblk & Hmat).
  pose proof (GPS.H_off_segments_hid BSEGS ABOTH SHC VSHc AINVc AFACTS both_in_hull E cs model _ _ _ _ _ _ HA) as HH.
  pose proof (GPS.lazy_cover_hid SHC VSHc E cs model AA Hshc Hshv Hblk) as Hcov.
  set (H := hid E cs model) in *.
  assert (MC : mclean H (Mr E cs model M)) by (intros a Ha; unfold GPS.Mr, mrestrict; fold H; rewrite Ha; reflexivity).
  (* [comment removed for export] *)
  assert (HW : Wp E fdv (pend ++ ext) = map (WriteEv (Z_to_bv 64 fdv)) (pending ++ extra)).
  { unfold Wp. f_equal. rewrite flat_map_app. reflexivity. }
  rewrite HW. unfold cfgF, GPS.mkstF. rewrite Hpc. rewrite (w_lit DNA.X_STDIO_WRITE (0xf360c%bv : word) eq_refl).
  rewrite <- (munrestrict_mrestrict H M) at 1.
  apply (@both_stdio_write fx SR (both_HW1 SR fx) (both_HW2 SR fx) (both_HW0 SR fx) H AA M R (Mr E cs model M) model su f (u (edenot E wbe)) (u (edenot E wpe)) fdv s l
           (edenot E bufe) (Z_to_bv 64 bsz) can (Z_to_bv 64 ra) pending extra T).
  all: try assumption.
  - exact both_segs_wx.
  - (* [comment removed for export] *)
    intros x Hx. apply (hid_ceil_false E cs _ _ _ M model x HA).
    pose proof (in_floor_sound BSEGS E _ (kn cs) _ _ _ spb (spk - DNA.FR_SW) (ELit DNA.FR_SW) x HK Hfl (co_floor HC)
                  ltac:(rewrite Hest2, Hl112; lia)) as [F1 _].
    pose proof sfloor_ge. lia.
  - (* [comment removed for export] *)
    intros x Hx. apply (hid_image_false' SHC AINVH SWIN HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c E cs _ _ _ M model x HA); cbn [g_img_lo g_img_hi GBOTH]; lia.
  - (* [comment removed for export] *)
    apply (rdn_visible E cs _ _ _ M model (length pending) (u (edenot E wbe)) pending HA); [| lia | lia].
    rewrite Z_to_bv_bv_unsigned. exact Rpend.
  - apply (rdn_visible E cs _ _ _ M model (length extra) (u s) extra HA); [| lia | lia].
    rewrite Z_to_bv_bv_unsigned. exact Rext.
  - transitivity spw; [rewrite <- G2; f_equal; apply bv_eq; reflexivity | symmetry; apply Z_to_bv_bv_unsigned].
  - lia.
  - lia.
  - exact (Hst 112%nat ltac:(lia)).
  - lia.
  - lia.
  - constructor; rewrite ?Z_to_bv_bv_unsigned; assumption.
  - destruct Hfdv; lia.
  - exact (fds_ok_chan12 E (a_fd cs) model fdv (co_fds HC) Hfdv).
  - exact (co_halt HC).
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite Hul. fold s in Lext, Dext. clear - Lext Dext. lia.
  - rewrite Hul. fold s in Lext. clear - Lext Bs47. lia.
  - rewrite Z_to_bv_bv_unsigned. exact Rpend.
  - (* [comment removed for export] *)
    intros regs' mem' mdl' Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST MC' Hminv' Hsame.
    unfold node_havoc in Hnh.
    match type of Hnh with (if ?c then _ else _) = _ => destruct c eqn:Hhv; [|discriminate Hnh] end.
    apply andb_prop in Hhv as [Hfr1 Hrs]. injection Hnh as Ecs1.
    assert (Hrs' : Forall (fun r => 0 < r < 32)%nat DNA.CLOB).
    { apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as X.
      apply andb_prop in X as [X1 X2]. apply Nat.ltb_lt in X1. apply Nat.ltb_lt in X2. lia. }
    destruct (fresh_ok_parts NXD cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    destruct (GPS.fresh_ok_parts2 NXD cs Hfresh) as (Ffake & Fmtr).
    destruct (fresh_ok_parts NXD _ Hfr1) as (Fsr1 & Fkn1 & _).
    set (E' := ext_list E (nxt cs) (map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) DNA.CLOB)).
    assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
    set (M' := munrestrict H M mem').
    destruct (same_but_materialized_frame model mdl' Hsame) as (_ & _ & SL & _ & _ & _ & _ & _ & _ & _ & _ & SFS & _).
    specialize (Hk E' fx regs' M' mdl' (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
    rewrite <- Ecs1 in Hk. unfold cfgF, GPS.mkstF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc set_pc set_reg set_kn] in Hk.
    apply Hk; [|exact SFS].
    pose proof (GPS.cs_ok_agree BSEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC1.
    assert (HidE : hid E' cs mdl' = H).
    { rewrite (GPS.hid_model SHC VSHc E' cs model mdl' SL). exact (GPS.hid_agree NXD SHC VSHc E E' cs model Hag Hfresh). }
    assert (MrE : Mr E' cs mdl' M' = mem').
    { unfold GPS.Mr. rewrite HidE. unfold M'. apply APS.mrestrict_munrestrict_clean. exact MC'. }
    destruct POST as [AG GR WE WP WB].
    eapply (GPS.cs_ok_frame_mat BSEGS SWIN PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc AF fx_ok UINV E' cs fx R M model _ fx regs' M' mdl' HC1).
    + (* [comment removed for export] *)
      cbn [mk_ss s_regs].
      assert (Hnz10 : bv_eqb (Z_to_bv 5 (Z.of_nat 10)) 0%bv = false) by reflexivity.
      assert (Hrx10 : ridx (Z_to_bv 5 (Z.of_nat 10)) = 10%nat) by (apply ridx_lit; lia).
      pose proof (regs_ok_upd E (s_regs (a_ss cs)) R (Z_to_bv 5 (Z.of_nat 10)) (edenot E (reg cs 12)) (reg cs 12) (co_regs HC) eq_refl) as HR2.
      rewrite Hnz10, Hrx10 in HR2.
      apply (regs_ok_havoc_to DNA.CLOB E _ _ regs' (nxt cs) HR2); [exact Fsr1 | exact Hrs' |].
      intros x Hx. destruct (bv_eq_dec _ x (Z_to_bv 5 (Z.of_nat 10))) as [->|Hne].
      * rewrite (r5_lit 10 10%bv eq_refl) at 1. rewrite Q10. unfold getr. rewrite Hnz10. symmetry. apply regupd_same.
      * transitivity (getr R x); [|unfold getr; destruct (bv_eqb x 0); [reflexivity|]; symmetry; apply regupd_other; exact Hne].
        destruct (clob_complement x Hne Hx) as [Hcs|H0].
        -- unfold MemsetLibF.RefMemcpyLib.callee_saved in Hcs. cbn [In] in Hcs.
           repeat (destruct Hcs as [<-|Hcs]; [first [assumption | (rewrite Q1; rewrite <- G1; f_equal; apply bv_eq; reflexivity) | (rewrite Q2; symmetry; transitivity spw; [rewrite <- G2; f_equal; apply bv_eq; reflexivity | symmetry; apply Z_to_bv_bv_unsigned])]|]).
           destruct Hcs.
        -- assert (x = 0%bv) by (apply ridx_inj; rewrite H0; reflexivity). subst x. reflexivity.
    + reflexivity.
    + (* [comment removed for export] *)
      cbn [mk_ss s_know]. rewrite MrE.
      eapply know_ok_agree'; [exact Hag | exact Fkn1 |].
      cbn [kn a_ss with_ss mk_ss s_know set_pc set_reg set_kn]. unfold DNA.havoc_scratch. rewrite Hsq.
      assert (E8 : elenZ E (ELit 8) = 8) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
      repeat apply Forall_cons.
      * cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite estart_lit0; lia|]. rewrite GCL.adenot_SA, estart_lit0. exact WP.
      * cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite estart_lit0; lia|]. rewrite GCL.adenot_SA, estart_lit0. exact WB.
      * cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite estart_lit0; lia|]. rewrite GCL.adenot_SA, estart_lit0, eaddz_vadd. exact WE.
      * change (know_ok BSEGS E mem' (fold_left hv [(spb, spk - DNA.FR_SW, ELit DNA.FR_SW); (ELit 0, f + 40, ELit 8); (ELit 0, f + 56, ELit 8); (ELit 0, f + 32, ELit 8)] (kn cs))).
        apply (know_ok_havocs E _ (Mr E cs model M) mem' (kn cs) HK GR).
        intros x Hx. apply Forall_cons_iff in Hx as [X1 Hx]. apply Forall_cons_iff in Hx as [X2 Hx]. apply Forall_cons_iff in Hx as [X3 Hx]. apply Forall_cons_iff in Hx as [X4 _].
        unfold off_r in X1, X2, X3, X4. cbn [fst snd] in X1, X2, X3, X4. rewrite Hest2, Hl112 in X1. rewrite estart_lit0, E8 in X2, X3, X4.
        apply AG; lia.
    + exact (co_fx HC).
    + (* [comment removed for export] *)
      intros a Ha. unfold M', munrestrict in Ha |- *.
      destruct (H a) eqn:HHa; [exfalso; exact (Ha eq_refl)|].
      assert (HMr : Mr E cs model M a = M a) by (unfold GPS.Mr, mrestrict; fold H; rewrite HHa; reflexivity).
      split.
      2:{ intros Hn0. destruct (M a) eqn:HMa; [|exact (Ha Hn0)]. apply (GR a); [rewrite HMr; discriminate | exact Hn0]. }
      left.
      destruct (Z_lt_ge_dec (u a) (su - 112)) as [Hlow|Hhigh]; [|destruct (Z_lt_ge_dec (u a) su) as [Hin|Habove]].
      * right. left. apply PERM_files.
        assert (Hx : ~ (~ (f + 32 <= u a < f + 48) /\ ~ (f + 56 <= u a < f + 64))) by (intros [X1 X2]; apply Ha; rewrite <- HMr; apply AG; lia).
        unfold DNA.STDOUT_F, DNA.STDERR_F in *. lia.
      * right. right. left.
        pose proof (in_floor_sound BSEGS E _ (kn cs) _ _ _ spb (spk - DNA.FR_SW) (ELit DNA.FR_SW) a HK Hfl (co_floor HC)
                      ltac:(rewrite Hest2, Hl112; lia)) as [F1 F2].
        rewrite (co_top HC) in F1. exact F1.
      * exfalso. apply Ha. rewrite <- HMr. apply AG; unfold DNA.STDOUT_F, DNA.STDERR_F in *; lia.
    + exact Hsame.
    + rewrite (GPS.blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)),
              (GPS.blocks_den_agree (nxt cs) E E' (a_fake cs) Hag Ffake),
              (GPS.bcost_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)),
              (GPS.uE_agree (nxt cs) E E' (a_meter cs) Hag Fmtr).
      exact (Hmat mdl' Hminv' Hsame).
Qed.
End NodesSoundA9.
End BoDrvNodesSoundA9.
Module BoDrvNodesAllA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA3 BoDrvNodesSoundA4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5 BoDrvNodesSoundA6 BoDrvNodesSoundA7 BoDrvNodesSoundA9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Lemma RZ_silent1_rz : GPS.RZ_SILENT1 BSEGS (realizes BSEGS).
Proof. exact (GPS.RZ_SILENT1_realizes BSEGS). Qed.
Lemma RZ_exit_rz : GPS.RZ_EXIT BSEGS (realizes BSEGS).
Proof. exact (GPS.RZ_EXIT_realizes BSEGS). Qed.
Lemma RZ_conseq_rz : GPS.RZ_CONSEQ (realizes BSEGS).
Proof. exact (GPS.RZ_CONSEQ_realizes BSEGS). Qed.

Section AllA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GBOTH SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH /\ (forall plo phi, In (plo, phi) (g_priv GBOTH) -> hi <= plo \/ phi <= lo).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Hypothesis bcap_ok : B0c + BCAP <= GBUDGET.
Hypothesis ccap_ok : C0c + CCAP <= GCOUNT.
Variable FTOPc : Z.
Hypothesis FTOPc_ok : Z.of_nat (length HIDFc) + FTOPc <= FMIN.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
#[local] Notation AINVc := (AINV_f SWIN GBOTH AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation RZ := (realizes BSEGS).

(* [comment removed for export] *)
Hypothesis GC : gcontracts BSEGS ITA ABOTH NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ GBOTH BCAP CCAP.
Hypothesis FZN_contract : callee_contract BSEGS SWIN GBOTH fx_ok RZ SHC KCAP AINVH BoDrvHooksA.BoFZ.ceN.
Hypothesis FZE_contract : callee_contract BSEGS SWIN GBOTH fx_ok RZ SHC KCAP AINVH BoDrvHooksA.BoFZ.ceE.
Hypothesis M2S_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Hypothesis PERM_files : forall a, (DNA.STDOUT_F <= a < DNA.STDOUT_F + 232 \/ DNA.STDERR_F <= a < DNA.STDERR_F + 232) -> in_wins PERMc a.
Hypothesis NONUL12 : forall E, UINV E -> forall j, (j = 1 \/ j = 2)%nat -> ~ In (Z_to_bv 8 0) (eb E j).
Hypothesis ABSENT2 : forall E, UINV E -> bv_unsigned (ev E 4%nat) = DNA.CLS_ABSENT ->
  eb E 2%nat <> [] -> openat_plain_name (eb E 2%nat) = true /\ fs_lookup FS0 (eb E 2%nat) = None.
Variable data : list byte.
Hypothesis FILE2 : forall E, UINV E -> bv_unsigned (ev E 4%nat) <= DNA.FCAP ->
  eb E 2%nat <> [] /\ openat_plain_name (eb E 2%nat) = true /\ fs_lookup FS0 (eb E 2%nat) = Some data
  /\ uE E (EVar 4) = flen data /\ (forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (3 + j)%nat = chunk j data).
Hypothesis DIR2 : forall E, UINV E -> bv_unsigned (ev E 4%nat) = DNA.CLS_DIR -> path_is_dirref (eb E 2%nat) = true.

Lemma NONUL2 : forall E, UINV E -> ~ In (Z_to_bv 8 0) (eb E 2%nat).
Proof. intros E HU. exact (NONUL12 E HU 2%nat (or_intror eq_refl)). Qed.

Ltac base := first [ assumption | exact RZ_silent1_rz | exact RZ_exit_rz | exact RZ_conseq_rz | exact NONUL2 ].
Ltac node :=
  first [ apply node_read_sound | apply node_close_sound | apply node_ioctl_sound | apply node_blobmemchr_sound | apply node_blobstrlen_sound
        | apply node_region_sound | apply node_qctail_printf_sound | apply node_qctail_strnlen_sound | apply node_qctail_memchr_sound
        | apply node_openat_toolong_sound | apply node_openat_absent_sound ]; try base.

Theorem XNa_sound_all : GPS.ext_stmt BSEGS NXD XNa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof. apply XNa_sound; try base; node. Qed.

Theorem XEa_sound_all : GPS.emit_stmt BSEGS NXD XEa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  apply XEa_sound. intros cs fd ps cs' E fx R M model T HC Hn HT Hk.
  exact (node_stdio_write_sound (SR_realizes BSEGS) SHC KCAP AINVH SWIN HP PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV UINV_agree PERM_files
           cs fd ps cs' E fx R M model T HC Hn HT Hk).
Qed.

Theorem XAa_sound_all : GPS.alt2_stmt BSEGS NXD XAa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  apply XAa_sound.
  - intros args Ta Tb. exact (node_openat_file2_sound SHC KCAP AINVH SWIN HP PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV UINV_agree NONUL2 data FILE2 args Ta Tb).
  - intros args Ta Tb. exact (node_openat_dir2_sound SHC KCAP AINVH SWIN HP PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV UINV_agree NONUL2 DIR2 args Ta Tb).
Qed.
End AllA.
End BoDrvNodesAllA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvCertSoundA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA BoDrvNodesSoundA11 BoDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvInstFactsA BoDrvUinvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma CHK0_eq : CHK0 = fun cs p => checkA BSEGS ITA ABOTH NXD LIMIT ISP0 XNa XEa XB0 XAa AP.XT0 (fun _ => None) 0%nat false BF0 FUEL0 None cs p.
Proof. reflexivity. Qed.

Section CertSoundA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GBOTH SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH /\ (forall plo phi, In (plo, phi) (g_priv GBOTH) -> hi <= plo \/ phi <= lo).
Variable SPTOPc : Z.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Hypothesis bcap_ok : B0c + BCAP <= GBUDGET.
Hypothesis ccap_ok : C0c + CCAP <= GCOUNT.
Variable FTOPc : Z.
Hypothesis FTOPc_ok : Z.of_nat (length HIDFc) + FTOPc <= FMIN.
(* [comment removed for export] *)
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).
(* [comment removed for export] *)
Variable UX : env -> Prop.
Hypothesis UX_agree : forall E E', env_agree NXD E E' -> UX E -> UX E'.
Definition UINVd (E : env) : Prop := U_drv a0 p fs data E /\ UX E.
Lemma UINVd_agree : forall E E', env_agree NXD E E' -> UINVd E -> UINVd E'.
Proof. intros E E' Hag [H1 H2]. split; [exact (U_drv_agree a0 p fs data E E' Hag H1) | exact (UX_agree E E' Hag H2)]. Qed.

#[local] Notation PERMc := PERM_A_lit.
#[local] Notation AINVat M0 := (AINV_f SWIN GBOTH AINVH PERMc SPTOPc HIDc HIDFc M0 B0c C0c).
#[local] Notation AINVc := (AINVat M0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation RZ := (realizes BSEGS).
#[local] Notation cs_okat M0 := (GPS.cs_ok BSEGS PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd).
#[local] Notation cs_okA := (cs_okat M0c).

(* [comment removed for export] *)
Hypothesis GC_all : forall M0 : word -> option byte,
  gcontracts BSEGS ITA ABOTH NXD PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ GBOTH BCAP CCAP.
Hypothesis FZN_contract : callee_contract BSEGS SWIN GBOTH fx_ok RZ SHC KCAP AINVH BoDrvHooksA.BoFZ.ceN.
Hypothesis FZE_contract : callee_contract BSEGS SWIN GBOTH fx_ok RZ SHC KCAP AINVH BoDrvHooksA.BoFZ.ceE.
Hypothesis M2S_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
(* [comment removed for export] *)
Hypothesis DTOR_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ exists cpm : byte, rdn BSEGS M (Z_to_bv 64 0x10da1c) 1 = Some [cpm] /\ bv_unsigned cpm <> 0.
Hypothesis DTOR_FRAME : forall L LF B C K M M' mdl, AINVH L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (bv_unsigned a) = true \/ in_mub (bv_unsigned a) = true) /\ M' a <> None) ->
  rdn BSEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  AINVH L LF B C K M' mdl.

(* [comment removed for export] *)
Lemma XNa_at : forall M0, GPS.ext_stmt BSEGS NXD XNa PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ.
Proof.
  intros M0.
  apply (XNa_sound_all SHC KCAP AINVH SWIN HP SWIN_img PERMc SPTOPc fs HIDc HIDFc M0 B0c C0c B0c_nonneg C0c_nonneg bcap_ok ccap_ok FTOPc FTOPc_ok UINVd UINVd_agree
           (GC_all M0) FZN_contract FZE_contract M2S_H).
  - intros E [HU _]. exact (U_drv_NONUL12 a0 p fs data E HU).
  - intros E [HU _]. exact (U_drv_ABSENT2 a0 p fs data E HU).
Qed.
Lemma XEa_at : forall M0, GPS.emit_stmt BSEGS NXD XEa PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ.
Proof.
  intros M0. apply (XEa_sound_all SHC KCAP AINVH SWIN HP PERMc SPTOPc fs HIDc HIDFc M0 B0c C0c FTOPc UINVd UINVd_agree).
  intros a Ha. rewrite <- (PERM_A_den (Env (fun _ => Z_to_bv 64 0) (fun _ => []))). exact (PERM_files_A _ a Ha).
Qed.
Lemma XAa_at : forall M0, GPS.alt2_stmt BSEGS NXD XAa PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ.
Proof.
  intros M0.
  exact (XAa_sound_all SHC KCAP AINVH SWIN HP PERMc SPTOPc fs HIDc HIDFc M0 B0c C0c FTOPc UINVd UINVd_agree
           (fun E HU => U_drv_NONUL12 a0 p fs data E (proj1 HU)) data
           (fun E HU => U_drv_FILE2 a0 p fs data E (proj1 HU)) (fun E HU => U_drv_DIR2 a0 p fs data E (proj1 HU))).
Qed.

(* [comment removed for export] *)
Lemma tail_sound : forall (M0' : word -> option byte) pl cs s,
  gplan_ok pl = true -> CHK0 cs pl = COk s ->
  forall E fx R M model, cs_okat M0' E cs fx R M model ->
  RZ (cfgF BSEGS fx R (pc cs) M model) (GPS.sd (fun _ _ _ => t_nil) t_nil E (m_fs model) s).
Proof.
  intros M0' pl cs s Hgp Hc E fx R M model HC.
  rewrite CHK0_eq in Hc.   (* [comment removed for export] *)
  exact (GPS.check_soundA BSEGS ITA ITA_ok ABOTH NXD LIMIT (fun _ => None) XNa XEa XB0 XAa AP.XT0 0%nat SWIN PERMc SPTOPc fs SHC VSHc (AINVat M0') KCAP FTOPc
           (AINV_f_frame SWIN GBOTH SHC AINVH HP both_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0' B0c C0c)
           (AINV_f_lazy SWIN GBOTH SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0' B0c C0c)
           ltac:(intros; rewrite both_A_img_hi, both_A_img_lo; eapply (AINV_f_facts SWIN GBOTH SHC AINVH HP); eassumption)
           fx_ok UINVd UINVd_agree (fun _ _ _ => t_nil) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
           RZ RZ_silent1_rz RZ_exit_rz RZ_conseq_rz (RUN_sound_fx BSEGS) both_in_hull both_hull_ok both_segs_wx
           (XNa_at M0') (XEa_at M0')
           (fun id args cs0 csa csb E0 fx0 R0 Mx mdl T _ Hn => ltac:(discriminate Hn))
           (XAa_at M0')
           (fun id args cs0 fd ps code E0 fx0 R0 Mx mdl _ Hn => ltac:(discriminate Hn))
           (fun h ch Hh => ltac:(discriminate Hh)) FUEL0 BF0 None pl cs s Hgp Hc E fx R M model t_nil HC
           ltac:(exact I) eq_refl).
Qed.

(* [comment removed for export] *)
Theorem XTa_sound : GPS.term_stmt BSEGS XTa PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc fx_ok UINVd RZ.
Proof.
  exact (XT70_sound RZ RZ_silent1_rz SHC KCAP AINVH SWIN HP PERMc SPTOPc fs HIDc HIDFc M0c B0c C0c FTOPc UINVd UINVd_agree
           M2S_H DTOR_H DTOR_FRAME PERM_flag_A CHK0 tail_sound RZ_conseq_rz).
Qed.

Variable D : env -> Fs.Fs -> TSet.
Hypothesis D_agree : forall E E' fs', env_agree NXD E E' -> D E fs' = D E' fs'.
Hypothesis D_nil : forall E fs', D E fs' [].
#[local] Notation HOLES := (fun (_ : nat) E fs' => D E fs').

Theorem drvA_cert_sound_rz : forall hs bf fuel pl cs s,
  gplan_ok pl = true ->
  CHKa hs bf fuel cs pl = COk s ->
  GPS.holes_stmt BSEGS hs PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc fx_ok UINVd HOLES RZ ->
  forall E fx R M model, cs_okA E cs fx R M model ->
  RZ (cfgF BSEGS fx R (pc cs) M model) (sd HOLES (D E (m_fs model)) E (m_fs model) s).
Proof.
  apply (drvA_cert_sound RZ RZ_silent1_rz RZ_exit_rz RZ_conseq_rz SHC KCAP AINVH SWIN HP PERMc SPTOPc fs HIDc HIDFc M0c B0c C0c FTOPc UINVd UINVd_agree).
  - exact (XNa_at M0c).
  - exact (XEa_at M0c).
  - exact (XAa_at M0c).
  - exact XTa_sound.
  - exact D_agree.
  - exact D_nil.
Qed.
End CertSoundA.
End BoDrvCertSoundA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGSoundA BoDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvInstFactsA BoDrvUinvA BoDrvCertSoundA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Lemma gplanUz : gplan_ok planUz = true. Proof. vmc. Qed.
Lemma gplanCOa : gplan_ok planCOa = true. Proof. vmc. Qed.
Lemma gplanCOz : gplan_ok planCOz = true. Proof. vmc. Qed.
Lemma gplanCOt : gplan_ok planCOt = true. Proof. vmc. Qed.
Lemma gplanD2 : gplan_ok planD2 = true. Proof. vmc. Qed.

Section S0SoundA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GBOTH SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH /\ (forall plo phi, In (plo, phi) (g_priv GBOTH) -> hi <= plo \/ phi <= lo).
Variable SPTOPc : Z.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Hypothesis bcap_ok : B0c + BCAP <= GBUDGET.
Hypothesis ccap_ok : C0c + CCAP <= GCOUNT.
Variable FTOPc : Z.
Hypothesis FTOPc_ok : Z.of_nat (length HIDFc) + FTOPc <= FMIN.
(* [comment removed for export] *)
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).
Definition UX0 (E : env) : Prop := True.
Lemma UX0_agree : forall E E', env_agree NXD E E' -> UX0 E -> UX0 E'. Proof. intros. exact I. Qed.
#[local] Notation UINVd := (UINVd a0 p fs data UX0).
#[local] Notation PERMc := PERM_A_lit.
#[local] Notation AINVc := (AINV_f SWIN GBOTH AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation RZ := (realizes BSEGS).
#[local] Notation cs_okA := (GPS.cs_ok BSEGS PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc fx_ok UINVd).

Hypothesis GC_all : forall M0 : word -> option byte,
  gcontracts BSEGS ITA ABOTH NXD PERMc SPTOPc fs SHC VSHc (AINV_f SWIN GBOTH AINVH PERMc SPTOPc HIDc HIDFc M0 B0c C0c) KCAP FTOPc fx_ok UINVd RZ GBOTH BCAP CCAP.
Hypothesis FZN_contract : callee_contract BSEGS SWIN GBOTH fx_ok RZ SHC KCAP AINVH BoDrvHooksA.BoFZ.ceN.
Hypothesis FZE_contract : callee_contract BSEGS SWIN GBOTH fx_ok RZ SHC KCAP AINVH BoDrvHooksA.BoFZ.ceE.
Hypothesis M2S_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Hypothesis DTOR_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn BSEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ exists cpm : byte, rdn BSEGS M (Z_to_bv 64 0x10da1c) 1 = Some [cpm] /\ bv_unsigned cpm <> 0.
Hypothesis DTOR_FRAME : forall L LF B C K M M' mdl, AINVH L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (bv_unsigned a) = true \/ in_mub (bv_unsigned a) = true) /\ M' a <> None) ->
  rdn BSEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  AINVH L LF B C K M' mdl.

Definition D0 (E : env) (fs' : Fs.Fs) : TSet := t_nil.
#[local] Notation HOLES := (fun (_ : nat) E fs' => D0 E fs').
Lemma holes0 : GPS.holes_stmt BSEGS HS0 PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc fx_ok UINVd HOLES RZ.
Proof. intros h ch Hh. discriminate Hh. Qed.

#[local] Notation SOUND := (drvA_cert_sound_rz SHC KCAP AINVH SWIN HP SWIN_img SPTOPc HIDc HIDFc M0c B0c C0c B0c_nonneg C0c_nonneg bcap_ok ccap_ok FTOPc FTOPc_ok
                              a0 p fs data UX0 UX0_agree GC_all FZN_contract FZE_contract M2S_H DTOR_H DTOR_FRAME D0 (fun _ _ _ _ => eq_refl) (fun _ _ => eq_refl)).
#[local] Notation DEN E model s := (sd HOLES (D0 E (m_fs model)) E (m_fs model) s).

Theorem usage1_sound : forall E fx R M model, cs_okA E tMu1n fx R M model -> RZ (cfgF BSEGS fx R (pc tMu1n) M model) (DEN E model shapeU).
Proof. exact (SOUND HS0 BF FUEL planU tMu1n shapeU gplanU certU1 holes0). Qed.
Theorem usage3_sound : forall E fx R M model, cs_okA E tMu3n fx R M model -> RZ (cfgF BSEGS fx R (pc tMu3n) M model) (DEN E model shapeU).
Proof. exact (SOUND HS0 BF FUEL planU tMu3n shapeU gplanU certU3 holes0). Qed.
Theorem usage1z_sound : forall E fx R M model, cs_okA E tMu1z fx R M model -> RZ (cfgF BSEGS fx R (pc tMu1z) M model) (DEN E model shapeUz).
Proof. exact (SOUND HS0 BF FUEL planUz tMu1z shapeUz gplanUz certU1z holes0). Qed.
Theorem usage3z_sound : forall E fx R M model, cs_okA E tMu3z fx R M model -> RZ (cfgF BSEGS fx R (pc tMu3z) M model) (DEN E model shapeUz).
Proof. exact (SOUND HS0 BF FUEL planUz tMu3z shapeUz gplanUz certU3z holes0). Qed.
Theorem cantopen_absent_sound : forall E fx R M model, cs_okA E tMoa fx R M model -> RZ (cfgF BSEGS fx R (pc tMoa) M model) (DEN E model shapeCOa).
Proof. exact (SOUND HS0 BF FUEL planCOa tMoa shapeCOa gplanCOa certCOa holes0). Qed.
Theorem cantopen_empty_sound : forall E fx R M model, cs_okA E tMoz fx R M model -> RZ (cfgF BSEGS fx R (pc tMoz) M model) (DEN E model shapeCOz).
Proof. exact (SOUND HS0 BF FUEL planCOz tMoz shapeCOz gplanCOz certCOz holes0). Qed.
Theorem cantopen_toolong_sound : forall E fx R M model, cs_okA E tMot fx R M model -> RZ (cfgF BSEGS fx R (pc tMot) M model) (DEN E model shapeCOt).
Proof. exact (SOUND HS0 BF FUEL planCOt tMot shapeCOt gplanCOt certCOt holes0). Qed.
(* [comment removed for export] *)
End S0SoundA.
