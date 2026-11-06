(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvNodesSoundA4.
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
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.ShapeNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.
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
#[local] Notation RZ := (realizes ASEGS).
Lemma RZ_silent1_rz : GPS.RZ_SILENT1 ASEGS RZ.
Proof. exact (GPS.RZ_SILENT1_realizes ASEGS). Qed.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
#[local] Notation AINVc := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation cs_okA := (GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV).
#[local] Notation Mr := (GPS.Mr SHC VSHc).
#[local] Notation A2 := (fun nd Ta Tb => forall cs csa csb E fx R M model,
    cs_okA E cs fx R M model -> nd cs = Some (csa, csb) -> Ta [] -> Tb [] ->
    (forall E' fx' R' M' model',
        env_agree NXD E E' /\ env_agree (nxt cs) E E' -> cs_okA E' csa fx' R' M' model' -> m_fs model' = m_fs model -> RZ (cfgF ASEGS fx' R' (pc csa) M' model') Ta) ->
    (forall E' fx' R' M' model',
        env_agree NXD E E' /\ env_agree (nxt cs) E E' -> cs_okA E' csb fx' R' M' model' -> m_fs model' = m_fs model -> RZ (cfgF ASEGS fx' R' (pc csb) M' model') Tb) ->
    RZ (cfgF ASEGS fx R (pc cs) M model) (t_alt2 Ta Tb)).

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
  know_ok ASEGS E (Mr E cs model M) k' ->
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
  - eapply (AINV_f_vm SWIN GASAN SHC AINVH HP); [exact CA | exact Hvm].
Qed.

Lemma alloc_fd_std : alloc_fd APS.fds_std = Z_to_bv 64 3.
Proof. vm_compute. reflexivity. Qed.


(* [comment removed for export] *)
Lemma rz_openat_pair : forall args L cs E fx R M model (mk : word -> Model) (f : afd) Ta Tb,
  cs_okA E cs fx R M model -> DNA.openat_ok ASEGS args cs = Some L -> fresh_ok NXD cs = true ->
  (forall path rest bs, args = path :: rest -> cstring_at E M (u (edenot E path)) bs -> Z.of_nat (length bs) = u (edenot E L) ->
     forall ms, ms_gpr ms 0 = AT_FDCWD -> ms_gpr ms 1 = edenot E path -> ms_gpr ms 2 = Z_to_bv 64 DNA.O_FLAGS -> ms_read_byte ms = mrb ASEGS M ->
     forall ef, check_syscall (sys_input ASEGS ms (Z_to_bv 64 56)) ef model = check_open_result_copyins (open_copyins ms) ef model mk) ->
  m_vm (mk (Z_to_bv 64 3)) = m_vm model -> m_halted (mk (Z_to_bv 64 3)) = m_halted model -> m_fs (mk (Z_to_bv 64 3)) = m_fs model ->
  APS.fds_ok E f (mk (Z_to_bv 64 3)) ->
  Ta [] -> Tb [] ->
  (forall E' fx' R' M' model',
      env_agree NXD E E' /\ env_agree (nxt cs) E E' -> cs_okA E' (DNA.openat_err_child cs) fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfgF ASEGS fx' R' (pc (DNA.openat_err_child cs)) M' model') Ta) ->
  (forall E' fx' R' M' model',
      env_agree NXD E E' /\ env_agree (nxt cs) E E' -> cs_okA E' (DNA.ret_with cs (ELit 3) (kn cs) (nxt cs) f) fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfgF ASEGS fx' R' (pc (DNA.ret_with cs (ELit 3) (kn cs) (nxt cs) f)) M' model') Tb) ->
  RZ (cfgF ASEGS fx R (pc cs) M model) (t_alt2 Ta Tb).
Proof.
  intros args L cs E fx R M model mk f Ta Tb HC Hok Hfresh Hspec Hvm Hh Hfsm Hfd HTa HTb Hka Hkb.
  destruct (openat_ok_soundI E cs fx R M model args L HC Hok) as (path & rest & bs & Hargs & Hec & G17 & G10 & G11 & G12 & Hafd & Hlen & Hceil & Hnw & Hstr).
  destruct (GPS.is_ecall_at_sound ASEGS cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  assert (E17 : Z_to_bv 5 17 = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11. rewrite E12 in G12.
  pose proof (u64_range (edenot E path)) as Rp. pose proof (u64_range (edenot E L)) as Rl.
  assert (Hfds : m_fds model = APS.fds_std) by (pose proof (co_fds HC) as X; rewrite Hafd in X; exact X).
  unfold cfgF.
  eapply (GPS.rz_step_ecall ASEGS RZ RZ_silent1_rz); [exact (co_halt HC) | eapply GPS.step_ecallF; eassumption | reflexivity | cbn; discriminate |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17))
    with (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17)).
  rewrite G17.
  set (ms := @epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (Z_to_bv 64 56)).
  assert (Hchk : forall ef, check_syscall (sys_input ASEGS ms (Z_to_bv 64 56)) ef model = check_open_result_copyins (open_copyins ms) ef model mk).
  { assert (Hrb : ms_read_byte ms = mrb ASEGS M) by (subst ms; apply ms_read_byte_ependA).
    assert (Ha1 : ms_gpr ms 1 = edenot E path) by (subst ms; rewrite ms_gpr_epend1; exact G11).
    assert (Ha0 : ms_gpr ms 0 = AT_FDCWD) by (subst ms; rewrite ms_gpr_epend0, G10; exact (ATFDCWD_eq)).
    assert (Ha2 : ms_gpr ms 2 = Z_to_bv 64 DNA.O_FLAGS) by (subst ms; rewrite ms_gpr_epend2; exact G12).
    clearbody ms. exact (Hspec path rest bs Hargs Hstr Hlen ms Ha0 Ha1 Ha2 Hrb). }
  set (effA := fun e : Z => with_copyins (open_copyins ms) (mkEffect (errno_ret e) [] [])).
  set (effB := with_copyins (open_copyins ms) (mkEffect (Z_to_bv 64 3) [] [])).
  set (IA := { e : Z | In e openat_errnos }).
  set (effs := fun i : IA + unit => match i with inl a => effA (proj1_sig a) | inr _ => effB end).
  set (mdls := fun i : IA + unit => match i with inl _ => model | inr _ => mk (Z_to_bv 64 3) end).
  apply (rz_alt2 ASEGS (mkCfg ms model) IA unit (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (mdls i)) Ta Tb
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
    pose proof (GPS.cs_ok_agree ASEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
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
  cs_okA E cs fx R M model -> DNA.openat_ok ASEGS args cs = Some L -> args = path :: rest ->
  cstring_at E M (u (edenot E path)) bs -> Z.of_nat (length bs) = u (edenot E L) -> (length bs <= 4095)%nat ->
  read_cstr (mrb ASEGS M) (edenot E path) = CstrOk bs.
Proof.
  intros E cs fx R M model args L path rest bs HC Hok Hargs Hstr Hlen Hl.
  destruct (openat_ok_soundI E cs fx R M model args L HC Hok) as (path' & rest' & bs' & Hargs' & _ & _ & _ & _ & _ & _ & Hlen' & _ & Hnw' & _).
  rewrite Hargs in Hargs'. injection Hargs' as <- <-.
  pose proof (u64_range (edenot E path)) as Rp. pose proof Hstr as (Sb & Sn & Sbs).
  rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E path)).
  apply (read_cstr_of_rdn ASEGS M _ bs).
  - exact Hl.
  - destruct Sbs as [-> | ->]; [intros [] | exact (NONUL2 E (co_uinv HC))].
  - apply (cstring_rdn E M _ bs Hstr); [lia|]. unfold two64 in *. lia.
Qed.

Theorem node_openat_file2_sound : forall args Ta Tb, A2 (DNA.node_openat_file2 ASEGS NXD args) Ta Tb.
Proof.
  intros args Ta Tb cs csa csb E fx R M model HC Hn HTa HTb Hka Hkb.
  unfold DNA.node_openat_file2 in Hn.
  destruct args as [|path [|lenE rest]]; [discriminate Hn | destruct (DNA.openat_ok ASEGS [path] cs); discriminate Hn |].
  destruct (DNA.openat_ok ASEGS (path :: lenE :: rest) cs) as [L|] eqn:Hok; [|discriminate Hn].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate Hn] end.
  injection Hn as <- <-.
  apply andb_prop in Hg as [Hg Hrng]. apply andb_prop in Hg as [Hg Hvl]. apply andb_prop in Hg as [Hg Hlen4]. apply andb_prop in Hg as [Hpl Hfresh].
  apply expr_eqb_eq in Hlen4. subst lenE.
  unfold DNA.path_len_ok in Hpl.
  destruct (xlo (kn cs) L) as [lo|] eqn:Hlo; [|discriminate Hpl]. destruct (xhi (kn cs) L) as [hi|] eqn:Hhi; [|discriminate Hpl].
  apply andb_prop in Hpl as [Hlo1 Hhi1]. apply Z.leb_le in Hlo1. apply Z.leb_le in Hhi1.
  pose proof (xlo_sound ASEGS E _ (kn cs) L lo (co_know HC) Hlo) as BL. pose proof (xhi_sound ASEGS E _ (kn cs) L hi (co_know HC) Hhi) as BH.
  assert (Hcls : u (ev E 4%nat) <= DNA.FCAP).
  { destruct (xlo (kn cs) (EVar 4)) as [l4|]; [|discriminate Hrng]. destruct (xhi (kn cs) (EVar 4)) as [h4|] eqn:Hh4; [|discriminate Hrng].
    apply andb_prop in Hrng as [_ Hr2]. apply Z.leb_le in Hr2.
    pose proof (xhi_sound ASEGS E _ (kn cs) _ _ (co_know HC) Hh4) as X. cbn [edenot] in X. lia. }
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
    apply (openat_rd_check ASEGS ms (Z_to_bv 64 56) model (eb E 2%nat) data).
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

Theorem node_openat_dir2_sound : forall args Ta Tb, A2 (DNA.node_openat_dir2 ASEGS NXD args) Ta Tb.
Proof.
  intros args Ta Tb cs csa csb E fx R M model HC Hn HTa HTb Hka Hkb.
  unfold DNA.node_openat_dir2 in Hn.
  destruct (DNA.openat_ok ASEGS args cs) as [L|] eqn:Hok; [|discriminate Hn].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate Hn] end.
  injection Hn as <- <-.
  apply andb_prop in Hg as [Hg Hcls]. apply andb_prop in Hg as [Hpl Hfresh].
  unfold DNA.path_len_ok in Hpl.
  destruct (xlo (kn cs) L) as [lo|] eqn:Hlo; [|discriminate Hpl]. destruct (xhi (kn cs) L) as [hi|] eqn:Hhi; [|discriminate Hpl].
  apply andb_prop in Hpl as [Hlo1 Hhi1]. apply Z.leb_le in Hlo1. apply Z.leb_le in Hhi1.
  pose proof (xlo_sound ASEGS E _ (kn cs) L lo (co_know HC) Hlo) as BL. pose proof (xhi_sound ASEGS E _ (kn cs) L hi (co_know HC) Hhi) as BH.
  pose proof (DIR2 E (co_uinv HC) (cls_is_sound E _ (kn cs) _ (co_know HC) Hcls)) as Hdir.
  destruct (openat_ok_soundI E cs fx R M model _ L HC Hok) as (path & rest & bs0 & Hargs' & _ & _ & _ & _ & _ & Hafd & _).
  assert (Hfds : m_fds model = APS.fds_std) by (pose proof (co_fds HC) as X; rewrite Hafd in X; exact X).
  apply (rz_openat_pair args L cs E fx R M model
           (fun fd => with_fds (fd_insert (m_fds model) fd State.FdDir) model)
           FdDir Ta Tb HC Hok Hfresh); try assumption.
  - intros path1 rest1 bs Hargs Hstr Hlen ms Ha0 Ha1 Ha2 Hrb ef.
    pose proof Hstr as (Sb & Sn & Sbs).
    assert (Hbs : bs = eb E 2%nat) by (destruct Sbs as [-> | ->]; [cbn in Hlen; lia | reflexivity]).
    apply (openat_dir_check ASEGS ms (Z_to_bv 64 56) model bs).
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
End AsDrvNodesSoundA4.
Require LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvNodesSoundA5.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.ShapeNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma read_file_check : forall segs ms x8 model p off data w,
  u x8 = 63 ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some (State.FdFile p off) -> fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  fs_lookup (m_fs model) p = Some data ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some w ->
  u (ms_gpr ms 2) <= rw_bytes_max -> 0 < u (ms_gpr ms 2) ->
  access_okb (ms_gpr ms 1) (u (ms_gpr ms 2)) = true ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = mkEffect (len_word (file_read data off (ms_gpr ms 2))) (delivered_writes (ms_gpr ms 1) (file_read data off (ms_gpr ms 2))) []
      /\ m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (State.FdFile p (bv_add off (len_word (file_read data off (ms_gpr ms 2)))))) model
      /\ evs = []))
  /\ (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled).
Proof.
  intros segs ms x8 model p off data w Hno Hfd Hfd32 Hfs Hw Hcnt Hpos Haok.
  set (bs := file_read data off (ms_gpr ms 2)).
  assert (HL : u (len_word (file_read data off (ms_gpr ms 2))) <= u (ms_gpr ms 2)).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (ms_gpr ms 2)) as Hc.
    rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat. rewrite Z.mod_small; lia. }
  split.
  - intros eff m' evs.
    rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite Haok. cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta.
    rewrite in_wmem_si.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
    unfold bs.
    destruct (file_read data off (ms_gpr ms 2)) as [|b bsr].
    + cbv beta iota. rewrite check_ret_only_ok_iff. cbn [delivered_writes length]. tauto.
    + destruct eff as [ret ws zs us cs copyins]. split.
      * intro H.
        destruct ws as [|[a bs'] [|? ?]]; try discriminate.
        destruct zs as [|? ?]; [|discriminate].
        destruct us as [|? ?]; [|discriminate].
        destruct cs as [|? ?]; [|discriminate].
        destruct copyins as [|? ?]; [|discriminate].
        destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr) && bv_eqb ret (len_word (b :: bsr)))%bool eqn:Hb;
          try rewrite Hb in H; [|discriminate].
        apply andb_true_iff in Hb as [Hb Hr]. apply andb_true_iff in Hb as [Ha Hbs].
        apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
        inversion H; subst. cbn [delivered_writes]. repeat split; congruence.
      * intros (Heff & -> & ->). cbn [delivered_writes] in Heff. inversion Heff; subst.
        rewrite bv_eqb_refl. rewrite (proj2 (listN_eqb_eq _ _) eq_refl). rewrite bv_eqb_refl. cbn [andb]. reflexivity.
  - intros eff Hs'.
    rewrite (check_syscall_63 segs ms x8 _ model Hno) in Hs'. unfold check_read in Hs'.
    rewrite Hfd32, Hfd in Hs'. cbv beta iota in Hs'.
    rewrite Haok in Hs'. cbn [negb] in Hs'. cbv beta iota in Hs'.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned in Hs'.
    rewrite Hfs in Hs'. cbv beta iota zeta in Hs'.
    rewrite in_wmem_si in Hs'.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs'. cbv beta iota in Hs'.
    revert Hs'. destruct (file_read data off (ms_gpr ms 2)) as [|b0 bsr]; intro Hs'.
    + exact (check_ret_only_no_unmodeled _ _ _ _ Hs').
    + destruct eff as [ret ws zs us cs copyins].
      destruct ws as [|[a bs'] [|? ?]]; try discriminate Hs'.
      destruct zs as [|? ?]; [|discriminate Hs']. destruct us as [|? ?]; [|discriminate Hs'].
      destruct cs as [|? ?]; [|discriminate Hs']. destruct copyins as [|? ?]; [|discriminate Hs'].
      revert Hs'. match goal with |- (if ?c then _ else _) = _ -> False => destruct c; intros Hs'; discriminate Hs' end.
Qed.

(* [comment removed for export] *)
Lemma read_dir_check : forall segs ms x8 model,
  u x8 = 63 -> fd_lookup (m_fds model) (ms_gpr ms 0) = Some State.FdDir -> fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  access_okb (ms_gpr ms 1) (u (ms_gpr ms 2)) = true ->
  forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff (errno_ret EISDIR) model [].
Proof.
  intros segs ms x8 model Hno Hfd Hfd32 Haok eff.
  rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read. rewrite Hfd32, Hfd, Haok. reflexivity.
Qed.

Section NodesSoundA5.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
#[local] Notation AINVc := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation cs_okA := (GPS.cs_ok ASEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV).
#[local] Notation N1 := (fun nd => GPS.node1_stmtN ASEGS NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ always nd).
#[local] Notation Mr := (GPS.Mr SHC VSHc).
#[local] Notation at_sys_soundI := (at_sys_sound SHC KCAP AINVH SWIN PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV).
#[local] Notation reg_is_soundI := (reg_is_sound SHC KCAP AINVH SWIN PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV).
#[local] Notation cs_ok_sys_retI := (cs_ok_sys_ret SHC KCAP AINVH SWIN HP PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV).

(* [comment removed for export] *)
Lemma hid_image_false : forall E cs B C K M mdl (a : word),
  AINVc (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  g_img_lo GASAN <= u a -> u a < g_img_hi GASAN -> GPS.hid SHC VSHc E cs mdl a = false.
Proof.
  intros E cs B C K M mdl a HA Hlo Hhi. unfold GPS.hid, GPS.lz.
  destruct (page_in_ranges (page_base a) (m_vm_lazy mdl)) eqn:Hp; [|reflexivity]. exfalso.
  unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hiv Hc]].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) (AINV_f_facts SWIN GASAN SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c _ _ _ _ _ _ _ HA) iv Hiv) as (L0 & L1 & L2).
  pose proof (GPS.page_base_le' a) as (P1 & P2 & P3).
  cbn [g_img_lo g_img_hi GASAN] in Hlo, Hhi, L2.
  unfold page_size in *. clear - H1 H2 P1 P2 P3 L2 Hlo Hhi. lia.
Qed.


(* [comment removed for export] *)
Lemma pages_in_image_not_lazy : forall Lc Lf B C K M mdl accs,
  AINVc Lc Lf B C K M mdl ->
  (forall a n, In (a, n) accs -> g_img_lo GASAN <= u a /\ u a + Z.of_nat n <= g_img_hi GASAN) ->
  forall p, In p (accesses_pages accs []) -> page_in_ranges p (m_vm_lazy mdl) = false.
Proof.
  intros Lc Lf B C K M mdl accs HA Hb p Hin.
  destruct (accesses_pages_in accs [] p Hin) as [[] | (a & n & k & Hin' & Hk & ->)].
  destruct (Hb a n Hin') as [Ha Hn].
  destruct (page_in_ranges (page_base_of (u a + Z.of_nat k)) (m_vm_lazy mdl)) eqn:Hp; [|reflexivity]. exfalso.
  unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hiv Hc]].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) (AINV_f_facts SWIN GASAN SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c _ _ _ _ _ _ _ HA) iv Hiv) as (L0 & L1 & L2).
  unfold page_base_of in H1, H2. unfold page_size in *.
  set (z := u a + Z.of_nat k) in *.
  pose proof (Z.mul_div_le z 4096 ltac:(lia)) as D1.
  pose proof (Z.mul_succ_div_gt z 4096 ltac:(lia)) as D2.
  pose proof (u64_range a) as Ra. cbn [g_img_lo g_img_hi GASAN] in Ha, Hn, L2.
  assert (Hq : 0 <= z / 4096 * 4096 < 2 ^ 64) by (split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia] | nia]).
  rewrite u64_lit in H1, H2 by exact Hq.
  assert (Hz : 65536 <= z < 6672384) by lia.
  assert (Hal : 16 <= z / 4096) by (apply Z.div_le_lower_bound; lia).
  clear - H1 H2 L2 Hz Hal D1 D2. lia.
Qed.

(* [comment removed for export] *)
Lemma cs_ok_sys_write : forall E cs fx R M M' model model' r v k' nx' f,
  cs_okA E cs fx R M model ->
  edenot E r = v ->
  m_vm model' = m_vm model -> m_halted model' = m_halted model -> m_fs model' = m_fs model ->
  APS.fds_ok E f model' ->
  know_ok ASEGS E (Mr E cs model M') k' ->
  (forall a : word, M' a <> M a -> GPS.in_wins PERMc (u a) /\ M' a <> None) ->
  cs_okA E (DNA.ret_with cs r k' nx' f) fx (regupd R 10 v) M' model'.
Proof.
  intros E cs fx R M M' model model' r v k' nx' f HC Hr Hvm Hh Hfs Hfd HK Hown.
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL].
  constructor; cbn [DNA.ret_with a_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_meter a_fake a_fbud mk_ss nxt pc];
    try assumption.
  - replace (10%bv : Prelude.reg) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
    apply APS.regs_ok_set_n; [exact CR | lia | exact Hr].
  - reflexivity.
  - rewrite (Mr_ret_with SHC HIDc HIDFc E cs r k' nx' f model model' M' Hvm). exact HK.
  - rewrite Hh. exact CH.
  - rewrite Hfs. exact CF.
  - eapply (AINV_f_vm SWIN GASAN SHC AINVH HP); [|exact Hvm].
    eapply (AINV_f_frame SWIN GASAN SHC AINVH HP asan_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c); [exact CA|].
    intros a Ha. destruct (Hown a Ha) as [Hw Hs]. split; [|exact Hs]. left. right. left. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma dst_ok_sound : forall E cs fx R M model cnt db dk,
  cs_okA E cs fx R M model -> DNA.dst_ok GASAN cs cnt = Some (db, dk) ->
  exists d nh wb wn, reg cs 11 = ELit d /\ db = ELit 0 /\ dk = d /\ xhi (kn cs) cnt = Some nh
    /\ getr R (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 d
    /\ u (edenot E cnt) <= nh /\ 0 <= nh
    /\ g_img_lo GASAN <= d /\ d + nh <= g_img_hi GASAN
    /\ In (wb, wb + wn) PERMc /\ wb <= d /\ d + nh <= wb + wn
    /\ (forall m, Z.of_nat m <= u (edenot E cnt) -> store_ok ASEGS (Mr E cs model M) (Z_to_bv 64 d) m = true).
Proof.
  intros E cs fx R M model cnt db dk HC H. unfold DNA.dst_ok in H.
  destruct (reg cs 11) as [d| | | | |op e1 e2| |] eqn:Hr11; try discriminate H;
    [|exfalso; clear - H; destruct op; try discriminate H; destruct e2; discriminate H]. cbn [split_lit] in H.
  destruct (xhi (kn cs) cnt) as [nh|] eqn:Hnh; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate H] end.
  injection H as <- <-.
  apply andb_prop in Hg as [Hg Hwin]. apply andb_prop in Hg as [Hg Hnh0]. apply andb_prop in Hg as [Hg Hhi]. apply andb_prop in Hg as [Hg Hlo].
  apply andb_prop in Hg as [Hfl Hwr].
  apply Z.leb_le in Hnh0. apply Z.leb_le in Hhi. apply Z.leb_le in Hlo.
  apply existsb_exists in Hwin as [[wbe wne] [Hin Hw]]. cbn [fst snd] in Hw.
  destruct wbe as [wb| | | | | | |]; try discriminate Hw. destruct wne as [wn| | | | | | |]; try discriminate Hw.
  apply andb_prop in Hw as [Hw Hw2]. apply andb_prop in Hw as [Hw Hw1]. apply andb_prop in Hw as [Hw Hw5]. apply andb_prop in Hw as [Hw3 Hw4].
  apply Z.leb_le in Hw1. apply Z.leb_le in Hw2. apply Z.leb_le in Hw3. apply Z.leb_le in Hw4. apply Z.ltb_lt in Hw5. change DNA.two64 with two64 in Hw5. unfold two64 in Hw5.
  pose proof (xhi_sound ASEGS E _ (kn cs) cnt nh (co_know HC) Hnh) as Bn.
  destruct (GCL.kwritable_x_sound ASEGS E _ (kn cs) (kn cs) (ELit 0) d cnt (co_know HC) (co_know HC) Hwr) as (W1 & W2 & W3).
  unfold estart, elenZ in W1, W2, W3. cbn [a_base a_off edenot] in W1, W2, W3.
  exists d, nh, wb, wn.
  assert (G11 : getr R (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 d).
  { rewrite (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 11 HC ltac:(lia)). rewrite Hr11. reflexivity. }
  assert (HinP : In (wb, wb + wn) PERMc).
  { rewrite <- (co_perm HC). unfold GPS.wins_den. apply in_map_iff. exists (ELit wb, ELit wn). split; [|exact Hin].
    cbn [fst snd]. unfold GPS.uE. cbn [edenot]. rewrite (u64_lit wb) by lia. rewrite (u64_lit wn) by lia. reflexivity. }
  assert (Hst : forall m, Z.of_nat m <= u (edenot E cnt) -> store_ok ASEGS (Mr E cs model M) (Z_to_bv 64 d) m = true).
  { intros m Hm. rewrite u64_lit in W1 by lia. rewrite Z.add_0_l in W1. exact (W1 m Hm). }
  repeat split; try assumption; try reflexivity; try lia.
Qed.

(* [comment removed for export] *)
Lemma Mr_grows : forall E cs model M M', mem_grows M M' -> mem_grows (Mr E cs model M) (Mr E cs model M').
Proof.
  intros E cs model M M' HG x. unfold GPS.Mr, mrestrict. destruct (GPS.hid SHC VSHc E cs model x); [intros H; exact H | apply HG].
Qed.
Lemma Mr_sub : forall E cs model M, mem_grows (Mr E cs model M) M.
Proof.
  intros E cs model M x. unfold GPS.Mr, mrestrict. destruct (GPS.hid SHC VSHc E cs model x); intros H; [exfalso; exact (H eq_refl) | exact H].
Qed.
Lemma Mr_wbytes_out : forall E cs model M (dw : word) bs (x : word),
  u dw + Z.of_nat (length bs) <= 2 ^ 64 ->
  u x < u dw \/ u dw + Z.of_nat (length bs) <= u x ->
  Mr E cs model (wbytes M dw bs) x = Mr E cs model M x.
Proof.
  intros E cs model M dw bs x Hnw Hx. unfold GPS.Mr, mrestrict. destruct (GPS.hid SHC VSHc E cs model x); [reflexivity|].
  apply wbytes_out; assumption.
Qed.

(* [comment removed for export] *)
Lemma havoc_after_write : forall E cs model M k (d : Z) (cnt : expr) bs,
  know_ok ASEGS E (Mr E cs model M) k ->
  0 <= d < 2 ^ 64 -> d + u (edenot E cnt) <= 2 ^ 64 ->
  Z.of_nat (length bs) <= u (edenot E cnt) ->
  know_ok ASEGS E (Mr E cs model (wbytes M (Z_to_bv 64 d) bs)) (kn_havoc k (ELit 0) d cnt).
Proof.
  intros E cs model M k d cnt bs HK Hd Hnw Hbs. pose proof (u64_range (edenot E cnt)) as Hc.
  eapply APS.know_ok_havoc; [exact HK | | apply Mr_grows; apply wbytes_grows].
  intros x Hx. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite u64_lit in Hx by lia.
  apply Mr_wbytes_out; rewrite u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma blob0_after_write : forall E cs Lc Lf B C K M0 mdl M (d : Z) (n : expr) (kb : nat) bs,
  AINVc Lc Lf B C K M0 mdl ->
  (forall a : word, g_img_lo GASAN <= u a -> u a < g_img_hi GASAN -> GPS.hid SHC VSHc E cs mdl a = false) ->
  g_img_lo GASAN <= d -> d + Z.of_nat (length bs) <= g_img_hi GASAN ->
  eb E kb = bs -> Z.of_nat (length bs) = u (edenot E n) ->
  kentry_ok ASEGS E (Mr E cs mdl (wbytes M (Z_to_bv 64 d) bs)) (KBlob (SA (ELit 0) d) n kb).
Proof.
  intros E cs Lc Lf B C K M0 mdl M d n kb bs HA Hhid Hlo Hhi Heb Hlen.
  pose proof (AINV_f_facts SWIN GASAN SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0c B0c C0c _ _ _ _ _ _ _ HA) as _.
  cbn [g_img_lo g_img_hi GASAN] in Hlo, Hhi, Hhid.
  cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite u64_lit by lia. rewrite Z.add_0_l.
  split; [lia|]. split; [rewrite Heb; exact Hlen|].
  intros i Hi. unfold GPS.Mr, mrestrict.
  rewrite (Hhid (Z_to_bv 64 (d + i))) by (rewrite u64_lit by lia; lia).
  replace (d + i) with (u (Z_to_bv 64 d) + Z.of_nat (Z.to_nat i)) by (rewrite u64_lit by lia; lia).
  rewrite wbytes_nth; [rewrite Heb; reflexivity | rewrite u64_lit by lia; lia | lia].
Qed.

(* [comment removed for export] *)
Lemma fds3_lookup3 : forall e, fd_lookup (APS.fds3 e) (Z_to_bv 64 3) = Some e. Proof. reflexivity. Qed.
Lemma fds3_insert3 : forall e e', fd_insert (APS.fds3 e) (Z_to_bv 64 3) e' = APS.fds3 e'. Proof. reflexivity. Qed.
Lemma fd32_3 : fd32 (Z_to_bv 64 3) = Z_to_bv 64 3. Proof. apply fd32_small. rewrite u64_lit; lia. Qed.

Lemma delivered_accesses_in : forall (buf : word) bs (a : word) n,
  In (a, n) (write_accesses (delivered_writes buf bs)) -> a = buf /\ n = length bs.
Proof.
  intros buf [|b r] a n H; cbn [delivered_writes write_accesses] in H; [destruct H|].
  destruct H as [H|[]]. injection H as <- <-. split; reflexivity.
Qed.
Lemma adv_delivered_epend : forall {fx0 : FPState} regs pc0 mem rom x8 r buf data,
  advance_past_svc (apply_effect (@epend fx0 regs pc0 mem rom x8) (mkEffect r (delivered_writes buf data) []))
  = @mkst fx0 (regupd regs 10 r) (v_addi pc0 4) (wbytes mem buf data) rom.
Proof.
  intros fx0 regs pc0 mem rom x8 r buf [|b data']; cbn [delivered_writes].
  - rewrite adv_eff_ret_epend. reflexivity.
  - apply adv_write1_epend.
Qed.

Lemma read_stepA : forall E cs fx R M model T p (offw : word) c (d cnt : Z),
  cs_okA E cs fx R M model ->
  is_ecall_at ASEGS cs = true ->
  getr R (Z_to_bv 5 17) = Z_to_bv 64 63 -> getr R (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 3 ->
  getr R (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 d -> u (getr R (Z_to_bv 5 (Z.of_nat 12))) = cnt ->
  1 <= cnt <= 65536 ->
  g_img_lo GASAN <= d -> d + cnt <= g_img_hi GASAN ->
  (forall m, Z.of_nat m <= cnt -> store_ok ASEGS (Mr E cs model M) (Z_to_bv 64 d) m = true) ->
  m_fds model = APS.fds3 (State.FdFile p offw) -> fs_lookup (m_fs model) p = Some c ->
  (let bs := file_read c offw (getr R (Z_to_bv 5 (Z.of_nat 12))) in
   Z.of_nat (length bs) <= cnt ->
   RZ (cfgF ASEGS fx (regupd R 10 (len_word bs)) (pc cs + 4) (wbytes M (Z_to_bv 64 d) bs)
          (with_fds (APS.fds3 (State.FdFile p (bv_add offw (len_word bs)))) model)) T) ->
  RZ (cfgF ASEGS fx R (pc cs) M model) T.
Proof.
  intros E cs fx R M model T p offw c d cnt HC Hec G17 G10 G11 Hcnt Hcr Hlo Hhi Hst Hfds Hfs HK.
  cbv zeta in HK.
  destruct (GPS.is_ecall_at_sound ASEGS cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  assert (E17 : Z_to_bv 5 17 = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11. rewrite E12 in Hcnt, HK.
  set (bs := file_read c offw (getr R 12)) in HK.
  assert (HLbs : Z.of_nat (length bs) <= cnt).
  { subst bs. rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat. rewrite Hcnt. lia. }
  specialize (HK HLbs).
  cbn [g_img_lo g_img_hi GASAN] in Hlo, Hhi.
  unfold cfgF.
  eapply (GPS.rz_step_ecall ASEGS RZ RZ_silent1); [exact (co_halt HC) | eapply GPS.step_ecallF; eassumption | reflexivity | cbn; discriminate |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17))
    with (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17)).
  set (ms := @epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17)).
  set (model' := with_fds (APS.fds3 (State.FdFile p (bv_add offw (len_word bs)))) model) in HK.
  set (eff := mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 d) bs) []).
  (* [comment removed for export] *)
  assert (Hst' : store_ok ASEGS M (Z_to_bv 64 d) (Z.to_nat cnt) = true).
  { eapply store_ok_mono; [apply Mr_sub | apply Hst; lia]. }
  destruct (read_bytes_map_of_store_ok ASEGS M (Z_to_bv 64 d) (Z.to_nat cnt) Hst' ltac:(lia)) as [wm Hwm].
  rewrite Z2Nat.id in Hwm by lia.
  assert (G0 : ms_gpr ms 0 = Z_to_bv 64 3) by (subst ms; rewrite ms_gpr_epend0; exact G10).
  assert (G1 : ms_gpr ms 1 = Z_to_bv 64 d) by (subst ms; rewrite ms_gpr_epend1; exact G11).
  assert (G2 : ms_gpr ms 2 = getr R 12) by (subst ms; rewrite ms_gpr_epend2; reflexivity).
  assert (Hcw : Z_to_bv 64 cnt = getr R 12) by (apply bv_eq; rewrite u64_lit by lia; symmetry; exact Hcnt).
  destruct (read_file_check ASEGS ms (getr R 17) model p offw c wm) as [Hchk Hnu].
  - rewrite G17. apply u64_lit. lia.
  - rewrite G0, Hfds. apply fds3_lookup3.
  - rewrite G0. apply fd32_3.
  - exact Hfs.
  - rewrite G1, G2, <- Hcw. unfold ms_writable_byte. subst ms. cbn [ms_mem epend]. exact Hwm.
  - rewrite G2, Hcnt. unfold rw_bytes_max. lia.
  - rewrite G2, Hcnt. lia.
  - rewrite G1, G2, Hcnt. unfold access_okb, TASK_SIZE. rewrite u64_lit by lia. apply andb_true_intro. split; apply Z.leb_le; lia.
  - rewrite G0, G1, G2 in Hchk. fold bs in Hchk.
    eapply RZ_silent1.
    { apply (node_chk_ev_nl ms model (getr R 17) unit (fun _ => eff) (fun _ => model') (fun _ => [])).
      - rewrite G17. reflexivity.
      - exact (co_halt HC).
      - reflexivity.
      - intros []. apply (proj2 (Hchk _ _ _)). subst eff model'. rewrite Hfds, fds3_insert3. repeat split; reflexivity.
      - intros eff0 m' ev H. exists tt. apply (proj1 (Hchk _ _ _)) in H as (-> & -> & ->). subst eff model'. rewrite Hfds, fds3_insert3.
        repeat split; reflexivity.
      - exact Hnu.
      - intros []. subst model'. rewrite with_fds_halted. exact (co_halt HC).
      - intros [] pg Hin. subst model'. cbn [m_vm_lazy with_fds].
        refine (pages_in_image_not_lazy _ _ _ _ _ _ model _ (co_ainv HC) _ pg Hin).
        intros a n Ha. subst eff. cbn [syscall_effect_accesses eff_copyins eff_writes app] in Ha.
        apply delivered_accesses_in in Ha as [-> ->]. cbn [g_img_lo g_img_hi GASAN]. rewrite u64_lit by lia.
        clear - Hlo Hhi HLbs Hcr. lia. }
    cbn beta. subst eff ms.
    rewrite adv_delivered_epend, (v_addi_pc (pc cs) Hpc0 Hpc4). exact HK.
Qed.

(* [comment removed for export] *)
Lemma u_esub : forall E a b, u (edenot E b) <= u (edenot E a) -> u (edenot E (esub a b)) = u (edenot E a) - u (edenot E b).
Proof.
  intros E a b H. pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E b)) as Rb.
  unfold esub. rewrite mkAlu_denot. unfold Sem.alu64, Sem.alu. rewrite bv_sub_unsigned, bv_wrap64_mod. rewrite Z.mod_small; lia.
Qed.
Lemma eadd_bv : forall E a b, edenot E (eadd a b) = bv_add (edenot E a) (edenot E b).
Proof. intros E a b. unfold eadd. rewrite mkAlu_denot. reflexivity. Qed.
Lemma u_bv_add_small : forall (a b : word), u a + u b < 2 ^ 64 -> u (bv_add a b) = u a + u b.
Proof.
  intros a b H. pose proof (u64_range a). pose proof (u64_range b). rewrite bv_add_unsigned, bv_wrap64_mod. apply Z.mod_small. lia.
Qed.
Lemma errno_EISDIR : errno_ret EISDIR = Z_to_bv 64 (two64 - 21).
Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma file_read_chunk0 : forall c (offw cntw : word),
  offw = Z_to_bv 64 0 -> cntw = Z_to_bv 64 65536 -> file_read c offw cntw = APS.chunk 0 c.
Proof.
  intros c offw cntw -> ->. rewrite file_read_unguarded. unfold APS.chunk. rewrite Nat.mul_0_r.
  unfold word_to_nat. rewrite (u64_lit 0) by lia. rewrite (u64_lit 65536) by lia. change (Z.to_nat 0) with 0%nat. cbn [skipn]. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem node_read_sound : N1 (DNA.node_read ASEGS GASAN).
Proof.
  intros cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DNA.node_read in Hn.
  destruct (a_fd cs) as [|kb len off|] eqn:Hafd; [discriminate Hn| |].
  - (* [comment removed for export] *)
    destruct (DNA.at_sys ASEGS cs 63 && DNA.reg_is cs 10 3)%bool eqn:Hg0; [|discriminate Hn]. cbn [negb] in Hn. cbv zeta beta in Hn.
    destruct (DNA.dst_ok GASAN cs (reg cs 12)) as [[db dk]|] eqn:Hdst; [|discriminate Hn].
    destruct (xlo2 (kn cs) (reg cs 12)) as [clo|] eqn:Hclo; [|discriminate Hn].
    destruct (xhi2 (kn cs) (reg cs 12)) as [chi|] eqn:Hchi; [|discriminate Hn].
    destruct (Z.leb 1 clo && Z.leb chi DNA.CHZ)%bool eqn:Hcr; [|discriminate Hn]. cbn [negb] in Hn.
    destruct (xlo2 (kn cs) (esub len off)) as [rlo|] eqn:Hrlo; [|discriminate Hn].
    destruct (xhi2 (kn cs) (esub len off)) as [rhi|] eqn:Hrhi; [|discriminate Hn].
    apply andb_prop in Hg0 as [H63 H10]. apply andb_prop in Hcr as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. unfold DNA.CHZ in Hc2.
    destruct (at_sys_soundI E cs fx R M model 63 HC H63) as (Hec & G17 & _).
    destruct (reg_is_soundI E cs fx R M model 10 3 HC ltac:(lia) H10) as [G10 _].
    destruct (dst_ok_sound E cs fx R M model (reg cs 12) db dk HC Hdst)
      as (d & nh & wb & wn & Hr11 & -> & -> & Hnh & G11 & Hcn & Hnh0 & Hdlo & Hdhi & HinP & Hwb & Hwn & Hst).
    pose proof Hdlo as Hdlo'. pose proof Hdhi as Hdhi'. cbn [g_img_lo g_img_hi GASAN] in Hdlo', Hdhi'.
    pose proof (APS.xlo2_sound ASEGS E _ (kn cs) _ _ (co_know HC) Hclo) as Lc1.
    pose proof (APS.xhi2_sound ASEGS E _ (kn cs) _ _ (co_know HC) Hchi) as Lc2.
    pose proof (APS.xlo2_sound ASEGS E _ (kn cs) _ _ (co_know HC) Hrlo) as Lr1.
    pose proof (APS.xhi2_sound ASEGS E _ (kn cs) _ _ (co_know HC) Hrhi) as Lr2.
    pose proof (co_fds HC) as Hfd. rewrite Hafd in Hfd. cbn [APS.fds_ok] in Hfd.
    destruct Hfd as (p & c & Hfds & Hfs & Hlen & Hoff & Hch). unfold APS.uE, GPS.uE in Hlen, Hoff.
    pose proof (u64_range (edenot E (reg cs 12))) as Rc. pose proof (u64_range (edenot E len)) as Rl. pose proof (u64_range (edenot E off)) as Ro.
    assert (Hrem : u (edenot E (esub len off)) = u (edenot E len) - u (edenot E off)) by (apply u_esub; exact Hoff).
    rewrite Hrem in Lr1, Lr2.
    pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 12 HC ltac:(lia)) as G12.
    pose proof Hlen as Hflen. unfold APS.flen in Hflen.
    assert (HEX : forall lh, xhi2 (kn cs) len = Some lh -> Z.ltb lh DNA.FCAP = true -> u (edenot E len) = Z.of_nat (length c)).
    { intros lh Hlh Hlt. apply Z.ltb_lt in Hlt. unfold DNA.FCAP in Hlt.
      pose proof (APS.xhi2_sound ASEGS E _ (kn cs) len lh (co_know HC) Hlh) as X. clear - X Hlt Hflen. lia. }
    assert (Hcl : u (edenot E len) <= Z.of_nat (length c)) by (clear - Hflen; lia).
    (* [comment removed for export] *)
    assert (Hhid : forall a : word, g_img_lo GASAN <= u a -> u a < g_img_hi GASAN -> GPS.hid SHC VSHc E cs model a = false).
    { intros a Ha1 Ha2. exact (hid_image_false E cs _ _ _ _ model a (co_ainv HC) Ha1 Ha2). }
    (* [comment removed for export] *)
    assert (OWN : forall bs (a : word), Z.of_nat (length bs) <= u (edenot E (reg cs 12)) ->
              wbytes M (Z_to_bv 64 d) bs a <> M a -> GPS.in_wins PERMc (u a) /\ wbytes M (Z_to_bv 64 d) bs a <> None).
    { intros bs a HL Ha. pose proof (u64_range a) as Ra'.
      assert (Hin : d <= u a < d + Z.of_nat (length bs)).
      { destruct (Z_lt_ge_dec (u a) d) as [Hlt|Hge].
        { exfalso. apply Ha. apply wbytes_out; rewrite u64_lit by lia; lia. }
        destruct (Z_lt_ge_dec (u a) (d + Z.of_nat (length bs))) as [Hlt2|Hge2]; [lia|].
        exfalso. apply Ha. apply wbytes_out; rewrite u64_lit by lia; lia. }
      split.
      - exists wb, (wb + wn). split; [exact HinP | lia].
      - replace a with (Z_to_bv 64 (u (Z_to_bv 64 d) + Z.of_nat (Z.to_nat (u a - d)))) by (apply bv_eq; rewrite (u64_lit d) by lia; rewrite u64_lit by lia; lia).
        rewrite wbytes_nth; [discriminate | rewrite u64_lit by lia; lia | lia]. }
    (* [comment removed for export] *)
    assert (BLOB : forall (n : expr) bs,
              bs = file_read c (edenot E off) (edenot E (reg cs 12)) ->
              Z.of_nat (length bs) = u (edenot E n) -> Z.of_nat (length bs) <= u (edenot E (reg cs 12)) ->
              know_ok ASEGS E (Mr E cs model (wbytes M (Z_to_bv 64 d) bs))
                (match lit_of off, lit_of (reg cs 12) with
                 | Some zo, Some zc => if (Z.eqb zo 0 && Z.eqb zc 65536)%bool then [KBlob (SA (ELit 0) d) n kb] else []
                 | _, _ => [] end)).
    { intros n bs Hbs HLn HLc.
      destruct (lit_of off) as [zo|] eqn:Hzo; [|constructor]. destruct (lit_of (reg cs 12)) as [zc|] eqn:Hzc; [|constructor].
      destruct (Z.eqb zo 0 && Z.eqb zc 65536)%bool eqn:Hb; [|constructor].
      apply andb_prop in Hb as [Hb1 Hb2]. apply Z.eqb_eq in Hb1. apply Z.eqb_eq in Hb2. subst zo zc.
      destruct (lit_of_sound E off 0 Hzo) as [Eoff _]. destruct (lit_of_sound E (reg cs 12) 65536 Hzc) as [Ecnt _].
      constructor; [|constructor].
      apply (blob0_after_write E cs _ _ _ _ _ _ model M d n kb bs (co_ainv HC) Hhid Hdlo); [clear - Hdhi' HLc Hcn; cbn [g_img_hi GASAN]; lia | | exact HLn].
      rewrite <- (Nat.add_0_r kb), (Hch 0%nat ltac:(lia)). rewrite Hbs. symmetry. apply file_read_chunk0; assumption. }
    match type of Hn with (if ?b then _ else _) = _ => destruct b eqn:Heof end.
    + (* [comment removed for export] *)
      injection Hn as <-.
      apply andb_prop in Heof as [Heof Hex]. apply andb_prop in Heof as [Hr0 Hr0']. apply Z.eqb_eq in Hr0. apply Z.eqb_eq in Hr0'. subst rlo rhi.
      destruct (xhi2 (kn cs) len) as [lh|] eqn:Hlh; [|discriminate Hex]. pose proof (HEX lh eq_refl Hex) as HL.
      apply (read_stepA E cs fx R M model T p (edenot E off) c d (u (edenot E (reg cs 12))) HC Hec G17 G10 G11);
        [rewrite G12; reflexivity | lia | exact Hdlo | clear - Hdhi' Hcn; cbn [g_img_hi GASAN]; lia | exact Hst | exact Hfds | exact Hfs |].
      cbv zeta. rewrite G12. intros HLbs.
      assert (Hbs0 : file_read c (edenot E off) (edenot E (reg cs 12)) = []).
      { apply length_zero_iff_nil. rewrite length_file_read. unfold word_to_nat. clear - HL Lr1 Lr2 Hoff Rc Ro Rl. lia. }
      rewrite Hbs0. cbn [wbytes]. change (len_word []) with (Z_to_bv 64 0).
      assert (Hadd0 : bv_add (edenot E off) (Z_to_bv 64 0) = edenot E off).
      { apply bv_eq. rewrite u_bv_add_small by (rewrite u64_lit by lia; lia). rewrite u64_lit by lia. lia. }
      rewrite Hadd0.
      refine (Hk E fx _ _ _ (conj (env_agree_refl _ _) (env_agree_refl _ _)) _ _); [|apply with_fds_fs].
      unfold DNA.ret_simple. rewrite Hafd.
      apply (cs_ok_sys_retI E cs fx R M model (ELit 0) (Z_to_bv 64 0) (FdFile kb len off) _ HC); [reflexivity | reflexivity | apply with_fds_halted | apply with_fds_fs |].
      cbn [APS.fds_ok]. exists p, c. rewrite with_fds_fds, with_fds_fs. unfold APS.uE, GPS.uE.
      split; [reflexivity|]. split; [exact Hfs|]. split; [exact Hlen|]. split; [exact Hoff | exact Hch].
    + match type of Hn with (if ?b then _ else _) = _ => destruct b eqn:Hfull end.
      * (* [comment removed for export] *)
        injection Hn as <-.
        assert (HF : u (edenot E (reg cs 12)) <= u (edenot E len) - u (edenot E off)).
        { apply orb_prop in Hfull as [H|H]; [apply Z.leb_le in H; lia|].
          apply (lin_ge0_sound ASEGS E _ (kn cs) _ _ (co_know HC)) in H. cbn [xt_den] in H. rewrite Hrem in H. lia. }
        apply (read_stepA E cs fx R M model T p (edenot E off) c d (u (edenot E (reg cs 12))) HC Hec G17 G10 G11);
          [rewrite G12; reflexivity | lia | exact Hdlo | clear - Hdhi' Hcn; cbn [g_img_hi GASAN]; lia | exact Hst | exact Hfds | exact Hfs |].
        cbv zeta. rewrite G12. intros HLbs.
        set (bs := file_read c (edenot E off) (edenot E (reg cs 12))) in *.
        assert (HLeq : Z.of_nat (length bs) = u (edenot E (reg cs 12))).
        { subst bs. rewrite length_file_read. unfold word_to_nat. clear - HF Hcl Hoff Rc Ro Rl. lia. }
        assert (Hlw : len_word bs = edenot E (reg cs 12)).
        { apply bv_eq. unfold len_word. rewrite u64_lit by lia. exact HLeq. }
        rewrite Hlw, <- (eadd_bv E off (reg cs 12)).
        refine (Hk E fx _ _ _ (conj (env_agree_refl _ _) (env_agree_refl _ _)) _ _); [|apply with_fds_fs].
        apply (cs_ok_sys_write E cs fx R M _ model _ (reg cs 12) (edenot E (reg cs 12)) _ (nxt cs) _ HC eq_refl);
          [reflexivity | apply with_fds_halted | apply with_fds_fs | | |].
        -- cbn [APS.fds_ok]. exists p, c. rewrite with_fds_fds, with_fds_fs. unfold APS.uE, GPS.uE.
           split; [reflexivity|]. split; [exact Hfs|]. split; [exact Hlen|]. split; [|exact Hch].
           rewrite eadd_bv, u_bv_add_small by lia. lia.
        -- apply Forall_app. split.
           ++ apply (BLOB (reg cs 12) bs eq_refl HLeq ltac:(lia)).
           ++ apply havoc_after_write; [exact (co_know HC) | lia | lia | lia].
        -- intros a Ha. exact (OWN bs a ltac:(lia) Ha).
      * (* [comment removed for export] *)
        match type of Hn with (if ?b then _ else _) = _ => destruct b eqn:Hshort; [|discriminate Hn] end.
        injection Hn as <-.
        apply andb_prop in Hshort as [Hshort Hex]. apply andb_prop in Hshort as [Hr1 Hlt]. apply Z.leb_le in Hr1.
        destruct (xhi2 (kn cs) len) as [lh|] eqn:Hlh; [|discriminate Hex]. pose proof (HEX lh eq_refl Hex) as HL.
        assert (HS : u (edenot E len) - u (edenot E off) <= u (edenot E (reg cs 12)) - 1).
        { apply orb_prop in Hlt as [H|H]; [apply Z.ltb_lt in H; lia|].
          apply (lin_ge0_sound ASEGS E _ (kn cs) _ _ (co_know HC)) in H. cbn [xt_den] in H. rewrite Hrem in H. lia. }
        apply (read_stepA E cs fx R M model T p (edenot E off) c d (u (edenot E (reg cs 12))) HC Hec G17 G10 G11);
          [rewrite G12; reflexivity | lia | exact Hdlo | clear - Hdhi' Hcn; cbn [g_img_hi GASAN]; lia | exact Hst | exact Hfds | exact Hfs |].
        cbv zeta. rewrite G12. intros HLbs.
        set (bs := file_read c (edenot E off) (edenot E (reg cs 12))) in *.
        assert (HLeq : Z.of_nat (length bs) = u (edenot E len) - u (edenot E off)).
        { subst bs. rewrite length_file_read. unfold word_to_nat. clear - HS HL Hoff Rc Ro Rl Hr1. lia. }
        assert (Hlw : len_word bs = edenot E (esub len off)).
        { apply bv_eq. unfold len_word. rewrite u64_lit by lia. rewrite Hrem. exact HLeq. }
        assert (Hol : bv_add (edenot E off) (len_word bs) = edenot E len).
        { apply bv_eq. rewrite u_bv_add_small by (unfold len_word; rewrite u64_lit by lia; lia). unfold len_word. rewrite u64_lit by lia. lia. }
        rewrite Hol, Hlw.
        refine (Hk E fx _ _ _ (conj (env_agree_refl _ _) (env_agree_refl _ _)) _ _); [|apply with_fds_fs].
        apply (cs_ok_sys_write E cs fx R M _ model _ (esub len off) (edenot E (esub len off)) _ (nxt cs) _ HC eq_refl);
          [reflexivity | apply with_fds_halted | apply with_fds_fs | | |].
        -- cbn [APS.fds_ok]. exists p, c. rewrite with_fds_fds, with_fds_fs. unfold APS.uE, GPS.uE.
           split; [reflexivity|]. split; [exact Hfs|]. split; [exact Hlen|]. split; [lia | exact Hch].
        -- apply Forall_app. split.
           ++ apply (BLOB (esub len off) bs eq_refl ltac:(rewrite Hrem; exact HLeq) ltac:(lia)).
           ++ apply havoc_after_write; [exact (co_know HC) | lia | lia | lia].
        -- intros a Ha. exact (OWN bs a ltac:(lia) Ha).
  - (* [comment removed for export] *)
    match type of Hn with (if ?b then _ else _) = _ => destruct b eqn:Hg; [|discriminate Hn] end. injection Hn as <-.
    apply andb_prop in Hg as [Hg Hc]. apply andb_prop in Hg as [H63 H10].
    destruct (DNA.dst_ok GASAN cs (reg cs 12)) as [[db dk]|] eqn:Hdst; [|discriminate Hc].
    destruct (xlo (kn cs) (reg cs 12)) as [cl|] eqn:Hcl; [|discriminate Hc].
    destruct (xhi (kn cs) (reg cs 12)) as [ch|] eqn:Hchh; [|discriminate Hc].
    apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. unfold DNA.CHZ in Hc2.
    pose proof (xlo_sound ASEGS E _ (kn cs) _ _ (co_know HC) Hcl) as Lc1.
    pose proof (xhi_sound ASEGS E _ (kn cs) _ _ (co_know HC) Hchh) as Lc2.
    destruct (at_sys_soundI E cs fx R M model 63 HC H63) as (Hec & G17 & _).
    destruct (reg_is_soundI E cs fx R M model 10 3 HC ltac:(lia) H10) as [G10 _].
    destruct (dst_ok_sound E cs fx R M model (reg cs 12) db dk HC Hdst)
      as (d & nh & wb & wn & Hr11 & -> & -> & Hnh & G11 & Hcn & Hnh0 & Hdlo & Hdhi & HinP & Hwb & Hwn & Hst).
    cbn [g_img_lo g_img_hi GASAN] in Hdlo, Hdhi.
    pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ _ _ _ E cs fx R M model 12 HC ltac:(lia)) as G12.
    pose proof (co_fds HC) as Hfd. rewrite Hafd in Hfd. cbn [APS.fds_ok] in Hfd.
    destruct (GPS.is_ecall_at_sound ASEGS cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
    assert (E17 : Z_to_bv 5 17 = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
    assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
    assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
    assert (E12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
    rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11. rewrite E12 in G12.
    unfold cfgF.
    eapply (GPS.rz_step_ecall ASEGS RZ RZ_silent1); [exact (co_halt HC) | eapply GPS.step_ecallF; eassumption | reflexivity | cbn; discriminate |].
    change (GPS.ependF fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17))
      with (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17)).
    assert (Hrd : forall eff, check_syscall (sys_input ASEGS (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom ASEGS) (getr R 17)) (getr R 17)) eff model
                              = check_ret_only eff (errno_ret EISDIR) model []).
    { intros eff. apply read_dir_check.
      - rewrite G17. apply u64_lit. lia.
      - rewrite ms_gpr_epend0, G10, Hfd. apply fds3_lookup3.
      - rewrite ms_gpr_epend0, G10. apply fd32_3.
      - rewrite ms_gpr_epend1, ms_gpr_epend2, G11, G12. unfold access_okb, TASK_SIZE. rewrite u64_lit by lia.
        apply andb_true_intro. split; apply Z.leb_le; lia. }
    eapply RZ_silent1.
    { apply (node_det_noacc ASEGS _ model (getr R 17) (mkEffect (errno_ret EISDIR) [] []) model []).
      - exact (co_halt HC).
      - reflexivity.
      - intros eff m' evs. rewrite Hrd, check_ret_only_ok_iff. tauto.
      - intros eff. rewrite Hrd. apply check_ret_only_no_unmodeled.
      - exact (co_halt HC).
      - reflexivity. }
    cbn beta. rewrite adv_eff_ret_epend, (v_addi_pc (pc cs) Hpc0 Hpc4), errno_EISDIR.
    refine (Hk E fx _ _ _ (conj (env_agree_refl _ _) (env_agree_refl _ _)) _ eq_refl).
    unfold DNA.ret_simple. rewrite Hafd.
    apply (cs_ok_sys_retI E cs fx R M model (ELit (two64 - 21)) (Z_to_bv 64 (two64 - 21)) FdDir model HC); try reflexivity.
    cbn [APS.fds_ok]. exact Hfd.
Qed.
End NodesSoundA5.
End AsDrvNodesSoundA5.
Module AsDrvUinvA.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.
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
End AsDrvUinvA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvNodesAllA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvNodesSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvNodesSoundA2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 AsDrvNodesSoundA4 AsDrvNodesSoundA5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11.AsDrvNodesSoundA6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11.AsDrvNodesSoundA7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11.AsDrvNodesSoundA9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Lemma RZ_silent1_rz : GPS.RZ_SILENT1 ASEGS (realizes ASEGS).
Proof. exact (GPS.RZ_SILENT1_realizes ASEGS). Qed.
Lemma RZ_exit_rz : GPS.RZ_EXIT ASEGS (realizes ASEGS).
Proof. exact (GPS.RZ_EXIT_realizes ASEGS). Qed.
Lemma RZ_conseq_rz : GPS.RZ_CONSEQ (realizes ASEGS).
Proof. exact (GPS.RZ_CONSEQ_realizes ASEGS). Qed.

Section AllA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
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
#[local] Notation AINVc := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation RZ := (realizes ASEGS).

(* [comment removed for export] *)
Hypothesis GC : gcontracts ASEGS ITA AASAN NXD PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ GASAN BCAP CCAP.
Hypothesis FZN_contract : callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP AINVH AsDrvHooksA.AsFZ.ceN.
Hypothesis FZE_contract : callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP AINVH AsDrvHooksA.AsFZ.ceE.
Hypothesis M2S_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
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

Theorem XNa_sound_all : GPS.ext_stmt ASEGS NXD XNa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof. apply XNa_sound; try base; node. Qed.

Theorem XEa_sound_all : GPS.emit_stmt ASEGS NXD XEa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  apply XEa_sound. intros cs fd ps cs' E fx R M model T HC Hn HT Hk.
  exact (node_stdio_write_sound (SR_realizes ASEGS) SHC KCAP AINVH SWIN HP PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV UINV_agree PERM_files
           cs fd ps cs' E fx R M model T HC Hn HT Hk).
Qed.

Theorem XAa_sound_all : GPS.alt2_stmt ASEGS NXD XAa PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  apply XAa_sound.
  - intros args Ta Tb. exact (node_openat_file2_sound SHC KCAP AINVH SWIN HP PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV UINV_agree NONUL2 data FILE2 args Ta Tb).
  - intros args Ta Tb. exact (node_openat_dir2_sound SHC KCAP AINVH SWIN HP PERMc SPTOPc FS0 HIDc HIDFc M0c B0c C0c FTOPc UINV UINV_agree NONUL2 DIR2 args Ta Tb).
Qed.
End AllA.
End AsDrvNodesAllA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvCertSoundA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 AsDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvInstFactsA AsDrvUinvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma CHK0_eq : CHK0 = fun cs p => checkA ASEGS ITA AASAN NXD LIMIT ISP0 XNa XEa XB0 XAa AP.XT0 (fun _ => None) 0%nat false BF0 FUEL0 None cs p.
Proof. reflexivity. Qed.

Section CertSoundA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable SWIN : list (Z * Z).
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
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
#[local] Notation AINVat M0 := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0 B0c C0c).
#[local] Notation AINVc := (AINVat M0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation RZ := (realizes ASEGS).
#[local] Notation cs_okat M0 := (GPS.cs_ok ASEGS PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd).
#[local] Notation cs_okA := (cs_okat M0c).

(* [comment removed for export] *)
Hypothesis GC_all : forall M0 : word -> option byte,
  gcontracts ASEGS ITA AASAN NXD PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ GASAN BCAP CCAP.
Hypothesis FZN_contract : callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP AINVH AsDrvHooksA.AsFZ.ceN.
Hypothesis FZE_contract : callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP AINVH AsDrvHooksA.AsFZ.ceE.
Hypothesis M2S_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
(* [comment removed for export] *)
Hypothesis DTOR_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ exists cpm : byte, rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [cpm] /\ bv_unsigned cpm <> 0.
Hypothesis DTOR_FRAME : forall L LF B C K M M' mdl, AINVH L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (bv_unsigned a) = true \/ in_mub (bv_unsigned a) = true) /\ M' a <> None) ->
  rdn ASEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  AINVH L LF B C K M' mdl.

(* [comment removed for export] *)
Lemma XNa_at : forall M0, GPS.ext_stmt ASEGS NXD XNa PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ.
Proof.
  intros M0.
  apply (XNa_sound_all SHC KCAP AINVH SWIN HP SWIN_img PERMc SPTOPc fs HIDc HIDFc M0 B0c C0c B0c_nonneg C0c_nonneg bcap_ok ccap_ok FTOPc FTOPc_ok UINVd UINVd_agree
           (GC_all M0) FZN_contract FZE_contract M2S_H).
  - intros E [HU _]. exact (U_drv_NONUL12 a0 p fs data E HU).
  - intros E [HU _]. exact (U_drv_ABSENT2 a0 p fs data E HU).
Qed.
Lemma XEa_at : forall M0, GPS.emit_stmt ASEGS NXD XEa PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ.
Proof.
  intros M0. apply (XEa_sound_all SHC KCAP AINVH SWIN HP PERMc SPTOPc fs HIDc HIDFc M0 B0c C0c FTOPc UINVd UINVd_agree).
  intros a Ha. rewrite <- (PERM_A_den (Env (fun _ => Z_to_bv 64 0) (fun _ => []))). exact (PERM_files_A _ a Ha).
Qed.
Lemma XAa_at : forall M0, GPS.alt2_stmt ASEGS NXD XAa PERMc SPTOPc fs SHC VSHc (AINVat M0) KCAP FTOPc fx_ok UINVd RZ.
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
  RZ (cfgF ASEGS fx R (pc cs) M model) (GPS.sd (fun _ _ _ => t_nil) t_nil E (m_fs model) s).
Proof.
  intros M0' pl cs s Hgp Hc E fx R M model HC.
  rewrite CHK0_eq in Hc.   (* [comment removed for export] *)
  exact (GPS.check_soundA ASEGS ITA ITA_ok AASAN NXD LIMIT (fun _ => None) XNa XEa XB0 XAa AP.XT0 0%nat SWIN PERMc SPTOPc fs SHC VSHc (AINVat M0') KCAP FTOPc
           (AINV_f_frame SWIN GASAN SHC AINVH HP asan_G_ro_img2 drvA_G_img_al drvA_G_img_shlo PERMc SPTOPc HIDc HIDFc M0' B0c C0c)
           (AINV_f_lazy SWIN GASAN SHC AINVH HP PERMc SPTOPc HIDc HIDFc M0' B0c C0c)
           ltac:(intros; rewrite asan_A_img_hi, asan_A_img_lo; eapply (AINV_f_facts SWIN GASAN SHC AINVH HP); eassumption)
           fx_ok UINVd UINVd_agree (fun _ _ _ => t_nil) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
           RZ RZ_silent1_rz RZ_exit_rz RZ_conseq_rz (RUN_sound_fx ASEGS) asan_in_hull asan_hull_ok asan_segs_wx
           (XNa_at M0') (XEa_at M0')
           (fun id args cs0 csa csb E0 fx0 R0 Mx mdl T _ Hn => ltac:(discriminate Hn))
           (XAa_at M0')
           (fun id args cs0 fd ps code E0 fx0 R0 Mx mdl _ Hn => ltac:(discriminate Hn))
           (fun h ch Hh => ltac:(discriminate Hh)) FUEL0 BF0 None pl cs s Hgp Hc E fx R M model t_nil HC
           ltac:(exact I) eq_refl).
Qed.

(* [comment removed for export] *)
Theorem XTa_sound : GPS.term_stmt ASEGS XTa PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc fx_ok UINVd RZ.
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
  GPS.holes_stmt ASEGS hs PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc fx_ok UINVd HOLES RZ ->
  forall E fx R M model, cs_okA E cs fx R M model ->
  RZ (cfgF ASEGS fx R (pc cs) M model) (sd HOLES (D E (m_fs model)) E (m_fs model) s).
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
End AsDrvCertSoundA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvInstFactsA AsDrvUinvA AsDrvCertSoundA.
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
Hypothesis HP : hprops SWIN GASAN SHC AINVH.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN ->
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
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
#[local] Notation AINVc := (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation RZ := (realizes ASEGS).
#[local] Notation cs_okA := (GPS.cs_ok ASEGS PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc fx_ok UINVd).

Hypothesis GC_all : forall M0 : word -> option byte,
  gcontracts ASEGS ITA AASAN NXD PERMc SPTOPc fs SHC VSHc (AINV_f SWIN GASAN AINVH PERMc SPTOPc HIDc HIDFc M0 B0c C0c) KCAP FTOPc fx_ok UINVd RZ GASAN BCAP CCAP.
Hypothesis FZN_contract : callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP AINVH AsDrvHooksA.AsFZ.ceN.
Hypothesis FZE_contract : callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP AINVH AsDrvHooksA.AsFZ.ceE.
Hypothesis M2S_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Hypothesis DTOR_H : forall L LF B C K M mdl, AINVH L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ exists cpm : byte, rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [cpm] /\ bv_unsigned cpm <> 0.
Hypothesis DTOR_FRAME : forall L LF B C K M M' mdl, AINVH L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (bv_unsigned a) = true \/ in_mub (bv_unsigned a) = true) /\ M' a <> None) ->
  rdn ASEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  AINVH L LF B C K M' mdl.

Definition D0 (E : env) (fs' : Fs.Fs) : TSet := t_nil.
#[local] Notation HOLES := (fun (_ : nat) E fs' => D0 E fs').
Lemma holes0 : GPS.holes_stmt ASEGS HS0 PERMc SPTOPc fs SHC VSHc AINVc KCAP FTOPc fx_ok UINVd HOLES RZ.
Proof. intros h ch Hh. discriminate Hh. Qed.

#[local] Notation SOUND := (drvA_cert_sound_rz SHC KCAP AINVH SWIN HP SWIN_img SPTOPc HIDc HIDFc M0c B0c C0c B0c_nonneg C0c_nonneg bcap_ok ccap_ok FTOPc FTOPc_ok
                              a0 p fs data UX0 UX0_agree GC_all FZN_contract FZE_contract M2S_H DTOR_H DTOR_FRAME D0 (fun _ _ _ _ => eq_refl) (fun _ _ => eq_refl)).
#[local] Notation DEN E model s := (sd HOLES (D0 E (m_fs model)) E (m_fs model) s).

Theorem usage1_sound : forall E fx R M model, cs_okA E tMu1n fx R M model -> RZ (cfgF ASEGS fx R (pc tMu1n) M model) (DEN E model shapeU).
Proof. exact (SOUND HS0 BF FUEL planU tMu1n shapeU gplanU certU1 holes0). Qed.
Theorem usage3_sound : forall E fx R M model, cs_okA E tMu3n fx R M model -> RZ (cfgF ASEGS fx R (pc tMu3n) M model) (DEN E model shapeU).
Proof. exact (SOUND HS0 BF FUEL planU tMu3n shapeU gplanU certU3 holes0). Qed.
Theorem usage1z_sound : forall E fx R M model, cs_okA E tMu1z fx R M model -> RZ (cfgF ASEGS fx R (pc tMu1z) M model) (DEN E model shapeUz).
Proof. exact (SOUND HS0 BF FUEL planUz tMu1z shapeUz gplanUz certU1z holes0). Qed.
Theorem usage3z_sound : forall E fx R M model, cs_okA E tMu3z fx R M model -> RZ (cfgF ASEGS fx R (pc tMu3z) M model) (DEN E model shapeUz).
Proof. exact (SOUND HS0 BF FUEL planUz tMu3z shapeUz gplanUz certU3z holes0). Qed.
Theorem cantopen_absent_sound : forall E fx R M model, cs_okA E tMoa fx R M model -> RZ (cfgF ASEGS fx R (pc tMoa) M model) (DEN E model shapeCOa).
Proof. exact (SOUND HS0 BF FUEL planCOa tMoa shapeCOa gplanCOa certCOa holes0). Qed.
Theorem cantopen_empty_sound : forall E fx R M model, cs_okA E tMoz fx R M model -> RZ (cfgF ASEGS fx R (pc tMoz) M model) (DEN E model shapeCOz).
Proof. exact (SOUND HS0 BF FUEL planCOz tMoz shapeCOz gplanCOz certCOz holes0). Qed.
Theorem cantopen_toolong_sound : forall E fx R M model, cs_okA E tMot fx R M model -> RZ (cfgF ASEGS fx R (pc tMot) M model) (DEN E model shapeCOt).
Proof. exact (SOUND HS0 BF FUEL planCOt tMot shapeCOt gplanCOt certCOt holes0). Qed.
(* [comment removed for export] *)
End S0SoundA.
