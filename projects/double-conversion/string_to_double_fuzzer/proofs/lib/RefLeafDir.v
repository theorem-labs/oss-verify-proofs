(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require DispatchCompute.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefStartupDefs.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec LibWritev RefNodes RefExitBase RefExit RefMemcpyLib RefMemcpyBase RefMemcpy RefStartup RefMainEntry Hoare RefPilotOOM_defs RefPilotOOM.
From Stdlib Require ZArith NArith List Lia Bool String.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec SymExec2 SymExec2Sound SymDriveX Spec RefStartup RefMainEntry RefMainEntryN RefReadBase RefWorld RefReadErr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec RefNodes RefNodesDir RefMemcpyLib RefLayout RefStartup RefMainEntry Frame MallocDefs RefEnframeBase RefReadBase RefWorld RefTargetPre RefReadErr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require RefPilotOOM_defs RefPilotOOM RefLim.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require SymXfer SymAbove RefW65x.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec RefStartup RefMainEntry RefReadBase RefWorld RefPilotOOM_defs RefPilotOOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module RefDirFront.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AllocSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.FileSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AgentLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibWritev OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefExitBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefExit OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpy OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStartup OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMainEntry OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefPilotOOM_defs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefPilotOOM.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Section FPW_1. Context {fx : PropExec.FPState}.


Section DirFront.
  Context {AL : RefLim.AllocLim}.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.

  (* [comment removed for export] *)
  Definition fdsD1 : list (word * FdEntry) := fd_insert (fds0) (Z_to_bv 64 3) FdDir.
  Definition modelD1 : Model := model1g sp0 tid brk mbase fs0 stdin0 FdDir.

  (* [comment removed for export] *)
  Definition dir_seg2_kont (T : TSet) : Prop :=
    forall vals R M,
      length vals = 38%nat -> vals_ev vals 0 = sp0 ->
      vals_ev vals 1 = p0 sp0 a0s dot_path envv -> vals_ev vals 2 = p1 sp0 a0s dot_path envv ->
      vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->   (* [comment removed for export] *)
      regs_ok (ENV a0s dot_path vals) srB0 R -> know_ok RSEGS (ENV a0s dot_path vals) M knA ->
      (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xa763c) M (seg_rom RSEGS)) modelD1) T.

  Lemma dot_nonul : ~ In (Z_to_bv 8 0) dot_path.
  Proof. cbn. intros [E|[]]. apply (f_equal bv_unsigned) in E. vm_compute in E. lia. Qed.

  Lemma dir_seg1 : forall KA T,
    open_err_branch sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 KA -> dir_seg2_kont T ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x32574) mem0 (seg_rom RSEGS))
                            (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0))
               (t_alt2 KA T).
  Proof.
    intros KA T HKA HT.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s dot_path envv uid hw rdraw tid regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s dot_path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s dot_path envv rdraw tid regs0) with (ENV a0s dot_path (vals0 sp0 a0s dot_path envv rdraw tid regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s dot_path envv rdraw tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, length_skipn, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 sp0 a0s dot_path envv) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s dot_path envv) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    assert (P6t : vals_ev vals 6 = canary_w rdraw) by reflexivity.   (* [comment removed for export] *)
    assert (P7t : vals_ev vals 7 = secret_w rdraw) by reflexivity.   (* [comment removed for export] *)
    destruct (main_str sp0 a0s dot_path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    assert (ABOVE : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV a0s dot_path vals) mem0 _ 0%nat 0xe6000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 sp0 a0s dot_path envv) (length dot_path + 1) = Some (dot_path ++ [Z_to_bv 8 0])).
    { rewrite <- Sr. apply rdn_agree. intros j Hj. apply ABOVE.
      pose proof (u64_range (p1 sp0 a0s dot_path envv)). unfold p1 in *. rewrite u_small by lia. lia. }
    (* [comment removed for export] *)
    eapply (rz_openat_dot RSEGS _ _ _ (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0) ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - (* [comment removed for export] *) rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - (* [comment removed for export] *) split; [cbn; lia|]. split; [apply dot_nonul|].
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. exact Sr'.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0xa7638 + 4)%Z with 0xa763c%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s dot_path)))
        with (ENV a0s dot_path (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P6t.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P7t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0xa7638 + 4)%Z with 0xa763c%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) FdDir) (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0)) with modelD1.
      pose proof (regs_set_a0 (ENV a0s dot_path vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      eapply (HT vals); try eassumption.
  Qed.
End DirFront.
End FPW_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefDirFront.

(* [comment removed for export] *)
Module RefDirTail.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStartup OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMainEntry OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMainEntryN OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefWorld OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadErr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPW_2. Context {fx : PropExec.FPState}.

Record dir_tail_pre (sp0 p1 : word) (tid can : Z) (mem0 : word -> option byte)   (* [comment removed for export] *)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := DIR_TAIL_PRE {
  dt_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);   (* [comment removed for export] *)
  dt_gp : getr R 3 = Z_to_bv 64 0x10800;
  dt_tp : getr R 4 = Z_to_bv 64 0xc4918;
  dt_s2 : getr R 18 = p1;                                  (* [comment removed for export] *)
  dt_stack : stack_writable M sp0;
  dt_img : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs;
  dt_tid : cell M 0xc4870 4 tid;
  dt_tidr : (0 < tid < 2 ^ 22)%Z;
  dt_self : cell M 0xc4850 8 0xc4850;
  dt_can : (0 <= can < 2 ^ 64)%Z;        (* [comment removed for export] *)
  dt_canary : cell M 0xe4b88 8 can;
  dt_pagesz : cell M 0xe4bd8 8 4096;
  dt_above : forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a
}.

Section DirTail.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0.

  Theorem dir_tail : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model),
    m_halted model = None -> m_vm_lazy model = [] ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) (bv_unsigned (canary_w rdraw)) mem0 R M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x327a0) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error dot_path) (m_fs model)).
  Proof.
    intros R M model Hh Hlazy Hfd2 P.
    destruct P as [Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htidr Mself Hcan Mcanary Mpagesz Habove].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    edestruct (main_strN sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat) as (Sr & Slo & Shi & Slen & t8 & Ht8);
      [cbn; lia|].
    cbn [nth length Nat.add dot_path app] in Sr, Slo, Shi, Ht8.
    set (pp := p1 sp0 a0s dot_path envv) in *.
    change (cat_argv_ptr sp0 [a0s; dot_path] envv 1) with pp in Sr, Slo, Shi, Ht8.
    change (Z.of_nat 1) with 1%Z in Ht8.
    pose proof (u64_range pp) as Hppr.
    assert (Hstr : rdn RSEGS M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0]).
    { rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia. }
    assert (Ht8' : rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8).
    { rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove.
      rewrite (u_small (bv_unsigned pp + 1)) by lia. rewrite u_small by lia. lia. }
    apply (ref_read_error_dot sp0 [] model Hvsp Hh Hlazy Hfd2 pp (bv_unsigned tid) R M
             Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htidr Mself (bv_unsigned (canary_w rdraw)) Hcan Mcanary
             Mpagesz Slo t8 ltac:(lia) Hstr Ht8').
  Qed.
End DirTail.
End FPW_2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefDirTail.

(* [comment removed for export] *)
Module RefDirMid.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AllocSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.FileSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AgentLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodesDir OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefLayout OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStartup OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMainEntry OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Frame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MallocDefs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefEnframeBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefWorld OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefTargetPre OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadErr RefDirTail.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefPilotOOM_defs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefPilotOOM.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymXfer OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymAbove OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefW65x.RefW65_defs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefW65x.RefW65 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefW65x.RefW65m OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefW65x.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPW_3. Context {fx : PropExec.FPState}.

Definition DFUEL : nat := 5000.
Definition DSTOPS : list Z := [0x327a0; 0xa6728; 0x3281c; 0x9835c; 0x96094]%Z.
Definition dscr0 : scripts := SCR [] [] [].
End FPW_3.

#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen DFUEL DSTOPS scr NX true.

(* [comment removed for export] *)
Section FPW_4. Context {fx : PropExec.FPState}.

Definition kn_cells : list kentry :=
  [KWr (SA (ELit 0) 0xb2000) 0x34000;
   KWord (SA (ELit 0) 0xc4870) 4 (EVar 4);          (* [comment removed for export] *)
   KWord (SA (ELit 0) 0xc4850) 8 (ELit 0xc4850);     (* [comment removed for export] *)
   KWord (SA (ELit 0) 0xe4bd8) 8 (ELit 4096)].       (* [comment removed for export] *)
Definition kn_img : list kentry := map (fun iv => KImg (fst iv) (snd iv)) re_ivs.
(* [comment removed for export] *)
Definition kn_D0 : list kentry := Eval vm_compute in (kn_RE 1 4194303 ++ kn_cells ++ kn_img ++ kn_M1).

Lemma kn_D0_eq : kn_D0 = kn_RE 1 4194303 ++ kn_cells ++ kn_img ++ kn_M1.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_a7480 : fetch_word RSEGS (Z_to_bv 64 0xa7638) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

Lemma know_of_img_clear : forall E M ivs,
  Forall (fun iv => img_clear M (fst iv) (snd iv)) ivs ->
  forallb (fun iv => Z.leb 0 (fst iv) && Z.leb (snd iv) (2 ^ 64)) ivs = true ->
  know_ok RSEGS E M (map (fun iv => KImg (fst iv) (snd iv)) ivs).
Proof.
  intros E M ivs H Hb. unfold know_ok. rewrite Forall_map. rewrite forallb_forall in Hb.
  apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) H _ Hin) as Hc.
  specialize (Hb _ Hin). apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [kentry_ok fst snd] in *. split; [exact H1|]. split; [exact H2|]. exact Hc.
Qed.

Lemma kword_of_cell : forall E M a n v,
  cell M a n v -> (n <= 8)%nat -> (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  kentry_ok RSEGS E M (KWord (SA (ELit 0) a) n (ELit v)).
Proof.
  intros E M a n v Hc Hn H0 H64. cbn [kentry_ok edenot]. split; [exact Hn|].
  split; [apply flat_intro; cbn [edenot]; rewrite ?u0; lia|].
  rewrite adenot_lit0. exact Hc.
Qed.

Section DirMid.
  Context {AL : RefLim.AllocLim}.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.

  Lemma dot_len : (length dot_path <= 4095)%nat.
  Proof. cbn. lia. Qed.

  (* [comment removed for export] *)
  Definition modelDir (VM : VmMaps) : Model :=
    mkModelA (fd_insert fds0 (Z_to_bv 64 3) FdDir) VM stdin0 fs0 None (Some tid) None.

  (* [comment removed for export] *)
  Definition after_malloc_dir (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 sp0 a0s dot_path envv) mb gm (canary_w rdraw) (secret_w rdraw) R M ->   (* [comment removed for export] *)
      world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned (secret_w rdraw)) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb gm -> vm_small VM gm ->
      above_sp0 sp0 mem0 M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x325c8) M (seg_rom RSEGS)) (modelDir VM)) K.

  Theorem dir_brk : forall K, after_malloc_dir K ->
    brk_ok_branch_g sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 FdDir (t_alt2 (t_die msg_oom fs0) K).
  Proof.
    intros K AM. exact (brk_ok_sem_g sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk dot_len FdDir K AM).
  Qed.

  Theorem dir_mmap : forall K, after_malloc_dir K ->
    mmap_ok_branch_g sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 FdDir
                     (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
  Proof.
    intros K AM. exact (mmap_ok_sem_g sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk dot_len FdDir K AM).
  Qed.

  (* [comment removed for export] *)
  Theorem dir_read : forall K,
    (forall R' M' VM', dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) (bv_unsigned (canary_w rdraw)) mem0 R' M' ->   (* [comment removed for export] *)
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x327a0) M' (seg_rom RSEGS)) (modelDir VM')) K) ->
    after_malloc_dir K.
  Proof.
    intros K TAIL R M VM mb gm area brkv mas EA RP W MF VP VS HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
    pose proof (rp_gm _ _ _ _ _ _ _ _ RP) as Hgm. pose proof (rp_p1 _ _ _ _ _ _ _ _ RP) as Hp1.
    set (p1v := p1 sp0 a0s dot_path envv) in *.
    set (vals := valsr sp0 p1v mb gm (bv_unsigned tid) (canary_w rdraw) (secret_w rdraw) R).
    set (E := ENVr vals []).
    assert (HL : length vals = 40%nat) by (subst vals; unfold valsr; rewrite length_app; cbn; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1v) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = tid) by (cbn; apply Z_to_bv_bv_unsigned).
    assert (P7 : vals_ev vals 7 = canary_w rdraw) by reflexivity.   (* [comment removed for export] *)
    pose proof (read_pre_regs sp0 p1v mb gm (bv_unsigned tid) (canary_w rdraw) (secret_w rdraw) R M [] RP : regs_ok E sr_RE R) as HR.
    assert (HK : know_ok RSEGS E M kn_D0).
    { rewrite kn_D0_eq. apply know_ok_app. split; [|apply know_ok_app; split; [|apply know_ok_app; split]].
      - apply (read_pre_know sp0 p1v mb gm (bv_unsigned tid) (canary_w rdraw) (secret_w rdraw) R M [] RP); lia.
      - destruct W. unfold kn_cells.
        repeat apply know_ok_cons; try apply Forall_nil.
        + split; [apply flat_intro; cbn [edenot]; rewrite ?u0; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite u0, Z.add_0_l.
          eapply (store_ok_window RSEGS M (Z_to_bv 64 0xb2000) (Z_to_bv 64 (0xb2000 + d)) 212992 m 0xb2000 0xe6000);
            [reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
        + cbn [kentry_ok edenot]. split; [lia|]. split; [apply flat_intro; cbn [edenot]; rewrite ?u0; lia|].
          rewrite adenot_lit0. change (ev E 4) with (vals_ev vals 4). rewrite P4, <- (Z_to_bv_bv_unsigned 64 tid). exact w_tid.
        + apply kword_of_cell; [exact w_self | lia | lia | cbn; lia].
        + apply kword_of_cell; [exact w_pagesz | lia | lia | cbn; lia].
      - apply know_of_img_clear; [apply re_ivs_of_world; exact (w_img _ _ _ _ _ _ _ _ W) | vm_compute; reflexivity].
      - (* [comment removed for export] *)
        subst E vals. exact (rp_malloc _ _ _ _ _ _ _ _ RP sp0 p1v (Z_to_bv 64 (bv_unsigned tid)) (Z_to_bv 64 0) (Z_to_bv 64 0) (tl (junk_vals R)) [[]]). }
    clearbody vals. subst E.
    (* [comment removed for export] *)
    run_block_keep dscr0 40%nat.
    assert (HA1 : above_sp0 sp0 mem0 M0).
    { lazymatch goal with EQM : M0 = mem_denot ?E ?Mo ?log |- _ =>
        lazymatch type of HK with know_ok _ _ _ ?kn =>
        intros xa Hxa; rewrite EQM, (mem_denot_above_kb RSEGS E M0 Mo kn log 0%nat 0xe6000 0x7fff7f800000 xa HK);
          [apply HA, Hxa | vm_compute; reflexivity | lia | cbn [ev ENVr]; pins; lia | cbn [ev ENVr]; pins; lia | lia | lia] end end. }
    clear EQM HA. rename HA1 into HA.
    (* [comment removed for export] *)
    eapply (rz_read_dir_mapped RSEGS R0 (Z_to_bv 64 0xa7638) M0 (modelDir VM) ECALLW (Z_to_bv 64 3) 65536 K fetch_a7480 is_ecall_ECALLW eq_refl eq_refl).
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). reflexivity.
    - change (bv_unsigned (Z_to_bv 64 3)) with 3%Z. lia.
    - reflexivity.
    - regv HR (12 : reg). reflexivity.
    - lia.
    - lia.
    - (* [comment removed for export] *)
      regv HR (11 : reg). cbn [edenot]. apply access_okb_true_intro; unfold STAGE; rewrite ?u_small by lia; cbn; lia.
    - rewrite v_addi_pc4 by lia. change (0xa7638 + 4)%Z with 0xa763c%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret EISDIR) (ELit (2 ^ 64 - 21)) HR ltac:(apply bv_eq; reflexivity)) as HR2 end.
      clear HR. rename HR2 into HR.
      (* [comment removed for export] *)
      run_block_keep dscr0 40%nat.
      assert (HA2 : above_sp0 sp0 mem0 M1).
      { lazymatch goal with EQM : M1 = mem_denot ?E ?Mo ?log |- _ =>
          lazymatch type of HK with know_ok _ _ _ ?kn =>
          intros xa Hxa; rewrite EQM, (mem_denot_above_kb RSEGS E M1 Mo kn log 0%nat 0xe6000 0x7fff7f800000 xa HK);
            [apply HA, Hxa | vm_compute; reflexivity | lia | cbn [ev ENVr]; pins; lia | cbn [ev ENVr]; pins; lia | lia | lia] end end. }
      clear EQM HA.
      change 206752%Z with 0x327a0%Z.
      apply (TAIL R1 M1 VM). constructor.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + unfold stack_writable. lazymatch type of HK with know_ok _ ?E _ ?kn =>
          apply (kwr_window E M1 kn (EVar 0) (-8388608) 8388608 _ HK); [vm_compute; reflexivity | cbn [edenot ev ENVr]; pins; lia] end.
      + lazymatch type of HK with know_ok _ ?E _ ?kn =>
          apply (img_clear_of_know E); apply (kderive_all_sound RSEGS _ M1 kn); [exact HK | vm_compute; reflexivity] end.
      + kcell HK.
      + exact Htid.
      + kcell HK.
      + exact (u64_range (canary_w rdraw)).   (* [comment removed for export] *)
      + kcell HK.
      + kcell HK.
      + exact HA2.
  Qed.
End DirMid.
End FPW_4.

End RefDirMid.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStartup OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMainEntry OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefWorld OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefPilotOOM_defs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefPilotOOM RefDirTail RefDirFront RefDirMid.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefLim.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Section FPW_5. Context {fx : PropExec.FPState}.


Lemma teq_pilot_dir : forall A O K : TSet,
  t_eq (t_alt2 A (t_alt2 (t_alt2 O (t_alt2 O (t_alt2 O K))) (t_alt2 O K))) (t_alt2 A (t_alt2 O K)).
Proof. intros A O K tr. unfold t_alt2. tauto. Qed.

Section LeafDir.
  Context {AL : AllocLim}.
  (* [comment removed for export] *)
  Hypothesis cannot_open_branch : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
      (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : AmbIn),
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 ->
    entry_stack_fits sp0 [a0s; dot_path] envv ->     (* [comment removed for export] *)
    main_entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0 ->
    open_err_branch sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open dot_path) fs0).

(* [comment removed for export] *)
Lemma ref_dir_path : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
    (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : AmbIn),
  valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; dot_path] envv ->
  (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0 -> valid_brk RSEGS brk ->
  realizes RSEGS (mkCfg (mkst regs0 (0x32574 : word) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputA [a0s; dot_path] envv fs0 stdin0))))
             (t_alt2 (t_die (msg_cannot_open dot_path) fs0) (t_opened_dir dot_path fs0)).
Proof.
  intros sp0 a0s envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits Htid ME Hbrk.
  set (K := t_die (msg_read_error dot_path) fs0).
  assert (AM : after_malloc_dir sp0 a0s envv rdraw tid mem0 fs0 stdin0 K).
  { apply (dir_read sp0 a0s envv rdraw tid mem0 fs0 stdin0 Hvsp Htid). intros R' M' VM' P. subst K.
    change fs0 with (m_fs (modelDir tid fs0 stdin0 VM')).
    apply (dir_tail sp0 a0s envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME R' M' (modelDir tid fs0 stdin0 VM') eq_refl eq_refl eq_refl P). }
  eapply rz_conseq; [ | apply teq_pilot_dir ].
  replace (0x32574 : word) with (Z_to_bv 64 0x32574) by (apply bv_eq; reflexivity).
  change (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputA [a0s; dot_path] envv fs0 stdin0)))
    with (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0).
  apply (dir_seg1 sp0 a0s envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME).
  - apply (cannot_open_branch sp0 a0s envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits ME).
  - unfold dir_seg2_kont. intros vals R M HL P0 P1 P2 P5 P6 P7 HR HK HA.
    change (modelD1 sp0 tid brk mbase fs0 stdin0) with (model1g sp0 tid brk mbase fs0 stdin0 FdDir).
    apply (oom_seg2 sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 Hvsp Hbrk ltac:(cbn; lia) FdDir
             (t_alt2 (t_die msg_oom fs0) K)
             (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K))
             vals R M
             (dir_brk sp0 a0s envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk K AM)
             (dir_mmap sp0 a0s envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk K AM)
             HL P0 P1 P2 P5 P6 P7 HR HK HA).
Qed.
End LeafDir.

End FPW_5.
