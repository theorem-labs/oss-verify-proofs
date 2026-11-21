(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (dir_seg2_kont and dir_seg1 written out from their encoded statements, dir_seg1 passing the entry draw to open_err_branch; the argv pointers taken from the entry draw; the path read also proved to end below TASK_SIZE; dir_seg2_kont's below-window premise and dir_seg1's proof of it use sp0 - 6144512, the floor of the stack the launch maps (was sp0 - 8388608)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemcpyLib Hoare.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_exit U_memcpy_base U_memcpy U_startup U_main_entry U_main_open_defs U_main_open.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_main_opendir () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.BB.SymRun.vals_ev"; "OSSVerify.KrLib.U.U_main_entry.p0"; "OSSVerify.KrLib.Spec.Spec.dot_path"; "OSSVerify.KrLib.U.U_main_entry.p1"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.regs_ok"; "OSSVerify.KrLib.U.U_main_open.ENV"; "OSSVerify.KrLib.U.U_main_open_defs.srB0"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.know_ok"; "OSSVerify.KrImg.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "OSSVerify.KrLib.U.U_main_open_defs.knA"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.PropExec.mkst"; "OSSVerify.KrLib.Lib.PropExec.fx0"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "DirFront.modelD1"; "OSSVerify.KrLib.Lib.Shape.TSet"; "OSSVerify.KrLib.U.U_main_open.open_err_branch"; "DirFront.dir_seg2_kont"; "OSSVerify.KrLib.U.U_main_open.model0"; "OSSVerify.KrLib.Lib.Shape.t_alt2"].


Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section DirFront.
  Context {AMB : Amb}.
  Context {LM : Lim}.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv tid rd regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.

  (* [comment removed for export] *)
  Definition fdsD1 : list (word * FdEntry) := fd_insert (fds0) (Z_to_bv 64 3) FdDir.
  Definition modelD1 : Model := model1g sp0 tid brk mbase fs0 stdin0 FdDir.

  (* [comment removed for export] *)
  Definition dir_seg2_kont (T : TSet) : Prop := (forall vals : (list word), (forall R : (bvmap (5)%N word), (forall M : (word -> (option byte)), (((length vals) = (38)%nat) -> (((vals_ev vals (0)%nat) = sp0) -> (((vals_ev vals (1)%nat) = (p0 a0s dot_path envv rd)) -> (((vals_ev vals (2)%nat) = (p1 a0s dot_path envv rd)) -> (((vals_ev vals (5)%nat) = tid) -> ((regs_ok (ENV a0s dot_path vals) srB0 R) -> ((know_ok RSEGS (ENV a0s dot_path vals) M knA) -> ((forall x : word, ((Z.le (bv_unsigned sp0) (bv_unsigned x)) -> ((M x) = (mem0 x)))) -> ((forall x : word, ((Z.lt (bv_unsigned x) (Z.sub (bv_unsigned sp0) 6144512%Z)) -> ((M x) = (mem0 x)))) -> (realizes RSEGS (mkCfg (mkst R (Z_to_bv (64)%N 0x4729c%Z) M (seg_rom RSEGS)) modelD1) T))))))))))))).

  #[using="Type"] Lemma dot_nonul : ~ In (Z_to_bv 8 0) dot_path.
  Proof. cbn. intros [E|[]]. apply (f_equal bv_unsigned) in E. vm_compute in E. lia. Qed.

  (* Was encoded (CDefT.buildp) over [open_err_branch]'s old arity; at the revision it reads the
     entry draw [rd], so the encoded term no longer typechecks (a build of this port said, at
     line 63, "Illegal application").
     Written out from its decode (cdeft_print.py), not re-encoded; the one change is [rd] in
     [open_err_branch]'s argument list, the section's own variable. *)
  #[using="rd Hva Hve Hvsp Htid ME"] Lemma dir_seg1 :
    forall KA T : TSet,
    @U_main_open.open_err_branch AMB LM sp0 a0s dot_path envv tid rd mem0 brk mbase fs0 stdin0 KA ->
    dir_seg2_kont T ->
    realizes RSEGS
      (mkCfg (@PropExec.mkst PropExec.fx0 regs0 (Z_to_bv 64 119372%Z) mem0 (PropExec.seg_rom RSEGS))
             (@U_main_open.model0 AMB LM sp0 a0s dot_path envv tid brk mbase fs0 stdin0))
      (t_alt2 KA T)
(* [comment removed for export] *).
  Proof.
    intros KA T HKA HT.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s dot_path envv tid rd regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s dot_path envv tid rd regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s dot_path envv tid rd regs0) with (ENV a0s dot_path (vals0 sp0 a0s dot_path envv tid rd regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s dot_path envv tid rd regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; apply vals0_length).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 a0s dot_path envv rd) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 a0s dot_path envv rd) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    ddestruct (main_str sp0 a0s dot_path envv tid rd regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    assert (ABOVE : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV a0s dot_path vals) mem0 _ 0%nat 0x7e000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    assert (BELOW : forall x : word, (bv_unsigned x < bv_unsigned sp0 - 6144512)%Z -> M x = mem0 x).
    { intros x Hx. rewrite EQM. apply (mem_denot_below (ENV a0s dot_path vals) mem0 _ 0%nat (-6144512));
        [vm_compute; reflexivity | lia | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 a0s dot_path envv rd) (length dot_path + 1) = Some (dot_path ++ [Z_to_bv 8 0])).
    { rewrite <- Sr. apply rdn_agree. intros j Hj. apply ABOVE.
      pose proof (u64_range (p1 a0s dot_path envv rd)). unfold p1 in *. rewrite u_small by lia. lia. }
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
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. split; [exact Sr'|].
      (* path_at's TASK_SIZE conjunct (read_cstr's access_okb) *)
      pose proof (main_str_top sp0 a0s dot_path envv tid rd regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as HTop.
      cbn [nth] in HTop. unfold p1, TASK_SIZE in *.
      assert (Hdl : length Uapi.dot_path = length dot_path) by reflexivity. lia.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x47298 + 4)%Z with 0x4729c%Z.
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
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x47298 + 4)%Z with 0x4729c%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) FdDir) (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0)) with modelD1.
      pose proof (regs_set_a0 (ENV a0s dot_path vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      eapply (HT vals); try eassumption.
  Qed.
End DirFront.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
