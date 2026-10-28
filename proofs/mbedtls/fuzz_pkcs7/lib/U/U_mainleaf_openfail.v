(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX Hoare BBFrame MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen Layout SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 MemcpyLib LibTail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_exit U_memcpy_base U_memcpy U_memchr U_strnlen U_startup U_startup_facts U_main_entry.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mainleaf_openfail_defs U_mainleaf_openfail_tail U_mainleaf_openfail_tail2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mainleaf_openfail () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.with_tid"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.BB.Amb.mkProcInputC"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.AgentSubmission.U.U_main_entry.p1"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.app"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "OpenFail.ENV"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sr_upd"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ridx"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knA"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "OpenFail.model0"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_cannot_open"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.AT_FDCWD"; "Stdlib.ZArith.BinInt.Z.ldiff"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.open_ignored_flags"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.regupd"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_addi"; "Corelib.Init.Peano.le"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.dot_path"; "LinuxProcessSemantics.LinuxProcessSem.Fs.fs_lookup"; "Corelib.Init.Datatypes.None"].


Lemma errno_ret_range : forall e, (1 <= e <= 4095)%Z ->
  (2 ^ 64 - 4095 <= bv_unsigned (errno_ret e))%Z.
Proof. intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  replace ((- e) mod 2 ^ 64)%Z with (2 ^ 64 - e)%Z; [lia|].
  apply Z.mod_unique with (q := (-1)%Z); lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma In_firstn : forall {A} (l : list A) n x, In x (firstn n l) -> In x l.
Proof.
  intros A l n x H. rewrite <- (firstn_skipn n l). apply in_app_iff. left. exact H.
Qed.

Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof.
  intros e He. unfold openat_errnos in He. cbn in He.
  unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.

Section OpenFail.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  (* [comment removed for export] *)
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rd regs0 mem0.

  (* [comment removed for export] *)
  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).
  Definition model0 : Model := ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "(0.Vtid,(1.(2.$3.)Vbrk,Vmbase,Vsp0,Vlim,(4.VAMB,(5.(6.(7.&8.))Va0s,(5.(6.(7.&8.))Vpath,(8.(6.(7.&8.)))))Venvv,Vfs0,Vstdin0,)))")
(* [comment removed for export] *).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  #[using="Type"] Lemma model0_halted : m_halted model0 = None.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_lazy : m_vm_lazy model0 = [].
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="a0s Hva"] Lemma path_noslash : path_has_slash path = false /\ path_eqb path dotdot_path = false.
  Proof.
    ddestruct Hva as (_ & _ & _ & _ & Hs). cbn [tl] in Hs. inversion Hs; subst. assumption.
  Qed.

  #[using="a0s Hva"] Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    ddestruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.
  #[using="a0s Hva"] Lemma path_len : (Z.of_nat (length path) <= 131071)%Z.
  Proof.
    ddestruct Hva as (_ & _ & Hl & _). inversion Hl as [|x l Hx Hl']; subst. inversion Hl'; subst. assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="AMB tid rd regs0 Hva Hve Hvsp ME SPlo SPhi"] Lemma path_facts : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "(9.(:.(;.(6.(7.&8.)))(<.$3.Vmem0,(=.Vsp0,Va0s,Vpath,Venvv,)(>.(?.(7.&8.)Vpath,)#1.))(10.(6.(7.&8.))(11.(7.&8.)Vpath,(5.(7.&8.)(12.&8.=)(8.(7.&8.))))))(9.(13.(14.&40.Vsp0,)(14.&40.(=.Vsp0,Va0s,Vpath,Venvv,)))(9.(13.(14.&40.(=.Vsp0,Va0s,Vpath,Venvv,))(15.(14.&40.Vsp0,)+2028;8.))(16.(6.(7.&8.))Lt8,(6.(7.&8.))(:.(;.(6.(7.&8.)))(<.$3.Vmem0,(12.&40.(15.(14.&40.(=.Vsp0,Va0s,Vpath,Venvv,))(17.(?.(7.&8.)Vpath,))))#8.)(10.(6.(7.&8.))R1.))))))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    ddestruct (main_str sp0 a0s path envv tid rd regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen. unfold p1.
    split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|].
    pose proof (lay_bsb_nw RPH sp0 rd [a0s; path] envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    ddestruct (read_word_stack RPH [] sp0 [a0s; path] envv 1 (length path) a_uid a_hwcap rd ltac:(cbn; lia) ltac:(cbn; lia) Hnw)
      as (t8 & Hl8 & Hr8).
    exists t8. rewrite w_add_nat in Hr8.
    pose proof (u64_range (cat_argv_ptr sp0 [a0s; path] envv 1)).
    rewrite (main_entry_rdn_above sp0 [a0s; path] envv tid rd regs0 mem0 ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv a_uid a_hwcap rd) as Hw. unfold wmem in Hw.
    apply Hw. (* [comment removed for export] *) exact Hr8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="rd regs0 Hva Hve Hvsp ME SPlo SPhi"] Theorem ref_open_fail_errno : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "Pe,$18.Pvals,(6.(7.&40.))PR,(19.&5.(7.&40.))PM,P,(7.&40.)(;.(7.&8.))P,(9.(13.+1.R4.)(13.R4.+???.))P,(:.$1:.(?.(7.&40.)R4.)#27.)P,(:.(7.&40.)(1;.R5.#0.)Vsp0,)P,(:.(7.&40.)(1;.R6.#26.)(1<.R7.))P,(:.(7.&40.)(1;.R7.#2.)(=.Vsp0,Va0s,Vpath,Venvv,))P,(1=.(1>.R8.)(1?.$20.(21.(22.&5.+:.$23.))(24.#26.))R7.)P,(25.$3.(1>.R9.)R7.$26.)P,Px,(7.&40.)P,(13.(14.&40.Vsp0,)(14.&40.R1.))(:.(;.(7.&8.))A1.R:.R2.A1.Vmem0,R2.)(27.$3.(28.(29.$2:.R:.(12.&40.+4729<.)R9.(2;.$3.))$2<.)(2=.(2>.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros e vals R M He HL P0 P38 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof path_len as HPl.
    ddestruct path_facts as (Sr & Slo & Shi & t8 & Ht8).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
    rewrite <- model0_fs.
    eapply (of_tail sp0 (blobs0 a0s path) model0 Hvsp model0_halted model0_lazy model0_fd2 path (p1 sp0 a0s path envv) t8 vals);
      try eassumption.
    - apply path_nonul.
    - rewrite P38. apply errno_ret_range. exact He.
    - lia.
    - (* [comment removed for export] *)
      exact (main_str_top sp0 a0s path envv tid rd regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)).
    - rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="rd Hva Hve Hvsp Htid ME SPlo SPhi"] Lemma of_blockA : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "PT,$2?.P,Pvals,(6.(7.&40.))PR,(19.&5.(7.&40.))PM,P,(7.&40.)(;.(7.&8.))P,(:.$1:.(?.(7.&40.)R3.)#26.)P,(:.(7.&40.)(1;.R4.#0.)Vsp0,)P,(:.(7.&40.)(1;.R5.#2.)(=.Vsp0,Va0s,Vpath,Venvv,))P,(1=.(1>.R6.)$20.R5.)P,(25.$3.(1>.R7.)R5.$26.)P,Px,(7.&40.)P,(13.(14.&40.Vsp0,)(14.&40.R1.))(:.(;.(7.&8.))A1.R8.R2.A1.Vmem0,R2.)(27.$3.(28.(29.$2:.R8.(12.&40.+47298.)R7.(2;.$3.))$2<.)R:.)(27.$3.(28.(29.$2:.Vregs0,(12.&40.+1=24<.)Vmem0,(2;.$3.))$2<.)R2.)")
(* [comment removed for export] *).
  Proof.
    intros T HA.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_regs_ok sp0 a0s path envv tid rd regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path envv tid rd regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path envv tid rd regs0) with (ENV (vals0 sp0 a0s path envv tid rd regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s path envv tid rd regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; apply vals0_length).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
    clearbody vals.
    pose proof model0_halted as Hh.
    run_blk_keep scr0 38%nat.
    apply (HA vals); try assumption.
    intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x7e000);
      [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma openat_regs : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "Pvals,(6.(7.&40.))PR,(19.&5.(7.&40.))P,(:.(7.&40.)(1;.R2.#2.)(=.Vsp0,Va0s,Vpath,Venvv,))P,(1=.(1>.R3.)$20.R2.)(9.(:.(7.&40.)(30.R3.(22.&5.+11.$23.))(12.&40.+38.))(9.(:.(7.&40.)(30.R3.(22.&5.+:.$23.))$31.)(9.(:.(7.&40.)(30.R3.(22.&5.+;.$23.))(=.Vsp0,Va0s,Vpath,Venvv,))(:.$18.(32.(14.&40.(30.R3.(22.&5.+<.$23.)))$33.)=))))")
(* [comment removed for export] *).
  Proof.
    intros vals R P2 HR. repeat split.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (11 : reg). cbn [edenot ev ENV]. exact P2.
    - regv HR (12 : reg). vm_compute. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="rd regs0 Hva Hve Hvsp ME SPlo SPhi"] Lemma after_openat_fail : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "Pe,$18.Pvals,(6.(7.&40.))PR,(19.&5.(7.&40.))PM,P,(7.&40.)(;.(7.&8.))P,(9.(13.+1.R4.)(13.R4.+???.))P,(:.$1:.(?.(7.&40.)R4.)#26.)P,(:.(7.&40.)(1;.R5.#0.)Vsp0,)P,(:.(7.&40.)(1;.R6.#2.)(=.Vsp0,Va0s,Vpath,Venvv,))P,(1=.(1>.R7.)$20.R6.)P,(25.$3.(1>.R8.)R6.$26.)P,Px,(7.&40.)P,(13.(14.&40.Vsp0,)(14.&40.R1.))(:.(;.(7.&8.))A1.R9.R2.A1.Vmem0,R2.)(27.$3.(28.(29.$2:.(34.R9.(22.&5.+:.$23.)(1<.R;.))(35.(12.&40.+47298.)+4.)R8.(2;.$3.))$2<.)(2=.(2>.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros e vals R M He HL P0 P2 HR HK Habove.
    rewrite v_addi_pc4 by lia. change (0x47298 + 4)%Z with 0x4729c%Z.
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals [errno_ret e] (blobs_ev (blobs0 a0s path)) sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    pose proof (env_app_know RSEGS vals [errno_ret e] (blobs_ev (blobs0 a0s path)) M knA ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
    eapply (ref_open_fail_errno e (vals ++ [errno_ret e])); try eassumption.
    - rewrite length_app, HL. reflexivity.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
    - rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
    - apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
      rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="rd Hva Hve Hvsp Htid ME SPlo SPhi"] Theorem ref_open_fail_toolong : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "P,(36.#1000.(?.(7.&8.)Vpath,))(27.$3.(28.(29.$2:.Vregs0,(12.&40.+1=24<.)Vmem0,(2;.$3.))$2<.)(2=.(2>.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros Hlong. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    ddestruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
    ddestruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x47298) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_toolong RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 (firstn 4096 path)).
    - rewrite A11. rewrite <- (firstn_app_l 4096 path [Z_to_bv 8 0]) at 1 || idtac.
      replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
        by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
      apply (rdn_firstn RSEGS M (length path + 1)); [| lia].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - intros Hin. apply path_nonul. eapply In_firstn. exact Hin.
    - apply (after_openat_fail ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rd Hva Hve Hvsp Htid ME SPlo SPhi"] Theorem ref_open_fail_empty : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "P,(:.(6.(7.&8.))Vpath,(8.(7.&8.)))(27.$3.(28.(29.$2:.Vregs0,(12.&40.+1=24<.)Vmem0,(2;.$3.))$2<.)(2=.(2>.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros Hnil. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    ddestruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
    ddestruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x47298) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_empty RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12).
    - split; [cbn; lia|]. split; [intros [] |]. rewrite A11.
      replace (length path + 1)%nat with 1%nat in Sr by (rewrite Hnil; reflexivity).
      replace (path ++ [Z_to_bv 8 0]) with [Z_to_bv 8 0] in Sr by (rewrite Hnil; reflexivity).
      cbn [length Nat.add app].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rd Hva Hve Hvsp Htid ME SPlo SPhi"] Theorem ref_open_fail_absent : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "P,(36.(?.(7.&8.)Vpath,)#???.)P,(37.(:.(6.(7.&8.))Vpath,(8.(7.&8.))))P,(37.(:.(6.(7.&8.))Vpath,$38.))P,(:.(;.(6.(7.&8.)))(39.Vfs0,Vpath,)(3:.(6.(7.&8.))))(27.$3.(28.(29.$2:.Vregs0,(12.&40.+1=24<.)Vmem0,(2;.$3.))$2<.)(2=.(2>.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros Hlen Hne Hnd Hfs. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    ddestruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
    ddestruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x47298) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_absent RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 path).
    - split; [exact Hlen|]. split; [apply path_nonul|]. rewrite A11.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - exact Hne.
    - exact Hnd.
    - exact (proj1 path_noslash).
    - exact (proj2 path_noslash).
    - exact Hfs.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rd Hva Hve Hvsp Htid ME SPlo SPhi"] Corollary ref_open_fail_toolong_w : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "P,(36.#1000.(?.(7.&8.)Vpath,))(27.$3.(28.(29.$2:.Vregs0,(22.&40.+1=24<.$23.)Vmem0,(2;.$3.))$2<.)(2=.(2>.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros H. replace (0x1d24c : word) with (Z_to_bv 64 0x1d24c) by (apply bv_eq; reflexivity).
    apply ref_open_fail_toolong. exact H.
  Qed.

  #[using="rd Hva Hve Hvsp Htid ME SPlo SPhi"] Corollary ref_open_fail_empty_w : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "P,(:.(6.(7.&8.))Vpath,(8.(7.&8.)))(27.$3.(28.(29.$2:.Vregs0,(22.&40.+1=24<.$23.)Vmem0,(2;.$3.))$2<.)(2=.(2>.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros H. replace (0x1d24c : word) with (Z_to_bv 64 0x1d24c) by (apply bv_eq; reflexivity).
    apply ref_open_fail_empty. exact H.
  Qed.

  #[using="rd Hva Hve Hvsp Htid ME SPlo SPhi"] Corollary ref_open_fail_absent_w : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail ()) "P,(36.(?.(7.&8.)Vpath,)#???.)P,(37.(:.(6.(7.&8.))Vpath,(8.(7.&8.))))P,(37.(:.(6.(7.&8.))Vpath,$38.))P,(:.(;.(6.(7.&8.)))(39.Vfs0,Vpath,)(3:.(6.(7.&8.))))(27.$3.(28.(29.$2:.Vregs0,(22.&40.+1=24<.$23.)Vmem0,(2;.$3.))$2<.)(2=.(2>.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros H1 H2 H3 H4. replace (0x1d24c : word) with (Z_to_bv 64 0x1d24c) by (apply bv_eq; reflexivity).
    apply ref_open_fail_absent; assumption.
  Qed.

End OpenFail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
