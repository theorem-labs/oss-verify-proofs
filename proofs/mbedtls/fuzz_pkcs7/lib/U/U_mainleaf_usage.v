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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_exit U_memcpy_base U_memcpy U_memchr U_strnlen U_startup U_startup_facts U_main_entry U_mainleaf_openfail_defs U_mainleaf_openfail_tail U_mainleaf_openfail_tail2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_main_entryN U_mainleaf_usage_defs U_mainleaf_usage_tail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mainleaf_usage () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.with_tid"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.BB.Amb.mkProcInputC"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.mem_denot"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_usage_tail.ENV"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_usage_defs.u_logM1"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_usage_tail.PRE7"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Usage.model0"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_usage"; "Stdlib.Lists.List.hd"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"].


Section Usage.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
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
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid rd regs0 mem0.
  Hypothesis Hargc : length av <> 2%nat.

  Definition model0 : Model := ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_usage ()) "(0.Vtid,(1.(2.$3.)Vbrk,Vmbase,Vsp0,Vlim,(4.VAMB,Vav,Venvv,Vfs0,Vstdin0,)))")
(* [comment removed for export] *).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  #[using="Type"] Lemma model0_halted : m_halted model0 = None. Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_fs : m_fs model0 = fs0. Proof. reflexivity. Qed.

  #[using="AMB sp0 envv tid rd regs0 mem0 Hva ME Hargc"] Lemma a0s_nonul : ~ In (Z_to_bv 8 0) (hd [] av).
  Proof.
    ddestruct Hva as ([H1 _] & _ & _ & Hn & _). destruct av as [|a0s rest]; [cbn in H1; lia|].
    inversion Hn; subst. assumption.
  Qed.

  #[using="AMB sp0 envv tid rd regs0 mem0 Hva ME Hargc"] Lemma hd_nth : hd [] av = nth 0 av [].
  Proof. destruct av; reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma umemcpy1_denot : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_usage ()) "Pvals,(5.(6.&40.))PM,P,(6.&40.)(7.(6.&8.))P,(8.(6.&40.)(9.R2.#0.)Vsp0,)(8.P,(6.&40.)(7.(6.&8.))(:.(;.R3.)R2.$<.)(=.R2.(>.&40.(?.(10.&40.Vsp0,)+230.))$11.))")
(* [comment removed for export] *).
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE7_word. cbn [mem_denot u_logM1].
    unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
    f_equal; f_equal; lia.
  Qed.

  
  #[using="rd Hva Hve Hvsp Htid ME Hargc SPlo SPhi"] Theorem ref_usage : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_usage ()) "(12.$3.(13.(14.$15.Vregs0,(>.&40.+1=24<.)Vmem0,(16.$3.))$17.)(18.(19.(1:.(5.(6.&8.))(1;.(6.&8.))Vav,))Vfs0,))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
    assert (HR : regs_ok (EN sp0 av envv tid rd regs0) sr_mainN regs0) by (eapply main_regs_okN; eassumption).
    assert (HK : know_ok RSEGS (EN sp0 av envv tid rd regs0) mem0 kn_mainN) by (eapply main_know_okN; eassumption).
    assert (Hac : ev (EN sp0 av envv tid rd regs0) 16 = argcN av) by (eapply evN_argc; eassumption).
    change (EN sp0 av envv tid rd regs0) with (ENV (valsN sp0 av envv tid rd regs0)) in HR, HK, Hac.
    set (vals := valsN sp0 av envv tid rd regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; apply valsN_length).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0N sp0 av envv) by reflexivity.
    cbn [ev ENV] in Hac.
    assert (STR := fun k Hk => main_strN sp0 av envv tid rd regs0 mem0 Hva Hve Hvsp ME k Hk) || idtac.
    edestruct (main_strN sp0 av envv tid rd regs0 mem0) as (Sr & Slo & Shi & Slen & t8 & Ht8); try eassumption.
    1:{ instantiate (1 := 0%nat). lia. }
    rewrite <- hd_nth in Sr, Slen, Ht8. set (a0s := hd [] av) in *.
    pose proof (u64_range (cat_argv_ptr sp0 av envv 0)) as Hppr.
    clearbody vals.
    pose proof model0_halted as Hh.
    (* [comment removed for export] *)
    run_blk_keep u_scrA 38%nat.
    { unfold sc_denot. cbn [branch_taken edenot ev ENV]. rewrite Hac.
      unfold bv_eqb. rewrite (u_argcN av Hva). change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
      apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    assert (Habove : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x7e000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    clear EQM.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x10499) 7 = Some PRE7).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kimg_cov 0x10499 7) in exact i)
                 _ _ 0x10499 7 HK eq_refl) by (cbn; lia). apply pre7_img. }
    assert (Hdst : store_ok RSEGS M dst 7 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kwr_cov (EVar 0) (-560) 7) in exact i)
                    _ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x10499) 7 PRE7).
    { constructor; subst dst; rewrite ?u_small by lia; rewrite ?PRE7_len; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10499) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x10499) 7 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 289344) with (0x46a40 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact model0_lazy | exact Hms |]. clear Hms.
    replace (0x41d64 : word) with (Z_to_bv 64 0x41d64) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev []) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M dst PRE7) u_knB0).
    { subst dst. rewrite <- (umemcpy1_denot vals M P0).
      eapply (carry_after RSEGS (ENV vals) M u_logM1 u_knA [] u_knB0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat u_logM1]. split; [lia|]. split; [|exact I].
      apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) (wbytes M dst PRE7) u_knB0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 70%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q1 : vals_ev vals1 1 = p0N sp0 av envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev [])) with (ENV vals1) in HR, HK.
    rewrite <- model0_fs.
    eapply (us_tail sp0 model0 Hvsp model0_halted model0_lazy model0_fd2 a0s (p0N sp0 av envv) t8 vals1); try eassumption.
    - apply a0s_nonul.
    - unfold p0N. lia.
    - (* [comment removed for export] *)
      unfold p0N. subst a0s. rewrite hd_nth. apply (main_strN_top sp0 av envv tid rd regs0 mem0 Hva Hve Hvsp ME 0%nat). lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  #[using="rd Hva Hve Hvsp Htid ME Hargc SPlo SPhi"] Corollary ref_usage_w : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_usage ()) "(12.$3.(13.(14.$15.Vregs0,(1<.&40.+1=24<.$1=.)Vmem0,(16.$3.))$17.)(18.(19.(1:.(5.(6.&8.))(1;.(6.&8.))Vav,))Vfs0,))")
(* [comment removed for export] *).
  Proof.
    replace (0x1d24c : word) with (Z_to_bv 64 0x1d24c) by (apply bv_eq; reflexivity). apply ref_usage.
  Qed.

End Usage.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
