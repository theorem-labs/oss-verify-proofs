(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Hoare Frame
  MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  Spec LibWritev RefNodes. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0ExitBase_u Bs0Exit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.musl Require Import Bs0MemcpyBase_u Bs0Memcpy_u Bs0Memchr_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0Strnlen_u
  Bs0Startup_u Bs0StartupFacts_u Bs0MainEntry_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibTail. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0OpenFail_defs_u Bs0OpenFail_tail_u Bs0OpenFail_tail2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0MainEntryN_u Bs0Usage_defs_u Bs0Usage_tail_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.


Section Usage.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
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
  Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hfits : entry_stack_fits sp0 av envv.   (* [comment removed for export] *)
  Hypothesis Hargc : length av <> 2%nat.

  Definition model0 : Model :=
    mkModelE fds_init (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp0) stdin0 fs0 None (Some tid) None.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma model0_halted : m_halted model0 = None. Proof. reflexivity. Qed.
  Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
  Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.
  Lemma model0_fs : m_fs model0 = fs0. Proof. reflexivity. Qed.

  Lemma a0s_nonul : ~ In (Z_to_bv 8 0) (hd [] av).
  Proof.
    destruct Hva as ([H1 _] & _ & _ & Hn & _). destruct av as [|a0s rest]; [cbn in H1; lia|].
    inversion Hn; subst. assumption.
  Qed.

  Lemma hd_nth : hd [] av = nth 0 av [].
  Proof. destruct av; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma umemcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV (blobsN hw rdraw) vals) M u_logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE7.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE7_word. cbn [mem_denot u_logM1].
    unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
    f_equal; f_equal; lia.
  Qed.

  Lemma pre7_len_w : length (word_to_le_bytes 7 (Z_to_bv 64 9071406455288693)) = 7%nat.
  Proof. apply length_N_to_le_bytes. Qed.

  Theorem ref_usage :
    srealizes RSEGS scfg (mkCfg (mkst regs0 (Z_to_bv 64 0x3427c) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_usage (hd [] av)) fs0).
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
    assert (HR : regs_ok (EN sp0 av envv hw rdraw tid regs0) sr_mainN regs0) by (eapply main_regs_okN; eassumption).
    assert (HK : know_ok RSEGS (EN sp0 av envv hw rdraw tid regs0) mem0 kn_mainN) by (eapply main_know_okN; eassumption).
    assert (Hac : ev (EN sp0 av envv hw rdraw tid regs0) 16 = argcN av) by (eapply evN_argc; eassumption).
    change (EN sp0 av envv hw rdraw tid regs0) with (ENV (blobsN hw rdraw) (valsN sp0 av envv tid regs0)) in HR, HK, Hac.
    set (vals := valsN sp0 av envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold valsN; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0N sp0 av envv) by reflexivity.
    cbn [ev ENV] in Hac.
    edestruct (main_strN sp0 av envv uid hw rdraw tid regs0 mem0) as (Sr & Slo & Shi & Slen & t8 & Ht8); try eassumption.
    1:{ instantiate (1 := 0%nat). lia. }
    pose proof (main_strN_fits sp0 av envv uid hw rdraw Hva Hve Hvsp Hfits 0%nat ltac:(lia)) as Sfit.
    rewrite <- hd_nth in Sr, Slen, Ht8, Sfit. set (a0s := hd [] av) in *.
    pose proof (u64_range (cat_argv_ptr sp0 av envv 0)) as Hppr.
    clearbody vals.
    pose proof model0_halted as Hh.
    (* [comment removed for export] *)
    run_blk_keep u_scrA 38%nat.
    { unfold sc_denot. cbn [branch_taken edenot ev ENV]. rewrite Hac.
      unfold bv_eqb. rewrite (u_argcN av Hva). change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
      apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    assert (Habove : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV (blobsN hw rdraw) vals) mem0 _ 0%nat 0xeb000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    clear EQM.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x11011) 7 = Some PRE7).
    { rewrite (kimg_rdn RSEGS (ENV (blobsN hw rdraw) vals) _ u_knA ltac:(let i := kidx u_knA (is_kimg_cov 0x11011 7) in exact i)
                 _ _ 0x11011 7 HK eq_refl) by (cbn; lia). apply pre7_img. }
    assert (Hdst : store_ok RSEGS M dst 7 = true).
    { pose proof (kwr_store_ok RSEGS (ENV (blobsN hw rdraw) vals) _ u_knA ltac:(let i := kidx u_knA (is_kwr_cov (EVar 0) (-560) 7) in exact i)
                    _ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x11011) 7 PRE7).
    { constructor; subst dst; rewrite ?u_small by lia; rewrite ?PRE7_len; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0xa0734 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x11011) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x11011) 7 _ (seg_rom RSEGS) MC Rc (0xa0734 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 701568) with (0xab480 : word) by (apply bv_eq; reflexivity).
    eapply srz_msteps; [exact Hh | exact model0_lazy | exact Hms |]. clear Hms.
    replace (0xa0734 : word) with (Z_to_bv 64 0xa0734) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev (blobsN hw rdraw)) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    assert (HK2 : know_ok RSEGS (ENV (blobsN hw rdraw) vals) (wbytes M dst PRE7) u_knB0).
    { subst dst. rewrite <- (umemcpy1_denot vals M P0).
      eapply (carry_after RSEGS (ENV (blobsN hw rdraw) vals) M u_logM1 u_knA [] u_knB0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat u_logM1]. split; [lia|]. split; [|exact I].
      apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev (blobsN hw rdraw)) (wbytes M dst PRE7) u_knB0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 70%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q1 : vals_ev vals1 1 = p0N sp0 av envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev (blobsN hw rdraw))) with (ENV (blobsN hw rdraw) vals1) in HR, HK.
    rewrite <- model0_fs.
    eapply (us_tail scfg sp0 (blobsN hw rdraw) model0 Hvsp model0_halted model0_lazy model0_fd2 a0s (p0N sp0 av envv) t8 vals1); try eassumption.
    - apply a0s_nonul.
    - unfold p0N. lia.
    - unfold p0N. lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  Corollary ref_usage_w :
    srealizes RSEGS scfg (mkCfg (mkst regs0 (0x3427c : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_usage (hd [] av)) fs0).
  Proof.
    replace (0x3427c : word) with (Z_to_bv 64 0x3427c) by (apply bv_eq; reflexivity). apply ref_usage.
  Qed.

End Usage.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
