(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Bs0Usage.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed ME, model0_fd2, model0_fs and 4 more; added entry, inp; removed Hfits; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/BudgetWit/Src0UsageB.v, 22 lines within its lines 38-171. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Hoare Frame
  MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  Spec LibWritev RefNodes Bs0ExitBase Bs0Exit RefMemcpyLib Bs0MemcpyBase Bs0Memcpy Bs0Memchr Bs0Strnlen
  Bs0Startup Bs0StartupFacts Bs0MainEntry LibTail Bs0OpenFail_defs Bs0OpenFail_tail Bs0OpenFail_tail2.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import Bs0MainEntryN Bs0Usage_defs Bs0Usage_tail.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Import SX2.
Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import Bs0Usage.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.BudgetWit Require Import Bs0Usage_tailB SpinAlgB SymDriveXB.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1.
Context {fx : PropExec.FPState}.
Context {bmK : BMode}.
Variable scfg : SpuriousCfg.
Section Usage.
Context {RE : RunEnv}. Context {RO : ReaderOn}.
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
Variable lim : Z.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Variable inp : ProcInput.
Variable entry : word.
Hypothesis ME : main_entry inp mbase entry sp0 av envv uid hw rdraw tid regs0 mem0.
Hypothesis Hargc : length av <> 2%nat.
Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
Lemma model0_halted : m_halted (Bs0Usage.model0 sp0 tid brk mbase fs0 stdin0 lim inp) = None. Proof. reflexivity. Qed.
Lemma model0_lazy : m_vm_lazy (Bs0Usage.model0 sp0 tid brk mbase fs0 stdin0 lim inp) = []. Proof. reflexivity. Qed.
Lemma model0_fd2 : fd_lookup (m_fds (Bs0Usage.model0 sp0 tid brk mbase fs0 stdin0 lim inp)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.
Lemma model0_fs : m_fs (Bs0Usage.model0 sp0 tid brk mbase fs0 stdin0 lim inp) = fs0. Proof. reflexivity. Qed.
Lemma a0s_nonul : ~ In (Z_to_bv 8 0) (hd [] av).
  Proof.
    destruct Hva as ([H1 _] & _ & _ & Hn & _). destruct av as [|a0s rest]; [cbn in H1; lia|].
    inversion Hn; subst. assumption.
  Qed.
Lemma hd_nth : hd [] av = nth 0 av [].
  Proof. destruct av; reflexivity. Qed.
Lemma umemcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV (blobsN hw rdraw) vals) M u_logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE7.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE7_word. cbn [mem_denot u_logM1].
    unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
    f_equal; f_equal; lia.
  Qed.
Theorem ref_usage_b :
    SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs0 (Z_to_bv 64 0x33f54) mem0 (seg_rom RSEGS)) (Bs0Usage.model0 sp0 tid brk mbase fs0 stdin0 lim inp))
               (t_die (msg_usage (hd [] av)) fs0).
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
    assert (HR : regs_ok (EN sp0 av envv hw rdraw tid regs0 inp) sr_mainN regs0) by (eapply main_regs_okN; eassumption).
    assert (HK : know_ok RSEGS (EN sp0 av envv hw rdraw tid regs0 inp) mem0 kn_mainN) by (eapply main_know_okN; eassumption).
    assert (Hac : ev (EN sp0 av envv hw rdraw tid regs0 inp) 16 = len_word av) by (eapply evN_argc; eassumption).
    change (EN sp0 av envv hw rdraw tid regs0 inp) with (ENV (blobsN hw rdraw) (valsN sp0 av envv rdraw tid regs0 inp)) in HR, HK, Hac.
    set (vals := valsN sp0 av envv rdraw tid regs0 inp) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold valsN; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0N av envv rdraw inp) by reflexivity.
    cbn [ev ENV] in Hac.
    edestruct (main_strN sp0 av envv uid hw rdraw tid regs0 mem0) as (Sr & Slo & Shi & Slen & t8 & Ht8); try eassumption.
    1:{ instantiate (1 := 0%nat). lia. }
    assert (Sfit : (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) + Z.of_nat (length (nth 0 av [])) + 9 <= 0x800000000000)%Z)
      by (eapply (main_strN_fits sp0 av envv uid hw rdraw tid regs0 mem0); try eassumption; lia).
    rewrite <- hd_nth in Sr, Slen, Ht8, Sfit. set (a0s := hd [] av) in *.
    pose proof (u64_range (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0)) as Hppr.
    clearbody vals.
    pose proof model0_halted as Hh.
    (* [comment removed for export] *)
    run_blk_keep_b u_scrA 38%nat.
    { unfold sc_denot. cbn [branch_taken edenot ev ENV]. rewrite Hac.
      unfold bv_eqb. unfold len_word. rewrite (u64_lit (Z.of_nat (length av))) by (pose proof (valid_argv_len av Hva); lia). change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
      apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    assert (Habove : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV (blobsN hw rdraw) vals) mem0 _ 0%nat 0xea000);
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
    lazymatch goal with |- SpinAlgB.rzb _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x9f14c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x11011) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x11011) 7 _ (seg_rom RSEGS) MC Rc (0x9f14c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 695960) with (0xa9e98 : word) by (apply bv_eq; reflexivity).
    eapply SpinAlgB.rzb_msteps; [exact Hh | exact model0_lazy | exact Hms |]. clear Hms.
    replace (0x9f14c : word) with (Z_to_bv 64 0x9f14c) by (apply bv_eq; reflexivity).
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
    assert (Q1 : vals_ev vals1 1 = p0N av envv rdraw inp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev (blobsN hw rdraw))) with (ENV (blobsN hw rdraw) vals1) in HR, HK.
    rewrite <- model0_fs.
    eapply (Bs0Usage_tailB.us_tail_b scfg sp0 (blobsN hw rdraw) (Bs0Usage.model0 sp0 tid brk mbase fs0 stdin0 lim inp) Hvsp model0_halted model0_lazy model0_fd2 ltac:(rdr) a0s (p0N av envv rdraw inp) t8 vals1); try eassumption.
    - apply a0s_nonul.
    - unfold p0N. lia.
    - unfold p0N. lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.
Corollary ref_usage_w_b :
    SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs0 (0x33f54 : word) mem0 (seg_rom RSEGS)) (Bs0Usage.model0 sp0 tid brk mbase fs0 stdin0 lim inp))
               (t_die (msg_usage (hd [] av)) fs0).
  Proof.
    replace (0x33f54 : word) with (Z_to_bv 64 0x33f54) by (apply bv_eq; reflexivity). apply ref_usage_b.
  Qed.
End Usage.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
