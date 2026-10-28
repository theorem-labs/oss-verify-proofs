(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibTail
  Spec LibWritev RefNodes RefMemcpyLib RefReadLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0Startup_u Bs0MainEntry_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import Hoare MemSplit.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0OpenFail_u Bs0ReadErr_defs_u Bs0ReadErr_tail_u Bs0ReadErr_u.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0Drv_defs_u Bs0DrvLib_u Bs0DrvA_u Bs0DrvG_defs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Local Ltac lia := first [ solve [ try (match goal with H : (length _ <= S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))))))))))))))))))))))%nat |- _ => clear dependent H end); Lia.lia ] | Lia.lia ].

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Definition STOPS_D : list Z := (0x344a8 :: STOPS)%Z.

(* [comment removed for export] *)
#[using="Type"] Lemma store_ok_of_defined_h : forall M (a : Z) (m : nat),
  (0 <= a)%Z -> (a + Z.of_nat m <= 2 ^ 64)%Z -> (forall i, (0 <= i < Z.of_nat m)%Z -> M (Z_to_bv 64 (a + i)) <> None) ->
  store_ok RSEGS M (Z_to_bv 64 a) m = true.
Proof.
  intros M a m Ha Ham Hdef. destruct m as [|m']; [reflexivity|].
  apply store_ok_of_all; [rewrite u_small by lia; lia|].
  intros x Hx. rewrite u_small in Hx by lia. unfold wview.
  specialize (Hdef (bv_unsigned x - a)%Z ltac:(lia)). replace (a + (bv_unsigned x - a))%Z with (bv_unsigned x) in Hdef by lia.
  rewrite Z_to_bv_bv_unsigned in Hdef. destruct (M x); [discriminate | exfalso; apply Hdef; reflexivity].
Qed.

End FPX_1.

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Tactic Notation "run_blockD_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_D scr NX true.

Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.
Section DrvH.
  Context {RE : RunEnv}.
  Variable L : heap_layout.
  Variable HI : heap_iface.
  Hypothesis HIok : heap_iface_ok L scfg HI.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable VM0 : VmMaps.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable cr0 : credit.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
  Hypothesis Hfs : sc_fs scfg = true.
  Hypothesis Hpd : path = dot_path.
  Hypothesis DL : drv_layout L sp0.
  Hypothesis HH0 : hi_heap HI [] cr0 mem0 VM0.
  Hypothesis Hcr0 : credit_ok L cr0 65536.

  Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  (* [comment removed for export] *)
  Let ENVd (vals : list word) : env := ENV a0s path hw rdraw [] vals.
  Let model0 : Model := model0 tid VM0 fs0 stdin0.
  (* [comment removed for export] *)
  Definition model1d (VM : VmMaps) : Model := mkModelE (fd_insert fds0 (Z_to_bv 64 3) FdDir) VM stdin0 fs0 None (Some tid) None.
  #[using="Type"] Lemma m1d_but : forall VM m', model_but_vm (model1d VM) m' -> m' = model1d (m_vmmaps m').
  Proof. intros VM m' H. exact H. Qed.

  Ltac norm_srget := repeat match goal with |- context [sr_get ?sr ?r] =>
                      let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end.
  (* [comment removed for export] *)
  Ltac kimg_clear HK lo hi :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let H := fresh "Hki" in
      pose proof (know_nth segs E M kn ltac:(let i := kidx kn (is_kimg_cov lo (hi - lo)) in exact i) _ HK eq_refl) as H;
      cbn [kentry_ok] in H; intros i Hi; apply (proj2 (proj2 H)); lia
    end.
  Ltac kimg_clear3 HK lo m1 m2 hi :=      (* [comment removed for export] *)
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let H1 := fresh "Hki" in let H2 := fresh "Hki" in let H3 := fresh "Hki" in
      pose proof (know_nth segs E M kn ltac:(let i := kidx kn (is_kimg_cov lo (m1 - lo)) in exact i) _ HK eq_refl) as H1;
      pose proof (know_nth segs E M kn ltac:(let i := kidx kn (is_kimg_cov m1 (m2 - m1)) in exact i) _ HK eq_refl) as H2;
      pose proof (know_nth segs E M kn ltac:(let i := kidx kn (is_kimg_cov m2 (hi - m2)) in exact i) _ HK eq_refl) as H3;
      cbn [kentry_ok] in H1, H2, H3; intros i Hi;
      destruct (Z_lt_ge_dec i m1); [apply (proj2 (proj2 H1)); lia|]; destruct (Z_lt_ge_dec i m2); [apply (proj2 (proj2 H2)); lia | apply (proj2 (proj2 H3)); lia]
    end.

  #[using="L HI HIok uid cr0 Hva Hve Hvsp Htid ME Hfits Hfs Hpd DL HH0 Hcr0 Hsp Hal ENVd"] Theorem drv_dir : forall KA,
    open_err_k scfg sp0 a0s path envv hw rdraw tid mem0 VM0 fs0 stdin0 KA ->
    srealizes RSEGS scfg (mkCfg (mkst regs0 (Z_to_bv 64 0x3427c) mem0 (seg_rom RSEGS)) model0)
              (t_alt2 KA (t_die (msg_read_error dot_path) fs0)).
  Proof.
    intros KA HKA.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    assert (Hplen : (length path <= 4095)%nat) by (rewrite Hpd; cbn; lia).
    pose proof (main_regs_ok_d sp0 a0s path envv uid hw rdraw tid regs0 mem0 [] Hvsp Htid ME) as HR.
    assert (HK : know_ok RSEGS (ENV a0s path hw rdraw [] (vals0 sp0 a0s path envv tid regs0)) mem0 (kn_d0 ++ [KImg 0xea3c8 0xeb000; KImg 0xb8501 0xc9ef0])).
    { apply Forall_app. split; [apply (main_know_ok_d sp0 a0s path envv uid hw rdraw tid regs0 mem0 [] Hva Hve Hvsp Htid ME)
                              | apply (main_kimg_alloc sp0 a0s path envv uid hw rdraw tid regs0 mem0 [] Hva Hve Hvsp Htid ME)]. }
    set (vals := vals0 sp0 a0s path envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 sp0 a0s path envv) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
    assert (P3 : vals_ev vals 3 = auxvp sp0 a0s path envv) by reflexivity.
    assert (P4 : vals_ev vals 4 = rnd sp0 a0s path envv) by reflexivity.
    assert (P5 : vals_ev vals 5 = tid) by reflexivity.
    destruct (path_facts sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME Hfits) as (Sr & Slo & Shi & Sfit & t8 & Ht8).
    assert (HA0 : above_sp0 sp0 mem0 mem0) by (intros a Ha; reflexivity).
    change (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [[]]))) with (ENVd vals) in HR, HK.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    assert (HH1 : hi_heap HI [] cr0 M VM0).
    { rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals _ []); [exact P0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH0]. }
    assert (HA : above_sp0 sp0 mem0 M).
    { rewrite EQM. apply (above_sp0_block sp0 a0s path hw rdraw mem0 [] Hvsp Hplen vals); [exact P0 | vm_compute; reflexivity | exact HA0]. }
    assert (Sr' : rdn RSEGS M (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite <- Sr. apply rdn_agree. intros j Hj. pose proof (u64_range (p1 sp0 a0s path envv)).
      apply HA. rewrite Hpd in Hj. cbn in Hj. rewrite u_small; lia. }
    clear EQM.
    (* [comment removed for export] *)
    eapply (rz_openat_dot RSEGS scfg _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17%bv : reg). reflexivity.
    - regv HR (10%bv : reg). apply bv_eq. reflexivity.
    - regv HR (12%bv : reg). vm_compute. reflexivity.
    - exact Hfs.
    - unfold model0. rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - split; [cbn; lia|]. split; [cbn; intros [E0|[]]; apply (f_equal bv_unsigned) in E0; vm_compute in E0; lia|].
      regv HR (11%bv : reg). cbn [edenot ev ENVd ENV]. rewrite P2. rewrite Hpd in Sr'. exact Sr'.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0xac428 + 4)%Z with 0xac42c%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path hw rdraw ++ [[]]))) with (ENVd (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])).
      + apply openat_errnos_range. exact He.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + eapply regs_ok_bagree; [apply (ENV_agree_r a0s path hw rdraw []) | vm_compute; reflexivity |].
        apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENVd ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + eapply know_ok_bagree; [apply (ENV_agree_r a0s path hw rdraw []) | vm_compute; reflexivity |].
        eapply ksubl_sound; [exact HK2 | vm_compute; reflexivity].
      + exact HA.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0xac428 + 4)%Z with 0xac42c%Z.
      unfold model0. rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) FdDir) (Bs0DrvA_u.model0 tid VM0 fs0 stdin0)) with (model1d VM0).
      pose proof (regs_set_a0 (ENVd vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2. clear HR. rename HR2 into HR.
      (* [comment removed for export] *)
      run_block_keep scr0 38%nat.
      cbn [mem_denot] in EQM. subst M0.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
      eapply (malloc_site scfg L HI HIok sp0 Hsp' Hal' DL vals _ _ kn _ _ (model1d VM0) [] cr0 65536 (-128) [] [] 0x342d0
                (t_die (msg_read_error dot_path) fs0));
        [ exact HR | exact HK
        | rewrite HL; vm_compute; reflexivity
        | rewrite HL; vm_compute; reflexivity
        | rewrite HL; lia
        | exact P0
        | apply (hiv_facts sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hplen); assumption
        | vm_compute; reflexivity
        | regv HR (2%bv : reg); cbn [edenot ev ENVd ENV]; rewrite P0; apply alu_add_w_lit
        | lia
        | reflexivity
        | regv HR (10%bv : reg); reflexivity
        | lia
        | exact Hcr0
        | regv HR (4%bv : reg); reflexivity
        | regv HR (1%bv : reg); reflexivity
        | lia | reflexivity
        | exact HH1
        | reflexivity | reflexivity | reflexivity
        | intros i nb Hf; discriminate
        | intros v b Hf; discriminate
        | apply t_emit_has_nil
        | ]
      end.
      intros R' M' model' A vals' E' HL' HA' HR' HK' HH' HBUT HBR HAP HAB HBLK HIMG. subst vals' E'.
      rewrite (m1d_but VM0 model' HBUT). rewrite (m1d_but VM0 model' HBUT) in HH'. cbn [m_vmmaps model1d mkModelE] in HH'.
      set (VM1 := m_vmmaps model') in *. clearbody VM1.
      set (vals1 := vals ++ junk_vals R') in *.
      change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path hw rdraw ++ [[]]))) with (ENVd vals1) in HR', HK'.
      rewrite HL in HL', HA', HR', HK'. change (38 + 10)%nat with 48%nat in HA'.
      lazymatch type of HK' with know_ok ?segs ?E ?Mx ?kn =>
        assert (HKC : know_ok segs E Mx knC0) by (eapply ksubl_sound; [exact HK' | vm_compute; reflexivity]); clear HK'; rename HKC into HK' end.
      change (sr_after_call_j _ _ 38) with srC0 in HR'.
      assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q2 : vals_ev vals1 2 = p1 sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (Q3 : vals_ev vals1 3 = auxvp sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
      assert (Q4 : vals_ev vals1 4 = rnd sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
      assert (Q5 : vals_ev vals1 5 = tid) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (HA1 : above_sp0 sp0 mem0 M') by (intros a Ha; rewrite (HAB a Ha); apply HA; exact Ha).
      pose proof (hz_of_block_range L sp0 DL _ _ HBR) as (B1 & B2 & B4).
      clear HR HK HH1 HA. rename HR' into HR. rename HK' into HK.
      (* [comment removed for export] *)
      run_block_keep scr0 70%nat.
      assert (HA2 : above_sp0 sp0 mem0 M0).
      { rewrite EQM. apply (above_sp0_block sp0 a0s path hw rdraw mem0 [] Hvsp Hplen vals1); [exact Q0 | vm_compute; reflexivity | exact HA1]. }
      assert (HH2 : hi_heap HI [(A, 65536%Z)] (debit L cr0 65536) M0 VM1).
      { rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals1 _ []); [exact Q0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH']. }
      destruct (hio_wf L scfg HI HIok _ _ _ _ HH2) as [WF _].
      destruct (WF (A, 65536%Z) ltac:(left; reflexivity)) as (_ & HDEF & _). cbn [fst snd] in HDEF.
      clear EQM.
      (* [comment removed for export] *)
      eapply (rz_read_dir_cnt RSEGS scfg _ _ M0 (model1d VM1) ECALLW (Z_to_bv 64 3) 65536); try apply is_ecall_ECALLW.
      + vm_compute. reflexivity.
      + reflexivity.
      + reflexivity.
      + regv HR (17%bv : reg). reflexivity.
      + regv HR (10%bv : reg). reflexivity.
      + rewrite u_small by lia. lia.
      + reflexivity.
      + regv HR (12%bv : reg). reflexivity.
      + lia.
      + regv HR (11%bv : reg). cbn [edenot ev ENVd ENV]. rewrite u_small by lia. unfold TASK_SIZE. lia.
      + rewrite v_addi_pc4 by lia. change (0xac428 + 4)%Z with 0xac42c%Z.
        replace (errno_ret EISDIR) with (Z_to_bv 64 18446744073709551595) by (apply bv_eq; reflexivity).
        pose proof (regs_set_a0 (ENVd vals1) _ _ (Z_to_bv 64 18446744073709551595) (ELit 18446744073709551595) HR eq_refl) as HR2.
        clear HR. rename HR2 into HR.
        (* [comment removed for export] *)
        run_blockD_keep scr0 70%nat.
        assert (HA3 : above_sp0 sp0 mem0 M1).
        { rewrite EQM. apply (above_sp0_block sp0 a0s path hw rdraw mem0 [] Hvsp Hplen vals1); [exact Q0 | vm_compute; reflexivity | exact HA2]. }
        clear EQM.
        change fs0 with (m_fs (model1d VM1)).
        pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
        replace (length path + 1)%nat with 2%nat in Sr by (rewrite Hpd; reflexivity).
        replace (path ++ [Z_to_bv 8 0]) with [Z_to_bv 8 46; Z_to_bv 8 0] in Sr by (rewrite Hpd; reflexivity).
        replace (Z.of_nat (length path)) with 1%Z in Ht8 by (rewrite Hpd; reflexivity).
        unshelve (eapply (ref_read_error_dot scfg sp0 (blobs0 a0s path hw rdraw ++ [[]]) (model1d VM1) Hvsp eq_refl eq_refl eq_refl
                  (p1 sp0 a0s path envv) (bv_unsigned tid) _ M1 _ _ _ _ _ _ _ Htid _ _ _ _ Slo t8)).
        all: lazymatch goal with
             | |- getr _ _ = _ =>
                 rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVd ENV]; rewrite ?Q0, ?Q2;
                 first [ reflexivity | rewrite alu_add_w_lit; f_equal; lia ]
             | |- stack_writable _ _ =>
                 intros d m Hd Hm;
                 lazymatch type of HK with know_ok ?segs ?E _ ?kn =>
                   pose proof (kwr_store_ok segs E M1 kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
                                 _ _ _ (-8388608 + d) m HK eq_refl ltac:(lia) ltac:(lia)) as W;
                   unfold adenot, v_addi in W; cbn [a_base a_off edenot ev ENVd ENV] in W; rewrite Q0 in W
                 end;
                 replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia; exact W
             | |- Forall _ re_ivs =>
                 unfold re_ivs; repeat (apply Forall_cons; [cbn [fst snd]; unfold img_clear|]); [..|apply Forall_nil];
                 first [ kimg_clear HK 0x10000%Z 0xb8500%Z | kimg_clear HK 0xb8501%Z 0xb8549%Z | kimg_clear HK 0xc8549%Z 0xc9ef0%Z | kimg_clear HK 0xe9fc8%Z 0xe9fe8%Z
                       | kimg_clear HK 0xc9f24%Z 0xc9f70%Z | kimg_clear HK 0xc9f78%Z 0xc9f90%Z | kimg_clear HK 0xc9f98%Z 0xc9fb0%Z
                       | kimg_clear HK 0xc9fc0%Z 0xc9fd0%Z | kimg_clear HK 0xc9fd8%Z 0xe9fc8%Z | kimg_clear3 HK 0xea000%Z 0xea008%Z 0xea228%Z 0xea230%Z | kimg_clear HK 0xea238%Z 0xea240%Z
                       | kimg_clear HK 0xea251%Z 0xea258%Z | kimg_clear HK 0xea260%Z 0xea268%Z | kimg_clear HK 0xea278%Z 0xea280%Z
                       | kimg_clear HK 0xea288%Z 0xea2b8%Z | kimg_clear HK 0xea770%Z 0xeb000%Z ]
             | |- cell _ 0xc9f18 4 _ =>
                 unfold cell; krd HK 0xc9f18%Z 4%nat Htc; rewrite Htc; cbn [ev ENVd ENV]; rewrite Q5;
                 rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
                 rewrite Z_to_bv_bv_unsigned; reflexivity
             | |- cell _ _ _ _ => unfold cell; krd_solve HK
             | |- forall i, _ -> ?Mx _ = Some _ =>
                 lazymatch type of HK with know_ok ?segs ?E _ ?kn =>
                   pose proof (know_nth segs E Mx kn ltac:(let i := kidx kn (kentry_eqb (KBlob (SA (ELit 0) 0xea230) (ELit 8) 2)) in exact i)
                                 _ HK eq_refl) as KB;
                   cbn [kentry_ok] in KB; destruct KB as (_ & _ & KB); unfold estart, elenZ in KB;
                   cbn [a_base a_off edenot eb ENVd ENV] in KB; rewrite ?(u_small 8), ?(u_small 0) in KB by lia;
                   intros i Hi; replace (959024 + i)%Z with (0 + 959024 + i)%Z by lia; apply KB; lia
                 end
             | |- length _ = 8%nat => cbn; reflexivity
             | |- rdn _ _ _ 2 = _ =>
                 rewrite <- Sr; apply rdn_agree; intros j Hj; apply HA3; rewrite !u_small by lia; lia
             | |- rdn _ _ _ 8 = _ =>
                 rewrite <- Ht8; apply rdn_agree; intros j Hj; apply HA3; rewrite (u_small (bv_unsigned (p1 sp0 a0s path envv) + 1)) by lia;
                 rewrite u_small by lia; lia
             | |- _ => lia
             end.
  Qed.

End DrvH.
End FPX_2.
