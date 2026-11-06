(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)






From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefStartupDefs.   
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame LibStdioCall
  Spec LibWritev RefNodes RefExitBase RefStdioDefs RefExit RefMemcpyLib RefMemcpyBase RefMemcpy
  RefStartup RefMainEntry Hoare MemSplit.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefPilotOOM_defs RefLim.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).






Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.






Section FPW_1. Context {fx : PropExec.FPState}.



Section Pilot.
  Context {AL : AllocLim}.
  Variable sp0 : word.
  Variables a0s path : list byte.
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
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpns : path_has_slash path = false.   (* [comment removed for export] *)
  Hypothesis Hpnd : path_is_dirref path = false.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).

  (* [comment removed for export] *)
  Ltac usmall_off := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 (bv_unsigned ?x + ?k))] => rewrite (u_small (bv_unsigned x + k)) by lia end.

  (* [comment removed for export] *)
  Definition fds0 : list (word * FdEntry) :=
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
     (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  (* [comment removed for export] *)
  Definition model0 : Model :=
    with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputA [a0s; path] envv fs0 stdin0)).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition model1g (fd3 : FdEntry) : Model :=
    mkModelA (fds1g fd3) (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk LIM mbase sp0) stdin0 fs0 None (Some tid) None.
  Definition fds1 : list (word * FdEntry) := fds1g (FdFile path (Z_to_bv 64 0)).
  Definition model1 : Model := model1g (FdFile path (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

  #[using="Type"] Lemma model0_eq : model0 = mkModelA fds0 (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk LIM mbase sp0)
                                     stdin0 fs0 None (Some tid) None.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma m1_vmmaps : forall fd3, m_vmmaps (model1g fd3) = mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk LIM mbase sp0.
  Proof. intros. reflexivity. Qed.
  #[using="Type"] Lemma m1_fs : forall fd3, m_fs (model1g fd3) = fs0.
  Proof. intros. reflexivity. Qed.
  #[using="Type"] Lemma m1_fds : forall fd3, m_fds (model1g fd3) = fds1g fd3.
  Proof. intros. reflexivity. Qed.
  #[using="Type"] Lemma m0_fds : m_fds model0 = fds0.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma m0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.

  #[using="Type"] Lemma fds1_2 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Hvsp Hplen"] Lemma above_sp0_block : forall vals log M,
    vals_ev vals 0 = sp0 -> log_below_b 0 0xe6000 log = true -> above_sp0 M ->
    above_sp0 (mem_denot (ENV vals) M log).
  Proof.
    intros vals log M P0 Hb HA a Ha. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    rewrite (mem_denot_above (ENV vals) M log 0%nat 0xe6000 a Hb); [apply HA; exact Ha | | |];
      cbn [ev ENV]; rewrite ?P0; lia.
  Qed.

  #[using="Type"] Lemma alloc_fd_fds0 : alloc_fd fds0 = Z_to_bv 64 3.
  Proof. exact (alloc_fd_init _ _ _). Qed.
  #[using="Type"] Lemma fd_lookup_fds0_3 : fd_lookup fds0 (Z_to_bv 64 3) = None.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac refresh_above vals P0 HA :=
    lazymatch type of HA with above_sp0 ?Mo =>
      lazymatch goal with EQ : ?Mn = mem_denot _ Mo ?log |- _ =>
        let HA' := fresh "HA" in
        pose proof (above_sp0_block vals log Mo P0 ltac:(vm_compute; reflexivity) HA) as HA';
        rewrite <- EQ in HA'; clear HA EQ; rename HA' into HA
      end
    end.
  (* [comment removed for export] *)
  Ltac name_state R M :=
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into R; rename Mn into M end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma msg_oom_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10c42) 19 = Some msg_oom.
  Proof. vm_compute. reflexivity. Qed.

  #[using="Hvsp Hplen"] Lemma oom_seg4 : forall fd3 vals R M,
    length vals = 71%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x9a1f0) M (seg_rom RSEGS)) (model1g fd3)) (t_die msg_oom fs0).
  Proof.
    intros fd3 vals R M HL P0 HR HK.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    (* [comment removed for export] *)
    run_block scr0 71%nat.
    (* [comment removed for export] *)
    unfold t_die, W.
    apply (stdio_call_sound vals (blobs_ev (blobs0 a0s path)) srF knF R M (model1g fd3) resG [] msg_oom
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n srF knF) HL) resG_eq));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resG];
      change (Z.of_nat (length msg_oom)) with 19%Z; change (Z.of_nat (@length byte [])) with 0%Z.
    - cbn [edenot]. lia.
    - cbn [edenot]. lit_u. lia.   (* [comment removed for export] *)
    - cbn [edenot]. lia.
    - cbn [edenot]. lit_u. reflexivity.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
      usmall_off. lit_u. lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
      usmall_off. lit_u. lit_u. lia.
    - cbn [edenot]. lit_u. lit_u. lia.
    - reflexivity.
    - cbn [edenot]. change (length msg_oom) with 19%nat.
      rewrite (kimg_rdn RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kimg_cov 0x10c42 19) in exact i)
                 _ _ 0x10c42 19 HK eq_refl) by (cbn; lia).
      apply msg_oom_img.
    - apply fds1_2.
    - reflexivity.
    - reflexivity.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK R M. intros R M HR HK.
      change (sc_sr resG) with srG0 in HR. change (sc_kn resG) with knG0 in HK. change (sc_ret resG) with 0x9b8d4%Z.
      set (vals' := vals ++ junk_vals R) in *.
      assert (HL' : length vals' = 103%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals'. clear HL P0. rename HL' into HL. rename P0' into P0.
      change (Env (vals_ev vals') (blobs_ev (blobs0 a0s path))) with (ENV vals') in HR, HK.
      run_block scr0 103%nat.
      (* [comment removed for export] *)
      apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs (model1g fd3))))).
      2:{ rewrite m1_fs. apply exit_leaf_eq. lia. }
      apply ref_exit_Z.
      (* [comment removed for export] *)
      pose proof (know_nth RSEGS _ _ knG ltac:(let i := kidx knG (is_krange (EVar 5)) in exact i) _ HK eq_refl)
        as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
      exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0xc4918), (bv_unsigned (vals_ev vals' 5)),
             (Z_to_bv 64 0xe5100), (Z_to_bv 64 0).   (* [comment removed for export] *)
      split; [|split; [reflexivity|split; [reflexivity|]]].
      + constructor.
        * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
          rewrite P0. f_equal; lia.
        * regv HR (4 : reg). reflexivity.
        * regv HR (10 : reg). reflexivity.
        * rewrite u_small by lia. lia.
        * rewrite u_small by lia. lia.
        * rewrite u_small by lia.
          pose proof (kwr_store_ok RSEGS (ENV vals') _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                        _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
          unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
          replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
        * lit_u. lia.
        * lit_u. lia.
        * lia.
        * lit_u. change (805144 - 168)%Z with 0xc4870%Z.
          krd HK 0xc4870%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
          rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
          rewrite Z_to_bv_bv_unsigned. reflexivity.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.   (* [comment removed for export] *)
        * krd_solve HK.   (* [comment removed for export] *)
        * krd_solve HK.   (* [comment removed for export] *)
        * repeat split; krd_solve HK.
        * repeat split; krd_solve HK.
      + left. split; [reflexivity|].
        exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma rtop : reserved_top (segments_reserved RSEGS) = 0xe6000%Z.
  Proof. vm_compute. reflexivity. Qed.

  #[using="Hbrk"] Lemma brk_lo : (0xe6000 <= bv_unsigned brk)%Z.
  Proof. pose proof (proj1 Hbrk) as H. rewrite rtop in H. exact H. Qed.
  #[using="path Hbrk Hplen"] Lemma brk_hi : (bv_unsigned brk <= 0x800e6000)%Z.
  Proof. pose proof (proj1 (proj2 Hbrk)) as H. rewrite rtop, brk_aslr_max_val in H. cbn in H. lia. Qed.
  #[using="Hbrk"] Lemma brk_al : (bv_unsigned brk mod 4096 = 0)%Z.
  Proof. exact (proj2 (proj2 Hbrk)). Qed.

  (* [comment removed for export] *)
  #[using="Hbrk Hplen"] Lemma ugly_b_sem : forall vals, vals_ev vals 70 = brk ->
    edenot (ENV vals) ugly_b = edenot (ENV vals) b_expr.
  Proof.
    intros vals P70. cbn [edenot ugly_b b_expr ev ENV]. rewrite P70.
    rewrite alu_add, alu_and, m_mul. unfold v_add, v_and, v_mul.
    pose proof brk_al as Hal. pose proof (u64_range brk) as Hb.
    set (y := bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (-1)) * bv_unsigned brk))).
    assert (Hy : (y mod 4096 = 0)%Z).
    { subst y. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
      rewrite Z.mod_mod_divide by (exists (2 ^ 52)%Z; reflexivity).
      destruct (proj1 (Z.mod_divide (bv_unsigned brk) 4096 ltac:(lia)) Hal) as [q Hq]. rewrite Hq.
      rewrite Z.mul_assoc. apply Z_mod_mult. }
    assert (Hand : Z.land (bv_unsigned (Z_to_bv 64 4095)) y = 0%Z).
    { change (bv_unsigned (Z_to_bv 64 4095)) with (Z.ones 12). rewrite Z.land_comm, Z.land_ones by lia.
      change (2 ^ 12)%Z with 4096%Z. exact Hy. }
    rewrite Hand. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  #[using="Hbrk Hplen"] Lemma brk_ne_req : forall vals, vals_ev vals 70 = brk ->
    branch_taken BC_NE (edenot (ENV vals) b_expr) (edenot (ENV vals) (EAlu ALU_ADD b_expr (ELit 8192))) = true.
  Proof.
    intros vals P70. cbn [edenot b_expr ev ENV]. rewrite P70, alu_add. unfold v_add.
    cbn [branch_taken]. unfold bv_eqb. pose proof brk_hi. pose proof (u64_range brk).
    change (bv_unsigned (Z_to_bv 64 8192)) with 8192%Z. rewrite u_small by lia.
    apply Bool.negb_true_iff. apply Z.eqb_neq. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="a0s Hva"] Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mmap_ok_branch_g (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M (a : word),
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
      regs_ok (ENV vals) srE R -> know_ok RSEGS (ENV vals) M knE -> above_sp0 M ->
      grant_ok_na_pin (model1g fd3) a 8192 = true ->      (* [comment removed for export] *)
      realizes RSEGS (mkCfg (mkst (regupd R 10 a) (Z_to_bv 64 0x9a1f0)
                                    (unfill a (Z_to_bv 64 8192) M) (seg_rom RSEGS))
                              (noaccess_model a (Z_to_bv 64 8192) (model1g fd3))) KB.
  Definition mmap_ok_branch : TSet -> Prop := mmap_ok_branch_g (FdFile path (Z_to_bv 64 0)).

  #[using="Hvsp Hbrk Hplen"] Lemma oom_seg3 : forall fd3 KB vals R M,
    mmap_ok_branch_g fd3 KB ->
    length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
    vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv -> vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
    regs_ok (ENV vals) srE0 R -> know_ok RSEGS (ENV vals) M knD2 -> above_sp0 M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x98b7c) M (seg_rom RSEGS)) (model1g fd3))
               (t_alt2 (t_die msg_oom fs0) KB).
  Proof.
    intros fd3 KB vals R M HKB HL P0 P70 P1 P2 P5t P6t P7t HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    (* [comment removed for export] *)
    run_block_keep scrE 71%nat.
    { (* [comment removed for export] *) unfold sc_denot. apply brk_ne_req. exact P70. }
    refresh_above vals P0 HA. clear R M. name_state R M.
    (* [comment removed for export] *)
    eapply (rz_mmap_noaccess RSEGS _ _ _ (model1g fd3) ECALLW 8192).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - (* [comment removed for export] *)
      change (page_round_up_Z 8192) with 8192%Z.
      assert (Ers : segments_reserved RSEGS = [(Z_to_bv 64 65536, Z_to_bv 64 139264); (Z_to_bv 64 204800, Z_to_bv 64 499712);
                                               (Z_to_bv 64 704512, Z_to_bv 64 24576); (Z_to_bv 64 729088, Z_to_bv 64 212992)])
        by (vm_compute; reflexivity).
      apply grant_exists_na_pin; rewrite ?m1_vmmaps; cbn [vm_reserved vm_maps vm_limit]; rewrite ?Ers; cbn [app].
      + lia.
      + repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
      + cbn [length app Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
      + unfold init_sp_ok, sp_window_lo. cbn [vm_init_sp]. lia.   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x9a1ec + 4)%Z with 0x9a1f0%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?R =>
        pose proof (regs_set_a0 E sr R (errno_ret ENOMEM) (ELit (2 ^ 64 - 12)) HR
                      ltac:(apply bv_eq; reflexivity)) as HR2 end.
      eapply (oom_seg4 fd3 vals); [exact HL | exact P0 | exact HR2 | exact HK].
    - (* [comment removed for export] *)
      intros a Hg. rewrite v_addi_pc4 by lia. change (0x9a1ec + 4)%Z with 0x9a1f0%Z.
      change (page_round_up_Z 8192) with 8192%Z in Hg |- *.
      eapply (HKB vals); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition brk_ok_branch_g (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
      regs_ok (ENV vals) srD2 R -> know_ok RSEGS (ENV vals) M knD2 -> above_sp0 M ->
      realizes RSEGS
        (mkCfg (mkst (regupd R 10 (Z_to_bv 64 (bv_unsigned brk + 8192))) (Z_to_bv 64 0x98b7c)
                     (zfill brk (Z_to_bv 64 8192) M) (seg_rom RSEGS))
               (mkModelA (fds1g fd3) (mkVmMapsFull (segments_reserved RSEGS) [(brk, Z_to_bv 64 8192)] [] brk
                                            (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                        stdin0 fs0 None (Some tid) None)) KB.
  Definition brk_ok_branch : TSet -> Prop := brk_ok_branch_g (FdFile path (Z_to_bv 64 0)).

  #[using="Hvsp Hbrk Hplen"] Lemma oom_seg2 : forall fd3 KBb KBm vals R M,
    brk_ok_branch_g fd3 KBb -> mmap_ok_branch_g fd3 KBm ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 ->
    vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv -> vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
    regs_ok (ENV vals) srB0 R -> know_ok RSEGS (ENV vals) M knA -> above_sp0 M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xa763c) M (seg_rom RSEGS)) (model1g fd3))
               (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb).
  Proof.
    intros fd3 KBb KBm vals R M HKBb HKBm HL P0 P1 P2 P5t P6t P7t HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    refresh_above vals P0 HA. clear R M. name_state R M.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knB ltac:(let i := kidx knB (is_krange (EVar 4)) in exact i) _ HK eq_refl)
      as Krnd; cbn [kentry_ok edenot ev ENV] in Krnd.
    pose proof (know_nth RSEGS _ _ knB ltac:(let i := kidx knB (is_kdisj (EVar 0) (EVar 4)) in exact i) _ HK eq_refl)
      as Kdj; cbn [kentry_ok] in Kdj; unfold estart in Kdj; cbn [a_base a_off edenot ev ENV] in Kdj; rewrite P0 in Kdj.
    krdv HK 4%nat 8%Z 8%nat Hrd8.
    { apply flat_intro; cbn [edenot ev ENV]; lia. }
    pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-384) 8) in exact i)
                  _ _ _ (-384) 8 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hwr8.
    set (dst := adenot (ENV vals) (SA (EVar 0) (-384))) in *.
    set (src := adenot (ENV vals) (SA (EVar 4) 8)) in *.
    assert (Hudst : bv_unsigned dst = (bv_unsigned sp0 - 384)%Z).
    { subst dst. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0, u_small by lia. lia. }
    assert (Husrc : bv_unsigned src = (bv_unsigned (vals_ev vals 4) + 8)%Z).
    { subst src. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite u_small by lia. lia. }
    assert (MC : mcH M dst src 8 (word_to_le_bytes 8 (vals_ev vals 7))).
    { constructor.
      - lia.
      - reflexivity.
      - exact Hrd8.
      - exact Hwr8.
      - lia.
      - lia.
      - lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x98a8c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x98a8c) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit).
    assert (G11 : getr R 11 = src) by (regv HR (11:reg); subst src; apply edenot_add_lit).
    assert (G12 : getr R 12 = Z_to_bv 64 8) by (regv HR (12:reg); reflexivity).
    destruct (ref_memcpy M dst src 8 _ (seg_rom RSEGS) MC R (Z_to_bv 64 0x98a8c) RT G1 G10 G11 G12)
      as (R2 & Hms & Hkeep). clear RT G1 G10 G11 G12.
    replace (Z_to_bv 64 681768) with (0xa6728 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    (* [comment removed for export] *)
    assert (HA' : above_sp0 (wbytes M dst (word_to_le_bytes 8 (vals_ev vals 7)))).
    { intros a Ha. rewrite wbytes_outside; [apply HA; exact Ha | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; right; lia]. }
    clear HA. rename HA' into HA.
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr _ R2 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep
                    callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?M0 ?kn =>
      let c := eval vm_compute in (carry [mc_store] kn []) in
      lazymatch c with (?kn', ?scs, ?hs) =>
        pose proof (know_after_store RSEGS E M0 kn (SA (EVar 0) (-384)) 8 (EVar 7) (word_to_le_bytes 8 (vals_ev vals 7))
                      kn' scs hs ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                      ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia) eq_refl) as HK2
      end end.
    clear HK. subst dst.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 70%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (P0' : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (P1' : vals_ev vals1 1 = p0 sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    assert (P2' : vals_ev vals1 2 = p1 sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (P5' : vals_ev vals1 5 = tid) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
    assert (P6' : vals_ev vals1 6 = canary_w rdraw) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6t).
    assert (P7' : vals_ev vals1 7 = secret_w rdraw) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P7t).
    clearbody vals1. clear HL P0 P1 P2 P5t P6t P7t. rename HL1 into HL. rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P5' into P5t. rename P6' into P6t. rename P7' into P7t.
    change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path))) with (ENV vals1) in HR, HK.
    (* [comment removed for export] *)
    run_block_keep scr0 70%nat.
    refresh_above vals1 P0 HA. clear Hrd8 Hwr8 Hudst Husrc MC Krnd Kdj. clear R2 M. try clear R. name_state R M.
    (* [comment removed for export] *)
    eapply (rz_brk_query RSEGS _ _ _ (model1g fd3) ECALLW).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). reflexivity.
    - rewrite v_addi_pc4 by lia. change (0x98b54 + 4)%Z with 0x98b58%Z.
      rewrite m1_vmmaps; cbn [vm_brk].
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals1 [brk] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals1 [brk] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      clear HR HK.
      set (vals2 := vals1 ++ [brk]) in *.
      assert (HL2 : length vals2 = 71%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (P0' : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (P70 : vals_ev vals2 70 = brk).
      { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals1)). rewrite vals_ev_app_r. reflexivity. }
      assert (P1' : vals_ev vals2 1 = p0 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
      assert (P2' : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (P5' : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
      assert (P6' : vals_ev vals2 6 = canary_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6t).
      assert (P7' : vals_ev vals2 7 = secret_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P7t).
      clearbody vals2. clear HL P0 P1 P2 P5t P6t P7t. rename HL2 into HL. rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P5' into P5t. rename P6' into P6t. rename P7' into P7t.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR2, HK2.
      pose proof (regs_set_a0 (ENV vals2) _ _ brk b_expr HR2 ltac:(cbn [edenot b_expr ev ENV]; exact P70)) as HR.
      clear HR2.
      (* [comment removed for export] *)
      lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
        assert (HK : know_ok RSEGS (ENV vals2) Mc knD0) end.
      { unfold knD0. apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]].
        - apply kalign_intro; [lia|]. cbn [edenot b_expr ev ENV]. rewrite P70. exact brk_al.
        - apply krange_intro. cbn [edenot b_expr ev ENV]. rewrite P70. pose proof brk_lo. pose proof brk_hi. lia. }
      clear HK2.
      (* [comment removed for export] *)
      run_block_keep scr0 71%nat.
      refresh_above vals2 P0 HA. clear R M. name_state R M.
      (* [comment removed for export] *)
      pose proof (regs_ok_esub (ENV vals2) ugly_b b_expr _ _ (ugly_b_sem vals2 P70) HR) as HR2.
      pose proof (know_ok_ksub RSEGS (ENV vals2) _ ugly_b b_expr _ (ugly_b_sem vals2 P70) HK) as HK2.
      clear HR HK. rename HR2 into HR. rename HK2 into HK.
      lazymatch type of HR with regs_ok _ ?sr _ => let sr' := eval vm_compute in sr in change sr with sr' in HR end.
      lazymatch type of HK with know_ok _ _ _ ?kn => let kn' := eval vm_compute in kn in change kn with kn' in HK end.
      (* [comment removed for export] *)
      eapply (rz_brk_grow RSEGS _ _ _ (model1g fd3) ECALLW 8192).
      + vm_compute. reflexivity.
      + apply is_ecall_ECALLW.
      + reflexivity.
      + reflexivity.
      + regv HR (17 : reg). reflexivity.
      + rewrite m1_vmmaps; cbn [vm_brk]. exact brk_al.
      + reflexivity.
      + lia.
      + rewrite m1_vmmaps; cbn [vm_brk]. pose proof brk_lo. lia.
      + rewrite m1_vmmaps; cbn [vm_brk]. pose proof brk_hi. lia.
      + rewrite m1_vmmaps; cbn [vm_brk vm_start_brk]. lia.
      + rewrite m1_vmmaps; cbn [vm_brk]. regv HR (10 : reg). rewrite edenot_add_lit.
        unfold adenot, v_addi. cbn [a_base a_off edenot b_expr ev ENV]. rewrite P70. reflexivity.
      + rewrite m1_vmmaps. cbn [vm_brk].
        apply (brk_grow_admissible_init (segments_reserved RSEGS) brk mbase sp0 LIM (model1g fd3));   (* [comment removed for export] *)
          rewrite ?rtop, ?alloc_ceiling_val; unfold sp_window_lo;
          first [exact brk_al | reflexivity | pose proof brk_lo; pose proof brk_hi; pose proof LIM_ge; lia].
      + (* [comment removed for export] *)
        rewrite v_addi_pc4 by lia. change (0x98b78 + 4)%Z with 0x98b7c%Z.
        rewrite m1_vmmaps; cbn [vm_brk].
        pose proof (regs_set_a0 (ENV vals2) _ _ brk b_expr HR ltac:(cbn [edenot b_expr ev ENV]; exact P70)) as HR2.
        eapply (oom_seg3 fd3 KBm vals2); try eassumption.
      + (* [comment removed for export] *)
        rewrite v_addi_pc4 by lia. change (0x98b78 + 4)%Z with 0x98b7c%Z.
        rewrite m1_vmmaps; cbn [vm_brk vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base].
        eapply (HKBb vals2); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_err_branch (KA : TSet) : Prop :=
    forall e vals R M,
      In e openat_errnos ->
      length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
      regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
      (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xa763c) M (seg_rom RSEGS)) model0) KA.

  #[using="uid hw fdata Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpns Hpnd Hplen"] Lemma oom_seg1 : forall KA KBb KBm,
    open_err_branch KA -> brk_ok_branch KBb -> mmap_ok_branch KBm ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x32574) mem0 (seg_rom RSEGS)) model0)
               (t_alt2 KA (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb)).
  Proof.
    intros KA KBb KBm HKA HKBb HKBm.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path envv rdraw tid regs0) with (ENV (vals0 sp0 a0s path envv rdraw tid regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s path envv rdraw tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, length_skipn, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 sp0 a0s path envv) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    assert (P6t : vals_ev vals 6 = canary_w rdraw) by reflexivity.   (* [comment removed for export] *)
    assert (P7t : vals_ev vals 7 = secret_w rdraw) by reflexivity.   (* [comment removed for export] *)
    destruct (main_str sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM. unfold p1. rewrite (rdn_mem_denot_above RSEGS (ENV vals) mem0 _ 0%nat 0xe6000);
        [exact Sr | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia
        | pose proof (u64_range (cat_argv_ptr sp0 [a0s; path] envv 1)); lia]. }
    (* [comment removed for export] *)
    eapply (rz_openat_file RSEGS _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - (* [comment removed for export] *) rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - (* [comment removed for export] *) split; [exact Hplen|]. split; [apply path_nonul|].
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. exact Sr'.
    - exact Hpne.
    - exact Hpns.   (* [comment removed for export] *)
    - exact Hpnd.   (* [comment removed for export] *)
    - rewrite m0_fs. exact Hfile.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0xa7638 + 4)%Z with 0xa763c%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
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
      + intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0xe6000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0xa7638 + 4)%Z with 0xa763c%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0)
        with (model1g (FdFile path (Z_to_bv 64 0))).
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      assert (HA : above_sp0 M).
      { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0xe6000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
      eapply (oom_seg2 (FdFile path (Z_to_bv 64 0)) KBb KBm vals); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="uid hw fdata Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpns Hpnd Hplen"] Theorem oom_pilot : forall KA KBb KBm,
    open_err_branch KA -> brk_ok_branch KBb -> mmap_ok_branch KBm ->
    realizes RSEGS
      (mkCfg (mkst regs0 (Z_to_bv 64 0x32574) mem0 (seg_rom RSEGS))
             (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputA [a0s; path] envv fs0 stdin0))))
      (t_alt2 KA (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb)).
  Proof. intros. apply oom_seg1; assumption. Qed.

End Pilot.

End FPW_1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
