(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the Pilot section takes the launch input, mmap base, entry point, uid and hwcap of the 12-argument main_entry and the stderr writes' channel reader, the reserved ledger is init_reserved with the vDSO pair, block C reads the auxv tail for either value of the launch's rseq flag, the mmap decline test is discharged from the NULL hint, and the path ends below TASK_SIZE; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes MmapSim AllocSim FileSim AgentLib SpecConsts SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame LibStdioCall Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LibWritev RefNodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefExitBase RefStdioDefs RefExit.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefMemcpyBase RefMemcpy RefStartup RefMainEntry.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare MemSplit.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefPilotOOM_defs RefLim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import ShapeLawsX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefNodesX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require AsanCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymDriveLet SymDriveLetRef.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveX.run_block_with ::= run_block_with_let_img.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require RefPilotOOM_lits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_sr ::= constr:(RefPilotOOM_lits.LITS_SR).
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_lg ::= constr:(RefPilotOOM_lits.LITS_LG).
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_kn ::= constr:(RefPilotOOM_lits.LITS_KN).
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_nobignat.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Pilot.
  Context {AMB : Amb}.
  (* [comment removed for export] *)
  Context {AL : AllocLim}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  (* LPS 08b1429: [main_entry] takes the launch's own input, the mmap base and the entry point, and
     its uid/hwcap (RefStartup.v:65); [mbase] is the Section's own. Same shape as
     RefMainEntry.v:127-130. *)
  Variable inp : ProcInput.
  Variable entry : word.
  Variables uid hw : word.
  Hypothesis ME : main_entry inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : path <> dot_path.
  Hypothesis Hplen : (length path <= 4095)%nat.
  (* LPS 08b1429/75d69e00: the launch's channel reader, needed by every write to stdout/stderr
     (RefStdioWrite.ref_stdio_write). WITNESSED at the top: a_channel_reader =
     in_channel_reader (mkProcInputC ..) (Amb.v:49, reflexivity) = true
     (Run.valid_input_channel_reader, [c0dd863a:theories/LinuxProcessSem/Run.v:5018]). *)
  Hypothesis Hrdr0 : a_channel_reader = true.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).

  (* [comment removed for export] *)
  Definition fds0 : list (word * FdEntry) :=
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
     (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  (* [comment removed for export] *)
  Definition model0 : Model :=
    with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; path] envv fs0 stdin0)).
  (* [comment removed for export] *)
  Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition model1g (fd3 : FdEntry) : Model :=
    (* LPS 08b1429: [init_model]'s reserved list is [init_reserved], which adds the vdso/vvar pair
       (Amb.with_tid_init_model_C). *)
    mkModelC (fds1g fd3) (mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 a_kernel) [] [] brk brk LIM mbase sp0) stdin0 fs0 None (Some tid) None.
  Definition fds1 : list (word * FdEntry) := fds1g (FdFile path (Z_to_bv 64 0)).
  Definition model1 : Model := model1g (FdFile path (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

  Lemma model0_eq : model0 = mkModelC fds0 (mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 a_kernel) [] [] brk brk LIM mbase sp0)
                                     stdin0 fs0 None (Some tid) None.
  Proof using Type. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma m1_vmmaps : forall fd3, m_vmmaps (model1g fd3) = mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 a_kernel) [] [] brk brk LIM mbase sp0.
  Proof using Type. intros. reflexivity. Qed.
  Lemma m1_fs : forall fd3, m_fs (model1g fd3) = fs0.
  Proof using Type. intros. reflexivity. Qed.
  Lemma m1_fds : forall fd3, m_fds (model1g fd3) = fds1g fd3.
  Proof using Type. intros. reflexivity. Qed.
  Lemma m0_fds : m_fds model0 = fds0.
  Proof using Type. reflexivity. Qed.
  Lemma m0_fs : m_fs model0 = fs0.
  Proof using Type. reflexivity. Qed.

  Lemma fds1_2 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof using Type. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma above_sp0_block : forall vals log M,
    vals_ev vals 0 = sp0 -> log_below_b 0 0x58000 log = true -> above_sp0 M ->
    above_sp0 (mem_denot (ENV vals) M log).
  Proof using Hvsp Hplen.
    intros vals log M P0 Hb HA a Ha. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    rewrite (mem_denot_above (ENV vals) M log 0%nat 0x58000 a Hb); [apply HA; exact Ha | | |];
      cbn [ev ENV]; rewrite ?P0; lia.
  Qed.

  Lemma alloc_fd_fds0 : alloc_fd fds0 = Z_to_bv 64 3.
  Proof using Type. exact (alloc_fd_init _ _ _). Qed.
  Lemma fd_lookup_fds0_3 : fd_lookup fds0 (Z_to_bv 64 3) = None.
  Proof using Type. reflexivity. Qed.

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
  Lemma msg_oom_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10317) 19 = Some msg_oom.
  Proof using Type. vm_compute. reflexivity. Qed.

  Lemma oom_seg4 : forall fd3 vals R M,
    length vals = 71%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1d704) M (seg_rom RSEGS)) (model1g fd3)) (t_die msg_oom fs0).
  Proof using Hvsp Hplen Hrdr0.
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
    - (* [comment removed for export] *) cbn [edenot]. lit_u. lia.
    - cbn [edenot]. lia.
    - cbn [edenot]. lit_u. reflexivity.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
      rewrite (u_small (bv_unsigned sp0 + -192)) by lia. lit_u. lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
      rewrite (u_small (bv_unsigned sp0 + -192)) by lia. lit_u. lit_u. lia.
    - cbn [edenot]. lit_u. lit_u. lia.
    - reflexivity.
    - cbn [edenot]. change (length msg_oom) with 19%nat.
      rewrite (kimg_rdn RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kimg_cov 0x10317 19) in exact i)
                 _ _ 0x10317 19 HK eq_refl) by (cbn; lia).
      apply msg_oom_img.
    - apply fds1_2.
    - exact Hrdr0.   (* LPS 08b1429: m_channel_reader (model1g fd3) is a_channel_reader *)
    - reflexivity.
    - reflexivity.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK R M. intros R M HR HK.
      change (sc_sr resG) with srG0 in HR. change (sc_kn resG) with knG0 in HK. change (sc_ret resG) with 0x1e330%Z.
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
      exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x367b0), (bv_unsigned (vals_ev vals' 5)),
             (Z_to_bv 64 0x56e70), (Z_to_bv 64 0).
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
        * lit_u. change (223152 - 168)%Z with 0x36708%Z.
          krd HK 0x36708%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
          rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
          rewrite Z_to_bv_bv_unsigned. reflexivity.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * repeat split; krd_solve HK.
        * repeat split; krd_solve HK.
      + left. split; [reflexivity|].
        exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma rtop : reserved_top (segments_reserved RSEGS) = 0x58000%Z.
  Proof using Type. vm_compute. reflexivity. Qed.

  Lemma brk_lo : (0x58000 <= bv_unsigned brk)%Z.
  Proof using Hbrk. pose proof (proj1 Hbrk) as H. rewrite rtop in H. exact H. Qed.
  Lemma brk_hi : (bv_unsigned brk <= 0x80038000)%Z.
  Proof using path Hbrk Hplen. pose proof (proj1 (proj2 Hbrk)) as H. rewrite rtop, brk_aslr_max_val in H. cbn in H. lia. Qed.
  Lemma brk_al : (bv_unsigned brk mod 4096 = 0)%Z.
  Proof using Hbrk. exact (proj2 (proj2 Hbrk)). Qed.

  (* [comment removed for export] *)
  Lemma ugly_b_sem : forall vals, vals_ev vals 70 = brk ->
    edenot (ENV vals) ugly_b = edenot (ENV vals) b_expr.
  Proof using Hbrk Hplen.
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
  Lemma brk_ne_req : forall vals, vals_ev vals 70 = brk ->
    branch_taken BC_NE (edenot (ENV vals) b_expr) (edenot (ENV vals) (EAlu ALU_ADD b_expr (ELit 8192))) = true.
  Proof using Hbrk Hplen.
    intros vals P70. cbn [edenot b_expr ev ENV]. rewrite P70, alu_add. unfold v_add.
    cbn [branch_taken]. unfold bv_eqb. pose proof brk_hi. pose proof (u64_range brk).
    change (bv_unsigned (Z_to_bv 64 8192)) with 8192%Z. rewrite u_small by lia.
    apply Bool.negb_true_iff. apply Z.eqb_neq. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma path_nsl : path_has_slash path = false.
  Proof using a0s Hva. destruct Hva as (_ & _ & _ & _ & Hs). inversion Hs as [|x l [Hx _] Hl]; subst. exact Hx. Qed.
  Lemma path_ndd : path <> dotdot_path.
  Proof using a0s Hva.
    destruct Hva as (_ & _ & _ & _ & Hs). inversion Hs as [|x l [_ Hx] Hl]; subst.
    intros E. rewrite E in Hx. vm_compute in Hx. discriminate Hx.
  Qed.

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof using a0s Hva.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.

  (* The tail words the plan's block C reads (RefPilotOOM_defs.kn_tail), at the input's own flag. *)
  Lemma auxv_tail_ok : forall vals M,
    vals_ev vals 3 = auxvp sp0 a0s path envv -> above_sp0 M ->
    know_ok RSEGS (ENV vals) M (kn_tail (kb_rseq (in_kernel inp))).
  Proof using Hva Hve Hvsp Htid ME.
    intros vals M P3 HA.
    pose proof (proj1 Hvsp) as HLO. pose proof (proj1 (proj2 Hvsp)) as HHI.
    unfold sp_window_lo, sp_window_hi in HLO, HHI.
    destruct (auxvp_u sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry uid hw ME) as [Hu _].
    (* RefMainEntry.auxv_word_any: [auxv_word_at] over the whole vector (pair 26 on is rseq's). *)
    assert (WA : forall j, (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
      rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8
      = Some (word_to_le_bytes 8 (nth j (RefLayout.auxv_words (launch_auxv inp sp0 mbase) RPH entry
                                            (in_uid inp) (in_gid inp) (in_hwcap inp)
                                            (rnd sp0 a0s path envv inp)
                                            (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                    (Z_to_bv 64 0))))
      by (intros j Hj; eapply RefMainEntry.auxv_word_any; eassumption).
    assert (Hb : (Z.of_nat (RefLayout.auxv_off [a0s; path] envv) + 464 <= 2240000)%Z)
      by (destruct Hve as [Hle _]; unfold RefLayout.auxv_off; cbn [length]; lia).
    (* One tail entry: the word at auxvp + 8j, j even, read from [mem0] (M agrees above sp0). *)
    assert (KW : forall (j : nat) (v : Z),
      (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat -> (52 <= j <= 56)%nat ->
      nth j (RefLayout.auxv_words (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp)
               (rnd sp0 a0s path envv inp) (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (Z_to_bv 64 0)
        = Z_to_bv 64 v ->
      kentry_ok RSEGS (ENV vals) M (KWord (SA (EVar 3) (8 * Z.of_nat j)) 8 (ELit v))).
    { intros j v Hj Hj' Hv. cbn [kentry_ok].
      split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off edenot ev ENV]; rewrite P3, Hu; lia|].
      unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV]. rewrite P3.
      rewrite (rdn_ext RSEGS 8 M mem0)
        by (rewrite u_small by lia; first [lia | intros x Hx; apply HA; lia]).
      rewrite (WA j Hj), Hv. reflexivity. }
    unfold know_ok, kn_tail.
    destruct (kb_rseq (in_kernel inp)) eqn:Er;
      repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with |- kentry_ok _ _ _ (KWord (SA _ ?k) _ (ELit ?v)) =>
           let j := eval vm_compute in (Z.to_nat (k / 8)) in
           change k with (8 * Z.of_nat j)%Z; apply (KW j v);
           [ try rewrite Er; cbn; lia | lia
           | unfold RefLayout.auxv_words, auxv_entries, launch_auxv; cbn [la_rseq]; try rewrite Er;
             cbn [flat_map app nth fst snd]; reflexivity ] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mmap_ok_branch_g (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M (hint a : word),
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 a0s path envv rdraw inp -> vals_ev vals 2 = p1 a0s path envv rdraw inp ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) srE R -> know_ok RSEGS (ENV vals) M knE -> above_sp0 M ->
      grant_ok_na_pin hint (model1g fd3) a 8192 = true ->      (* [comment removed for export] *)
      realizes RSEGS (mkCfg (mkst (regupd R 10 a) (Z_to_bv 64 0x1d704)
                                    (unfill a (Z_to_bv 64 8192) M) (seg_rom RSEGS))
                              (noaccess_model a (Z_to_bv 64 8192) (model1g fd3))) KB.
  Definition mmap_ok_branch : TSet -> Prop := mmap_ok_branch_g (FdFile path (Z_to_bv 64 0)).

  Lemma oom_seg3 : forall fd3 KB vals R M,
    mmap_ok_branch_g fd3 KB ->
    length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
    vals_ev vals 1 = p0 a0s path envv rdraw inp -> vals_ev vals 2 = p1 a0s path envv rdraw inp -> vals_ev vals 5 = tid ->
    regs_ok (ENV vals) srE0 R -> know_ok RSEGS (ENV vals) M knD2 -> above_sp0 M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1c5f4) M (seg_rom RSEGS)) (model1g fd3))
               (t_alt2 (t_die msg_oom fs0) KB).
  Proof using Hvsp Hbrk Hplen Hrdr0.
    intros fd3 KB vals R M HKB HL P0 P70 P1 P2 P5t HR HK HA.
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
      assert (Ers : segments_reserved RSEGS = [(Z_to_bv 64 65536, Z_to_bv 64 12288); (Z_to_bv 64 77824, Z_to_bv 64 73728);
                                               (Z_to_bv 64 151552, Z_to_bv 64 4096); (Z_to_bv 64 155648, Z_to_bv 64 204800)])
        by (vm_compute; reflexivity).
      (* LPS 08b1429: the reserved ledger is [init_reserved], i.e. the image's four entries plus the
         vdso/vvar pair [vdso_reserved a_kernel top] (none or two entries, of 4 and at most 16 pages
         for EVERY kernel build: [vdso_text_pages_le]), so both side conditions hold for any build. *)
      assert (Hvr : forall kb top,
                 Forall (fun p : word * word => bv_unsigned (snd p) <= 2 ^ 30)%Z (vdso_reserved kb top)
                 /\ (length (vdso_reserved kb top) <= 2)%nat).
      { intros kb top. pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
        unfold vdso_reserved. cbv zeta.
        destruct (top - vdso_len kb <? page_size)%Z; [split; [constructor | cbn; lia]|].
        split; [|cbn; lia].
        repeat constructor; cbn [snd]; unfold vdso_vvar_pages, page_size; rewrite u_small by lia; lia. }
      apply grant_exists_na; rewrite ?m1_vmmaps; cbn [vm_reserved vm_maps vm_limit].
      + unfold AsanCeil.init_sp_ok. cbn [vm_init_sp]. exact (proj1 Hvsp).
      + lia.
      + unfold init_reserved; rewrite Ers, app_nil_r. apply Forall_app; split;
          [repeat constructor; cbn [snd]; rewrite u_small by lia; lia | exact (proj1 (Hvr _ _))].
      + unfold init_reserved; rewrite Ers, app_nil_r, length_app.
        lazymatch goal with |- context [length (vdso_reserved ?k ?t)] => pose proof (proj2 (Hvr k t)) end.
        cbn [length]. lia.
      + vm_compute. reflexivity.
    - (* LPS 727298f3 (LPS #144, revised by LPS #146): [check_mmap] tests [place_declined_b] ahead of the
         [alt] in the [mmap_noaccess_b] arm too, so [rz_mmap_noaccess] carries the
         model's own decline test.  The hint is the call's own a0, which this walk
         pins to the literal NULL, and a NULL hint is never declined
         ([RefNodesX.place_declined_b_null]).  Proved, never assumed. *)
      regv HR (10 : reg). apply place_declined_b_null.
    - (* [comment removed for export] *)
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x1d700 + 4)%Z with 0x1d704%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?R =>
        pose proof (regs_set_a0 E sr R (errno_ret ENOMEM) (ELit (2 ^ 64 - 12)) HR
                      ltac:(apply bv_eq; reflexivity)) as HR2 end.
      eapply (oom_seg4 fd3 vals); [exact HL | exact P0 | exact HR2 | exact HK].
    - (* [comment removed for export] *)
      intros a Hg. rewrite v_addi_pc4 by lia. change (0x1d700 + 4)%Z with 0x1d704%Z.
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
      vals_ev vals 1 = p0 a0s path envv rdraw inp -> vals_ev vals 2 = p1 a0s path envv rdraw inp ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) srD2 R -> know_ok RSEGS (ENV vals) M knD2 -> above_sp0 M ->
      realizes RSEGS
        (mkCfg (mkst (regupd R 10 (Z_to_bv 64 (bv_unsigned brk + 8192))) (Z_to_bv 64 0x1c5f4)
                     (zfill brk (Z_to_bv 64 8192) M) (seg_rom RSEGS))
               (mkModelC (fds1g fd3) (mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 a_kernel) [(brk, Z_to_bv 64 8192)] [] brk
                                            (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                        stdin0 fs0 None (Some tid) None)) KB.
  Definition brk_ok_branch : TSet -> Prop := brk_ok_branch_g (FdFile path (Z_to_bv 64 0)).

  (* LPS 08b1429/75d69e00: [oom_seg2]'s tail from 0x1c5f0, after block D, split out so that both
     CONFIG_RSEQ cases of block C (RefPilotOOM_defs.kn_tail) reach it: block D overwrites the one
     register those cases leave different (a2), so the state here is [srD]/[knD] in both, and
     one script serves both. *)
  Lemma oom_seg2d : forall fd3 KBb KBm vals2 R M,
    brk_ok_branch_g fd3 KBb -> mmap_ok_branch_g fd3 KBm ->
    length vals2 = 71%nat -> vals_ev vals2 0 = sp0 -> vals_ev vals2 70 = brk ->
    vals_ev vals2 1 = p0 a0s path envv rdraw inp -> vals_ev vals2 2 = p1 a0s path envv rdraw inp ->
    vals_ev vals2 5 = tid ->
    regs_ok (ENV vals2) srD R -> know_ok RSEGS (ENV vals2) M knD -> above_sp0 M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1c5f0) M (seg_rom RSEGS)) (model1g fd3))
               (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb).
  Proof using Hva Hve Hvsp Htid ME Hbrk Hplen Hrdr0.
    intros fd3 KBb KBm vals2 R M HKBb HKBm HL P0 P70 P1 P2 P5t HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
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
      + rewrite m1_vmmaps. cbn [vm_brk]. unfold model1g.
        (* LPS 08b1429: the ledger is [init_reserved], whose vdso/vvar pair sits at
           [launch_vdso_top mbase sp0] >= mmap_base_min (the launch's own base,
           [Run.entry_launch_ok_va_base]); the heap grow ends far below it for every kernel build. *)
        assert (Hmb : (mmap_base_min <= bv_unsigned mbase)%Z).
        { destruct (main_entry_launch inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME)
            as (b' & _ & _ & _ & _ & _ & Hok).
          exact (proj1 (entry_launch_ok_va_base Sv48 (mkEntry sp0 b' mbase rdraw) inp Hok)). }
        assert (Hvt : (bv_unsigned brk + 8192 + page_size + vdso_len a_kernel <= Placement.launch_vdso_top mbase sp0)%Z).
        { pose proof (vdso_len_bounds a_kernel). pose proof brk_hi.
          assert (Hlt : (mmap_base_min <= Placement.launch_vdso_top mbase sp0)%Z).
          { unfold Placement.launch_vdso_top. apply Placement.page_round_down_Z_greatest;
              [| unfold mmap_base_min, page_size; reflexivity].
            pose proof (proj1 Hvsp). unfold sp_window_lo, stack_max_size, mmap_base_min in *. lia. }
          unfold mmap_base_min, page_size in *. lia. }
        apply (brk_grow_admissible_init_vdso (segments_reserved RSEGS) brk mbase sp0 a_kernel LIM (model1g fd3) 8192);
          rewrite ?rtop, ?AsanCeil.alloc_ceiling_val;
          first [exact Hvt | exact (proj1 Hvsp) | exact brk_al | reflexivity | pose proof brk_lo; pose proof brk_hi; pose proof LIM_ge; lia].
      + (* [comment removed for export] *)
        rewrite v_addi_pc4 by lia. change (0x1c5f0 + 4)%Z with 0x1c5f4%Z.
        rewrite m1_vmmaps; cbn [vm_brk].
        pose proof (regs_set_a0 (ENV vals2) _ _ brk b_expr HR ltac:(cbn [edenot b_expr ev ENV]; exact P70)) as HR2.
        eapply (oom_seg3 fd3 KBm vals2); try eassumption.
      + (* [comment removed for export] *)
        rewrite v_addi_pc4 by lia. change (0x1c5f0 + 4)%Z with 0x1c5f4%Z.
        rewrite m1_vmmaps; cbn [vm_brk vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base].
        eapply (HKBb vals2); try eassumption.
  Qed.

  Lemma oom_seg2 : forall fd3 KBb KBm vals R M,
    brk_ok_branch_g fd3 KBb -> mmap_ok_branch_g fd3 KBm ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 ->
    vals_ev vals 1 = p0 a0s path envv rdraw inp -> vals_ev vals 2 = p1 a0s path envv rdraw inp -> vals_ev vals 5 = tid ->
    (* LPS 08b1429/75d69e00: block C reads the auxv's tail, so the environment's auxv base is named *)
    vals_ev vals 3 = auxvp sp0 a0s path envv ->
    regs_ok (ENV vals) srB0 R -> know_ok RSEGS (ENV vals) M knA -> above_sp0 M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2409c) M (seg_rom RSEGS)) (model1g fd3))
               (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb).
  Proof using Hva Hve Hvsp Htid ME Hbrk Hplen Hrdr0.
    intros fd3 KBb KBm vals R M HKBb HKBm HL P0 P1 P2 P5t P3 HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    refresh_above vals P0 HA. clear R M. name_state R M.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knB ltac:(let i := kidx knB (is_krange (EVar 6)) in exact i) _ HK eq_refl)
      as Krnd; cbn [kentry_ok edenot ev ENV] in Krnd.
    pose proof (know_nth RSEGS _ _ knB ltac:(let i := kidx knB (is_kdisj (EVar 0) (EVar 6)) in exact i) _ HK eq_refl)
      as Kdj; cbn [kentry_ok] in Kdj; unfold estart in Kdj; cbn [a_base a_off edenot ev ENV] in Kdj; rewrite P0 in Kdj.
    krdv HK 6%nat 8%Z 8%nat Hrd8.
    { apply flat_intro; cbn [edenot ev ENV]; lia. }
    pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-384) 8) in exact i)
                  _ _ _ (-384) 8 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hwr8.
    set (dst := adenot (ENV vals) (SA (EVar 0) (-384))) in *.
    set (src := adenot (ENV vals) (SA (EVar 6) 8)) in *.
    assert (Hudst : bv_unsigned dst = (bv_unsigned sp0 - 384)%Z).
    { subst dst. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0, u_small by lia. lia. }
    assert (Husrc : bv_unsigned src = (bv_unsigned (vals_ev vals 6) + 8)%Z).
    { subst src. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite u_small by lia. lia. }
    assert (MC : mcH M dst src 8 (word_to_le_bytes 8 (edenot (ENV vals) (EVar 7)))).
    { constructor.
      - lia.
      - reflexivity.
      - exact Hrd8.
      - exact Hwr8.
      - lia.
      - lia.
      - lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x1c504)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x1c504) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit).
    assert (G11 : getr R 11 = src) by (regv HR (11:reg); subst src; apply edenot_add_lit).
    assert (G12 : getr R 12 = Z_to_bv 64 8) by (regv HR (12:reg); reflexivity).
    destruct (ref_memcpy M dst src 8 _ (seg_rom RSEGS) MC R (Z_to_bv 64 0x1c504) RT G1 G10 G11 G12)
      as (R2 & Hms & Hkeep). clear RT G1 G10 G11 G12.
    replace (Z_to_bv 64 144960) with (0x23640 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    (* [comment removed for export] *)
    assert (HA' : above_sp0 (wbytes M dst (word_to_le_bytes 8 (edenot (ENV vals) (EVar 7))))).
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
        pose proof (know_after_store RSEGS E M0 kn (SA (EVar 0) (-384)) 8 (EVar 7) (word_to_le_bytes 8 (edenot (ENV vals) (EVar 7)))
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
    assert (P1' : vals_ev vals1 1 = p0 a0s path envv rdraw inp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    assert (P2' : vals_ev vals1 2 = p1 a0s path envv rdraw inp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (P3' : vals_ev vals1 3 = auxvp sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
    assert (P5' : vals_ev vals1 5 = tid) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
    clearbody vals1. clear HL P0 P1 P2 P3 P5t. rename HL1 into HL. rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P3' into P3. rename P5' into P5t.
    change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path))) with (ENV vals1) in HR, HK.
    (* [comment removed for export] *)
    (* LPS 08b1429/75d69e00: block C walks the auxv to AT_NULL, whose position depends on the input's
       free CONFIG_RSEQ flag (RefPilotOOM_defs.kn_tail). Split on the flag HERE, above every
       computation, give each case its own tail words, and run the block in each; both reach
       0x1c5cc with the same registers but a2 (dead) and the same knowledge plus the tail,
       which is dropped right after so the rest of the proof is shared. *)
    lazymatch type of HA with above_sp0 ?Ma => pose proof (auxv_tail_ok vals1 Ma P3 HA) as HKt end.
    lazymatch type of HK with know_ok ?s ?E ?Mk ?kn =>
      assert (HKa : know_ok s E Mk (kn ++ kn_tail (kb_rseq (in_kernel inp))))
        by (unfold know_ok in *; apply Forall_app; split; assumption) end.
    clear HK HKt. rename HKa into HK.
    destruct (kb_rseq (in_kernel inp)) eqn:Er; cbn [kn_tail] in HK.
    all: run_block_keep scr0 70%nat.
    all: refresh_above vals1 P0 HA. all: clear Hrd8 Hwr8 Hudst Husrc MC Krnd Kdj. all: clear R2 M. all: try clear R. all: name_state R M.
    all: lazymatch type of HK with know_ok ?s ?E ?Mk _ =>
           first [ change (know_ok s E Mk (knC ++ kn_tail true)) in HK
                 | change (know_ok s E Mk (knC ++ kn_tail false)) in HK ] end.
    all: unfold know_ok in HK; apply Forall_app in HK as [HK _]; fold (know_ok RSEGS (ENV vals1) M knC) in HK.
    (* The two cases differ only in a2, which block D writes (0x1c5d0: neg a2, a0) before reading;
       so the brk query and block D run in both, and both reach [oom_seg2d]'s common state. *)
    all: eapply (rz_brk_query RSEGS _ _ _ (model1g fd3) ECALLW);
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | reflexivity | reflexivity
      | regv HR (17 : reg); reflexivity | regv HR (10 : reg); reflexivity | ].
    all: rewrite v_addi_pc4 by lia; change (0x1c5cc + 4)%Z with 0x1c5d0%Z.
    all: rewrite m1_vmmaps; cbn [vm_brk].
    all: lazymatch type of HR with regs_ok _ ?sr ?Rc =>
           pose proof (env_app_regs vals1 [brk] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    all: lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
           pose proof (env_app_know RSEGS vals1 [brk] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
    all: clear HR HK.
    all: set (vals2 := vals1 ++ [brk]) in *.
    all: assert (HL2 : length vals2 = 71%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
    all: assert (P0' : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    all: assert (P70 : vals_ev vals2 70 = brk)
           by (subst vals2; rewrite <- HL; rewrite <- (Nat.add_0_r (length vals1)); rewrite vals_ev_app_r; reflexivity).
    all: assert (P1' : vals_ev vals2 1 = p0 a0s path envv rdraw inp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    all: assert (P2' : vals_ev vals2 2 = p1 a0s path envv rdraw inp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    all: assert (P5' : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
    all: clearbody vals2. all: clear HL P0 P1 P2 P3 P5t.
    all: rename HL2 into HL; rename P0' into P0; rename P1' into P1; rename P2' into P2; rename P5' into P5t.
    all: change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR2, HK2.
    all: pose proof (regs_set_a0 (ENV vals2) _ _ brk b_expr HR2 ltac:(cbn [edenot b_expr ev ENV]; exact P70)) as HR.
    all: clear HR2.
    all: lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
           assert (HK : know_ok RSEGS (ENV vals2) Mc knD0)
             by (unfold knD0; apply know_ok_cons;
                 [ apply kalign_intro; [lia|]; cbn [edenot b_expr ev ENV]; rewrite P70; exact brk_al
                 | apply know_ok_cons;
                   [ apply krange_intro; cbn [edenot b_expr ev ENV]; rewrite P70;
                     pose proof brk_lo; pose proof brk_hi; lia
                   | exact HK2 ] ]) end.
    all: clear HK2.
    all: run_block_keep scr0 71%nat.
    all: refresh_above vals2 P0 HA. all: clear R M. all: name_state R M.
    all: eapply (oom_seg2d fd3 KBb KBm vals2 R M); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_err_branch (KA : TSet) : Prop :=
    forall e vals R M,
      In e openat_errnos ->
      length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
      vals_ev vals 1 = p0 a0s path envv rdraw inp -> vals_ev vals 2 = p1 a0s path envv rdraw inp ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
      (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2409c) M (seg_rom RSEGS)) model0) KA.

  Lemma oom_seg1 : forall KA KBb KBm,
    open_err_branch KA -> brk_ok_branch KBb -> mmap_ok_branch KBm ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x139e0) mem0 (seg_rom RSEGS)) model0)
               (t_alt2 KA (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb)).
  Proof using rdraw fdata Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpnd Hplen Hrdr0.
    intros KA KBb KBm HKA HKBb HKBm.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    (* LPS 08b1429: RefMainEntry's lemmas take every Section variable in declaration order
       (RefMainEntry.v:46), and its environment names the launch input. *)
    pose proof (main_regs_ok sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry uid hw ME) as HR.
    pose proof (main_know_ok sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry uid hw ME) as HK.
    change (E0 sp0 a0s path envv rdraw tid regs0 inp) with (ENV (vals0 sp0 a0s path envv rdraw tid regs0 inp)) in HR, HK.
    set (vals := vals0 sp0 a0s path envv rdraw tid regs0 inp) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals2_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 a0s path envv rdraw inp) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 a0s path envv rdraw inp) by reflexivity.
    assert (P3 : vals_ev vals 3 = auxvp sp0 a0s path envv) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    destruct (main_str sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry uid hw ME 1%nat ltac:(lia))
      as (Sr & Slo & Shi & Slen & Send).
    cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 a0s path envv rdraw inp) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM. unfold p1. rewrite (rdn_mem_denot_above RSEGS (ENV vals) mem0 _ 0%nat 0x58000);
        [exact Sr | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia
        | pose proof (u64_range (cat_argv_ptr (ed_top rdraw) [a0s; path] envv (in_execfn inp) 1)); lia]. }
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
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2.
      (* LPS 08b1429: the openat path read also states the string ends below TASK_SIZE; the
         launch's argv strings end at or below 2^47 ([RefMainEntry.main_str]'s last conjunct). *)
      split; [| exact Sr'].
      cbn [nth] in Send. replace (2 ^ 47)%Z with TASK_SIZE in Send by reflexivity.
      unfold p1. unfold TASK_SIZE in *. lia.
    - exact Hpne.
    - exact Hpnd.
    - exact path_ndd.
    - exact path_nsl.
    - rewrite m0_fs. exact Hfile.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x24098 + 4)%Z with 0x2409c%Z.
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
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x58000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x24098 + 4)%Z with 0x2409c%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0)
        with (model1g (FdFile path (Z_to_bv 64 0))).
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      assert (HA : above_sp0 M).
      { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x58000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
      eapply (oom_seg2 (FdFile path (Z_to_bv 64 0)) KBb KBm vals); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem oom_pilot : forall KA KBb KBm,
    open_err_branch KA -> brk_ok_branch KBb -> mmap_ok_branch KBm ->
    realizes RSEGS
      (mkCfg (mkst regs0 (Z_to_bv 64 0x139e0) mem0 (seg_rom RSEGS))
             (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; path] envv fs0 stdin0))))
      (t_alt2 KA (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb)).
  Proof using rdraw fdata Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpnd Hplen Hrdr0. intros. apply oom_seg1; assumption. Qed.

End Pilot.
