(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require MmapBase.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame S8LibStdioCall
  Spec LibWritev RefNodes S8ExitBase S8StdioDefs S8Exit RefMemcpyLib S8MemcpyBase S8Memcpy
  S8Startup S8MainEntry Hoare MemSplit ArgvSpan.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import S8PilotOOM_defs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require SymDriveKN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Tactic Notation "run_block" constr(scr) constr(NX) := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.SymDriveKN.run_block_gen_kn FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.SymDriveKN.run_block_gen_kn FUEL STOPS scr NX true.


Definition LIM : Z := source_alloc_limit.

Section Pilot.
  (* over the launch input (argv = [a0s; path] by Hav), the ruled VLAUNCH + LOK, and
     the launch's channel reader, as S0OpenFail. The start model is Run.init_config's (with_vdso over init_model);
     fs0 names its file system; after the openat the model is model0 with fd 3 inserted (model1g), so its ledger
     is init_model's: the image's segments PLUS the vDSO pair (State.init_reserved). *)
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable inp : ProcInput.
  Local Notation envv := (in_envp inp) (only parsing).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.
  Variable fdata : list byte.
  Hypothesis Hav : in_argv inp = [a0s; path].
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hcr : in_channel_reader inp = true.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup (in_fs inp) path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : path <> dot_path.
  Hypothesis Hplen : (length path <= 4095)%nat.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).

  Definition fds0 : list (word * FdEntry) :=
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
     (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  Definition model0 : Model :=
    with_tid tid (with_vdso (vdso_run_init (ed_vdso rdraw))
                   (init_model (segments_reserved RSEGS) brk mbase sp0 LIM inp)).
  Definition fs0 : Fs := m_fs model0.
  (* the launch's reserved ledger (the image's segments, then the vDSO pair). *)
  Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition model1g (fd3 : FdEntry) : Model := with_fds (fds1g fd3) model0.

  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.


  Lemma m1_fs : forall fd3, m_fs (model1g fd3) = fs0.
  Proof. intros. reflexivity. Qed.
  Lemma m1_rdr : forall fd3, m_channel_reader (model1g fd3) = true.
  Proof. intros. exact Hcr. Qed.
  Lemma m0_fds : m_fds model0 = fds0.
  Proof. reflexivity. Qed.
  Lemma m0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.

  Lemma fds1_2 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. intros. reflexivity. Qed.

  Lemma above_sp0_block : forall vals log M,
    vals_ev vals 0 = sp0 -> log_below_b 0 0x94000 log = true -> above_sp0 M ->
    above_sp0 (mem_denot (ENV vals) M log).
  Proof.
    intros vals log M P0 Hb HA a Ha. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    rewrite (mem_denot_above (ENV vals) M log 0%nat 0x94000 a Hb); [apply HA; exact Ha | | |];
      cbn [ev ENV]; rewrite ?P0; lia.
  Qed.

  Lemma alloc_fd_fds0 : alloc_fd fds0 = Z_to_bv 64 3.
  Proof. exact (alloc_fd_init _ _ _). Qed.
  Lemma fd_lookup_fds0_3 : fd_lookup fds0 (Z_to_bv 64 3) = None.
  Proof. reflexivity. Qed.

  Ltac refresh_above vals P0 HA :=
    lazymatch type of HA with above_sp0 ?Mo =>
      lazymatch goal with EQ : ?Mn = mem_denot _ Mo ?log |- _ =>
        let HA' := fresh "HA" in
        pose proof (above_sp0_block vals log Mo P0 ltac:(vm_compute; reflexivity) HA) as HA';
        rewrite <- EQ in HA'; clear HA EQ; rename HA' into HA
      end
    end.
  Ltac name_state R M :=
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into R; rename Mn into M end.


  Lemma msg_oom_img {RCa1 : RunCtx}  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 0x10320) 19 = Some msg_oom.
  Proof. vm_compute. reflexivity. Qed.

  Lemma oom_seg4 : forall fd3 vals R M,
    length vals = 73%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srF0 R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M knE ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x1adbc) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) (model1g fd3)) (t_die msg_oom fs0).
  Proof.
    intros fd3 vals R M HL P0 HR HK.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    run_block scr0 73%nat.
    unfold t_die, W.
    apply (stdio_call_sound vals (blobs_ev (blobs0 a0s path)) srF knF R M (model1g fd3) resG [] msg_oom
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n srF knF) HL) resG_eq));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resG];
      change (Z.of_nat (length msg_oom)) with 19%Z; change (Z.of_nat (@length byte [])) with 0%Z.
    - cbn [edenot]. lia.
    - cbn [edenot]. lia.
    - cbn [edenot]. lit_u. reflexivity.
    - lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
      rewrite (u_small (bv_unsigned sp0 + -192)) by lia. lit_u. lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
      rewrite (u_small (bv_unsigned sp0 + -192)) by lia. lit_u. lit_u. lia.
    - cbn [edenot]. lit_u. lit_u. lia.
    - cbn [edenot]. lit_u. unfold TASK_SIZE. lia.
    - cbn [edenot]. lit_u. lit_u. unfold TASK_SIZE. lia.
    - reflexivity.
    - cbn [edenot]. change (length msg_oom) with 19%nat.
      rewrite (kimg_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) _ knF ltac:(let i := kidx knF (is_kimg_cov 0x10320 19) in exact i)
                 _ _ 0x10320 19 HK eq_refl) by (cbn; lia).
      apply msg_oom_img.
    - apply fds1_2.
    - apply m1_rdr.
    - reflexivity.
    - reflexivity.
    - apply t_exit_has_nil.
    -
      clear HR HK R M. intros R M HR HK.
      change (sc_sr resG) with srG0 in HR. change (sc_kn resG) with knG0 in HK. change (sc_ret resG) with 0x1b360%Z.
      set (vals' := vals ++ junk_vals R) in *.
      assert (HL' : length vals' = 105%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals'. clear HL P0. rename HL' into HL. rename P0' into P0.
      change (Env (vals_ev vals') (blobs_ev (blobs0 a0s path))) with (ENV vals') in HR, HK.
      run_block scr0 105%nat.
      apply (rz_conseq (run_segments RSEGS rc_inp rc_sp rc_mb) _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs (model1g fd3))))).
      2:{ rewrite m1_fs. apply exit_leaf_eq. lia. }
      apply ref_exit_Z.
      pose proof (know_nth (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ knG ltac:(let i := kidx knG (is_krange (EVar 5)) in exact i) _ HK eq_refl)
        as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
      exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x72fe0), (bv_unsigned (vals_ev vals' 5)),
             (Z_to_bv 64 0x936a8), (Z_to_bv 64 0).
      split; [|split; [reflexivity|split; [reflexivity|]]].
      + constructor.
        * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
          rewrite P0. f_equal; lia.
        * regv HR (4 : reg). reflexivity.
        * regv HR (10 : reg). reflexivity.
        * rewrite u_small by lia. lia.
        * rewrite u_small by lia. lia.
        * rewrite u_small by lia.
          pose proof (kwr_store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals') _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                        _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
          unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
          replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
        * lit_u. lia.
        * lit_u. lia.
        * lia.
        * lit_u. change (471008 - 168)%Z with 0x72f38%Z.
          krd HK 0x72f38%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
          rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
          rewrite Z_to_bv_bv_unsigned. reflexivity.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * exists (Z_to_bv 64 0x22c80). krd_solve HK.
        * left. split; krd_solve HK.
        * repeat split; krd_solve HK.
        * repeat split; krd_solve HK.
      + left. split; [reflexivity|].
        exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.






  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.

  (* RefNodes.path_at's TASK_SIZE conjunct, from the launch (as S0OpenFail). *)

  Lemma path_noslash : path_has_slash path = false.
  Proof.
    destruct Hva as (_ & _ & _ & _ & Hs). cbn [tl] in Hs. inversion Hs as [|x l Hx Hl]; subst. exact (proj1 Hx).
  Qed.
  Lemma path_nodotdot : path_eqb path dotdot_path = false.
  Proof.
    destruct Hva as (_ & _ & _ & _ & Hs). cbn [tl] in Hs. inversion Hs as [|x l Hx Hl]; subst. exact (proj2 Hx).
  Qed.








  Definition open_err_branch (KA : TSet) : Prop :=
    forall e vals R M,
      In e openat_errnos ->
      length vals = 41%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 40 = errno_ret e ->
      vals_ev vals 1 = p0 inp rdraw -> vals_ev vals 2 = p1 inp rdraw ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 40)) R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M knA ->
      (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
      realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x20b14) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0) KA.




End Pilot.
