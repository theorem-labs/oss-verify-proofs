(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require MmapBase.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame S0LibStdioCall
  Spec LibWritev RefNodes S0ExitBase S0StdioDefs S0Exit RefMemcpyLib S0MemcpyBase S0Memcpy
  S0Startup S0MainEntry Hoare MemSplit ArgvSpan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import S0PilotOOM_defs.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require SymDriveKN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Tactic Notation "run_block" constr(scr) constr(NX) := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.SymDriveKN.run_block_gen_kn FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.SymDriveKN.run_block_gen_kn FUEL STOPS scr NX true.


Definition LIM : Z := source_alloc_limit.
Lemma LIM_ge : (2 ^ 34 <= LIM)%Z.
Proof. unfold LIM. rewrite source_alloc_limit_val. apply Z.leb_le. reflexivity. Qed.

(* port727 (): knowledge minus the auxv-tail entries (S0PilotOOM_defs.drop_tail) still holds. *)
Lemma know_ok_drop_tail : forall segs E M kn, know_ok segs E M kn -> know_ok segs E M (drop_tail kn).
Proof.
  intros segs E M kn H. unfold know_ok, drop_tail in *. apply Forall_forall. intros k Hk.
  apply filter_In in Hk. destruct Hk as [Hk _]. exact (proj1 (Forall_forall _ _) H k Hk).
Qed.

Section Pilot.
  (* port727 (): over the launch input (argv = [a0s; path] by Hav), the ruled VLAUNCH + LOK, and
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
  Lemma model0_rdr : m_channel_reader model0 = true.
  Proof. exact Hcr. Qed.
  (* port727: the launch's reserved ledger (the image's segments, then the vDSO pair). *)
  Definition RES : list (word * word) := init_reserved (segments_reserved RSEGS) mbase sp0 (in_kernel inp).
  Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition model1g (fd3 : FdEntry) : Model := with_fds (fds1g fd3) model0.

  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

  (* port727 (): the auxv tail (S0MainEntry.kn_auxv_tail: the kernel's words past AT_EXECFN) holds
     in any later state whose env keeps sp0 / auxvp at EVar 0 / 3 and whose memory agrees with mem0 above sp0: the
     tail lies above sp0 (auxvp_u), and the entry's own facts carry it there. *)
  Lemma tail_transfer : forall vals M,
    vals_ev vals 0 = sp0 -> vals_ev vals 3 = auxvp sp0 inp -> above_sp0 M ->
    know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M (kn_auxv_tail (kb_rseq (in_kernel inp))).
  Proof.
    intros vals M P0 P3 HA.
    pose proof (main_know_ok_tail sp0 a0s path inp mbase brk rdraw tid regs0 mem0 Hav Hva Hvl Hlau Hvsp Htid ME)
      as HK0.
    apply know_ok_app in HK0. destruct HK0 as [_ HT].
    destruct (auxvp_u sp0 inp mbase brk rdraw Hvl Hlau Hvsp) as [Hau _].
    set (E := E0 sp0 a0s path inp rdraw tid regs0) in HT.
    assert (A0 : edenot (ENV vals) (EVar 0) = edenot E (EVar 0)) by exact P0.
    assert (A3 : edenot (ENV vals) (EVar 3) = edenot E (EVar 3)) by exact P3.
    assert (U3 : (bv_unsigned sp0 <= bv_unsigned (edenot E (EVar 3)))%Z)
      by (change (edenot E (EVar 3)) with (auxvp sp0 inp); rewrite Hau; lia).
    unfold know_ok in *. apply Forall_forall. intros K HIn.
    pose proof (proj1 (Forall_forall _ _) HT K HIn) as HKo. clear HT.
    destruct (kb_rseq (in_kernel inp)); cbn [kn_auxv_tail In] in HIn;
      repeat destruct HIn as [<- | HIn]; try contradiction.
    all: cbn [kentry_ok] in HKo |- *.
    all: first
      [ unfold estart in *; cbn [a_base a_off] in *; rewrite A0, A3; exact HKo
      | destruct HKo as (Hw & Hf & Hr); split; [exact Hw|];
        pose proof (flat_u _ _ _ Hf) as Hu;
        unfold flat, estart, adenot in *; cbn [a_base a_off] in *; rewrite A3;
        split; [exact Hf|];
        etransitivity; [|exact Hr];
        apply rdn_agree; intros j Hj; apply HA;
        rewrite Hu; rewrite u_small by lia; lia ].
  Qed.


  Lemma m1_vmmaps : forall fd3, m_vmmaps (model1g fd3) = mkVmMapsFull RES [] [] brk brk LIM mbase sp0.
  Proof. intros. reflexivity. Qed.
  Lemma m1_fs : forall fd3, m_fs (model1g fd3) = fs0.
  Proof. intros. reflexivity. Qed.
  Lemma m1_rdr : forall fd3, m_channel_reader (model1g fd3) = true.
  Proof. intros. exact Hcr. Qed.
  Lemma fs0_inp : fs0 = in_fs inp.
  Proof. reflexivity. Qed.
  Lemma m0_fds : m_fds model0 = fds0.
  Proof. reflexivity. Qed.
  Lemma m0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.

  Lemma fds1_2 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. intros. reflexivity. Qed.

  Lemma above_sp0_block : forall vals log M,
    vals_ev vals 0 = sp0 -> log_below_b 0 0x51000 log = true -> above_sp0 M ->
    above_sp0 (mem_denot (ENV vals) M log).
  Proof.
    intros vals log M P0 Hb HA a Ha. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    rewrite (mem_denot_above (ENV vals) M log 0%nat 0x51000 a Hb); [apply HA; exact Ha | | |];
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


  Lemma msg_oom_img {RCa1 : RunCtx}  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 0x10358) 19 = Some msg_oom.
  Proof. vm_compute. reflexivity. Qed.

  Lemma oom_seg4 : forall fd3 vals R M,
    length vals = 73%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srF0 R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M knE ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x17800) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) (model1g fd3)) (t_die msg_oom fs0).
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
      rewrite (kimg_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) _ knF ltac:(let i := kidx knF (is_kimg_cov 0x10358 19) in exact i)
                 _ _ 0x10358 19 HK eq_refl) by (cbn; lia).
      apply msg_oom_img.
    - apply fds1_2.
    - apply m1_rdr.
    - reflexivity.
    - reflexivity.
    - apply t_exit_has_nil.
    -
      clear HR HK R M. intros R M HR HK.
      change (sc_sr resG) with srG0 in HR. change (sc_kn resG) with knG0 in HK. change (sc_ret resG) with 0x17e78%Z.
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
      exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x2fb00), (bv_unsigned (vals_ev vals' 5)),
             (Z_to_bv 64 0x501d0), (Z_to_bv 64 0).
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
        * lit_u. change (195328 - 168)%Z with 0x2fa58%Z.
          krd HK 0x2fa58%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
          rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
          rewrite Z_to_bv_bv_unsigned. reflexivity.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * krd_solve HK.
        * exists (Z_to_bv 64 0x1f798). krd_solve HK.
        * left. split; krd_solve HK.
        * repeat split; krd_solve HK.
        * repeat split; krd_solve HK.
      + left. split; [reflexivity|].
        exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.


  Lemma rtop : reserved_top (segments_reserved RSEGS) = 0x51000%Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma brk_lo : (0x51000 <= bv_unsigned brk)%Z.
  Proof. pose proof (proj1 Hbrk) as H. rewrite rtop in H. exact H. Qed.
  Lemma brk_hi : (bv_unsigned brk <= 0x80030000)%Z.
  Proof. pose proof (proj1 (proj2 Hbrk)) as H. rewrite rtop, brk_aslr_max_val in H. cbn in H. lia. Qed.
  Lemma brk_al : (bv_unsigned brk mod 4096 = 0)%Z.
  Proof. exact (proj2 (proj2 Hbrk)). Qed.

  (* port727 (): the launch's ledger RES = the image's four segments ++ the vDSO pair
     (State.init_reserved). The facts the mmap and brk arms need of it: every entry is small, there are few, and
     the brk range [brk, brk + 8192 + page) misses all of it (the image segments end at 0x31000 <= brk; the pair
     lies below min (mbase, sp0 - stack_max_size), far above brk <= 0x80030000, by the launch's mmap base band). *)
  Lemma vdso_reserved_small : forall kb top,
    Forall (fun p => (bv_unsigned (snd p) <= 2 ^ 30)%Z) (vdso_reserved kb top).
  Proof.
    intros kb top. unfold vdso_reserved. cbv zeta.
    match goal with |- context [if ?c then _ else _] => destruct c end; [constructor|].
    pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
    unfold vdso_vvar_pages, page_size.
    repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
  Qed.
  Lemma Ers : segments_reserved RSEGS = [(Z_to_bv 64 65536, Z_to_bv 64 12288); (Z_to_bv 64 77824, Z_to_bv 64 45056);
                                         (Z_to_bv 64 122880, Z_to_bv 64 4096); (Z_to_bv 64 126976, Z_to_bv 64 204800)].
  Proof. vm_compute. reflexivity. Qed.
  Lemma RES_small : Forall (fun p => (bv_unsigned (snd p) <= 2 ^ 30)%Z) RES.
  Proof.
    unfold RES, init_reserved. apply Forall_app. split; [|apply vdso_reserved_small].
    rewrite Ers. repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
  Qed.
  Lemma RES_len : (Z.of_nat (length RES) <= 40000)%Z.
  Proof.
    unfold RES, init_reserved. rewrite length_app, Ers.
    match goal with |- context [length (vdso_reserved ?k ?t)] =>
      assert (length (vdso_reserved k t) <= 2)%nat
        by (unfold vdso_reserved; cbv zeta;
            match goal with |- context [if ?c then _ else _] => destruct c end; cbn [length]; lia) end.
    cbn [length]. lia.
  Qed.
  Lemma mbase_lo : (mmap_base_min <= bv_unsigned mbase)%Z.
  Proof.
    destruct Hlau as (_ & _ & Hb).
    exact (proj1 (MmapBase.valid_launch_base_sv48_in_band _ _ Hb)).
  Qed.
  Lemma RES_free_brk : region_free RES brk (Z_to_bv 64 (8192 + page_size)) = true.
  Proof.
    unfold RES, init_reserved. rewrite region_free_app. apply andb_true_intro. split.
    - apply region_free_above_top. rewrite rtop. exact brk_lo.
    - apply region_free_intro. intros b s Hin.
      pose proof mbase_lo as Hmb. unfold mmap_base_min in Hmb.
      pose proof (vdso_len_bounds (in_kernel inp)) as Hvb. unfold page_size in Hvb.
      pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
      pose proof (u64_range mbase) as Hmr. pose proof brk_hi as Hbh.
      set (x := Z.min (bv_unsigned mbase) (bv_unsigned sp0 - stack_max_size)) in Hin.
      assert (Hxlo : (0x154555557000 <= x)%Z) by (unfold x, stack_max_size; lia).
      assert (Hxhi : (x < 2 ^ 64)%Z) by (unfold x; lia).
      pose proof (Z.mul_succ_div_gt x 4096 ltac:(lia)) as Hg.
      pose proof (Z.mul_div_le x 4096 ltac:(lia)) as Hl.
      destruct (vdso_reserved_above (in_kernel inp) (page_round_down_Z x) b s
                  ltac:(unfold page_round_down_Z, page_size, two_pow_64; lia) Hin) as [Hb1 Hb2].
      unfold page_round_down_Z, page_size in Hb1.
      unfold page_size. left. rewrite u_small by lia. lia.
  Qed.
  Lemma brk_grow_ok_m1 : forall fd3,
    Mmap.brk_grow_ok (model1g fd3) (Z_to_bv 64 (bv_unsigned brk + 8192)) (Z_to_bv 64 (bv_unsigned brk + 8192))
    = true.
  Proof.
    intros fd3. pose proof brk_lo. pose proof brk_hi. pose proof LIM_ge.
    apply (brk_grow_ok_aligned_intro (model1g fd3) 8192); rewrite ?m1_vmmaps; cbn [vm_brk vm_reserved vm_maps vm_limit].
    - exact brk_al.
    - reflexivity.
    - lia.
    - lia.
    - first [rewrite alloc_ceiling_val; lia | unfold AsanCeil.alloc_ceiling; lia].
    - apply init_sp_ok_of_valid_sp. exact Hvsp.
    - rewrite app_nil_r. exact RES_free_brk.
    - rewrite vm_backing_used_simple by reflexivity. rewrite ?m1_vmmaps. cbn. lia.
  Qed.

  Lemma ugly_b_sem : forall vals, vals_ev vals 72 = brk ->
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

  Lemma brk_ne_req : forall vals, vals_ev vals 72 = brk ->
    branch_taken BC_NE (edenot (ENV vals) b_expr) (edenot (ENV vals) (EAlu ALU_ADD b_expr (ELit 8192))) = true.
  Proof.
    intros vals P70. cbn [edenot b_expr ev ENV]. rewrite P70, alu_add. unfold v_add.
    cbn [branch_taken]. unfold bv_eqb. pose proof brk_hi. pose proof (u64_range brk).
    change (bv_unsigned (Z_to_bv 64 8192)) with 8192%Z. rewrite u_small by lia.
    apply Bool.negb_true_iff. apply Z.eqb_neq. lia.
  Qed.

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.

  (* port727 (): RefNodes.path_at's TASK_SIZE conjunct, from the launch (as S0OpenFail). *)
  Lemma path_below_task_size_lt :
    (bv_unsigned (p1 inp rdraw) + Z.of_nat (length path) < TASK_SIZE)%Z.
  Proof.
    pose proof (argv_str_below_task_size inp mbase sp0 brk rdraw 1%nat Hlau ltac:(rewrite Hav; cbn; lia)) as H.
    unfold p1. rewrite Hav in H |- *. cbn [nth] in H. lia.
  Qed.

  Lemma path_noslash : path_has_slash path = false.
  Proof.
    destruct Hva as (_ & _ & _ & _ & Hs). cbn [tl] in Hs. inversion Hs as [|x l Hx Hl]; subst. exact (proj1 Hx).
  Qed.
  Lemma path_nodotdot : path_eqb path dotdot_path = false.
  Proof.
    destruct Hva as (_ & _ & _ & _ & Hs). cbn [tl] in Hs. inversion Hs as [|x l Hx Hl]; subst. exact (proj2 Hx).
  Qed.


  Definition mmap_ok_branch_g (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M (hint a : word),
      length vals = 73%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 72 = brk ->
      vals_ev vals 1 = p0 inp rdraw -> vals_ev vals 2 = p1 inp rdraw ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) srE R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M knE -> above_sp0 M ->
      grant_ok_na hint (model1g fd3) a 8192 = true ->
      realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst (regupd R 10 a) (Z_to_bv 64 0x17800)
                                    (unfill a (Z_to_bv 64 8192) M) (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)))
                              (noaccess_model a (Z_to_bv 64 8192) (model1g fd3))) KB.
  Definition mmap_ok_branch : TSet -> Prop := mmap_ok_branch_g (FdFile path (Z_to_bv 64 0)).

  Lemma oom_seg3 : forall fd3 KB vals R M,
    mmap_ok_branch_g fd3 KB ->
    length vals = 73%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 72 = brk ->
    vals_ev vals 1 = p0 inp rdraw -> vals_ev vals 2 = p1 inp rdraw -> vals_ev vals 5 = tid ->
    regs_ok (ENV vals) srE0 R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M knD2 -> above_sp0 M ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x166ec) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) (model1g fd3))
               (t_alt2 (t_die msg_oom fs0) KB).
  Proof.
    intros fd3 KB vals R M HKB HL P0 P70 P1 P2 P5t HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    run_block_keep scrE 73%nat.
    { unfold sc_denot. apply brk_ne_req. exact P70. }
    refresh_above vals P0 HA. clear R M. name_state R M.
    eapply (rz_mmap_noaccess (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ _ (model1g fd3) ECALLW 8192).
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
    - (* port727 (): the NULL hint is never declined (place_declined_b's first conjunct). *)
      regv HR (10 : reg). reflexivity.
    -
      change (page_round_up_Z 8192) with 8192%Z.
      apply grant_exists_na; rewrite ?m1_vmmaps; cbn [vm_reserved vm_maps vm_limit].
      + apply init_sp_ok_of_valid_sp. exact Hvsp.
      + lia.
      + reflexivity.
      + rewrite app_nil_r. apply RES_small.
      + rewrite app_nil_r. pose proof RES_len. lia.
    -
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x177fc + 4)%Z with 0x17800%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?R =>
        pose proof (regs_set_a0 E sr R (errno_ret ENOMEM) (ELit (2 ^ 64 - 12)) HR
                      ltac:(apply bv_eq; reflexivity)) as HR2 end.
      eapply (oom_seg4 fd3 vals); [exact HL | exact P0 | exact HR2 | exact HK].
    -
      intros a Hg. rewrite v_addi_pc4 by lia. change (0x177fc + 4)%Z with 0x17800%Z.
      change (page_round_up_Z 8192) with 8192%Z in Hg |- *.
      eapply (HKB vals); try eassumption.
  Qed.


  Definition brk_ok_branch_g (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 73%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 72 = brk ->
      vals_ev vals 1 = p0 inp rdraw -> vals_ev vals 2 = p1 inp rdraw ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) srD2 R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M knD2 -> above_sp0 M ->
      realizes (run_segments RSEGS rc_inp rc_sp rc_mb)
        (mkCfg (mkst (regupd R 10 (Z_to_bv 64 (bv_unsigned brk + 8192))) (Z_to_bv 64 0x166ec)
                     (zfill brk (Z_to_bv 64 8192) M) (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)))
               (* port727: the grown model as RefNodes.rz_brk_grow gives it (over model1g's ledger). *)
               (with_vmmaps (mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk
                                          (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                            (model1g fd3))) KB.
  Definition brk_ok_branch : TSet -> Prop := brk_ok_branch_g (FdFile path (Z_to_bv 64 0)).

  (* port727 (): after run D the two kernels' runs have joined (srD / knD, runD_rseq_agrees):
     the brk-grow step, as before. *)
  Lemma oom_seg2b : forall fd3 KBb KBm vals2 R M,
    brk_ok_branch_g fd3 KBb -> mmap_ok_branch_g fd3 KBm ->
    length vals2 = 73%nat -> vals_ev vals2 0 = sp0 -> vals_ev vals2 72 = brk ->
    vals_ev vals2 1 = p0 inp rdraw -> vals_ev vals2 2 = p1 inp rdraw -> vals_ev vals2 5 = tid ->
    regs_ok (ENV vals2) srD R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals2) M knD -> above_sp0 M ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x166e8) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) (model1g fd3))
               (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb).
  Proof.
    intros fd3 KBb KBm vals2 R M HKBb HKBm HL P0 P70 P1 P2 P5t HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (regs_ok_esub (ENV vals2) ugly_b b_expr _ _ (ugly_b_sem vals2 P70) HR) as HR2.
    pose proof (know_ok_ksub (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals2) _ ugly_b b_expr _ (ugly_b_sem vals2 P70) HK) as HK2.
    clear HR HK. rename HR2 into HR. rename HK2 into HK.
    lazymatch type of HR with regs_ok _ ?sr _ => let sr' := eval vm_compute in sr in change sr with sr' in HR end.
    lazymatch type of HK with know_ok _ _ _ ?kn => let kn' := eval vm_compute in kn in change kn with kn' in HK end.
    eapply (rz_brk_grow (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ _ (model1g fd3) ECALLW 8192).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - rewrite m1_vmmaps; cbn [vm_brk]. exact brk_al.
    - reflexivity.
    - lia.
    - rewrite m1_vmmaps; cbn [vm_brk]. pose proof brk_lo. lia.
    - rewrite m1_vmmaps; cbn [vm_brk]. pose proof brk_hi. lia.
    - rewrite m1_vmmaps; cbn [vm_brk vm_start_brk]. lia.
    - rewrite m1_vmmaps; cbn [vm_brk]. regv HR (10 : reg). rewrite edenot_add_lit.
      unfold adenot, v_addi. cbn [a_base a_off edenot b_expr ev ENV]. rewrite P70. reflexivity.
    - rewrite m1_vmmaps. cbn [vm_brk]. apply brk_grow_ok_m1.
    -
      rewrite v_addi_pc4 by lia. change (0x166e8 + 4)%Z with 0x166ec%Z.
      rewrite m1_vmmaps; cbn [vm_brk].
      pose proof (regs_set_a0 (ENV vals2) _ _ brk b_expr HR ltac:(cbn [edenot b_expr ev ENV]; exact P70)) as HR2.
      eapply (oom_seg3 fd3 KBm vals2); try eassumption.
    -
      rewrite v_addi_pc4 by lia. change (0x166e8 + 4)%Z with 0x166ec%Z.
      rewrite m1_vmmaps; cbn [vm_brk vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base vm_init_sp].
      eapply (HKBb vals2); try eassumption.
  Qed.

  (* port727 (): run C (the rest of get_random_secret's auxv scan, over this kernel's tail), the brk
     query and run D. One script for both kernels (rs = CONFIG_RSEQ, `all:`); it ends where they join (oom_seg2b). *)
  Lemma oom_seg2c : forall rs fd3 KBb KBm vals1 R M,
    brk_ok_branch_g fd3 KBb -> mmap_ok_branch_g fd3 KBm ->
    length vals1 = 72%nat -> vals_ev vals1 0 = sp0 ->
    vals_ev vals1 1 = p0 inp rdraw -> vals_ev vals1 2 = p1 inp rdraw -> vals_ev vals1 5 = tid ->
    regs_ok (ENV vals1) srC0 R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals1) M (knC0 rs) -> above_sp0 M ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x165fc) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) (model1g fd3))
               (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb).
  Proof.
    intros rs fd3 KBb KBm vals1 R M HKBb HKBm HL P0 P1 P2 P5t HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    destruct rs; unfold knC0 in HK.
    all: run_block_keep scr0 72%nat.
    all: refresh_above vals1 P0 HA; clear R M; name_state R M.
    all: eapply (rz_brk_query (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ _ (model1g fd3) ECALLW);
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | reflexivity | reflexivity
      | regv HR (17 : reg); reflexivity | regv HR (10 : reg); reflexivity | ].
    all: rewrite v_addi_pc4 by lia; change (0x166c4 + 4)%Z with 0x166c8%Z.
    all: rewrite m1_vmmaps; cbn [vm_brk].
    all: lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals1 [brk] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    all: lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know (run_segments RSEGS rc_inp rc_sp rc_mb) vals1 [brk] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
    all: clear HR HK.
    all: set (vals2 := vals1 ++ [brk]) in *.
    all: assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
    all: assert (P0' : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    all: assert (P70 : vals_ev vals2 72 = brk)
      by (subst vals2; rewrite <- HL; rewrite <- (Nat.add_0_r (length vals1)); rewrite vals_ev_app_r; reflexivity).
    all: assert (P1' : vals_ev vals2 1 = p0 inp rdraw)
      by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    all: assert (P2' : vals_ev vals2 2 = p1 inp rdraw)
      by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    all: assert (P5' : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
    all: clearbody vals2; clear HL P0 P1 P2 P5t; rename HL2 into HL; rename P0' into P0; rename P1' into P1;
      rename P2' into P2; rename P5' into P5t.
    all: change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR2, HK2.
    all: pose proof (regs_set_a0 (ENV vals2) _ _ brk b_expr HR2 ltac:(cbn [edenot b_expr ev ENV]; exact P70)) as HR.
    all: clear HR2.
    all: lazymatch type of HK2 with know_ok _ _ ?Mc ?kn0 =>
      assert (HK : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals2) Mc (KAlign b_expr 4096 :: KRange b_expr 0x51000 0x80030000 :: kn0))
        by (apply know_ok_cons;
            [ apply kalign_intro; [lia|]; cbn [edenot b_expr ev ENV]; rewrite P70; exact brk_al
            | apply know_ok_cons;
              [ apply krange_intro; cbn [edenot b_expr ev ENV]; rewrite P70; pose proof brk_lo; pose proof brk_hi; lia
              | exact HK2 ] ])
    end.
    all: clear HK2.
    all: run_block_keep scr0 73%nat.
    all: refresh_above vals2 P0 HA; clear R M; name_state R M.
    all: pose proof (know_ok_drop_tail _ _ _ _ HK) as HK3; clear HK.
    all: lazymatch type of HK3 with know_ok _ _ _ ?kn =>
      let kn' := eval vm_compute in kn in change kn with kn' in HK3 end.
    all: eapply (oom_seg2b _ _ _ vals2); eassumption.
  Qed.

  Lemma oom_seg2 : forall fd3 KBb KBm vals R M,
    brk_ok_branch_g fd3 KBb -> mmap_ok_branch_g fd3 KBm ->
    length vals = 40%nat -> vals_ev vals 0 = sp0 ->
    vals_ev vals 1 = p0 inp rdraw -> vals_ev vals 2 = p1 inp rdraw -> vals_ev vals 3 = auxvp sp0 inp ->
    vals_ev vals 5 = tid ->
    regs_ok (ENV vals) srB0 R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M knA -> above_sp0 M ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x1d62c) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) (model1g fd3))
               (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb).
  Proof.
    intros fd3 KBb KBm vals R M HKBb HKBm HL P0 P1 P2 P3 P5t HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    run_block_keep scr0 40%nat.
    refresh_above vals P0 HA. clear R M. name_state R M.
    pose proof (know_nth (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ knB ltac:(let i := kidx knB (is_krange (EVar 4)) in exact i) _ HK eq_refl)
      as Krnd; cbn [kentry_ok edenot ev ENV] in Krnd.
    pose proof (know_nth (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ knB ltac:(let i := kidx knB (is_kdisj (EVar 0) (EVar 4)) in exact i) _ HK eq_refl)
      as Kdj; cbn [kentry_ok] in Kdj; unfold estart in Kdj; cbn [a_base a_off edenot ev ENV] in Kdj; rewrite P0 in Kdj.
    krdv HK 4%nat 8%Z 8%nat Hrd8.
    { apply flat_intro; cbn [edenot ev ENV]; lia. }
    pose proof (kwr_store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-384) 8) in exact i)
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
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x165fc)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x165fc) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit).
    assert (G11 : getr R 11 = src) by (regv HR (11:reg); subst src; apply edenot_add_lit).
    assert (G12 : getr R 12 = Z_to_bv 64 8) by (regv HR (12:reg); reflexivity).
    destruct (ref_memcpy M dst src 8 _ (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) MC R (Z_to_bv 64 0x165fc) RT G1 G10 G11 G12)
      as (R2 & Hms & Hkeep). clear RT G1 G10 G11 G12.
    replace (Z_to_bv 64 118020) with (0x1cd04 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    assert (HA' : above_sp0 (wbytes M dst (word_to_le_bytes 8 (vals_ev vals 7)))).
    { intros a Ha. rewrite wbytes_outside; [apply HA; exact Ha | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; right; lia]. }
    clear HA. rename HA' into HA.
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr _ R2 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep
                    callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    lazymatch type of HK with know_ok _ ?E ?M0 ?kn =>
      let c := eval vm_compute in (carry [mc_store] kn []) in
      lazymatch c with (?kn', ?scs, ?hs) =>
        pose proof (know_after_store (run_segments RSEGS rc_inp rc_sp rc_mb) E M0 kn (SA (EVar 0) (-384)) 8 (EVar 7) (word_to_le_bytes 8 (vals_ev vals 7))
                      kn' scs hs ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                      ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia) eq_refl) as HK2
      end end.
    clear HK. subst dst.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know (run_segments RSEGS rc_inp rc_sp rc_mb) vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 72%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (P0' : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (P1' : vals_ev vals1 1 = p0 inp rdraw) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    assert (P2' : vals_ev vals1 2 = p1 inp rdraw) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (P5' : vals_ev vals1 5 = tid) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
    assert (P3' : vals_ev vals1 3 = auxvp sp0 inp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
    clearbody vals1. clear HL P0 P1 P2 P3 P5t. rename HL1 into HL. rename P0' into P0. rename P1' into P1. rename P2' into P2.
    rename P3' into P3. rename P5' into P5t.
    change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path))) with (ENV vals1) in HR, HK.
    (* port727 (): the scan goes on past AT_RANDOM to the vector's 0 key, into the kernel's tail:
       add the tail (above sp0, never written: tail_transfer) and go on per kernel (oom_seg2c). *)
    pose proof (tail_transfer vals1 _ P0 P3 HA) as HT.
    pose proof (proj2 (know_ok_app _ _ _ _ _) (conj HK HT)) as HK'. clear HK HT.
    eapply (oom_seg2c (kb_rseq (in_kernel inp)) fd3 KBb KBm vals1); eassumption.
  Qed.


  Definition open_err_branch (KA : TSet) : Prop :=
    forall e vals R M,
      In e openat_errnos ->
      length vals = 41%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 40 = errno_ret e ->
      vals_ev vals 1 = p0 inp rdraw -> vals_ev vals 2 = p1 inp rdraw ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 40)) R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M knA ->
      (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
      realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x1d62c) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0) KA.

  Lemma oom_seg1 : forall KA KBb KBm,
    open_err_branch KA -> brk_ok_branch KBb -> mmap_ok_branch KBm ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs0 (Z_to_bv 64 0x13d50) mem0 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0)
               (t_alt2 KA (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb)).
  Proof.
    intros KA KBb KBm HKA HKBb HKBm.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s path inp mbase rdraw tid regs0 mem0 Hav Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path inp mbase brk rdraw tid regs0 mem0 Hav Hva Hvl Hlau Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path inp rdraw tid regs0) with (ENV (vals0 sp0 inp rdraw tid regs0)) in HR, HK.
    set (vals := vals0 sp0 inp rdraw tid regs0) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 inp rdraw) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 inp rdraw) by reflexivity.
    assert (P3 : vals_ev vals 3 = auxvp sp0 inp) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    destruct (main_str sp0 a0s path inp mbase brk rdraw tid regs0 mem0 Hav Hva Hvl Hlau Hvsp ME 1%nat ltac:(lia))
      as (Sr & Slo & Shi & Slen).
    rewrite Hav in Sr, Slo, Shi, Slen. cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    run_block_keep scr0 40%nat.
    assert (Sr' : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (p1 inp rdraw) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM. unfold p1. rewrite Hav. rewrite (rdn_mem_denot_above (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) mem0 _ 0%nat 0x51000);
        [exact Sr | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia
        | match goal with |- context [cat_argv_ptr ?t ?av ?ev ?ef ?k] =>
            pose proof (u64_range (cat_argv_ptr t av ev ef k)) end; lia]. }
    eapply (rz_openat_file (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - split; [exact Hplen|]. split; [apply path_nonul|].
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2.
      split; [exact path_below_task_size_lt | exact Sr'].
    - exact Hpne.
    - exact Hpnd.
    - apply path_noslash.
    - apply path_nodotdot.
    - rewrite m0_fs. exact Hfile.
    -
      intros e He. rewrite v_addi_pc4 by lia. change (0x1d628 + 4)%Z with 0x1d62c%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know (run_segments RSEGS rc_inp rc_sp rc_mb) vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
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
      + intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x51000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    -
      rewrite v_addi_pc4 by lia. change (0x1d628 + 4)%Z with 0x1d62c%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0)
        with (model1g (FdFile path (Z_to_bv 64 0))).
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      assert (HA : above_sp0 M).
      { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x51000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
      eapply (oom_seg2 (FdFile path (Z_to_bv 64 0)) KBb KBm vals); try eassumption.
  Qed.


  Theorem oom_pilot : forall KA KBb KBm,
    open_err_branch KA -> brk_ok_branch KBb -> mmap_ok_branch KBm ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb)
      (mkCfg (mkst regs0 (Z_to_bv 64 0x13d50) mem0 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)))
             (with_tid tid (with_vdso (vdso_run_init (ed_vdso rdraw))
                              (init_model (segments_reserved RSEGS) brk mbase sp0 LIM inp))))
      (t_alt2 KA (t_alt2 (t_alt2 (t_die msg_oom fs0) KBm) KBb)).
  Proof. intros. apply oom_seg1; assumption. Qed.

End Pilot.
