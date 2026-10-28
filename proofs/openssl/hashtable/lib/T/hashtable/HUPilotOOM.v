(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame HULibStdioCall
  Spec LibWritev RefNodes HUExitBase HUStdioDefs HUExit RefMemcpyLib HUMemcpyBase HUMemcpy
  HUStartupDefs HUMainEntryDefs Hoare MemSplit ExistsRun RefNodesEx PhaseG RefNodesG SymXfer.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUPilotOOM_defs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Export H0Lim.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
(* [comment removed for export] *)
Tactic Notation "gg_block" constr(scr) constr(NX) := gg_block_gen FUEL STOPS scr NX false.
Tactic Notation "gg_block_keep" constr(scr) constr(NX) := gg_block_gen FUEL STOPS scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section Pilot.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.        (* [comment removed for export] *)
  Variable rdraw : EntryDraw. (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Variable lim : Z.                              (* [comment removed for export] *)
  Hypothesis lim_ge : (LIM <= lim)%Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  (* [comment removed for export] *)
  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path rdraw)).
  Definition valsP : list word := vals0 sp0 a0s path envv tid regs0 ++ [rndw0 rdraw; rndw1 rdraw; can rdraw].
  Hypothesis HR0 : regs_ok (ENV valsP) sr_main regs0.
  Hypothesis HK0 : know_ok RSEGS (ENV valsP) mem0 kn_exec.
  Hypothesis Hstr : rdn RSEGS mem0 (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0]).
  Hypothesis Hstr_lo : (bv_unsigned sp0 <= bv_unsigned (p1 sp0 a0s path envv))%Z.
  Hypothesis Hstr_hi : (bv_unsigned (p1 sp0 a0s path envv) + Z.of_nat (length path) + 1 <= 0x800000000000)%Z.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpns : path_has_slash path = false.   (* [comment removed for export] *)
  Hypothesis Hpnd : path_is_dirref path = false.
  Hypothesis Hplen : (length path <= 4095)%nat.


  (* [comment removed for export] *)
  Definition fds0 : list (word * FdEntry) :=
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
     (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  (* [comment removed for export] *)
  Definition model0 : Model :=
    with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA [a0s; path] envv fs0 stdin0)).
  (* [comment removed for export] *)
  Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition model1g (fd3 : FdEntry) : Model :=
    mkModelA (fds1g fd3) (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp0) stdin0 fs0 None (Some tid) None.
  Definition fds1 : list (word * FdEntry) := fds1g (FdFile path (Z_to_bv 64 0)).
  Definition model1 : Model := model1g (FdFile path (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

  Lemma model0_eq : model0 = mkModelA fds0 (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp0)
                                     stdin0 fs0 None (Some tid) None.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma m1_vmmaps : forall fd3, m_vmmaps (model1g fd3) = mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp0.
  Proof. intros. reflexivity. Qed.
  Lemma m1_fs : forall fd3, m_fs (model1g fd3) = fs0.
  Proof. intros. reflexivity. Qed.
  Lemma m1_fds : forall fd3, m_fds (model1g fd3) = fds1g fd3.
  Proof. intros. reflexivity. Qed.
  Lemma m0_fds : m_fds model0 = fds0.
  Proof. reflexivity. Qed.
  Lemma m0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.

  Lemma fds1_2 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma above_sp0_block : forall vals log M,
    vals_ev vals 0 = sp0 -> log_below_b 0 0x354000 log = true -> above_sp0 M ->
    above_sp0 (mem_denot (ENV vals) M log).
  Proof.
    intros vals log M P0 Hb HA a Ha. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    rewrite (mem_denot_above (ENV vals) M log 0%nat 0x354000 a Hb); [apply HA; exact Ha | | |];
      cbn [ev ENV]; rewrite ?P0; lia.
  Qed.

  Lemma alloc_fd_fds0 : alloc_fd fds0 = Z_to_bv 64 3.
  Proof. exact (alloc_fd_init _ _ _). Qed.
  Lemma fd_lookup_fds0_3 : fd_lookup fds0 (Z_to_bv 64 3) = None.
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
    lazymatch goal with
    | |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into R; rename Mn into M
    | |- GG _ _ _ _ (mkCfg (mkst ?Rn _ ?Mn _) _) => rename Rn into R; rename Mn into M
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma msg_oom_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1950d) 19 = Some msg_oom.
  Proof. vm_compute. reflexivity. Qed.

  Lemma oom_seg4 : forall fd3 vals R M,
    length vals = 74%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b3e24) M (seg_rom RSEGS)) (model1g fd3)) (t_die msg_oom fs0).
  Proof.
    intros fd3 vals R M HL P0 HR HK.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    (* [comment removed for export] *)
    run_block scr0 74%nat.
    (* [comment removed for export] *)
    unfold t_die, W.
    apply (stdio_call_sound vals (blobs_ev (blobs0 a0s path rdraw)) srF knF R M (model1g fd3) resG [] msg_oom
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n srF knF) HL) resG_eq));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resG];
      change (Z.of_nat (length msg_oom)) with 19%Z; change (Z.of_nat (@length byte [])) with 0%Z.
    - cbn [edenot]. lia.
    - cbn [edenot]. lit_u. lia.   (* [comment removed for export] *)
    - cbn [edenot]. lia.
    - cbn [edenot]. lit_u. reflexivity.
    - lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
      rewrite (u_small (bv_unsigned sp0 + -192)) by lia. lit_u. lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
      rewrite (u_small (bv_unsigned sp0 + -192)) by lia. lit_u. lit_u. lia.
    - cbn [edenot]. lit_u. lit_u. lia.
    - reflexivity.
    - cbn [edenot]. change (length msg_oom) with 19%nat.
      rewrite (kimg_rdn RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kimg_cov 0x1950d 19) in exact i)
                 _ _ 0x1950d 19 HK eq_refl) by (cbn; lia).
      apply msg_oom_img.
    - apply fds1_2.
    - reflexivity.
    - reflexivity.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK R M. intros R M HR HK.
      change (sc_sr resG) with srG0 in HR. change (sc_kn resG) with knG0 in HK. change (sc_ret resG) with 0x2b5f50%Z.
      set (vals' := vals ++ junk_vals R) in *.
      assert (HL' : length vals' = 106%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals'. clear HL P0. rename HL' into HL. rename P0' into P0.
      change (Env (vals_ev vals') (blobs_ev (blobs0 a0s path rdraw))) with (ENV vals') in HR, HK.
      run_block scr0 106%nat.
      (* [comment removed for export] *)
      apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs (model1g fd3))))).
      2:{ rewrite m1_fs. apply exit_leaf_eq. lia. }
      apply ref_exit_Z.
      (* [comment removed for export] *)
      pose proof (know_nth RSEGS _ _ knG ltac:(let i := kidx knG (is_krange (EVar 5)) in exact i) _ HK eq_refl)
        as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
      exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x331ae8), (bv_unsigned (vals_ev vals' 5)),
             (Z_to_bv 64 0x3521c0), (Z_to_bv 64 0).
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
        * lit_u. change (3349224 - 168)%Z with 0x331a40%Z.
          krd HK 0x331a40%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
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

  Lemma rtop : reserved_top (segments_reserved RSEGS) = 0x354000%Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma brk_lo : (0x354000 <= bv_unsigned brk)%Z.
  Proof. pose proof (proj1 Hbrk) as H. rewrite rtop in H. exact H. Qed.
  Lemma brk_hi : (bv_unsigned brk <= 0x80354000)%Z.
  Proof. pose proof (proj1 (proj2 Hbrk)) as H. rewrite rtop, brk_aslr_max_val in H. cbn in H. lia. Qed.
  Lemma brk_al : (bv_unsigned brk mod 4096 = 0)%Z.
  Proof. exact (proj2 (proj2 Hbrk)). Qed.

  (* [comment removed for export] *)
  Lemma ugly_b_sem : forall vals, vals_ev vals 73 = brk ->
    edenot (ENV vals) ugly_b = edenot (ENV vals) b_expr.
  Proof.
    intros vals P73. cbn [edenot ugly_b b_expr ev ENV]. rewrite P73.
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
  Lemma brk_ne_req : forall vals, vals_ev vals 73 = brk ->
    branch_taken BC_NE (edenot (ENV vals) b_expr) (edenot (ENV vals) (EAlu ALU_ADD b_expr (ELit 8192))) = true.
  Proof.
    intros vals P73. cbn [edenot b_expr ev ENV]. rewrite P73, alu_add. unfold v_add.
    cbn [branch_taken]. unfold bv_eqb. pose proof brk_hi. pose proof (u64_range brk).
    change (bv_unsigned (Z_to_bv 64 8192)) with 8192%Z. rewrite u_small by lia.
    apply Bool.negb_true_iff. apply Z.eqb_neq. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mmap_ok_branch_g (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M (hint a : word),
      length vals = 74%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 73 = brk ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) srE R -> know_ok RSEGS (ENV vals) M knE -> above_sp0 M ->
      grant_ok_na hint (model1g fd3) a 8192 = true ->      (* [comment removed for export] *)
      realizes RSEGS (mkCfg (mkst (regupd R 10 a) (Z_to_bv 64 0x2b3e24)
                                    (unfill a (Z_to_bv 64 8192) M) (seg_rom RSEGS))
                              (noaccess_model a (Z_to_bv 64 8192) (model1g fd3))) KB.
  Definition mmap_ok_branch : TSet -> Prop := mmap_ok_branch_g (FdFile path (Z_to_bv 64 0)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition brk_ok_branch_G (mode : bool) (Q : config -> Prop) (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 74%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 73 = brk ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) srD2 R -> know_ok RSEGS (ENV vals) M knD2 -> above_sp0 M ->
      GG RSEGS mode Q KB
        (mkCfg (mkst (regupd R 10 (Z_to_bv 64 (bv_unsigned brk + 8192))) (Z_to_bv 64 0x2b2474)
                     (zfill brk (Z_to_bv 64 8192) M) (seg_rom RSEGS))
               (mkModelA (fds1g fd3) (mkVmMapsFull (segments_reserved RSEGS) [(brk, Z_to_bv 64 8192)] [] brk
                                            (Z_to_bv 64 (bv_unsigned brk + 8192)) lim mbase sp0)
                        stdin0 fs0 None (Some tid) None)).
  Definition brk_ok_branch_g (fd3 : FdEntry) (KB : TSet) : Prop := brk_ok_branch_G true (fun _ => True) fd3 KB.
  Definition brk_ok_branch_M (mode : bool) (Q : config -> Prop) : TSet -> Prop :=
    brk_ok_branch_G mode Q (FdFile path (Z_to_bv 64 0)).
  Definition brk_ok_branch : TSet -> Prop := brk_ok_branch_g (FdFile path (Z_to_bv 64 0)).

  Lemma oom_seg2 : forall mode Q fd3 KBb vals R M,     (* [comment removed for export] *)
    brk_ok_branch_G mode Q fd3 KBb ->
    length vals = 41%nat -> vals_ev vals 0 = sp0 ->
    vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv -> vals_ev vals 5 = tid ->
    regs_ok (ENV vals) srB0 R -> know_ok RSEGS (ENV vals) M knA -> above_sp0 M ->
    GG RSEGS mode Q KBb
       (mkCfg (mkst R (Z_to_bv 64 0x2bd1e0) M (seg_rom RSEGS)) (model1g fd3)).
  Proof.
    intros mode Q fd3 KBb vals R M HKBb HL P0 P1 P2 P5t HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    (* [comment removed for export] *)
    gg_block_keep scr0 41%nat.
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
    assert (MC : mcH M dst src 8 (word_to_le_bytes 8 (vals_ev vals 39))).
    { constructor.
      - lia.
      - reflexivity.
      - exact Hrd8.
      - exact Hwr8.
      - lia.
      - lia.
      - lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x2b2384)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x2b2384) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit).
    assert (G11 : getr R 11 = src) by (regv HR (11:reg); subst src; apply edenot_add_lit).
    assert (G12 : getr R 12 = Z_to_bv 64 8) by (regv HR (12:reg); reflexivity).
    destruct (ref_memcpy M dst src 8 _ (seg_rom RSEGS) MC R (Z_to_bv 64 0x2b2384) RT G1 G10 G11 G12)
      as (R2 & Hms & Hkeep). clear RT G1 G10 G11 G12.
    replace (Z_to_bv 64 2867236) with (0x2bc024 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply gg_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    (* [comment removed for export] *)
    assert (HA' : above_sp0 (wbytes M dst (word_to_le_bytes 8 (vals_ev vals 39)))).
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
        pose proof (know_after_store RSEGS E M0 kn (SA (EVar 0) (-384)) 8 (EVar 39) (word_to_le_bytes 8 (vals_ev vals 39))
                      kn' scs hs ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                      ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia) eq_refl) as HK2
      end end.
    clear HK. subst dst.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 73%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (P0' : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (P1' : vals_ev vals1 1 = p0 sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    assert (P2' : vals_ev vals1 2 = p1 sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (P5' : vals_ev vals1 5 = tid) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
    clearbody vals1. clear HL P0 P1 P2 P5t. rename HL1 into HL. rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P5' into P5t.
    change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path rdraw))) with (ENV vals1) in HR, HK.
    (* [comment removed for export] *)
    gg_block_keep scr0 73%nat.
    refresh_above vals1 P0 HA. clear Hrd8 Hwr8 Hudst Husrc MC Krnd Kdj. clear R2 M. try clear R. name_state R M.
    (* [comment removed for export] *)
    eapply (gg_brk_query RSEGS mode Q _ _ _ (model1g fd3) ECALLW).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). reflexivity.
    - rewrite v_addi_pc4 by lia. change (0x2b244c + 4)%Z with 0x2b2450%Z.
      rewrite m1_vmmaps; cbn [vm_brk].
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals1 [brk] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals1 [brk] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      clear HR HK.
      set (vals2 := vals1 ++ [brk]) in *.
      assert (HL2 : length vals2 = 74%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (P0' : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (P73 : vals_ev vals2 73 = brk).
      { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals1)). rewrite vals_ev_app_r. reflexivity. }
      assert (P1' : vals_ev vals2 1 = p0 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
      assert (P2' : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (P5' : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
      clearbody vals2. clear HL P0 P1 P2 P5t. rename HL2 into HL. rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P5' into P5t.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path rdraw))) with (ENV vals2) in HR2, HK2.
      pose proof (regs_set_a0 (ENV vals2) _ _ brk b_expr HR2 ltac:(cbn [edenot b_expr ev ENV]; exact P73)) as HR.
      clear HR2.
      (* [comment removed for export] *)
      lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
        assert (HK : know_ok RSEGS (ENV vals2) Mc knD0) end.
      { unfold knD0. apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]].
        - apply kalign_intro; [lia|]. cbn [edenot b_expr ev ENV]. rewrite P73. exact brk_al.
        - apply krange_intro. cbn [edenot b_expr ev ENV]. rewrite P73. pose proof brk_lo. pose proof brk_hi. lia. }
      clear HK2.
      (* [comment removed for export] *)
      gg_block_keep scr0 74%nat.
      refresh_above vals2 P0 HA. clear R M. name_state R M.
      (* [comment removed for export] *)
      pose proof (regs_ok_esub (ENV vals2) ugly_b b_expr _ _ (ugly_b_sem vals2 P73) HR) as HR2.
      pose proof (know_ok_ksub RSEGS (ENV vals2) _ ugly_b b_expr _ (ugly_b_sem vals2 P73) HK) as HK2.
      clear HR HK. rename HR2 into HR. rename HK2 into HK.
      lazymatch type of HR with regs_ok _ ?sr _ => let sr' := eval vm_compute in sr in change sr with sr' in HR end.
      lazymatch type of HK with know_ok _ _ _ ?kn => let kn' := eval vm_compute in kn in change kn with kn' in HK end.
      (* [comment removed for export] *)
      eapply (gg_brk_grow RSEGS mode Q _ _ _ (model1g fd3) ECALLW 8192).
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
        unfold adenot, v_addi. cbn [a_base a_off edenot b_expr ev ENV]. rewrite P73. reflexivity.
      + rewrite m1_vmmaps. cbn [vm_brk]. unfold model1g.
        apply (brk_grow_admissible_init (segments_reserved RSEGS) brk mbase sp0 lim fs0 stdin0 (fds1g fd3) (Some tid) None);
          rewrite ?rtop, ?stack_max_size_val;
          first [exact brk_al | reflexivity | pose proof brk_lo; pose proof brk_hi; pose proof LIM_ge; pose proof lim_ge; unfold LIM in *; lia].
      + (* [comment removed for export] *)
        rewrite v_addi_pc4 by lia. change (0x2b2470 + 4)%Z with 0x2b2474%Z.
        rewrite m1_vmmaps; cbn [vm_brk vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base vm_init_sp].
        eapply (HKBb vals2); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_err_branch (KA : TSet) : Prop :=
    forall e vals R M,
      In e openat_errnos ->
      length vals = 42%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 41 = errno_ret e ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 41)) R -> know_ok RSEGS (ENV vals) M knA ->
      (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2bd1e0) M (seg_rom RSEGS)) model0) KA.

  Lemma oom_seg1 : forall mode Q KA KBb,     (* [comment removed for export] *)
    (mode = true -> open_err_branch KA) -> brk_ok_branch_M mode Q KBb ->
    GG RSEGS mode Q (t_alt2 KA KBb)
       (mkCfg (mkst regs0 (Z_to_bv 64 0xe1984) mem0 (seg_rom RSEGS)) model0).
  Proof.
    intros mode Q KA KBb HKA HKBb.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof HR0 as HR. pose proof HK0 as HK. unfold valsP in HR, HK.
    set (vals := vals0 sp0 a0s path envv tid regs0 ++ _) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals0; rewrite !length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 sp0 a0s path envv) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    pose proof Hstr as Sr. pose proof Hstr_lo as Slo.
    clearbody vals.
    (* [comment removed for export] *)
    gg_block_keep scr0 41%nat.
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM. rewrite (rdn_mem_denot_above RSEGS (ENV vals) mem0 _ 0%nat 0x354000);
        [exact Sr | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia
        | lia]. }
    (* [comment removed for export] *)
    eapply (gg_openat_file RSEGS _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
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
    - exact Hpns.
    - exact Hpnd.
    - rewrite m0_fs. exact Hfile.
    - (* [comment removed for export] *)
      intros Hmode e He. rewrite v_addi_pc4 by lia. change (0x2bd1dc + 4)%Z with 0x2bd1e0%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path rdraw))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA Hmode e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x354000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x2bd1dc + 4)%Z with 0x2bd1e0%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0)
        with (model1g (FdFile path (Z_to_bv 64 0))).
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      assert (HA : above_sp0 M).
      { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x354000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
      eapply (oom_seg2 mode Q (FdFile path (Z_to_bv 64 0)) KBb vals); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem oom_pilot : forall mode Q KA KBb,     (* [comment removed for export] *)
    (mode = true -> open_err_branch KA) -> brk_ok_branch_M mode Q KBb ->
    GG RSEGS mode Q (t_alt2 KA KBb)
      (mkCfg (mkst regs0 (Z_to_bv 64 0xe1984) mem0 (seg_rom RSEGS))
             (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA [a0s; path] envv fs0 stdin0)))).
  Proof. intros. apply oom_seg1; assumption. Qed.

  (* [comment removed for export] *)
  Corollary oom_pilot_rz : forall KA KBb,     (* [comment removed for export] *)
    open_err_branch KA -> brk_ok_branch KBb ->
    realizes RSEGS
      (mkCfg (mkst regs0 (Z_to_bv 64 0xe1984) mem0 (seg_rom RSEGS))
             (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA [a0s; path] envv fs0 stdin0))))
      (t_alt2 KA KBb).
  Proof.
    intros KA KBb HA HB.
    apply (rz_of_gg RSEGS (fun _ => True)). apply oom_pilot; [intros _; exact HA | exact HB].
  Qed.

End Pilot.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma regs_exec_of_main : forall sp0 a0s path envv rdraw tid regs0,
  regs_ok (E0 sp0 a0s path envv rdraw tid regs0) sr_main regs0 ->
  regs_ok (ENV a0s path rdraw (valsP sp0 a0s path envv rdraw tid regs0)) sr_main regs0.
Proof.
  intros sp0 a0s path envv rdraw tid regs0 HR. unfold ENV, valsP, E0 in *.
  apply env_app_regs; [|exact HR]. unfold vals0. rewrite length_app, junk_vals_length. vm_compute. reflexivity.
Qed.

Lemma word_to_le_bytes_le_word : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (le_bytes_to_word bs) = bs.
Proof. intros bs H. unfold le_bytes_to_word. apply word_to_le_bytes_of_lez; [exact H | lia]. Qed.

(* [comment removed for export] *)
Lemma kword_of_bytes : forall E M a (bs : list byte) v,
  flat E a 8 -> length bs = 8%nat ->
  (forall i, (0 <= i < 8)%Z -> M (Z_to_bv 64 (estart E a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
  edenot E v = le_bytes_to_word bs ->
  kentry_ok RSEGS E M (KWord a 8 v).
Proof.
  intros E M a bs v Hf Hl Hb Hv. cbn [kentry_ok]. split; [lia|]. split; [exact Hf|].
  rewrite Hv, (word_to_le_bytes_le_word bs Hl).
  apply rdn_pointwise; [exact Hl | unfold flat in Hf; unfold adenot, estart in *; cbn [a_base a_off] in *;
                                    destruct a as [b k]; cbn [a_base a_off] in *; pose proof (u64_range (v_addi (edenot E b) k)); unfold v_addi; rewrite u_small by lia; lia |].
  intros j Hj. unfold adenot, estart in *. destruct a as [b k]; cbn [a_base a_off] in *.
  unfold flat in Hf. cbn [a_base a_off] in Hf. unfold estart in Hf. cbn [a_base a_off] in Hf.
  unfold v_addi. rewrite u_small by lia.
  rewrite <- (Nat2Z.id j) at 2. apply Hb. lia.
Qed.

Lemma know_exec_of_main : forall sp0 a0s path envv rdraw tid regs0 mem,
  know_ok RSEGS (E0 sp0 a0s path envv rdraw tid regs0) mem kn_main ->
  know_ok RSEGS (ENV a0s path rdraw (valsP sp0 a0s path envv rdraw tid regs0)) mem kn_exec.
Proof.
  intros sp0 a0s path envv rdraw tid regs0 mem HK.
  set (E := E0 sp0 a0s path envv rdraw tid regs0) in HK.
  set (E' := ENV a0s path rdraw (valsP sp0 a0s path envv rdraw tid regs0)).
  assert (HLv : length (vals0 sp0 a0s path envv tid regs0) = 38%nat)
    by (unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
  (* [comment removed for export] *)
  assert (HK1 : know_ok RSEGS E' mem kn_main_noblob).
  { unfold E', ENV, valsP. apply env_app_know; [rewrite HLv; vm_compute; reflexivity|].
    unfold know_ok in *. unfold kn_main_noblob. apply incl_Forall with (l1 := kn_main); [|exact HK].
    intros K HKin. apply filter_In in HKin. tauto. }
  (* [comment removed for export] *)
  pose proof (know_nth RSEGS E mem kn_main ltac:(let i := eval vm_compute in (kindex (kentry_eqb (KBlob (SA (EVar 4) 0) (ELit 16) 2)) kn_main 0) in
                                              lazymatch i with Some ?j => exact j end) _ HK eq_refl) as Brnd.
  pose proof (know_nth RSEGS E mem kn_main ltac:(let i := eval vm_compute in (kindex (kentry_eqb (KBlob (SA (ELit 0) 0x331ad8) (ELit 8) 3)) kn_main 0) in
                                              lazymatch i with Some ?j => exact j end) _ HK eq_refl) as Bcan1.
  pose proof (know_nth RSEGS E mem kn_main ltac:(let i := eval vm_compute in (kindex (kentry_eqb (KBlob (SA (ELit 0) 0x351b28) (ELit 8) 3)) kn_main 0) in
                                              lazymatch i with Some ?j => exact j end) _ HK eq_refl) as Bcan2.
  cbn [kentry_ok] in Brnd, Bcan1, Bcan2. unfold elenZ in Brnd, Bcan1, Bcan2. cbn [edenot] in Brnd, Bcan1, Bcan2.
  change (eb E 2) with (rnd16 rdraw) in Brnd. change (eb E 3) with (guard8 rdraw) in Bcan1, Bcan2.
  rewrite (u64_lit 16) in Brnd by lia. rewrite (u64_lit 8) in Bcan1, Bcan2 by lia.
  destruct Brnd as (Fr & Lr & Br). destruct Bcan1 as (F1 & L1 & B1). destruct Bcan2 as (F2 & L2 & B2).
  assert (Ev4 : ev E' 4 = ev E 4) by reflexivity.
  assert (E38 : ev E' 38 = rndw0 rdraw).
  { unfold E', ENV, valsP. cbn [ev]. replace 38%nat with (length (vals0 sp0 a0s path envv tid regs0) + 0)%nat by (rewrite HLv; reflexivity).
    rewrite vals_ev_app_r. reflexivity. }
  assert (E39 : ev E' 39 = rndw1 rdraw).
  { unfold E', ENV, valsP. cbn [ev]. replace 39%nat with (length (vals0 sp0 a0s path envv tid regs0) + 1)%nat by (rewrite HLv; reflexivity).
    rewrite vals_ev_app_r. reflexivity. }
  assert (E40 : ev E' 40 = can rdraw).
  { unfold E', ENV, valsP. cbn [ev]. replace 40%nat with (length (vals0 sp0 a0s path envv tid regs0) + 2)%nat by (rewrite HLv; reflexivity).
    rewrite vals_ev_app_r. reflexivity. }
  assert (Lf : length (firstn 8 (rnd16 rdraw)) = 8%nat) by (rewrite length_firstn; lia).
  assert (Ls : length (skipn 8 (rnd16 rdraw)) = 8%nat) by (rewrite length_skipn; lia).
  unfold kn_exec. change (know_ok RSEGS E' mem (kn_main_noblob ++ kn_rndcan)).
  unfold know_ok. apply Forall_app. split; [exact HK1|]. unfold kn_rndcan.
  repeat apply Forall_cons; [| | | | apply Forall_nil].
  - apply (kword_of_bytes E' mem _ (firstn 8 (rnd16 rdraw))).
    + unfold flat in *. unfold estart in *. cbn [a_base a_off edenot] in *. rewrite Ev4. lia.
    + exact Lf.
    + intros i Hi. unfold estart. cbn [a_base a_off edenot]. rewrite Ev4.
      unfold estart in Br. cbn [a_base a_off edenot] in Br. rewrite (Br i) by lia.
      rewrite nth_firstn. replace (Z.to_nat i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
    + cbn [edenot]. exact E38.
  - apply (kword_of_bytes E' mem _ (skipn 8 (rnd16 rdraw))).
    + unfold flat in *. unfold estart in *. cbn [a_base a_off edenot] in *. rewrite Ev4. lia.
    + exact Ls.
    + intros i Hi. unfold estart. cbn [a_base a_off edenot]. rewrite Ev4.
      unfold estart in Br. cbn [a_base a_off edenot] in Br.
      replace (bv_unsigned (ev E 4) + 8 + i)%Z with (bv_unsigned (ev E 4) + 0 + (8 + i))%Z by lia.
      rewrite (Br (8 + i)%Z) by lia. rewrite nth_skipn. f_equal. f_equal. lia.
    + cbn [edenot]. exact E39.
  - apply (kword_of_bytes E' mem _ (guard8 rdraw)).
    + unfold flat in *. unfold estart in *. cbn [a_base a_off edenot] in *. lia.
    + lia.
    + intros i Hi. exact (B1 i Hi).
    + cbn [edenot]. exact E40.
  - apply (kword_of_bytes E' mem _ (guard8 rdraw)).
    + unfold flat in *. unfold estart in *. cbn [a_base a_off edenot] in *. lia.
    + lia.
    + intros i Hi. exact (B2 i Hi).
    + cbn [edenot]. exact E40.
Qed.
