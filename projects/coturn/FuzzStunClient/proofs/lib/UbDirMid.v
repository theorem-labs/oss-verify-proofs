(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefNodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbExitBase.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib RefLayout.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbStartup UbMainEntry Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import MallocDefs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbEnframeBase UbReadBase UbWorld UbTargetPre UbReadErr UbDirTail.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbPilotOOM_defs UbPilotOOM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymXfer SymAbove UbW65_defs UbW65 UbW65m UbW65x.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefNodesX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymAboveX.
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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymDriveLet SymDriveLetUb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveX.run_block_with ::= run_block_with_let_img.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require UbDirMid_lits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_sr ::= constr:(UbDirMid_lits.LITS_SR).
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_lg ::= constr:(UbDirMid_lits.LITS_LG).
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_kn ::= constr:(UbDirMid_lits.LITS_KN).
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition DFUEL : nat := 5000.
Definition DSTOPS : list Z := [0x13cec; 0x23ae8; 0x13d68; 0x1c27c; 0x1bfa0]%Z.
Definition dscr0 : scripts := SCR [] [] [].
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen DFUEL DSTOPS scr NX true.

(* [comment removed for export] *)
Definition kn_cells : list kentry :=
  [KWr (SA (ELit 0) 0x26000) 0x32000;
   KWord (SA (ELit 0) 0x36bb8) 4 (EVar 5);          (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x36b98) 8 (ELit 0x36b98);     (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x56f18) 8 (ELit 4096)].       (* [comment removed for export] *)
Definition kn_img : list kentry := map (fun iv => KImg (fst iv) (snd iv)) re_ivs.
Definition kn_D0 : list kentry := Eval vm_compute in (kn_RE 1 4194303 ++ kn_M1 ++ kn_cells ++ kn_img).

Lemma kn_D0_eq : kn_D0 = kn_RE 1 4194303 ++ kn_M1 ++ kn_cells ++ kn_img.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_23f50 : fetch_word RSEGS (Z_to_bv 64 0x24540) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

Lemma know_of_img_clear : forall E M ivs,
  Forall (fun iv => img_clear M (fst iv) (snd iv)) ivs ->
  forallb (fun iv => Z.leb 0 (fst iv) && Z.leb (snd iv) (2 ^ 64)) ivs = true ->
  know_ok RSEGS E M (map (fun iv => KImg (fst iv) (snd iv)) ivs).
Proof.
  intros E M ivs H Hb. unfold know_ok. rewrite Forall_map. rewrite forallb_forall in Hb.
  apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) H _ Hin) as Hc.
  specialize (Hb _ Hin). apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [kentry_ok fst snd] in *. split; [exact H1|]. split; [exact H2|]. exact Hc.
Qed.

Lemma kword_of_cell : forall E M a n v,
  cell M a n v -> (n <= 8)%nat -> (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  kentry_ok RSEGS E M (KWord (SA (ELit 0) a) n (ELit v)).
Proof.
  intros E M a n v Hc Hn H0 H64. cbn [kentry_ok edenot]. split; [exact Hn|].
  split; [apply flat_intro; cbn [edenot]; rewrite ?u0; lia|].
  rewrite adenot_lit0. exact Hc.
Qed.

Section DirMid.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.

  Lemma dot_len : (length dot_path <= 4095)%nat.
  Proof. cbn. lia. Qed.

  (* [comment removed for export] *)
  Definition modelDir (VM : VmMaps) : Model :=
    mkModelC (fd_insert fds0 (Z_to_bv 64 3) FdDir) VM stdin0 fs0 None (Some tid) None.

  (* [comment removed for export] *)
  Definition after_malloc_dir (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm sec cn : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 sp0 a0s dot_path envv) mb gm sec cn R M ->
      world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb gm -> vm_small VM gm ->
      above_sp0 sp0 mem0 M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b14) M (seg_rom RSEGS)) (modelDir VM)) K.

  Theorem dir_brk : forall K, after_malloc_dir K ->
    brk_ok_branch_g sp0 a0s dot_path envv tid mem0 brk mbase fs0 stdin0 FdDir (t_alt2 (t_die msg_oom fs0) K).
  Proof.
    intros K AM. exact (brk_ok_sem_g sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk dot_len FdDir K AM).
  Qed.

  Theorem dir_mmap : forall K, after_malloc_dir K ->
    mmap_ok_branch_g sp0 a0s dot_path envv tid mem0 brk mbase fs0 stdin0 FdDir
                     (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
  Proof.
    intros K AM. exact (mmap_ok_sem_g sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk dot_len FdDir K AM).
  Qed.

  (* [comment removed for export] *)
  Theorem dir_read : forall K,
    (forall R' M' VM', dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) mem0 R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x13cec) M' (seg_rom RSEGS)) (modelDir VM')) K) ->
    after_malloc_dir K.
  Proof.
    intros K TAIL R M VM mb gm sec cn area brkv mas EA RP W MF VP VS HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
    pose proof (rp_gm _ _ _ _ _ _ _ _ RP) as Hgm. pose proof (rp_p1 _ _ _ _ _ _ _ _ RP) as Hp1.
    set (p1v := p1 sp0 a0s dot_path envv) in *.
    set (vals := valsr sp0 p1v mb gm sec cn (bv_unsigned tid) R).
    set (E := ENVr vals []).
    assert (HL : length vals = 40%nat) by (subst vals; unfold valsr; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1v) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = cn) by reflexivity.
    assert (P5 : vals_ev vals 5 = tid) by (cbn; apply Z_to_bv_bv_unsigned).
    pose proof (read_pre_regs sp0 p1v mb gm sec cn (bv_unsigned tid) R M [] RP : regs_ok E sr_RE R) as HR.
    assert (HK : know_ok RSEGS E M kn_D0).
    { rewrite kn_D0_eq. apply know_ok_app. split; [|apply know_ok_app; split; [|apply know_ok_app; split]].
      - apply (read_pre_know sp0 p1v mb gm sec cn (bv_unsigned tid) R M [] RP); lia.
      - exact (rp_malloc _ _ _ _ _ _ _ _ RP sp0 p1v (Z_to_bv 64 (bv_unsigned tid)) (Z_to_bv 64 0) (junk_vals R) [[]]).
      - destruct W. unfold kn_cells.
        repeat apply know_ok_cons; try apply Forall_nil.
        + split; [apply flat_intro; cbn [edenot]; rewrite ?u0; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite u0, Z.add_0_l.
          apply UbExitBase.store_ok_data; rewrite u_small by lia; lia.
        + cbn [kentry_ok edenot]. split; [lia|]. split; [apply flat_intro; cbn [edenot]; rewrite ?u0; lia|].
          rewrite adenot_lit0. change (ev E 5) with (vals_ev vals 5). rewrite P5, <- (Z_to_bv_bv_unsigned 64 tid). exact w_tid.
        + apply kword_of_cell; [exact w_self | lia | lia | cbn; lia].
        + apply kword_of_cell; [exact w_pagesz | lia | lia | cbn; lia].
      - apply know_of_img_clear; [apply re_ivs_of_world; exact (w_img _ _ _ _ _ _ W) | vm_compute; reflexivity]. }
    clearbody vals. subst E.
    (* [comment removed for export] *)
    run_block_keep dscr0 40%nat.
    assert (HA1 : above_sp0 sp0 mem0 M0).
    { lazymatch goal with EQM : M0 = mem_denot ?E ?Mo ?log |- _ =>
        lazymatch type of HK with know_ok _ _ _ ?kn =>
        intros xa Hxa; rewrite EQM, (mem_denot_above_kbx RSEGS E M0 Mo kn log 0%nat 0x58000 0x7fff7f800000 xa HK);
          [apply HA, Hxa | vm_compute; reflexivity | lia | cbn [ev ENVr]; pins; lia | cbn [ev ENVr]; pins; lia | lia | lia] end end. }
    clear EQM HA. rename HA1 into HA.
    (* [comment removed for export] *)
    eapply (rz_read_dir_mapped RSEGS R0 (Z_to_bv 64 0x24540) M0 (modelDir VM) ECALLW (Z_to_bv 64 3) 65536 K fetch_23f50 is_ecall_ECALLW eq_refl eq_refl).
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). reflexivity.
    - change (bv_unsigned (Z_to_bv 64 3)) with 3%Z. lia.
    - reflexivity.
    - regv HR (12 : reg). reflexivity.
    - lia.
    - lia.
    - (* [comment removed for export] *)
      regv HR (11 : reg). cbn [edenot]. unfold TASK_SIZE. rewrite u_small by lia. lia.
    - (* [comment removed for export] *)
      regv HR (11 : reg). cbn [edenot]. apply UbExitBase.store_ok_data; rewrite u_small by lia; lia.
    - rewrite v_addi_pc4 by lia. change (0x24540 + 4)%Z with 0x24544%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret EISDIR) (ELit (2 ^ 64 - 21)) HR ltac:(apply bv_eq; reflexivity)) as HR2 end.
      clear HR. rename HR2 into HR.
      (* [comment removed for export] *)
      run_block_keep dscr0 40%nat.
      assert (HA2 : above_sp0 sp0 mem0 M1).
      { lazymatch goal with EQM : M1 = mem_denot ?E ?Mo ?log |- _ =>
          lazymatch type of HK with know_ok _ _ _ ?kn =>
          intros xa Hxa; rewrite EQM, (mem_denot_above_kbx RSEGS E M1 Mo kn log 0%nat 0x58000 0x7fff7f800000 xa HK);
            [apply HA, Hxa | vm_compute; reflexivity | lia | cbn [ev ENVr]; pins; lia | cbn [ev ENVr]; pins; lia | lia | lia] end end. }
      clear EQM HA.
      change 81080%Z with 0x13cec%Z.
      apply (TAIL R1 M1 VM). constructor.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + unfold stack_writable. lazymatch type of HK with know_ok _ ?E _ ?kn =>
          apply (kwr_window E M1 kn (EVar 0) (-8388608) 8388608 _ HK); [vm_compute; reflexivity | cbn [edenot ev ENVr]; pins; lia] end.
      + lazymatch type of HK with know_ok _ ?E _ ?kn =>
          apply (img_clear_of_know E); apply (kderive_all_sound RSEGS _ M1 kn); [exact HK | vm_compute; reflexivity] end.
      + kcell HK.
      + exact Htid.
      + kcell HK.
      + exists (bv_unsigned cn). kcell HK.
      + kcell HK.
      + exact HA2.
  Qed.
End DirMid.
