(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
  Spec LibWritev RefNodes RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Startup_u5 Pm6MainEntry_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Hoare MemSplit.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6OpenFail_defs_u5 Pm6OpenFail_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Drv_defs_u5 Pm6DrvLib_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvA.
  Context {RE : RunEnv}.
  (* [comment removed for export] *)
  Variable L : heap_layout.
  Variable HI : heap_iface.
  Hypothesis HIok : heap_iface_ok L scfg HI.
  (* [comment removed for export] *)
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
  Variable fdata : list byte.
  Variable cr0 : credit.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hppl : openat_plain_name path = true.
  Hypothesis Hfs : sc_fs scfg = true.
  Hypothesis Hplen : (length path <= 4095)%nat.
  Hypothesis DL : drv_layout L sp0.
  (* [comment removed for export] *)
  Hypothesis HH0 : hi_heap HI [] cr0 mem0 VM0.
  Hypothesis Hcr0 : credit_ok L cr0 65536.

  Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata])).

  (* [comment removed for export] *)
  Definition fds0 : list (word * FdEntry) :=
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
     (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  Definition model0 : Model := mkModelE fds_init VM0 stdin0 fs0 None (Some tid) None.
  Definition fds1 : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0)).
  Definition model1 (VM : VmMaps) : Model := mkModelE fds1 VM stdin0 fs0 None (Some tid) None.

  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

  Lemma model0_eq : model0 = mkModelE fds0 VM0 stdin0 fs0 None (Some tid) None.
  Proof. reflexivity. Qed.
  Lemma m0_fds : m_fds model0 = fds0. Proof. reflexivity. Qed.
  Lemma m0_fs : m_fs model0 = fs0. Proof. reflexivity. Qed.
  Lemma m0_vm : m_vmmaps model0 = VM0. Proof. reflexivity. Qed.
  Lemma m1_vm : forall VM, m_vmmaps (model1 VM) = VM. Proof. reflexivity. Qed.
  Lemma alloc_fd_fds0 : alloc_fd fds0 = Z_to_bv 64 3. Proof. exact (alloc_fd_init _ _ _). Qed.
  Lemma fd_lookup_fds0_3 : fd_lookup fds0 (Z_to_bv 64 3) = None. Proof. reflexivity. Qed.
  Lemma model1_but : forall VM m', model_but_vm (model1 VM) m' -> m' = model1 (m_vmmaps m').
  Proof. intros VM m' H. exact H. Qed.

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ENV_agree : forall vals, blob_agree 4 (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw))) (ENV vals).
  Proof. intros vals. unfold ENV. apply (blob_agree_app (vals_ev vals) (blobs0 a0s path hw rdraw) [fdata]). Qed.

  Lemma main_regs_ok_d : regs_ok (ENV (vals0 sp0 a0s path envv tid regs0)) sr_main regs0.
  Proof.
    pose proof (main_regs_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hvsp Htid ME) as HR.
    eapply regs_ok_bagree; [apply ENV_agree | vm_compute; reflexivity | exact HR].
  Qed.

  Lemma main_know_ok_d : know_ok RSEGS (ENV (vals0 sp0 a0s path envv tid regs0)) mem0 kn_d0.
  Proof.
    pose proof (main_know_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    eapply know_ok_bagree; [apply ENV_agree | vm_compute; reflexivity |].
    eapply ksubl_sound; [exact HK | exact kn_d0_sub].
  Qed.

  (* [comment removed for export] *)
  Definition open_err_k (KA : TSet) : Prop :=
    forall e vals R M,
      (1 <= e <= 4095)%Z ->
      length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
      vals_ev vals 2 = p1 sp0 a0s path envv ->
      regs_ok (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw))) (sr_upd Pm6OpenFail_defs_u5.srA (ridx 10) (EVar 38)) R ->
      know_ok RSEGS (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw))) M Pm6OpenFail_defs_u5.knA ->
      above_sp0 M ->
      srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xbeff4) M (seg_rom RSEGS)) model0) KA.

  Lemma ENV_agree_r : forall vals, blob_agree 4 (ENV vals) (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw))).
  Proof.
    intros vals. destruct (ENV_agree vals) as [A B]. split; [intros n; symmetry; apply A | intros k Hk; symmetry; apply B; exact Hk].
  Qed.

  (* [comment removed for export] *)
  Lemma main_kimg_alloc : know_ok RSEGS (ENV (vals0 sp0 a0s path envv tid regs0)) mem0 [KImg 0xfd418 0xfe000; KImg 0xcb541 0xdcf40].
  Proof.
    pose proof (main_know_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    constructor; [|constructor; [|constructor]].
    - exact (know_nth RSEGS _ _ kn_main ltac:(let i := kidx kn_main (is_kimg_cov 0xfd418 (0xfe000 - 0xfd418)) in exact i) _ HK eq_refl).
    - exact (know_nth RSEGS _ _ kn_main ltac:(let i := kidx kn_main (is_kimg_cov 0xcb541 (0xdcf40 - 0xcb541)) in exact i) _ HK eq_refl).
  Qed.

  (* [comment removed for export] *)
  Definition file_k (KF : TSet) : Prop :=
    forall vals R M VM (A1 : Z),
      length vals = 70%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 48 = Z_to_bv 64 A1 ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv -> vals_ev vals 5 = tid ->
      regs_ok (ENV vals) srC0 R -> know_ok RSEGS (ENV vals) M knC0 ->
      above_sp0 M -> block_range L A1 65536 ->
      hi_heap HI [(A1, 65536%Z)] (debit L cr0 65536) M VM ->
      srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x3a1c4) M (seg_rom RSEGS)) (model1 VM)) KF.

  (* [comment removed for export] *)
  Lemma hiv_facts : forall vals,
    vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv ->
    forall i, In i [3%nat; 4%nat] -> (bv_unsigned sp0 <= bv_unsigned (vals_ev vals i))%Z /\ (bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64)%Z.
  Proof.
    intros vals P3 P4 i Hi.
    destruct (auxvp_u sp0 a0s path envv uid hw rdraw Hva Hve Hvsp) as [A1 A2].
    destruct (rnd_u sp0 a0s path envv uid hw rdraw Hva Hve Hvsp) as (R1 & R2 & _ & _).
    destruct Hi as [<-|[<-|[]]]; [rewrite P3 | rewrite P4]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma above_sp0_block : forall vals log M,
    vals_ev vals 0 = sp0 -> log_below_b 0 0xfe000 log = true -> above_sp0 M ->
    above_sp0 (mem_denot (ENV vals) M log).
  Proof.
    intros vals log M P0 Hb HA a Ha.
    rewrite (mem_denot_above (ENV vals) M log 0%nat 0xfe000 a Hb); [apply HA; exact Ha | | |];
      cbn [ev ENV]; rewrite ?P0; lia.
  Qed.

  Lemma alu_add_w_lit : forall (x : word) k, alu64 ALU_ADD x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
  Proof.
    intros x k. rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  Theorem drv_open : forall KA KF,
    open_err_k KA -> file_k KF -> KF [] ->
    srealizes RSEGS scfg (mkCfg (mkst regs0 (Z_to_bv 64 0x3a170) mem0 (seg_rom RSEGS)) model0) (t_alt2 KA KF).
  Proof.
    intros KA KF HKA HKF HKF0.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof main_regs_ok_d as HR.
    assert (HK : know_ok RSEGS (ENV (vals0 sp0 a0s path envv tid regs0)) mem0 (kn_d0 ++ [KImg 0xfd418 0xfe000; KImg 0xcb541 0xdcf40]))
      by (apply Forall_app; split; [apply main_know_ok_d | apply main_kimg_alloc]).
    set (vals := vals0 sp0 a0s path envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 sp0 a0s path envv) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
    assert (P3 : vals_ev vals 3 = auxvp sp0 a0s path envv) by reflexivity.
    assert (P4 : vals_ev vals 4 = rnd sp0 a0s path envv) by reflexivity.
    assert (P5 : vals_ev vals 5 = tid) by reflexivity.
    destruct (main_str sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen.
    assert (HA0 : above_sp0 mem0) by (intros a Ha; reflexivity).
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    assert (HH1 : hi_heap HI [] cr0 M VM0).
    { rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals _ []); [exact P0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH0]. }
    assert (HA : above_sp0 M).
    { rewrite EQM. apply above_sp0_block; [exact P0 | vm_compute; reflexivity | exact HA0]. }
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite <- Sr. apply rdn_agree. intros j Hj. pose proof (u64_range (p1 sp0 a0s path envv)).
      apply HA. unfold p1 in *. rewrite u_small; lia. }
    clear EQM.
    (* [comment removed for export] *)
    eapply (rz_openat_file RSEGS scfg _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - exact Hfs.
    - rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - split; [exact Hplen|]. split; [apply path_nonul|].
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. exact Sr'.
    - exact Hpne.
    - exact Hppl.
    - rewrite m0_fs. exact Hfile.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0xbeff0 + 4)%Z with 0xbeff4%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])).
      + apply openat_errnos_range. exact He.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + eapply regs_ok_bagree; [apply ENV_agree_r | vm_compute; reflexivity |].
        apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + eapply know_ok_bagree; [apply ENV_agree_r | vm_compute; reflexivity |].
        eapply ksubl_sound; [exact HK2 | vm_compute; reflexivity].
      + exact HA.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0xbeff0 + 4)%Z with 0xbeff4%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0) with (model1 VM0).
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2. clear HR. rename HR2 into HR.
      (* [comment removed for export] *)
      run_block_keep scr0 38%nat.
      cbn [mem_denot] in EQM. subst M0.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
      eapply (malloc_site scfg L HI HIok sp0 Hsp' Hal' DL vals _ _ kn _ _ (model1 VM0) [] cr0 65536 (-128) [] [] 0x3a1c4 KF) end;
        [ exact HR | exact HK
        | rewrite HL; vm_compute; reflexivity
        | rewrite HL; vm_compute; reflexivity
        | rewrite HL; lia
        | exact P0
        | apply hiv_facts; assumption
        | vm_compute; reflexivity
        | regv HR (2 : reg); cbn [edenot ev ENV]; rewrite P0; apply alu_add_w_lit
        | lia
        | reflexivity
        | regv HR (10 : reg); reflexivity
        | lia
        | exact Hcr0
        | regv HR (4 : reg); reflexivity
        | regv HR (1 : reg); reflexivity
        | lia | reflexivity
        | exact HH1
        | reflexivity | reflexivity | reflexivity
        | intros i nb Hf; discriminate
        | intros v b Hf; discriminate
        | exact HKF0
        | ].
      + (* [comment removed for export] *)
        intros R' M' model' A vals' E' HL' HA' HR' HK' HH' HBUT HBR HAP HAB HBLK HIMG. subst vals' E'.
        rewrite (model1_but VM0 model' HBUT).
        apply (HKF (vals ++ junk_vals R') R' M' (m_vmmaps model') A); try assumption.
        * rewrite HL', HL. reflexivity.
        * rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
        * rewrite <- HA'. rewrite HL. reflexivity.
        * rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
        * rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
        * rewrite vals_ev_app_l by (rewrite HL; lia). exact P3.
        * rewrite vals_ev_app_l by (rewrite HL; lia). exact P4.
        * rewrite vals_ev_app_l by (rewrite HL; lia). exact P5.
        * rewrite HL in HR'. exact HR'.
        * rewrite HL in HK'. eapply ksubl_sound; [exact HK' | vm_compute; reflexivity].
        * intros a Ha. rewrite (HAB a Ha). apply HA. exact Ha.
  Qed.

End DrvA.
End FPX_1.
