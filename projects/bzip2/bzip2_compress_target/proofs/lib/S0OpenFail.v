(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the open-failure walk over the launch input ProcInput, the new auxv, the vDSO and the m_channel_reader premise). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.MiniExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Plain.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require FileSim AgentLib ArgvEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require StoreOk.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require RefLayout SymExec SymExec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive SymDriveX SymDriveH4 Spec LibWritev RefNodes S0ExitBase S0Exit RefMemcpyLib S0MemcpyBase S0Memcpy S0Memchr S0Strnlen S0Startup.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require S0MainEntry.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require S0MainEntry LibTail.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Hoare OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Frame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.FileSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ArgvEnv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk.MuslStrlen OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefLayout OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDriveH4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.LibWritev OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ExitBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Exit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0MemcpyBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Memcpy OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Memchr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Strnlen OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Startup OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0MainEntry.S0StartupFacts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0MainEntry OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.LibTail.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require S0OpenFail_defs S0OpenFail_tail2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0OpenFail_defs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0OpenFail_tail2.S7OpenFail_tail OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0OpenFail_tail2.
Import ListNotations.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymHide.
Import SymHide.OptIn.
(* [comment removed for export] *)
Local Ltac SymHide.sc_cands ::= constr:((S0OpenFail_defs.srA, (S0OpenFail_defs.knA, (S0OpenFail_defs.srB0, (S0OpenFail_defs.knB0, (S0OpenFail_defs.srB, (S0OpenFail_defs.knB, (S0OpenFail_defs.knC0, (S0OpenFail_defs.srC0, (S0OpenFail_defs.srC, (S0OpenFail_defs.knC, (S0OpenFail_defs.srD0, (S0OpenFail_defs.srD, (S0OpenFail_defs.knD, (S0OpenFail_defs.knE0, (S0OpenFail_defs.srE0, (S0OpenFail_defs.srE, (S0OpenFail_defs.knE, (S0OpenFail_defs.srF0, (S0OpenFail_defs.srF, (S0OpenFail_defs.knF, (S0OpenFail_defs.knG0, (S0OpenFail_defs.srG0, (S0OpenFail_defs.srG, (S0OpenFail_defs.knG, (S0OpenFail_defs.knH0, (S0OpenFail_defs.srH0, (S0OpenFail_defs.srH, (S0OpenFail_defs.knH, (S0OpenFail_defs.srI0, (S0OpenFail_defs.knI0, (S0OpenFail_defs.srI, (S0OpenFail_defs.knI, (S0OpenFail_defs.srG3, (S0OpenFail_defs.knG3, (S0OpenFail_defs.srH30, (S0OpenFail_defs.knH30, (S0OpenFail_defs.srH3, (S0OpenFail_defs.knH3, (S0OpenFail_defs.srI30, (S0OpenFail_defs.knI30, (S0OpenFail_defs.srI3, (S0OpenFail_defs.knI3, (S0OpenFail_defs.srF4, (S0OpenFail_defs.knF4, (S0OpenFail_defs.srG40, (S0OpenFail_defs.knG40, (S0OpenFail_defs.srG4, (S0OpenFail_defs.knG4, (S0OpenFail_defs.knH40, (S0OpenFail_defs.srH40, (S0OpenFail_defs.srH4, (S0OpenFail_defs.knH4, (S0OpenFail_defs.srI40, (S0OpenFail_defs.knI40, (S0OpenFail_defs.srI4, (S0OpenFail_defs.knI4, tt))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma errno_ret_range : forall e, (1 <= e <= 4095)%Z ->
  (2 ^ 64 - 4095 <= bv_unsigned (errno_ret e))%Z.
Proof. intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  replace ((- e) mod 2 ^ 64)%Z with (2 ^ 64 - e)%Z; [lia|].
  apply Z.mod_unique with (q := (-1)%Z); lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma In_firstn : forall {A} (l : list A) n x, In x (firstn n l) -> In x l.
Proof.
  intros A l n x H. rewrite <- (firstn_skipn n l). apply in_app_iff. left. exact H.
Qed.

Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof.
  intros e He. unfold openat_errnos in He. cbn in He.
  unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.

(* [comment removed for export] *)
Lemma total_arg_bytes_firstn_nth : forall k (av : list (list byte)), (k < length av)%nat ->
  (total_arg_bytes_nat (firstn k av) + length (nth k av []) + 1 <= total_arg_bytes_nat av)%nat.
Proof.
  induction k as [|k IH]; intros [|a av] Hk; cbn [firstn nth length] in *; try lia.
  - rewrite total_arg_bytes_cons. change (total_arg_bytes_nat []) with 0%nat. lia.
  - rewrite !total_arg_bytes_cons. specialize (IH av ltac:(lia)). lia.
Qed.

Section OpenFail.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  (* [comment removed for export] *)
  Variable lim : Z.
  (* the launch, read from the run's own input ([mkProcInputA]) *)
  Local Notation inp := (mkProcInputA [a0s; path] envv fs0 stdin0) (only parsing).
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_launch inp hw mbase sp0 brk rnd tid regs0 mem0.
  (* LPS 75d69e00: the far end of fd 2 reads ([State.m_channel_reader]); without it
     the die-tail's writev raises SIGPIPE.  [Run.valid_input]'s reader clause gives
     it at the top, and [model0] takes it from this same [stdin0]. *)
  Hypothesis HRDR : ia_channel_reader stdin0 = true.

  (* [comment removed for export] *)
  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rnd)).
  Definition model0 : Model :=
    with_tid tid (with_vdso (ia_vdso stdin0) (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA [a0s; path] envv fs0 stdin0))).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma model0_halted : m_halted model0 = None.
  Proof. reflexivity. Qed.
  Lemma model0_lazy : m_vm_lazy model0 = [].
  Proof. reflexivity. Qed.
  Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.
  Lemma model0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.
  Lemma model0_rdr : m_channel_reader model0 = true.
  Proof. exact HRDR. Qed.

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    cps_destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.   (* [comment removed for export] *)
  Qed.
  Lemma path_len : (Z.of_nat (length path) <= 131071)%Z.
  Proof.
    cps_destruct Hva as (_ & _ & Hl & _). inversion Hl as [|x l Hx Hl']; subst. inversion Hl'; subst. assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma path_facts :
    rdn RSEGS mem0 (p1 inp rnd) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (p1 inp rnd))%Z
    /\ (bv_unsigned (p1 inp rnd) <= bv_unsigned sp0 + 2107576)%Z   (* [comment removed for export] *)
    /\ (bv_unsigned (p1 inp rnd) + Z.of_nat (length path) + 1 <= 0x800000000000)%Z   (* [comment removed for export] *)
    /\ exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (p1 inp rnd) + Z.of_nat (length path))) 8 = Some t8.
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof ME as (_ & Hvl & Hlau & ME').
    edestruct (main_str inp mbase (0x133fc : word) sp0 brk a0s path rnd tid regs0 mem0) as (Sr & Slo & Shi & Slen);
      try eassumption; try reflexivity.
    1:{ instantiate (1 := 1%nat). lia. }
    cbn [nth in_argv in_envp in_execfn mkProcInputA] in Sr, Slo, Shi, Slen. unfold p1. cbn [in_argv in_envp in_execfn mkProcInputA].
    pose proof (argv_ptr_fits inp mbase sp0 brk rnd 1%nat Hlau ltac:(cbn; lia)) as Hf. cbn [nth in_argv in_envp in_execfn mkProcInputA] in Hf.
    split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|].
    split; [exact Hf|].
    cps_destruct (read_word_stack Sv48 RSEGS inp mbase RPH (0x133fc : word) sp0 brk rnd 1 (length path) Hlau ltac:(cbn; lia) ltac:(cbn; lia))
      as (t8 & Hl8 & Hr8).
    exists t8. rewrite w_add_nat in Hr8.
    pose proof (u64_range (cat_argv_ptr (ed_top rnd) [a0s; path] envv (ia_execfn stdin0) 1)).
    cbn [nth in_argv in_envp in_execfn mkProcInputA] in Hr8.
    rewrite (main_entry_rdn_above inp mbase (0x133fc : word) sp0 rnd tid regs0 mem0 ME') by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH (0x133fc : word) sp0 rnd) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem ref_open_fail_errno : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
    vals_ev vals 2 = p1 inp rnd ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x27510) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P38 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof path_len as HPl.
    cps_destruct path_facts as (Sr & Slo & Shi & Sts & t8 & Ht8).
    pose proof (u64_range (p1 inp rnd)) as Hpr.
    rewrite <- model0_fs.
    eapply (of_tail sp0 (blobs0 a0s path hw rnd) model0 Hvsp model0_halted model0_lazy model0_fd2 model0_rdr path (p1 inp rnd) t8 vals);
      try eassumption.
    - apply path_nonul.
    - rewrite P38. apply errno_ret_range. exact He.
    - lia.
    - (* [comment removed for export] *) lia.
    - rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma of_blockA : forall T,
    (forall vals R M,
       length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 inp rnd ->
       regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
       (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2750c) M (seg_rom RSEGS)) model0) T) ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x13548) mem0 (seg_rom RSEGS)) model0) T.
  Proof.
    intros T HA.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof ME as (Hhw & Hvl & Hlau & ME').
    assert (HR : regs_ok (E0 inp sp0 a0s path rnd tid regs0) sr_main regs0)
      by (eapply (main_regs_ok inp mbase (0x133fc : word) sp0 a0s path rnd tid regs0 mem0); try eassumption; reflexivity).
    assert (HK : know_ok RSEGS (E0 inp sp0 a0s path rnd tid regs0) mem0 kn_main)
      by (eapply (main_know_ok inp mbase (0x133fc : word) sp0 brk a0s path rnd tid regs0 mem0); try eassumption; reflexivity).
    unfold E0 in HR, HK. rewrite Hhw in HR, HK.
    change (Env (vals_ev (vals0 inp sp0 rnd tid regs0)) (blobs_ev (blobs0 a0s path hw rnd))) with (ENV (vals0 inp sp0 rnd tid regs0)) in HR, HK.
    set (vals := vals0 inp sp0 rnd tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 inp rnd) by reflexivity.
    clearbody vals.
    pose proof model0_halted as Hh.
    run_blk_keep scr0 38%nat.
    apply (HA vals); try assumption.
    intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x5c000);
      [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma openat_regs : forall vals R,
    vals_ev vals 2 = p1 inp rnd -> regs_ok (ENV vals) srA R ->
    getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = p1 inp rnd
    /\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
  Proof.
    intros vals R P2 HR. repeat split.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (11 : reg). cbn [edenot ev ENV]. exact P2.
    - regv HR (12 : reg). vm_compute. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma after_openat_fail : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 inp rnd ->
    regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0x2750c) 4) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P2 HR HK Habove.
    rewrite v_addi_pc4 by lia. change (0x2750c + 4)%Z with 0x27510%Z.
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals [errno_ret e] (blobs_ev (blobs0 a0s path hw rnd)) sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    pose proof (env_app_know RSEGS vals [errno_ret e] (blobs_ev (blobs0 a0s path hw rnd)) M knA ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path hw rnd))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
    eapply (ref_open_fail_errno e (vals ++ [errno_ret e])); try eassumption.
    - rewrite length_app, HL. reflexivity.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
    - rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
    - apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
      rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_toolong :
    (4096 <= length path)%nat ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x13548) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlong. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    cps_destruct path_facts as (Sr & Slo & Shi & Sts & _).
    pose proof (u64_range (p1 inp rnd)) as Hpr. pose proof path_len as HPl.
    cps_destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x2750c) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_toolong RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 (firstn 4096 path)).
    - (* the path lies below TASK_SIZE and is at least 4096 bytes long *)
      rewrite A11. unfold TASK_SIZE. lia.
    - rewrite A11. rewrite <- (firstn_app_l 4096 path [Z_to_bv 8 0]) at 1 || idtac.
      replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
        by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
      apply (rdn_firstn RSEGS M (length path + 1)); [| lia].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - intros Hin. apply path_nonul. eapply In_firstn. exact Hin.
    - apply (after_openat_fail ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_empty :
    path = [] ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x13548) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hnil. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    cps_destruct path_facts as (Sr & Slo & Shi & Sts & _).
    pose proof (u64_range (p1 inp rnd)) as Hpr.
    cps_destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x2750c) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_empty RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12).
    - split; [cbn; lia|]. split; [intros [] |].
      split; [rewrite A11; unfold TASK_SIZE; cbn [length]; lia|]. rewrite A11.
      replace (length path + 1)%nat with 1%nat in Sr by (rewrite Hnil; reflexivity).
      replace (path ++ [Z_to_bv 8 0]) with [Z_to_bv 8 0] in Sr by (rewrite Hnil; reflexivity).
      cbn [length Nat.add app].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_absent :
    (length path <= 4095)%nat -> path <> [] -> openat_plain_name path = true -> fs_lookup fs0 path = None ->   (* [comment removed for export] *)
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x13548) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlen Hne Hnd Hfs. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    cps_destruct path_facts as (Sr & Slo & Shi & Sts & _).
    pose proof (u64_range (p1 inp rnd)) as Hpr. pose proof path_len as HPl.
    cps_destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x2750c) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_absent RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 path).
    - split; [exact Hlen|]. split; [apply path_nonul|].
      split; [rewrite A11; unfold TASK_SIZE; lia|]. rewrite A11.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - exact Hne.
    - exact Hnd.
    - exact Hfs.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  Corollary ref_open_fail_toolong_w :
    (4096 <= length path)%nat ->
    realizes RSEGS (mkCfg (mkst regs0 (0x13548 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H. replace (0x13548 : word) with (Z_to_bv 64 0x13548) by (apply bv_eq; reflexivity).
    apply ref_open_fail_toolong. exact H.
  Qed.

  Corollary ref_open_fail_empty_w :
    path = [] ->
    realizes RSEGS (mkCfg (mkst regs0 (0x13548 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H. replace (0x13548 : word) with (Z_to_bv 64 0x13548) by (apply bv_eq; reflexivity).
    apply ref_open_fail_empty. exact H.
  Qed.

  Corollary ref_open_fail_absent_w :
    (length path <= 4095)%nat -> path <> [] -> openat_plain_name path = true -> fs_lookup fs0 path = None ->
    realizes RSEGS (mkCfg (mkst regs0 (0x13548 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H1 H2 H3 H4. replace (0x13548 : word) with (Z_to_bv 64 0x13548) by (apply bv_eq; reflexivity).
    apply ref_open_fail_absent; assumption.
  Qed.

End OpenFail.
End ACeilS1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
