(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the process input's new fields; the new initial stack layout; the vDSO mapping; the reader fact of the output channels). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefStartupDefs.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame
  MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  Spec LibWritev RefNodes RefExitBase RefExit RefMemcpyLib RefMemcpyBase RefMemcpy RefMemchr RefStrnlen
  RefStartup RefStartupFacts RefMainEntry LibTail.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require RefOpenFail_defs RefOpenFail_tail2 RefMainEntryN.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefArgvTask.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefOpenFail_defs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefOpenFail_tail2.RefOpenFail_tail OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefOpenFail_tail2.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPW_1. Context {fx : PropExec.FPState}.


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

Section OpenFail.
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
  Variable stdin0 : AmbIn.
  (* [comment removed for export] *)
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.   (* [comment removed for export] *)
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Local Notation INP := (mkProcInputA [a0s; path] envv fs0 stdin0) (only parsing).
  Local Notation uid := (ia_uid stdin0) (only parsing).
  Local Notation hw := (ia_hwcap stdin0) (only parsing).
  Hypothesis ME : main_entry sp0 INP mbase rdraw tid regs0 mem0.
  Hypothesis Hvl : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) INP.
  (* LPS 727298f3: the "cannot open" message is a write to stderr, which needs the channel reader;
     the input's reader is its ambient [ia_channel_reader], discharged at the top. *)
  Hypothesis Hcr : ia_channel_reader stdin0 = true.

  (* [comment removed for export] *)
  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).
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
  #[using="Hcr"] Lemma model0_rdr : m_channel_reader model0 = true.
  Proof. first [exact Hcr | (cbn; exact Hcr)]. Qed.
  Lemma model0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.
  Lemma path_len : (Z.of_nat (length path) <= 131071)%Z.
  Proof.
    destruct Hva as (_ & _ & Hl & _ & _). inversion Hl as [|x l Hx Hl']; subst. inversion Hl'; subst. assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma path_facts :
    rdn RSEGS mem0 (p1 INP rdraw) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (p1 INP rdraw))%Z
    /\ (bv_unsigned (p1 INP rdraw) <= bv_unsigned sp0 + 2107576)%Z
    /\ (bv_unsigned (p1 INP rdraw) + Z.of_nat (length path) + 1 <= 0x800000000000)%Z   (* [comment removed for export] *)
    /\ exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (p1 INP rdraw) + Z.of_nat (length path))) 8 = Some t8.
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* LPS 727298f3: the string, its bounds and the 8 bytes after it all come from
       RefMainEntryN.main_strN (the read the dir path's [dir_tail] makes, RefLeafDir.v). *)
    edestruct (RefMainEntryN.main_strN sp0 INP mbase brk rdraw tid regs0 mem0 Hva Hve Hvsp Hvl Hlau Htid ME 1%nat)
      as (Sr & Slo & Shi & Slen & t8 & Ht8); [cbn; lia|].
    unfold p1.
    split; [exact Sr|]. split; [exact Slo|]. split; [lia|].
    split; [exact (cat_argv_ptr_task INP mbase sp0 brk rdraw 1 Hlau ltac:(cbn; lia))|].
    exists t8. exact Ht8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem ref_open_fail_errno : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
    vals_ev vals 2 = p1 INP rdraw ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xa763c) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof using All.
    intros e vals R M He HL P0 P38 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof path_len as HPl.
    destruct path_facts as (Sr & Slo & Shi & Stask & t8 & Ht8).
    pose proof (u64_range (p1 INP rdraw)) as Hpr.
    rewrite <- model0_fs.
    eapply (of_tail sp0 (blobs0 a0s path) model0 Hvsp model0_halted model0_lazy model0_fd2 model0_rdr path (p1 INP rdraw) t8 vals);
      try eassumption.
    - apply path_nonul.
    - rewrite P38. apply errno_ret_range. exact He.
    - lia.
    - right. exact Stask.
    - rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma of_blockA : forall T,
    (forall vals R M,
       length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 INP rdraw ->
       regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
       (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xa7638) M (seg_rom RSEGS)) model0) T) ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x32574) mem0 (seg_rom RSEGS)) model0) T.
  Proof.
    intros T HA.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_regs_ok sp0 a0s path INP mbase brk rdraw tid regs0 mem0 eq_refl Hva Hve Hvsp Hvl Hlau Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path INP mbase brk rdraw tid regs0 mem0 eq_refl Hva Hve Hvsp Hvl Hlau Htid ME) as HK.
    change (E0 sp0 a0s path INP rdraw tid regs0) with (ENV (vals0 sp0 INP rdraw tid regs0)) in HR, HK.
    set (vals := vals0 sp0 INP rdraw tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, length_skipn, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 INP rdraw) by reflexivity.
    clearbody vals.
    pose proof model0_halted as Hh.
    run_blk_keep scr0 38%nat.
    apply (HA vals); try assumption.
    intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0xe6000);
      [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma openat_regs : forall vals R,
    vals_ev vals 2 = p1 INP rdraw -> regs_ok (ENV vals) srA R ->
    getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = p1 INP rdraw
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
    length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 INP rdraw ->
    regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0xa7638) 4) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P2 HR HK Habove.
    rewrite v_addi_pc4 by lia. change (0xa7638 + 4)%Z with 0xa763c%Z.
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals [errno_ret e] (blobs_ev (blobs0 a0s path)) sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    pose proof (env_app_know RSEGS vals [errno_ret e] (blobs_ev (blobs0 a0s path)) M knA ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
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
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x32574) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlong. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & Stask & _).
    pose proof (u64_range (p1 INP rdraw)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0xa7638) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_toolong RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 (firstn 4096 path)).
    - rewrite A11. unfold TASK_SIZE in *. lia.
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
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x32574) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hnil. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & Stask & _).
    pose proof (u64_range (p1 INP rdraw)) as Hpr.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0xa7638) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_empty RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12).
    - split; [cbn; lia|]. split; [intros [] |].
      split; [rewrite A11; cbn [length]; unfold TASK_SIZE; lia |]. rewrite A11.
      replace (length path + 1)%nat with 1%nat in Sr by (rewrite Hnil; reflexivity).
      replace (path ++ [Z_to_bv 8 0]) with [Z_to_bv 8 0] in Sr by (rewrite Hnil; reflexivity).
      cbn [length Nat.add app].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_absent :
    (length path <= 4095)%nat -> path <> [] -> path_has_slash path = false -> path_is_dirref path = false -> fs_lookup fs0 path = None ->   (* [comment removed for export] *)
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x32574) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlen Hne Hns Hnd Hfs. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & Stask & _).
    pose proof (u64_range (p1 INP rdraw)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0xa7638) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_absent RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 path).
    - split; [exact Hlen|]. split; [apply path_nonul|].
      split; [rewrite A11; unfold TASK_SIZE; lia |]. rewrite A11.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - exact Hne.
    - exact Hns.
    - exact Hnd.
    - exact Hfs.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  Corollary ref_open_fail_toolong_w :
    (4096 <= length path)%nat ->
    realizes RSEGS (mkCfg (mkst regs0 (0x32574 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof using All.
    intros H. replace (0x32574 : word) with (Z_to_bv 64 0x32574) by (apply bv_eq; reflexivity).
    apply ref_open_fail_toolong. exact H.
  Qed.

  Corollary ref_open_fail_empty_w :
    path = [] ->
    realizes RSEGS (mkCfg (mkst regs0 (0x32574 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof using All.
    intros H. replace (0x32574 : word) with (Z_to_bv 64 0x32574) by (apply bv_eq; reflexivity).
    apply ref_open_fail_empty. exact H.
  Qed.

  Corollary ref_open_fail_absent_w :
    (length path <= 4095)%nat -> path <> [] -> path_has_slash path = false -> path_is_dirref path = false -> fs_lookup fs0 path = None ->   (* [comment removed for export] *)
    realizes RSEGS (mkCfg (mkst regs0 (0x32574 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof using All.
    intros H1 H2 H3 H3' H4. replace (0x32574 : word) with (Z_to_bv 64 0x32574) by (apply bv_eq; reflexivity).
    apply ref_open_fail_absent; assumption.
  Qed.

End OpenFail.
End FPW_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
