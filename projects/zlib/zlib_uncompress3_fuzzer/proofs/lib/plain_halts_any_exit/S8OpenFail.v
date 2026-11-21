(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame
  MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  Spec LibWritev RefNodes S8ExitBase S8Exit RefMemcpyLib S8MemcpyBase S8Memcpy S8Memchr S8Strnlen
  S8Startup S8StartupFacts S8MainEntry LibTail ArgvSpan.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require S8OpenFail_defs S8OpenFail_tail2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.S8OpenFail_defs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.S8OpenFail_tail2.S0OpenFail_tail OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.S8OpenFail_tail2.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
(* the entry pc as the launch block sees it. *)
Local Notation ENT := (Z_to_bv 64 (Z.of_N Src_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc)) (only parsing).
Local Notation RPH := Src_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs (only parsing).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
  (* over the launch input (argv = [a0s; path] by Hav), the ruled VLAUNCH + LOK, and
     the launch's channel reader (valid_input's in_channel_reader; LibWritev's premise). The start model is
     Run.init_config's (with_vdso over init_model); fs0 names its file system. *)
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
  Variable lim : Z.
  Hypothesis Hav : in_argv inp = [a0s; path].
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hcr : in_channel_reader inp = true.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs0 mem0.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).
  Definition model0 : Model :=
    with_tid tid (with_vdso (vdso_run_init (ed_vdso rdraw))
                   (init_model (segments_reserved RSEGS) brk mbase sp0 lim inp)).
  Definition fs0 : Fs := m_fs model0.
  Lemma model0_rdr : m_channel_reader model0 = true.
  Proof. exact Hcr. Qed.
  Lemma Hva_inp : valid_argv (in_argv inp). Proof. rewrite Hav. exact Hva. Qed.

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

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.
  Lemma path_len : (Z.of_nat (length path) <= 131071)%Z.
  Proof.
    destruct Hva as (_ & _ & Hl & _). inversion Hl as [|x l Hx Hl']; subst. inversion Hl'; subst. assumption.
  Qed.
  Lemma path_below_task_size :
    (bv_unsigned (p1 inp rdraw) + Z.of_nat (length path) <= TASK_SIZE)%Z.
  Proof.
    pose proof (argv_str_below_task_size inp mbase sp0 brk rdraw 1%nat Hlau ltac:(rewrite Hav; cbn; lia)) as H.
    unfold p1. rewrite Hav in H |- *. cbn [nth] in H. lia.
  Qed.
  (* the strict form, for RefNodes.path_at's TASK_SIZE conjunct. *)
  Lemma path_below_task_size_lt :
    (bv_unsigned (p1 inp rdraw) + Z.of_nat (length path) < TASK_SIZE)%Z.
  Proof.
    pose proof (argv_str_below_task_size inp mbase sp0 brk rdraw 1%nat Hlau ltac:(rewrite Hav; cbn; lia)) as H.
    unfold p1. rewrite Hav in H |- *. cbn [nth] in H. lia.
  Qed.

  Lemma path_facts :
    rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem0 (p1 inp rdraw) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (p1 inp rdraw))%Z
    /\ (bv_unsigned (p1 inp rdraw) <= bv_unsigned sp0 + 2107576)%Z
    /\ exists t8, rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem0 (Z_to_bv 64 (bv_unsigned (p1 inp rdraw) + Z.of_nat (length path))) 8 = Some t8.
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct (main_str sp0 a0s path inp mbase brk rdraw tid regs0 mem0 Hav Hva Hvl Hlau Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    unfold p1. rewrite Hav in Sr, Slo, Shi, Slen |- *. cbn [nth] in Sr, Slo, Shi, Slen.
    split; [exact Sr|]. split; [exact Slo|]. split; [lia|].
    pose proof (lay_bsb_nw Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau ltac:(unfold sp_window_hi; lia)) as Hnw.
    destruct (read_word_stack Sv48 (run_segments RSEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 brk rdraw 1 (length path) Hlau
                ltac:(rewrite Hav; cbn; lia) ltac:(rewrite Hav; cbn; lia) Hnw)
      as (t8 & Hl8 & Hr8).
    rewrite Hav in Hr8. cbn [nth] in Hr8.
    exists t8. rewrite w_add_nat in Hr8.
    pose proof (u64_range (cat_argv_ptr (ed_top rdraw) [a0s; path] envv (in_execfn inp) 1)).
    rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs0 mem0 ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack (run_segments RSEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 rdraw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.


  Theorem ref_open_fail_errno : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 41%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 40 = errno_ret e ->
    vals_ev vals 2 = p1 inp rdraw ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 40)) R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x20b14) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P38 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof path_len as HPl.
    destruct path_facts as (Sr & Slo & Shi & t8 & Ht8).
    pose proof (u64_range (p1 inp rdraw)) as Hpr.
    rewrite <- model0_fs.
    eapply (of_tail sp0 (blobs0 a0s path) model0 Hvsp model0_halted model0_lazy model0_fd2 model0_rdr path (p1 inp rdraw) t8 vals);
      try eassumption.
    - apply path_nonul.
    - rewrite P38. apply errno_ret_range. exact He.
    - lia.
    - apply path_below_task_size.
    - rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.


  Lemma of_blockA : forall T,
    (forall vals R M,
       length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 inp rdraw ->
       regs_ok (ENV vals) srA R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M knA ->
       (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
       realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x20b10) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0) T) ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs0 (Z_to_bv 64 0x148d4) mem0 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0) T.
  Proof.
    intros T HA.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_regs_ok sp0 a0s path inp mbase rdraw tid regs0 mem0 Hav Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path inp mbase brk rdraw tid regs0 mem0 Hav Hva Hvl Hlau Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path inp rdraw tid regs0) with (ENV (vals0 sp0 inp rdraw tid regs0)) in HR, HK.
    set (vals := vals0 sp0 inp rdraw tid regs0) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 inp rdraw) by reflexivity.
    clearbody vals.
    pose proof model0_halted as Hh.
    run_blk_keep scr0 40%nat.
    apply (HA vals); try assumption.
    intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x94000);
      [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
  Qed.

  Lemma openat_regs : forall vals R,
    vals_ev vals 2 = p1 inp rdraw -> regs_ok (ENV vals) srA R ->
    getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = p1 inp rdraw
    /\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
  Proof.
    intros vals R P2 HR. repeat split.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (11 : reg). cbn [edenot ev ENV]. exact P2.
    - regv HR (12 : reg). vm_compute. reflexivity.
  Qed.

  Lemma after_openat_fail : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 inp rdraw ->
    regs_ok (ENV vals) srA R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0x20b10) 4) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P2 HR HK Habove.
    rewrite v_addi_pc4 by lia. change (0x20b10 + 4)%Z with 0x20b14%Z.
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals [errno_ret e] (blobs_ev (blobs0 a0s path)) sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    pose proof (env_app_know (run_segments RSEGS rc_inp rc_sp rc_mb) vals [errno_ret e] (blobs_ev (blobs0 a0s path)) M knA ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
    eapply (ref_open_fail_errno e (vals ++ [errno_ret e])); try eassumption.
    - rewrite length_app, HL. reflexivity.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
    - rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
    - apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
      rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
  Qed.

  Theorem ref_open_fail_toolong :
    (4096 <= length path)%nat ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs0 (Z_to_bv 64 0x148d4) mem0 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlong. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 inp rdraw)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word (run_segments RSEGS rc_inp rc_sp rc_mb) (Z_to_bv 64 0x20b10) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_toolong (run_segments RSEGS rc_inp rc_sp rc_mb) R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 (firstn 4096 path)).
    - rewrite A11. rewrite <- (firstn_app_l 4096 path [Z_to_bv 8 0]) at 1 || idtac.
      replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
        by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
      apply (rdn_firstn (run_segments RSEGS rc_inp rc_sp rc_mb) M (length path + 1)); [| lia].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - intros Hin. apply path_nonul. eapply In_firstn. exact Hin.
    - rewrite A11. pose proof path_below_task_size. lia.
    - apply (after_openat_fail ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia.
  Qed.

  Theorem ref_open_fail_empty :
    path = [] ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs0 (Z_to_bv 64 0x148d4) mem0 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hnil. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 inp rdraw)) as Hpr.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word (run_segments RSEGS rc_inp rc_sp rc_mb) (Z_to_bv 64 0x20b10) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_empty (run_segments RSEGS rc_inp rc_sp rc_mb) R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12).
    - split; [cbn; lia|]. split; [intros [] |].
      split; [rewrite A11; pose proof path_below_task_size_lt; rewrite Hnil in *; cbn [length] in *; lia|].
      rewrite A11.
      replace (length path + 1)%nat with 1%nat in Sr by (rewrite Hnil; reflexivity).
      replace (path ++ [Z_to_bv 8 0]) with [Z_to_bv 8 0] in Sr by (rewrite Hnil; reflexivity).
      cbn [length Nat.add app].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  Theorem ref_open_fail_absent :
    (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs0 (Z_to_bv 64 0x148d4) mem0 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlen Hne Hnd Hfs. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 inp rdraw)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word (run_segments RSEGS rc_inp rc_sp rc_mb) (Z_to_bv 64 0x20b10) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_absent (run_segments RSEGS rc_inp rc_sp rc_mb) R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 path).
    - split; [exact Hlen|]. split; [apply path_nonul|].
      split; [rewrite A11; exact path_below_task_size_lt|]. rewrite A11.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - exact Hne.
    - exact Hnd.
    - destruct Hva as (_ & _ & _ & _ & Hs). cbn [tl] in Hs. inversion Hs as [|x l Hx Hl]; subst. exact (proj1 Hx).
    - destruct Hva as (_ & _ & _ & _ & Hs). cbn [tl] in Hs. inversion Hs as [|x l Hx Hl]; subst. exact (proj2 Hx).
    - exact Hfs.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  Corollary ref_open_fail_toolong_w :
    (4096 <= length path)%nat ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs0 (0x148d4 : word) mem0 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H. replace (0x148d4 : word) with (Z_to_bv 64 0x148d4) by (apply bv_eq; reflexivity).
    apply ref_open_fail_toolong. exact H.
  Qed.

  Corollary ref_open_fail_empty_w :
    path = [] ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs0 (0x148d4 : word) mem0 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H. replace (0x148d4 : word) with (Z_to_bv 64 0x148d4) by (apply bv_eq; reflexivity).
    apply ref_open_fail_empty. exact H.
  Qed.

  Corollary ref_open_fail_absent_w :
    (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs0 (0x148d4 : word) mem0 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H1 H2 H3 H4. replace (0x148d4 : word) with (Z_to_bv 64 0x148d4) by (apply bv_eq; reflexivity).
    apply ref_open_fail_absent; assumption.
  Qed.

End OpenFail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
