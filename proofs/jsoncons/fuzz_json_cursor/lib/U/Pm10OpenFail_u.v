(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Hoare Frame
  MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  Spec LibWritev RefNodes. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10ExitBase_u Pm10Exit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.musl Require Import Pm10MemcpyBase_u Pm10Memcpy_u Pm10Memchr_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10Strnlen_u
  Pm10Startup_u Pm10StartupFacts_u Pm10MainEntry_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import LibTail.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10OpenFail_defs_u Pm10OpenFail_tail_u Pm10OpenFail_tail2_u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.

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
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.

  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
  Hypothesis Hfs : sc_fs scfg = true.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw)).
  Definition model0 : Model :=
    mkModelE fds_init (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp0) stdin0 fs0 None (Some tid) None.

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
    destruct Hva as (_ & _ & Hl & _ & _). inversion Hl as [|x l Hx Hl']; subst. inversion Hl'; subst. assumption.
  Qed.

  Lemma path_facts :
    rdn RSEGS mem0 (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (p1 sp0 a0s path envv))%Z
    /\ (bv_unsigned (p1 sp0 a0s path envv) <= bv_unsigned sp0 + 2107576)%Z
    /\ (bv_unsigned (p1 sp0 a0s path envv) + Z.of_nat (length path) + 17 <= 0x800000000000)%Z
    /\ exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (p1 sp0 a0s path envv) + Z.of_nat (length path))) 8 = Some t8.
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct (main_str sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    pose proof (main_str_fits sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hfits 1%nat ltac:(lia)) as Sfit.
    cbn [nth] in Sr, Slo, Shi, Slen, Sfit. unfold p1.
    split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|]. split; [exact Sfit|].
    pose proof (lay_bsb_nw RPH sp0 rdraw [a0s; path] envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    destruct (read_word_stack RPH RSEGS sp0 [a0s; path] envv 1 (length path) uid hw rdraw ltac:(cbn; lia) ltac:(cbn; lia) Hnw)
      as (t8 & Hl8 & Hr8).
    exists t8. rewrite w_add_nat in Hr8.
    pose proof (u64_range (cat_argv_ptr sp0 [a0s; path] envv 1)).
    rewrite (main_entry_rdn_above sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv uid hw rdraw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.

  Theorem ref_open_fail_errno : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
    vals_ev vals 2 = p1 sp0 a0s path envv ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xb8840) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P38 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof path_len as HPl.
    destruct path_facts as (Sr & Slo & Shi & Sfit & t8 & Ht8).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
    rewrite <- model0_fs.
    eapply (of_tail scfg sp0 (blobs0 a0s path hw rdraw) model0 Hvsp model0_halted model0_lazy model0_fd2 path (p1 sp0 a0s path envv) t8 vals);
      try eassumption.
    - apply path_nonul.
    - rewrite P38. apply errno_ret_range. exact He.
    - lia.
    - lia.
    - rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  Lemma of_blockA : forall T,
    (forall vals R M,
       length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
       regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
       (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
       srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xb883c) M (seg_rom RSEGS)) model0) T) ->
    srealizes RSEGS scfg (mkCfg (mkst regs0 (Z_to_bv 64 0x3924c) mem0 (seg_rom RSEGS)) model0) T.
  Proof.
    intros T HA.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_regs_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path envv hw rdraw tid regs0) with (ENV (vals0 sp0 a0s path envv tid regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s path envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
    clearbody vals.
    pose proof model0_halted as Hh.
    run_blk_keep scr0 38%nat.
    apply (HA vals); try assumption.
    intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0xf8000);
      [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
  Qed.

  Lemma openat_regs : forall vals R,
    vals_ev vals 2 = p1 sp0 a0s path envv -> regs_ok (ENV vals) srA R ->
    getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = p1 sp0 a0s path envv
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
    length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    srealizes RSEGS scfg (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0xb883c) 4) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P2 HR HK Habove.
    rewrite v_addi_pc4 by lia. change (0xb883c + 4)%Z with 0xb8840%Z.
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals [errno_ret e] (blobs_ev (blobs0 a0s path hw rdraw)) sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    pose proof (env_app_know RSEGS vals [errno_ret e] (blobs_ev (blobs0 a0s path hw rdraw)) M knA ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path hw rdraw))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
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
    srealizes RSEGS scfg (mkCfg (mkst regs0 (Z_to_bv 64 0x3924c) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlong. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0xb883c) = Some ECALLW) by vmc_refl.
    eapply (rz_openat_toolong RSEGS scfg R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 (firstn 4096 path)).
    - rewrite A11. rewrite <- (firstn_app_l 4096 path [Z_to_bv 8 0]) at 1 || idtac.
      replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
        by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
      apply (rdn_firstn RSEGS M (length path + 1)); [| lia].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - intros Hin. apply path_nonul. eapply In_firstn. exact Hin.
    - apply (after_openat_fail ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia.
  Qed.

  Theorem ref_open_fail_empty :
    path = [] ->
    srealizes RSEGS scfg (mkCfg (mkst regs0 (Z_to_bv 64 0x3924c) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hnil. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0xb883c) = Some ECALLW) by vmc_refl.
    eapply (rz_openat_empty RSEGS scfg R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12).
    - split; [cbn; lia|]. split; [intros [] |]. rewrite A11.
      replace (length path + 1)%nat with 1%nat in Sr by (rewrite Hnil; reflexivity).
      replace (path ++ [Z_to_bv 8 0]) with [Z_to_bv 8 0] in Sr by (rewrite Hnil; reflexivity).
      cbn [length Nat.add app].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  Theorem ref_open_fail_absent :
    (length path <= 4095)%nat -> path <> [] -> openat_plain_name path = true -> fs_lookup fs0 path = None ->
    srealizes RSEGS scfg (mkCfg (mkst regs0 (Z_to_bv 64 0x3924c) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlen Hne Hnd Hfsl. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0xb883c) = Some ECALLW) by vmc_refl.
    eapply (rz_openat_absent RSEGS scfg R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 path).
    - split; [exact Hlen|]. split; [apply path_nonul|]. rewrite A11.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - exact Hne.
    - exact Hnd.
    - exact Hfsl.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  Corollary ref_open_fail_toolong_w :
    (4096 <= length path)%nat ->
    srealizes RSEGS scfg (mkCfg (mkst regs0 (0x3924c : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H. replace (0x3924c : word) with (Z_to_bv 64 0x3924c) by (apply bv_eq; reflexivity).
    apply ref_open_fail_toolong. exact H.
  Qed.

  Corollary ref_open_fail_empty_w :
    path = [] ->
    srealizes RSEGS scfg (mkCfg (mkst regs0 (0x3924c : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H. replace (0x3924c : word) with (Z_to_bv 64 0x3924c) by (apply bv_eq; reflexivity).
    apply ref_open_fail_empty. exact H.
  Qed.

  Corollary ref_open_fail_absent_w :
    (length path <= 4095)%nat -> path <> [] -> openat_plain_name path = true -> fs_lookup fs0 path = None ->
    srealizes RSEGS scfg (mkCfg (mkst regs0 (0x3924c : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H1 H2 H3 H4. replace (0x3924c : word) with (Z_to_bv 64 0x3924c) by (apply bv_eq; reflexivity).
    apply ref_open_fail_absent; assumption.
  Qed.

End OpenFail.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
