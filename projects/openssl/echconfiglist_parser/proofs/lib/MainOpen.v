(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (main_entry is a record over the run's input, with valid_launch and entry_launch_ok_va; the open walk runs over the run's list RSEGS ++ rt_tail, and path_facts/arg0_facts use the launch's argv pointer with a +8 ceiling from argv_ptr_room). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout StepTac
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame SymAux
  Spec RefNodes RefStartup RefStartupFacts RefMainEntry RefMainEntryN LibTail LibDiagKn RefPrintfFirst
  MainDefs MainWalk_defs MainSegs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase RomStable RunTail.
Import ListNotations.
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition regA : list sregion := [(SA (EVar 0) (-224), 176)]%Z.
Lemma covA : log_covered regA (s_log (fst (fst rA))) = true. Proof. vm_compute. reflexivity. Qed.
Definition cA := Eval vm_compute in carryM rA kn_main.
Lemma cA_knA : fst (fst cA) = knA. Proof. vm_compute. reflexivity. Qed.
Lemma rC_facts : s_pc (fst (fst rC)) = 0x26f4e8%Z /\ snd (fst rC) = [] /\ s_log (fst (fst rC)) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Definition regF : list sregion := [(SA (EVar 0) (-240), 16); (SA (ELit 0) 0x2ef3d4, 4)]%Z.
Lemma covF : log_covered regF (s_log (fst (fst rF))) = true. Proof. vm_compute. reflexivity. Qed.
Definition cF := Eval vm_compute in carryM rF knF0.
Lemma cF_knF : fst (fst cF) = knF. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma rF_facts : s_pc (fst (fst rF)) = 0xddb80%Z
  /\ snd (fst rF) = [SCBr false BC_LTU (EAluw ALU_ADD (EVar 40) (ELit 0)) (ELit 18446744073709547521)]%Z
  /\ snd (fst cF) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition scF (e : Z) : Prop :=
  branch_taken BC_LTU (sext 64 (alu32 ALU_ADD (low32 (errno_ret e)) (low32 (Z_to_bv 64 0))))
               (Z_to_bv 64 18446744073709547521) = false.
Lemma scF_openat : forall e, In e openat_errnos -> scF e.
Proof.
  intros e He. unfold openat_errnos in He. cbn [In] in He.
  destruct He as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity.
Qed.
Lemma scF_ENAMETOOLONG : scF ENAMETOOLONG. Proof. vm_compute. reflexivity. Qed.
Lemma scF_ENOENT : scF ENOENT. Proof. vm_compute. reflexivity. Qed.
Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof.
  intros e He. unfold openat_errnos in He. cbn in He.
  unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.
Lemma errno_ret_range : forall e, (1 <= e <= 4095)%Z ->
  (2 ^ 64 - 4095 <= bv_unsigned (errno_ret e))%Z.
Proof. intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  replace ((- e) mod 2 ^ 64)%Z with (2 ^ 64 - e)%Z; [lia|].
  apply Z.mod_unique with (q := (-1)%Z); lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
(* [comment removed for export] *)
Definition regU : list sregion := [(SA (EVar 0) (-128), 80)]%Z.
Lemma covU : log_covered regU (s_log (fst (fst rU))) = true. Proof. vm_compute. reflexivity. Qed.
Definition cU := Eval vm_compute in carryM rU kn_mainN.
Lemma cU_knU : fst (fst cU) = knU. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma path_nonul : forall a0s path, valid_argv [a0s; path] -> ~ In (Z_to_bv 8 0) path.
Proof.
  intros a0s path Hva. destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
Qed.
Lemma path_len : forall a0s path, valid_argv [a0s; path] -> (Z.of_nat (length path) <= 131071)%Z.
Proof.
  intros a0s path Hva. destruct Hva as (_ & _ & Hl & _). inversion Hl as [|x l Hx Hl']; subst. inversion Hl'; subst. assumption.
Qed.

Section Open.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variables (brk mbase : word) (lim : Z) (fs0 : Fs) (stdin0 : InputStream).
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  (** 75d69e00: [main_entry] is a RECORD over the run's whole input
      ([RefStartup.v:68]: [inp], [mbase], [entry], [sp0], the draw, tid, regs,
      mem).  The input is the one this section already builds for [model0], and
      the entry is the image's, exactly as [RefStartup.v:257] spells it. *)
  Let inp : ProcInput := mkProcInputC [a0s; path] envv fs0 stdin0.
  Let entryw : word := (0xdd764 : word).
  Hypothesis ME : main_entry inp mbase entryw sp0 rdraw tid regs0 mem0.
  (** [Run.valid_input]'s launch clause and [Run.valid_entry]'s FIFTH conjunct;
      the interface OpensslResume published, exported at the
      [RefStartup -> MainTop] boundary.  No new Section Variable is needed for
      the reroute: [bsb_bound]'s [v] is the literal [Sv48], [mbase] is already
      a Variable, and [ph]/[entry] are its own binders fixed by unification. *)
  Hypothesis Hvl  : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  (* main's walk from its entry reaches the target call (time() reads the vDSO), so the
     segments of the file-argument path are walks over the run's list *)
  Context {RT : RunTail}.
  Local Notation VS := (RSEGS ++ rt_tail) (only parsing).

  Let model0 : Model := MainDefs.model0 tid brk mbase sp0 rdraw lim inp.
  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).
  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  (** [p1]'s discharged signature: [RefMainEntry.v] is ported to the [inp]/[ed_top] shape. *)
  Let pp : word := p1 inp a0s path envv rdraw.

  Lemma model0_halted : m_halted model0 = None. Proof. reflexivity. Qed.
  Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
  Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.
  Lemma model0_fd1 : fd_lookup (m_fds model0) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)). Proof. reflexivity. Qed.
  Lemma model0_fs : m_fs model0 = fs0. Proof. reflexivity. Qed.

  Definition regA_w : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp0 - 224), 176%Z)].

  (* [comment removed for export] *)
  Definition frameA (M : word -> option byte) : Prop :=
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x26e9f0))
    /\ forall i, (i < 8)%nat -> exists w : word,
         rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 120 + 8 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 w).

  (* [comment removed for export] *)
  (* The pointer's ceiling is [+ 8], not the pre-revision [+ 17]: the lemma it came from,
     [build_stack_bytes_within_span], is deleted upstream as false of the kernel's block,
     and at this revision the bound is the model's own chain -- [MuslStrlen.argv_ptr_room]
     (the string's NUL is followed inside the image by at least nine more bytes),
     [PropExec.length_entry_stack_image_launch] (the image ends at [ed_top]) and
     [PropExec.entry_page_top_within_window] ([ed_top <= 2^47]).  [+ 8] is what every
     consumer takes ([RefOpenFailCS.v:45,144], [RefReadErr], [RefUsageCS.v:55,241]).
     [entry_stack_fits] no longer enters the proof; the premise is kept so callers stay. *)
  Lemma path_facts :
    rdn RSEGS mem0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned pp)%Z
    /\ (bv_unsigned pp <= bv_unsigned sp0 + 2107648)%Z
    /\ (entry_stack_fits sp0 [a0s; path] envv -> (bv_unsigned pp + Z.of_nat (length path) + 8 <= 0x800000000000)%Z)
    /\ exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8.
  Proof using Hva Hve Hvsp Htid ME Hvl Hlau.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hav : in_argv inp = [a0s; path]) by reflexivity.
    (* [RefMainEntryN.main_strN] at k = 1; its argv/envp are this input's, [a0s; path]/[envv]
       by conversion, so every conjunct closes by [exact]. *)
    destruct (main_strN inp mbase entryw sp0 brk rdraw tid regs0 mem0 Hva Hve Hvsp Htid Hvl Hlau ME
                1%nat ltac:(rewrite Hav; cbn; lia)) as (Sr & Slo & Shi & _ & St8).
    assert (Hroom : (bv_unsigned pp + Z.of_nat (length path) + 9
                     <= bv_unsigned sp0 + Z.of_nat (length (entry_stack_image inp mbase RPH entryw sp0 rdraw)))%Z).
    { (* Discharged BY TYPE. *)
      pose proof (MuslStrlen.argv_ptr_room Sv48 inp mbase RPH entryw sp0 brk rdraw) as Hr.
      repeat lazymatch type of Hr with
             | ?P -> _ =>
                 let h := fresh "Hd" in
                 assert (h : P) by
                   first [ exact Hva | exact Hve | exact Hvl | exact Hlau
                         | unfold sp_window_lo; lia
                         | unfold sp_window_hi; lia ];
                 specialize (Hr h); clear h
             end.
      exact (Hr 1%nat ltac:(rewrite Hav; cbn; lia)). }
    pose proof (length_entry_stack_image_launch Sv48 inp mbase RPH entryw sp0 brk rdraw Hlau) as Himg.
    pose proof (entry_page_top_within_window Sv48 inp mbase sp0 brk rdraw Hlau) as Htop.
    unfold entry_page_top, va_stack_top, sp_window_hi in Htop.
    split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|]. split.
    - intros _. lia.
    - exact St8.
  Qed.

  (* [comment removed for export] *)
  Lemma seg_A : forall T,
    (forall vals R M,
       length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 5 = tid ->
       regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
       frame_mod mem0 M regA_w -> frameA M ->
       realizes VS (mkCfg (mkst R (Z_to_bv 64 0x27aa74) M (seg_rom VS)) model0) T) ->
    realizes VS (mkCfg (mkst regs0 (Z_to_bv 64 0xdd8b8) mem0 (seg_rom VS)) model0) T.
  Proof using Hva Hve Hvsp Htid ME Hvl Hlau.
    intros T HA. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [RefMainEntry]'s Section MainEntryProofs exports are [Proof using All]
       ([RefMainEntry.v:238-258]); both argv/envp ties are [eq_refl] on this input. *)
    pose proof (main_regs_ok inp mbase entryw sp0 brk a0s path envv rdraw tid regs0 mem0
                  Hva Hve Hvsp Htid eq_refl eq_refl Hvl Hlau ME) as HR.
    pose proof (main_know_ok inp mbase entryw sp0 brk a0s path envv rdraw tid regs0 mem0
                  Hva Hve Hvsp Htid eq_refl eq_refl Hvl Hlau ME) as HK.
    change (E0 inp sp0 a0s path envv rdraw tid regs0) with (ENV (vals0 inp sp0 a0s path envv rdraw tid regs0)) in HR, HK.
    set (vals := vals0 inp sp0 a0s path envv rdraw tid regs0) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals0; rewrite !length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = pp) by reflexivity.
    assert (P5 : vals_ev vals 5 = tid) by reflexivity.
    clearbody vals.
    eapply (rz_run_lf_rt RSEGS FUELM STOPSM scrA 0xdd8b8%Z sr_main kn_main 40%nat (fst (fst rA)) (snd (fst rA)) (snd rA)
              (fst (fst cA)) (snd (fst cA)) (snd cA) (ENV vals) mem0 (seg_rom VS) regs0 model0);
      [ vm_cast_no_check (@eq_refl _ rA) | vm_cast_no_check (@eq_refl _ cA) | exact HR | exact HK
      | apply Forall_nil | apply Forall_nil | reflexivity | reflexivity | ].
    intros R M HR' HK' EQM LF. rewrite cA_knA in HK'.
    change (s_pc (fst (fst rA))) with 0x27aa74%Z. change (s_regs (fst (fst rA))) with srA in HR'.
    assert (RF : regions_flat (ENV vals) regA).
    { intros r Hr. unfold regA in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
      unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]. rewrite P0. lia. }
    pose proof (log_covered_frame (ENV vals) mem0 regA _ covA RF LF) as FR. rewrite <- EQM in FR.
    unfold regA, rdenot, estart in FR. cbn [map fst snd a_base a_off edenot ev ENV] in FR. rewrite P0 in FR.
    replace (bv_unsigned sp0 + -224)%Z with (bv_unsigned sp0 - 224)%Z in FR by lia.
    apply (HA vals R M HL P0 P2 P5 HR' HK' FR).
    (* [comment removed for export] *)
    split.
    - krdv HK' 0%nat (-56)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia|].
      unfold adenot, v_addi in Hrd. cbn [a_base a_off edenot ev ENV] in Hrd. rewrite P0 in Hrd.
      replace (bv_unsigned sp0 + -56)%Z with (bv_unsigned sp0 - 56)%Z in Hrd by lia. exact Hrd.
    - intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [ .. | lia];
      lazymatch goal with |- exists w, rdn _ _ (Z_to_bv 64 (?b + 8 * Z.of_nat ?k)) 8 = _ =>
        let off := eval vm_compute in (-120 + 8 * Z.of_nat k)%Z in
        krdv HK' 0%nat off 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia|];
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENV] in Hrd; rewrite P0 in Hrd;
        eexists; replace (b + 8 * Z.of_nat k)%Z with (bv_unsigned sp0 + off)%Z by (cbn; lia); exact Hrd
      end.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_regs' : forall vals R,
    vals_ev vals 2 = pp -> regs_ok (ENV vals) srA R ->
    getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = pp
    /\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
  Proof.
    intros vals R P2 HR. repeat split.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (11 : reg). cbn [edenot ev ENV]. exact P2.
    - regv HR (12 : reg). vm_compute. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma path_at_A : forall M,
    frame_mod mem0 M regA_w -> (length path <= 4095)%nat ->
    (length path <= 4095)%nat /\ ~ In (Z_to_bv 8 0) path /\ rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]).
  Proof using Hva Hve Hvsp Htid ME Hvl Hlau.
    intros M [FM _] Hlen. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (path_len a0s path Hva) as HPl.
    split; [exact Hlen|]. split; [apply (path_nonul a0s path Hva)|].
    pose proof (u64_range pp).
    rewrite <- Sr. apply rdn_agree. intros j Hj. apply FM. cbn [outside]. split; [|exact I].
    unfold in_rng. unorm. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma seg_C : forall vals R M (mo : Model) T,
    m_halted mo = None -> m_vm_lazy mo = [] ->
    length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
    (forall R', getr R' 1 = Z_to_bv 64 0xdd914 -> getr R' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) ->
                getr R' 4 = Z_to_bv 64 0x2ef478 -> getr R' 8 = Z_to_bv 64 2 -> getr R' 10 = Z_to_bv 64 0x10000 ->
                getr R' 18 = pp -> getr R' 20 = Z_to_bv 64 3 -> getr R' 21 = Z_to_bv 64 0x10000 ->
                realizes VS (mkCfg (mkst R' (Z_to_bv 64 0x26f4e8) M (seg_rom VS)) mo) T) ->
    realizes VS (mkCfg (mkst (regupd R 10 (Z_to_bv 64 3)) (Z_to_bv 64 0x27aa78) M (seg_rom VS)) mo) T.
  Proof.
    intros vals R M mo T Hh Hlazy HL P0 P2 HR HK HC. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (regs_set_a0 (ENV vals) srA R (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR3.
    change (sr_upd srA (ridx 10) (ELit 3)) with srC0 in HR3.
    eapply (rz_run_rt RSEGS FUELM STOPSM noscr 0x27aa78%Z srC0 knA 40%nat (fst (fst rC)) (snd (fst rC)) (snd rC)
              (fst (fst (carryM rC knA))) (snd (fst (carryM rC knA))) (snd (carryM rC knA)) (ENV vals) M (seg_rom VS) _ mo);
      [ vm_cast_no_check (@eq_refl _ rC) | vm_cast_no_check (@eq_refl _ (carryM rC knA)) | exact HR3 | exact HK
      | apply Forall_nil | scs_nil | exact Hh | exact Hlazy | ].
    intros R' M' HR' HK' EQM. destruct rC_facts as (Epc & _ & Elog).
    rewrite Epc. change (s_regs (fst (fst rC))) with srC in HR'.
    assert (EM : M' = M) by (rewrite EQM, Elog; reflexivity). rewrite EM.
    apply HC; first [ regv HR' (1:reg); reflexivity | regv HR' (4:reg); reflexivity | regv HR' (8:reg); reflexivity
                    | regv HR' (10:reg); reflexivity | regv HR' (20:reg); reflexivity | regv HR' (21:reg); reflexivity
                    | regv HR' (18:reg); cbn [edenot ev ENV]; exact P2
                    | regv HR' (2:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV]; rewrite P0; f_equal; lia ].
  Qed.
  (* [comment removed for export] *)
  Definition regF_w : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp0 - 240), 16%Z); (Z_to_bv 64 0x2ef3d4, 4%Z)].

  Lemma seg_F : forall (e : Z) vals R M (mo : Model) T,
    m_halted mo = None -> m_vm_lazy mo = [] ->
    (1 <= e <= 4095)%Z -> scF e ->
    length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
    (forall R' M', getr R' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R' 4 = Z_to_bv 64 0x2ef478 -> getr R' 18 = pp ->
                  frame_mod M M' regF_w ->
                  realizes VS (mkCfg (mkst R' (Z_to_bv 64 0xddb80) M' (seg_rom VS)) mo) T) ->
    realizes VS (mkCfg (mkst (regupd R 10 (errno_ret e)) (Z_to_bv 64 0x27aa78) M (seg_rom VS)) mo) T.
  Proof.
    intros e vals R M mo T Hh Hlazy He HSC HL P0 P2 HR HK HC. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    pose proof (env_app_regs vals [errno_ret e] (blobs_ev (blobs0 a0s path)) srA R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know RSEGS vals [errno_ret e] (blobs_ev (blobs0 a0s path)) M knA ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK1.
    change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR1, HK1.
    assert (Q40 : vals_ev (vals ++ [errno_ret e]) 40 = errno_ret e).
    { rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
    assert (Q0 : vals_ev (vals ++ [errno_ret e]) 0 = sp0) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev (vals ++ [errno_ret e]) 2 = pp) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    set (vals1 := vals ++ [errno_ret e]) in *. clearbody vals1.
    pose proof (regs_set_a0 (ENV vals1) srA R (errno_ret e) (EVar 40) HR1 ltac:(cbn [edenot ev ENV]; exact Q40)) as HR2.
    change (sr_upd srA (ridx 10) (EVar 40)) with srF0 in HR2.
    assert (HK2 : know_ok RSEGS (ENV vals1) M knF0).
    { unfold knF0. apply Forall_cons; [| exact HK1]. apply krange_intro. cbn [edenot ev ENV]. rewrite Q40.
      pose proof (errno_ret_range e He). pose proof (u64_range (errno_ret e)). lia. }
    eapply (rz_run_lf_rt RSEGS FUELM STOPSM scrF 0x27aa78%Z srF0 knF0 41%nat (fst (fst rF)) (snd (fst rF)) (snd rF)
              (fst (fst cF)) (snd (fst cF)) (snd cF) (ENV vals1) M (seg_rom VS) _ mo);
      [ vm_cast_no_check (@eq_refl _ rF) | vm_cast_no_check (@eq_refl _ cF) | exact HR2 | exact HK2
      | | rewrite (proj2 (proj2 rF_facts)); apply Forall_nil | exact Hh | exact Hlazy | ].
    { rewrite (proj1 (proj2 rF_facts)). apply Forall_cons; [|apply Forall_nil].
      unfold sc_denot. cbn [edenot ev ENV]. rewrite Q40. exact HSC. }
    intros R' M' HR' HK' EQM LF.
    rewrite (proj1 rF_facts). change (s_regs (fst (fst rF))) with srF in HR'.
    assert (RF : regions_flat (ENV vals1) regF).
    { intros r Hr. unfold regF in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]];
        unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]; rewrite ?Q0, ?(u_small 0) by lia; lia. }
    pose proof (log_covered_frame (ENV vals1) M regF _ covF RF LF) as FR. rewrite <- EQM in FR.
    unfold regF, rdenot, estart in FR. cbn [map fst snd a_base a_off edenot ev ENV] in FR. rewrite Q0, ?(u_small 0) in FR by lia.
    replace (bv_unsigned sp0 + -240)%Z with (bv_unsigned sp0 - 240)%Z in FR by lia.
    apply (HC R' M').
    - regv HR' (2:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite Q0. f_equal; lia.
    - regv HR' (4:reg). reflexivity.
    - regv HR' (18:reg). cbn [edenot ev ENV]. exact Q2.
    - exact FR.
  Qed.
End Open.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Usage.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable model0 : Model.
  (** 75d69e00.  Unlike [Section Open], this section does NOT build the run's
      input -- it takes [av]/[envv] and an opaque [model0] -- so the input and
      the launch facts are parameters here, with [av]/[envv] tied to [inp] by
      [Hargv]/[Henvp] as this unit's ported [RefMainEntry.v:92-119] does. *)
  Variable inp : ProcInput.
  Variables (mbase brk entryw : word).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Henvp : in_envp inp = envv.
  (** [Run.valid_input]'s launch clause and [Run.valid_entry]'s FIFTH conjunct,
      spelled exactly as [Section Open] and [MainTop]'s section carry them. *)
  Hypothesis Hvl  : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis ME : main_entry inp mbase entryw sp0 rdraw tid regs0 mem0.
  Hypothesis Hargc : length av <> 2%nat.
  Hypothesis Hh0 : m_halted model0 = None.
  Hypothesis Hlazy0 : m_vm_lazy model0 = [].

  Definition ENVU (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).
  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Definition regU_w : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp0 - 128), 80%Z)].

  (* [comment removed for export] *)
  Definition frameU (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x26e9f0))
    /\ (exists w : word, rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 64)) 8 = Some (word_to_le_bytes 8 w))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 72)) 8 = Some (word_to_le_bytes 8 (getr R 9))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 80)) 8 = Some (word_to_le_bytes 8 (getr R 18))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 88)) 8 = Some (word_to_le_bytes 8 (getr R 19))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 96)) 8 = Some (word_to_le_bytes 8 (getr R 20))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 104)) 8 = Some (word_to_le_bytes 8 (getr R 21))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 112)) 8 = Some (word_to_le_bytes 8 (getr R 22))
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 120)) 8 = Some (word_to_le_bytes 8 (getr R 23)).

  (* [comment removed for export] *)
  Lemma seg_U : forall T,
    (forall R M,
       getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 4 = Z_to_bv 64 0x2ef478 -> getr R 8 = Z_to_bv 64 2 ->
       getr R 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
       frame_mod mem0 M regU_w -> frameU R M ->
       rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + 8)) 8 = Some (word_to_le_bytes 8 (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0)) ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xdda70) M (seg_rom RSEGS)) model0) T) ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0xdd8b8) mem0 (seg_rom RSEGS)) model0) T.
  Proof using All.
    intros T HU. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
    (* [RefMainEntryN]'s exports are over the input ([RefMainEntryN.v:31-56]); [Hargv]/[Henvp]
       carry this section's [av]/[envv] premises onto it. *)
    assert (Hva_in : valid_argv (in_argv inp)) by (rewrite Hargv; exact Hva).
    assert (Hve_in : valid_envp (in_envp inp)) by (rewrite Henvp; exact Hve).
    pose proof (main_regs_okN inp mbase entryw sp0 brk rdraw tid regs0 mem0 Hva_in Hve_in Hvsp Htid Hvl Hlau ME) as HR.
    pose proof (main_know_okN inp mbase entryw sp0 brk rdraw tid regs0 mem0 Hva_in Hve_in Hvsp Htid Hvl Hlau ME) as HK.
    pose proof (evN_argc inp mbase entryw sp0 brk rdraw tid regs0 mem0 Hva_in Hve_in Hvsp Htid Hvl Hlau ME) as Hac.
    change (EN inp sp0 rdraw tid regs0) with (ENVU (valsN inp sp0 rdraw tid regs0)) in HR, HK, Hac.
    set (vals := valsN inp sp0 rdraw tid regs0) in *.
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0).
    { change (vals_ev vals 1) with (p0N inp rdraw). unfold p0N. rewrite Hargv, Henvp. reflexivity. }
    assert (PJ : forall i, (i < 32)%nat -> vals_ev vals (6 + i) = getr regs0 (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. exact (evN_junk inp sp0 rdraw tid regs0 i Hi). }
    cbn [ev ENVU] in Hac.
    clearbody vals.
    eapply (rz_run_lf RSEGS FUELM STOPSM scrU 0xdd8b8%Z sr_mainN kn_mainN 40%nat (fst (fst rU)) (snd (fst rU)) (snd rU)
              (fst (fst cU)) (snd (fst cU)) (snd cU) (ENVU vals) mem0 (seg_rom RSEGS) regs0 model0);
      [ vm_cast_no_check (@eq_refl _ rU) | vm_cast_no_check (@eq_refl _ cU) | exact HR | exact HK
      | | apply Forall_nil | exact Hh0 | exact Hlazy0 | ].
    { (* [comment removed for export] *)
      lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [|apply Forall_nil]. unfold sc_denot. cbn [branch_taken edenot ev ENVU]. rewrite Hac.
      unfold bv_eqb. rewrite (u_argcN inp Hva_in), Hargv. change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
      apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    intros R M HR' HK' EQM LF. rewrite cU_knU in HK'.
    change (s_pc (fst (fst rU))) with 0xdda70%Z. change (s_regs (fst (fst rU))) with srU in HR'.
    assert (RF : regions_flat (ENVU vals) regU).
    { intros r Hr. unfold regU in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
      unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENVU]. rewrite P0. lia. }
    pose proof (log_covered_frame (ENVU vals) mem0 regU _ covU RF LF) as FR. rewrite <- EQM in FR.
    unfold regU, rdenot, estart in FR. cbn [map fst snd a_base a_off edenot ev ENVU] in FR. rewrite P0 in FR.
    replace (bv_unsigned sp0 + -128)%Z with (bv_unsigned sp0 - 128)%Z in FR by lia.
    apply (HU R M).
    - regv HR' (2:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVU]. rewrite P0. f_equal; try lia.
    - regv HR' (4:reg). reflexivity.
    - regv HR' (8:reg). reflexivity.
    - regv HR' (11:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVU]. rewrite P0. f_equal; try lia.
    - exact FR.
    - (* [comment removed for export] *)
      unfold frameU.
      repeat split.
      + krdv HK' 0%nat (-56)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        replace (bv_unsigned sp0 - 56)%Z with (bv_unsigned sp0 + -56)%Z by lia. exact Hrd.
      + eexists. krdv HK' 0%nat (-64)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        replace (bv_unsigned sp0 - 64)%Z with (bv_unsigned sp0 + -64)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-72)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (9:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 72)%Z with (bv_unsigned sp0 + -72)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-80)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (18:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 80)%Z with (bv_unsigned sp0 + -80)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-88)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (19:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 88)%Z with (bv_unsigned sp0 + -88)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-96)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (20:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 96)%Z with (bv_unsigned sp0 + -96)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-104)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (21:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 104)%Z with (bv_unsigned sp0 + -104)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-112)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (22:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 112)%Z with (bv_unsigned sp0 + -112)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-120)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (23:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 120)%Z with (bv_unsigned sp0 + -120)%Z by lia. exact Hrd.
    - (* [comment removed for export] *)
      krdv HK' 0%nat 8%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
      unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0, P1 in Hrd. exact Hrd.
  Qed.

  (* [comment removed for export] *)
  (* As [path_facts]: the pointer is the launch's ([CatExec.v:332-334]) and its ceiling is
     [+ 8], the model's chain argv_ptr_room / length_entry_stack_image_launch /
     entry_page_top_within_window; [+ 8] is what [RefUsageCS.v:55,241] takes. *)
  Lemma arg0_facts :
    rdn RSEGS mem0 (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) (length (nth 0 av []) + 1) = Some (nth 0 av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) <= bv_unsigned sp0 + 2107648)%Z
    /\ (Z.of_nat (length (nth 0 av [])) <= 131071)%Z
    /\ (exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) + Z.of_nat (length (nth 0 av [])))) 8 = Some t8)
    /\ (entry_stack_fits sp0 av envv -> (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) + Z.of_nat (length (nth 0 av [])) + 8 <= 0x800000000000)%Z)
    /\ ~ In (Z_to_bv 8 0) (nth 0 av []).
  Proof using AMB Hva Hve Hvsp Htid Hargv Henvp Hvl Hlau ME.
    (* [lia] below must not read the section's [Hargc], which this lemma does not take *)
    try clear Hargc.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
    assert (Hva_in : valid_argv (in_argv inp)) by (rewrite Hargv; exact Hva).
    assert (Hve_in : valid_envp (in_envp inp)) by (rewrite Henvp; exact Hve).
    assert (Hk : (0 < length (in_argv inp))%nat) by (rewrite Hargv; lia).
    destruct (main_strN inp mbase entryw sp0 brk rdraw tid regs0 mem0 Hva_in Hve_in Hvsp Htid Hvl Hlau ME 0%nat Hk)
      as (Sr & Slo & Shi & Slen & St8).
    (* Discharged BY TYPE. *)
    pose proof (MuslStrlen.argv_ptr_room Sv48 inp mbase RPH entryw sp0 brk rdraw) as Hroom.
    repeat lazymatch type of Hroom with
           | ?P -> _ =>
               let h := fresh "Hd" in
               assert (h : P) by
                 first [ exact Hva_in | exact Hve_in | exact Hvl | exact Hlau
                       | unfold sp_window_lo; lia
                       | unfold sp_window_hi; lia ];
               specialize (Hroom h); clear h
           end.
    specialize (Hroom 0%nat Hk).
    pose proof (length_entry_stack_image_launch Sv48 inp mbase RPH entryw sp0 brk rdraw Hlau) as Himg.
    pose proof (entry_page_top_within_window Sv48 inp mbase sp0 brk rdraw Hlau) as Htop.
    unfold entry_page_top, va_stack_top, sp_window_hi in Htop.
    rewrite Hargv, Henvp in Sr, Slo, Shi, St8, Hroom. rewrite Hargv in Slen.
    split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|]. split; [exact Slen|]. split; [exact St8|]. split.
    - intros _. lia.
    - destruct Hva as (_ & _ & _ & Hn & _). apply (proj1 (Forall_forall _ _) Hn). apply nth_In. lia.
  Qed.
End Usage.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
