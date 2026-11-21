(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes Frame MmapSim AllocSim FileSim AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymAux Spec RefNodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import U9Startup U9MainEntry. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import Hoare MemSplit ArgvSpan. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import U9PilotOOM_defs U9PilotOOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition STOPS_F : list Z := [0x1a6e8]%Z.
Definition rBF {RCa1 : RunCtx}  := Eval vm_compute in sym_exec (run_segments RSEGS rc_inp rc_sp rc_mb) FUEL true STOPS_F scr0 ssB0 [].
Definition srBF {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rBF)).
(* [comment removed for export] *)
Definition regsF : list sregion := [(SA (EVar 0) (-8388608)%Z, 8388608%Z)].

Lemma front_itinerary {RCa1 : RunCtx}  :
  (s_pc (fst (fst rBF)), snd (fst rBF), s_log (fst (fst rBF))) = (0x1a6e8%Z, [], [])
  /\ log_covered regsF logA = true.
Proof. vm_compute. split; reflexivity. Qed.

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require U9World.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP9 Require Import U9SoDefs U9PrintfFirst.

(* a worker port727 (): RefNodes.path_at's TASK_SIZE conjunct for argv[1], from the launch (as S0OpenFail). *)
Lemma argv1_below_task_size : forall (sp0 brk mbase : word) (rdraw : EntryDraw) (inp : ProcInput) a0s path,
  in_argv inp = [a0s; path] -> entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp ->
  (bv_unsigned (p1 inp rdraw) + Z.of_nat (length path) < TASK_SIZE)%Z.
Proof.
  intros sp0 brk mbase rdraw inp a0s path Hav Hlau.
  pose proof (argv_str_below_task_size inp mbase sp0 brk rdraw 1%nat Hlau ltac:(rewrite Hav; cbn; lia)) as H.
  unfold p1. rewrite Hav in H |- *. cbn [nth] in H. lia.
Qed.

Section Front.
  (* a worker port727 (): over the launch input (argv = [a0s; path] by Hav), the ruled VLAUNCH + LOK and the
     launch's channel reader, as S0PilotOOM (whose model0 / model1g this section's MODEL0 / MODEL1 are). *)
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
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.  (* a worker (A1) tool *)
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

  Abbreviation MODEL0 := (model0 sp0 inp rdraw tid brk mbase).
  Abbreviation MODEL1 := (model1g sp0 inp rdraw tid brk mbase (FdFile path (Z_to_bv 64 0))).

  (* [comment removed for export] *)
  Definition at_malloc (T : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte),
      getr R 1 = Z_to_bv 64 0x1494c -> getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) ->
      getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x74250 ->
      getr R 8 = Z_to_bv 64 2 ->                                        (* [comment removed for export] *)
      getr R 10 = Z_to_bv 64 65536 -> getr R 18 = p1 inp rdraw ->
      getr R 20 = Z_to_bv 64 3 -> getr R 21 = Z_to_bv 64 65536 ->
      frame_mod mem0 M [(Z_to_bv 64 (bv_unsigned sp0 - 8388608), 8388608%Z)] ->
      U9World.main_frame (bv_unsigned sp0) M ->
      realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x1a6e8) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) MODEL1) T.

  Lemma front_to_malloc : forall KA T,
    open_err_branch sp0 a0s path inp rdraw tid mem0 brk mbase KA -> at_malloc T ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs0 (Z_to_bv 64 0x148f8) mem0 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) MODEL0) (t_alt2 KA T).
  Proof.
    intros KA T HKA HT.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s path inp mbase rdraw tid regs0 mem0 Hav Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path inp mbase brk rdraw tid regs0 mem0 Hav Hva Hvl Hlau Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path inp rdraw tid regs0) with (ENV a0s path (vals0 sp0 inp rdraw tid regs0)) in HR, HK.
    set (vals := vals0 sp0 inp rdraw tid regs0) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 inp rdraw) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 inp rdraw) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    destruct (main_str sp0 a0s path inp mbase brk rdraw tid regs0 mem0 Hav Hva Hvl Hlau Hvsp ME 1%nat ltac:(lia))
      as (Sr & Slo & Shi & Slen).
    rewrite Hav in Sr, Slo, Shi, Slen. cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_lf HR HK FUEL STOPS scr0 40%nat.
    clear HR HK. intros R M HR HK EQM LF. cbn [s_pc s_regs s_log] in HR, EQM, LF |- *.
    (* [comment removed for export] *)
    assert (FM : frame_mod mem0 M [(Z_to_bv 64 (bv_unsigned sp0 - 8388608), 8388608%Z)]).
    { rewrite EQM.
      replace [(Z_to_bv 64 (bv_unsigned sp0 - 8388608), 8388608%Z)] with (map (rdenot (ENV a0s path vals)) regsF).
      2:{ unfold regsF, rdenot, estart. cbn [map fst snd a_base a_off edenot ev ENV]. rewrite P0.
          replace (bv_unsigned sp0 + -8388608)%Z with (bv_unsigned sp0 - 8388608)%Z by lia. reflexivity. }
      apply log_covered_frame; [exact (proj2 front_itinerary) | | exact LF].
      intros r Hr. unfold regsF in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
      unfold flat, estart. cbn [fst snd a_base a_off edenot ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    assert (Sr' : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (p1 inp rdraw) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM. unfold p1. rewrite Hav.
      rewrite (rdn_mem_denot_above (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV a0s path vals) mem0 _ 0%nat 0x95000);
        [exact Sr | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia
        | match goal with |- context [cat_argv_ptr ?t ?av ?ev ?ef ?k] =>
            pose proof (u64_range (cat_argv_ptr t av ev ef k)) end; lia]. }
    (* [comment removed for export] *)
    eapply (rz_openat_file (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ _ MODEL0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17%bv : reg). reflexivity.
    - regv HR (10%bv : reg). apply bv_eq. reflexivity.
    - regv HR (12%bv : reg). vm_compute. reflexivity.
    - rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - split; [exact Hplen|]. split; [apply (path_nonul a0s path Hva)|].
      regv HR (11%bv : reg). cbn [edenot ev ENV]. rewrite P2.
      split; [exact (argv1_below_task_size sp0 brk mbase rdraw inp a0s path Hav Hlau) | exact Sr'].
    - exact Hpne.
    - exact Hpnd.
    - apply (path_noslash a0s path Hva).
    - apply (path_nodotdot a0s path Hva).
    - rewrite m0_fs. exact Hfile.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x21d74 + 4)%Z with 0x21d78%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know (run_segments RSEGS rc_inp rc_sp rc_mb) vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV a0s path (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + intros x Hx. rewrite EQM. apply (mem_denot_above (ENV a0s path vals) mem0 _ 0%nat 0x95000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x21d74 + 4)%Z with 0x21d78%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert (fds0) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) MODEL0) with MODEL1.
      pose proof (regs_set_a0 (ENV a0s path vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      clear HR. rename HR2 into HR. clear EQM LF.
      (* [comment removed for export] *)
      run_block_lf HR HK FUEL STOPS_F scr0 40%nat.
      clear HR. intros R2 M2 HR HK2 EQM2 _. cbn [s_pc s_regs s_log mem_denot] in HR, EQM2 |- *. subst M2. clear HK2.
      apply HT.
      + regv HR (1%bv : reg). reflexivity.
      + regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. try (f_equal; lia); try reflexivity.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
      + regv HR (8%bv : reg). reflexivity.
      + regv HR (10%bv : reg). reflexivity.
      + regv HR (18%bv : reg). cbn [edenot ev ENV]. exact P2.
      + regv HR (20%bv : reg). reflexivity.
      + regv HR (21%bv : reg). reflexivity.
      + exact FM.
      + (* [comment removed for export] *)
        constructor; unfold U9World.cell;
          lazymatch goal with |- rdn _ _ (Z_to_bv 64 (_ - ?k)) 8 = _ =>
            let H := fresh "Hc" in
            krdv HK 0%nat (- k)%Z 8%nat H;
            [ apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
            | unfold adenot, v_addi in H; cbn [a_base a_off edenot ev ENV] in H; rewrite ?edenot_add_lit in H;
              unfold adenot, v_addi in H; cbn [a_base a_off edenot ev ENV] in H; rewrite ?P0 in H;
              replace (bv_unsigned sp0 - k)%Z with (bv_unsigned sp0 + - k)%Z by lia; exact H ]
          end.
  Qed.
End Front.

(* [comment removed for export] *)
Section FrontDot.
  (* a worker port727 (): as Section Front, with argv = [a0s; dot_path]. *)
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable inp : ProcInput.
  Local Notation envv := (in_envp inp) (only parsing).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
#[local] Instance RC_a1_2 : RunCtx := mkRunCtx inp sp0 mbase.  (* a worker (A1) tool *)
  Hypothesis Hav : in_argv inp = [a0s; dot_path].
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hcr : in_channel_reader inp = true.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.

  Abbreviation MODEL0 := (model0 sp0 inp rdraw tid brk mbase).
  Abbreviation MODEL1 := (model1g sp0 inp rdraw tid brk mbase FdDir).

  (* [comment removed for export] *)
  Definition at_malloc_dot (T : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte),
      getr R 1 = Z_to_bv 64 0x1494c -> getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) ->
      getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x74250 ->
      getr R 8 = Z_to_bv 64 2 ->                                        (* [comment removed for export] *)
      getr R 10 = Z_to_bv 64 65536 -> getr R 18 = p1 inp rdraw ->
      getr R 20 = Z_to_bv 64 3 -> getr R 21 = Z_to_bv 64 65536 ->
      frame_mod mem0 M [(Z_to_bv 64 (bv_unsigned sp0 - 8388608), 8388608%Z)] ->
      U9World.main_frame (bv_unsigned sp0) M ->
      realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x1a6e8) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) MODEL1) T.

  Lemma front_to_malloc_dot : forall KA T,
    open_err_branch sp0 a0s dot_path inp rdraw tid mem0 brk mbase KA -> at_malloc_dot T ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs0 (Z_to_bv 64 0x148f8) mem0 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) MODEL0) (t_alt2 KA T).
  Proof.
    intros KA T HKA HT.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s dot_path inp mbase rdraw tid regs0 mem0 Hav Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s dot_path inp mbase brk rdraw tid regs0 mem0 Hav Hva Hvl Hlau Hvsp Htid ME) as HK.
    change (E0 sp0 a0s dot_path inp rdraw tid regs0) with (ENV a0s dot_path (vals0 sp0 inp rdraw tid regs0)) in HR, HK.
    set (vals := vals0 sp0 inp rdraw tid regs0) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 inp rdraw) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 inp rdraw) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    destruct (main_str sp0 a0s dot_path inp mbase brk rdraw tid regs0 mem0 Hav Hva Hvl Hlau Hvsp ME 1%nat ltac:(lia))
      as (Sr & Slo & Shi & Slen).
    rewrite Hav in Sr, Slo, Shi, Slen. cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_lf HR HK FUEL STOPS scr0 40%nat.
    clear HR HK. intros R M HR HK EQM LF. cbn [s_pc s_regs s_log] in HR, EQM, LF |- *.
    (* [comment removed for export] *)
    assert (FM : frame_mod mem0 M [(Z_to_bv 64 (bv_unsigned sp0 - 8388608), 8388608%Z)]).
    { rewrite EQM.
      replace [(Z_to_bv 64 (bv_unsigned sp0 - 8388608), 8388608%Z)] with (map (rdenot (ENV a0s dot_path vals)) regsF).
      2:{ unfold regsF, rdenot, estart. cbn [map fst snd a_base a_off edenot ev ENV]. rewrite P0.
          replace (bv_unsigned sp0 + -8388608)%Z with (bv_unsigned sp0 - 8388608)%Z by lia. reflexivity. }
      apply log_covered_frame; [exact (proj2 front_itinerary) | | exact LF].
      intros r Hr. unfold regsF in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
      unfold flat, estart. cbn [fst snd a_base a_off edenot ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    assert (Sr' : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (p1 inp rdraw) (length dot_path + 1) = Some (dot_path ++ [Z_to_bv 8 0])).
    { rewrite EQM. unfold p1. rewrite Hav.
      rewrite (rdn_mem_denot_above (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV a0s dot_path vals) mem0 _ 0%nat 0x95000);
        [exact Sr | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia
        | match goal with |- context [cat_argv_ptr ?t ?av ?ev ?ef ?k] =>
            pose proof (u64_range (cat_argv_ptr t av ev ef k)) end; lia]. }
    (* [comment removed for export] *)
    eapply (rz_openat_dot (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ _ MODEL0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17%bv : reg). reflexivity.
    - regv HR (10%bv : reg). apply bv_eq. reflexivity.
    - regv HR (12%bv : reg). vm_compute. reflexivity.
    - rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - split; [cbn; lia|]. split; [cbn; intros [E|[]]; apply (f_equal bv_unsigned) in E; vm_compute in E; lia|].
      regv HR (11%bv : reg). cbn [edenot ev ENV]. rewrite P2.
      split; [exact (argv1_below_task_size sp0 brk mbase rdraw inp a0s dot_path Hav Hlau) | exact Sr'].
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x21d74 + 4)%Z with 0x21d78%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know (run_segments RSEGS rc_inp rc_sp rc_mb) vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s dot_path))) with (ENV a0s dot_path (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + intros x Hx. rewrite EQM. apply (mem_denot_above (ENV a0s dot_path vals) mem0 _ 0%nat 0x95000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x21d74 + 4)%Z with 0x21d78%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert (fds0) (Z_to_bv 64 3) FdDir) MODEL0) with MODEL1.
      pose proof (regs_set_a0 (ENV a0s dot_path vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      clear HR. rename HR2 into HR. clear EQM LF.
      (* [comment removed for export] *)
      run_block_lf HR HK FUEL STOPS_F scr0 40%nat.
      clear HR. intros R2 M2 HR HK2 EQM2 _. cbn [s_pc s_regs s_log mem_denot] in HR, EQM2 |- *. subst M2. clear HK2.
      apply HT.
      + regv HR (1%bv : reg). reflexivity.
      + regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. try (f_equal; lia); try reflexivity.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
      + regv HR (8%bv : reg). reflexivity.
      + regv HR (10%bv : reg). reflexivity.
      + regv HR (18%bv : reg). cbn [edenot ev ENV]. exact P2.
      + regv HR (20%bv : reg). reflexivity.
      + regv HR (21%bv : reg). reflexivity.
      + exact FM.
      + (* [comment removed for export] *)
        constructor; unfold U9World.cell;
          lazymatch goal with |- rdn _ _ (Z_to_bv 64 (_ - ?k)) 8 = _ =>
            let H := fresh "Hc" in
            krdv HK 0%nat (- k)%Z 8%nat H;
            [ apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
            | unfold adenot, v_addi in H; cbn [a_base a_off edenot ev ENV] in H; rewrite ?edenot_add_lit in H;
              unfold adenot, v_addi in H; cbn [a_base a_off edenot ev ENV] in H; rewrite ?P0 in H;
              replace (bv_unsigned sp0 - k)%Z with (bv_unsigned sp0 + - k)%Z by lia; exact H ]
          end.
  Qed.
End FrontDot.
