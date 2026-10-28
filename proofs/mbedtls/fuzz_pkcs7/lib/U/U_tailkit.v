(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit StartupAux ArgvEnv Layout SymExec SymExec2 SymExec2Sound SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_img U_startup_defs U_startup U_startup_facts U_main_entry U_main_entryN U_read_base U_world U_stdio_readerr_defs U_stdio_readerr U_stdio_refused U_stdio_oomtail U_main_open U_main_cut.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_tailkit () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "tail_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_oom"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_refused"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.U.U_startup_facts.D_main_missb"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.None"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_rdn8 : ltac2:(CDefT.buildp (gd_tbl_P_tailkit ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pv,(0.&40.)P,(3.$4.R3.R2.(5.$6.(7.R1.)(8.$6.)))(9.(1.(:.(0.&8.)))(;.$4.R4.(<.&40.R3.)#8.)(=.(:.(0.&8.))(>.#8.R2.)))")
(* [comment removed for export] *).
Proof.
  intros m A v [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  pose proof (bytes_at_rdn RSEGS m A (le8 v) 0 8 HB ltac:(rewrite length_le8; lia)) as H.
  rewrite Z.add_0_r in H. unfold wa in H. rewrite H.
  change (skipn 0 (le8 v)) with (le8 v). rewrite firstn_all2; [reflexivity|]. rewrite length_le8. lia.
Qed.

Lemma rw_cells_rdn4 : ltac2:(CDefT.buildp (gd_tbl_P_tailkit ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pv,(0.&40.)P,(3.$4.R3.R2.(5.$6.(?.R1.)(8.$6.)))(9.(1.(:.(0.&8.)))(;.$4.R4.(<.&40.R3.)#4.)(=.(:.(0.&8.))(>.#4.R2.)))")
(* [comment removed for export] *).
Proof.
  intros m A v [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  pose proof (bytes_at_rdn RSEGS m A (le4 v) 0 4 HB ltac:(rewrite length_le4; lia)) as H.
  rewrite Z.add_0_r in H. unfold wa in H. rewrite H.
  change (skipn 0 (le4 v)) with (le4 v). rewrite firstn_all2; [reflexivity|]. rewrite length_le4. lia.
Qed.

Lemma rw_cells_rdn1 : forall m A b,
  rw_cells RSEGS m A [C1 b] -> rdn RSEGS m (Z_to_bv 64 A) 1 = Some [b].
Proof.
  intros m A b [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  pose proof (bytes_at_rdn RSEGS m A [b] 0 1 HB ltac:(cbn; lia)) as H.
  rewrite Z.add_0_r in H. unfold wa in H. rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record tail_mem (sp0 : word) (tid : Z) (M : word -> option byte) : Prop := TAIL_MEM {
  tm_win : forall a : word, (bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0)%Z -> wview RSEGS M a <> None;
  tm_ro  : forall a : Z, (0x10000 <= a < 0x4bcd8)%Z -> M (Z_to_bv 64 a) = None;
  tm_got : rdn RSEGS M (Z_to_bv 64 0x4bcd8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7d330));
  tm_data : forall a : Z, (0x4bce0 <= a < 0x4cf20)%Z -> M (Z_to_bv 64 a) = None;
  tm_comp : rdn RSEGS M (Z_to_bv 64 0x4cf68) 1 = Some [Z_to_bv 8 0];
  tm_tid  : rdn RSEGS M (Z_to_bv 64 0x5d020) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  tm_tidr : (0 < tid < 2 ^ 22)%Z;
  tm_lock : rdn RSEGS M (Z_to_bv 64 0x7d328) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  tm_canary : exists canw : word, rdn RSEGS M (Z_to_bv 64 0x7d330) 8 = Some (word_to_le_bytes 8 canw);   (* [comment removed for export] *)
  tm_needlocks : rdn RSEGS M (Z_to_bv 64 0x7d353) 1 = Some [Z_to_bv 8 0];
  tm_stdin : rdn RSEGS M (Z_to_bv 64 0x7d770) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  tm_ofl  : rdn RSEGS M (Z_to_bv 64 0x7d780) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  tm_atx  : forall a : Z, (0x7d108 <= a < 0x7d120)%Z -> M (Z_to_bv 64 a) = None   (* [comment removed for export] *)
}.

Section Kit.
  Variable sp0 : word.
  Variable model : Model.
  Variable tid : Z.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  #[using="Hvsp SPlo SPhi"] Lemma tm_stack_writable : forall M, tail_mem sp0 tid M -> stack_writable M sp0.
  Proof.
    intros M TM d m Hd Hdm. pose proof SPlo. pose proof SPhi.
    apply store_ok_of_all; rewrite u_small by lia; [lia|].
    intros x Hx. apply (tm_win _ _ _ TM). lia.
  Qed.

  #[using="Type"] Lemma tm_img : forall M, tail_mem sp0 tid M -> Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Proof.
    intros M TM. unfold re_ivs. repeat constructor; cbn [fst snd]; intros i Hi.
    - apply (tm_ro _ _ _ TM). lia.
    - apply (tm_data _ _ _ TM). lia.
    - apply (tm_atx _ _ _ TM). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Theorem oom_tail : ltac2:(CDefT.buildp (gd_tbl_P_tailkit ()) "Ppc,$2.PR,(10.&5.(0.&40.))PM,P,(0.&40.)(1.(0.&8.))P,(11.(9.$2.R3.+1=4;4.)(9.$2.R3.+1=4?4.))P,(9.(0.&40.)(12.R3.(13.&5.+2.$14.))(<.&40.(15.(16.&40.Vsp0,)+80.)))P,(9.(0.&40.)(12.R4.(13.&5.+3.$14.))(<.&40.+10800.))P,(9.(0.&40.)(12.R5.(13.&5.+4.$14.))(<.&40.+5=0<8.))P,(17.Vsp0,Vtid,R5.)(18.$4.(19.(1:.$1;.R7.(<.&40.R8.)R6.(1<.$4.))Vmodel,)(1=.$1>.(1?.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros pc R M Hpc Rsp Rgp Rtp TM. pose proof TM as TM'. destruct TM' as [W RO GOT DA CO TI TR LO [canw CA] NL SI OF AT].
    apply (ref_oom_tail sp0 [] model Hvsp Hh Hlazy Hfd2 tid R M canw Rsp Rgp Rtp
             (tm_stack_writable M TM) (tm_img M TM) GOT CO TI TR LO CA NL SI OF pc Hpc).
  Qed.

  (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Theorem refused_tail : ltac2:(CDefT.buildp (gd_tbl_P_tailkit ()) "PR,(10.&5.(0.&40.))PM,P,(0.&40.)(1.(0.&8.))P,(9.(0.&40.)(12.R2.(13.&5.+2.$14.))(<.&40.(15.(16.&40.Vsp0,)+80.)))P,(9.(0.&40.)(12.R3.(13.&5.+3.$14.))(<.&40.+10800.))P,(9.(0.&40.)(12.R4.(13.&5.+4.$14.))(<.&40.+5=0<8.))P,(17.Vsp0,Vtid,R4.)(18.$4.(19.(1:.$1;.R6.(<.&40.+1=494.)R5.(1<.$4.))Vmodel,)(1=.$20.(1?.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros R M Rsp Rgp Rtp TM. pose proof TM as TM'. destruct TM' as [W RO GOT DA CO TI TR LO [canw CA] NL SI OF AT].
    apply (ref_refused_tail sp0 [] model Hvsp Hh Hlazy Hfd2 tid R M canw Rsp Rgp Rtp
             (tm_stack_writable M TM) (tm_img M TM) GOT CO TI TR LO CA NL SI OF).
  Qed.

  (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Theorem dir_tail {AMB : Amb} : forall (a0s : list byte) (envv : list (list byte)) (tidw : word) (rd : EntryDraw)
      (regs0 : bvmap 5 word) (mem0 : word -> option byte) R M,
    valid_argv [a0s; dot_path] -> valid_envp envv -> (0 < bv_unsigned tidw < 2 ^ 22)%Z ->
    main_entry sp0 [a0s; dot_path] envv tidw rd regs0 mem0 ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x5d0c8 ->
    getr R 18 = p1 sp0 a0s dot_path envv ->
    tail_mem sp0 tid M ->
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1d478) M (seg_rom RSEGS)) model)
             (t_die (msg_read_error dot_path) (m_fs model)).
  Proof.
    intros a0s envv tidw rd regs0 mem0 R M Hva Hve Htid ME Rsp Rgp Rtp Rs2 TM Habove.
    pose proof TM as TM'. destruct TM' as [W RO GOT DA CO TI TR LO [canw CA] NL SI OF AT].
    pose proof SPlo. pose proof SPhi.
    edestruct (main_strN sp0 [a0s; dot_path] envv tidw rd regs0 mem0 Hva Hve Hvsp ME 1%nat) as (Sr & Slo & Shi & Slen & t8 & Ht8);
      [cbn; lia|].
    cbn [nth length Nat.add dot_path app] in Sr, Slo, Shi, Ht8.
    set (pp := p1 sp0 a0s dot_path envv) in *.
    change (cat_argv_ptr sp0 [a0s; dot_path] envv 1) with pp in Sr, Slo, Shi, Ht8.
    change (Z.of_nat 1) with 1%Z in Ht8.
    pose proof (u64_range pp) as Hppr.
    assert (Hstr : rdn RSEGS M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0]).
    { rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia. }
    assert (Ht8' : rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8).
    { rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove.
      rewrite (u_small (bv_unsigned pp + 1)) by lia. rewrite u_small by lia. lia. }
    apply (ref_read_error_dot sp0 [] model Hvsp Hh Hlazy Hfd2 pp tid R M canw
             Rsp Rgp Rtp Rs2 (tm_stack_writable M TM) (tm_img M TM) GOT CO TI TR LO CA NL SI OF Slo t8 ltac:(lia) Hstr Ht8').
  Qed.
End Kit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma img_49818_1 : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x4cf68) 1%nat = Some [Z_to_bv 8 0].
Proof. vm_refl_bv. Qed.

Section AtCut.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rd regs0 mem0.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  #[using="AMB sp0 a0s path envv tid rd regs0 Hvsp ME SPlo"] Lemma mem0_none_low : forall a : Z, (0 <= a < 0x4cf20 \/ 0x7d108 <= a < 0x7d120)%Z -> mem0 (Z_to_bv 64 a) = None.
  Proof.
    intros a Ha. pose proof SPlo as Hlo. unfold sp_window_lo in Hlo.
    rewrite (main_entry_mem_data sp0 [a0s; path] envv tid rd regs0 mem0 ME)
      by (rewrite stack_max_size_val, u_small by lia; lia).
    pose proof (u64_range tid).
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite MemSplit.wbytes_outside by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite !u_small by lia; lia)).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="AMB sp0 a0s path envv tid rd regs0 Hvsp ME SPlo"] Lemma mem0_img_rdn : ltac2:(CDefT.buildp (gd_tbl_P_tailkit ()) "Pa,$2.Pn,$21.P,(9.$22.(23.R2.R1.)$24.)(9.(1.(:.(0.&8.)))(;.$4.Vmem0,(<.&40.R3.)R2.)(;.$4.L,(0.&40.)(25.(0.&8.))(<.&40.R3.)R2.))")
(* [comment removed for export] *).
  Proof.
    intros a n Hb. apply (main_entry_rdn_image sp0 [a0s; path] envv tid rd SPlo regs0 mem0 ME). exact Hb.
  Qed.

  #[using="AMB rd regs0 Hvsp Htid ME SPlo SPhi"] Theorem cut_tail_mem : forall M, cut_mem sp0 a0s path envv mem0 M -> tail_mem sp0 (bv_unsigned tid) M.
  Proof.
    intros M CM. pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range tid) as Htr.
    assert (BE : forall a : Z, (0 <= a < 0x7e000)%Z -> M (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
    { intros a Ha. apply (cm_below _ _ _ _ _ _ CM). rewrite u_small by lia. lia. }
    assert (RD : forall (a : Z) (n : nat), (0 <= a)%Z -> (a + Z.of_nat n <= 0x7e000)%Z ->
                 rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS mem0 (Z_to_bv 64 a) n).
    { intros a n Ha Hn. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply BE. lia. }
    split.
    - apply (cm_win _ _ _ _ _ _ CM).
    - intros a Ha. rewrite BE by lia. apply mem0_none_low. lia.
    - rewrite RD by (cbn; lia). rewrite mem0_img_rdn by (vm_compute; reflexivity). exact img_48590_8.
    - intros a Ha. rewrite BE by lia. apply mem0_none_low. lia.
    - rewrite RD by (cbn; lia). rewrite mem0_img_rdn by (vm_compute; reflexivity). exact img_49818_1.
    - rewrite RD by (cbn; lia). rewrite Z_to_bv_bv_unsigned.
      eapply (@main_entry_tid AMB sp0 [a0s; path] envv tid rd) with (regs := regs0); first [exact SPlo | exact SPhi | exact Hva | exact ME].
    - exact Htid.
    - rewrite RD by (cbn; lia). rewrite mem0_img_rdn by (vm_compute; reflexivity). exact img_59c58_4.
    - exists (canary_w rd). rewrite RD by (cbn; lia). rewrite canary_store.
      eapply (@main_entry_guard AMB sp0 [a0s; path] envv tid rd) with (regs := regs0); first [exact SPlo | exact SPhi | exact Hva | exact ME].
    - rewrite RD by (cbn; lia). rewrite mem0_img_rdn by (vm_compute; reflexivity). exact img_59c83_1.
    - rewrite RD by (cbn; lia). rewrite mem0_img_rdn by (vm_compute; reflexivity). exact img_5a0a0_8.
    - rewrite RD by (cbn; lia). rewrite mem0_img_rdn by (vm_compute; reflexivity). exact img_5a0b0_8.
    - intros a Ha. rewrite BE by lia. apply mem0_none_low. lia.
  Qed.
End AtCut.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
