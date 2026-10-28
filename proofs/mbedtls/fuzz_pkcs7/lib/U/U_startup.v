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
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb ShapeX FileSim StartupTac ArgvEnv Layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_img U_startup_defs U_startup1 U_startup_memset U_startup2 U_startup3 U_startup4 U_code_3b000_3c000.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_startup () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.StartupTac.bwd"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.InputStream"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "main_entry"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.State.with_tid"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "RocqVerifyHarness.AgentSubmission.BB.Amb.mkProcInputC"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.init_pc"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.phdrs"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_sp"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_brk"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.Run.entry_stack_fits"; "RocqVerifyHarness.AgentSubmission.BB.Amb.amb_of"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.wrap_mem"; "RocqVerifyHarness.AgentSubmission.BB.Amb.a_uid"; "RocqVerifyHarness.AgentSubmission.BB.Amb.a_hwcap"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.State.stack_max_size"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.D_main"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.build_stack_bytes"; "LinuxProcessSemantics.LinuxProcessSem.State.sp_window_hi"].


Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bwd_rz : ltac2:(CDefT.buildp (gd_tbl_P_startup ()) "Psegs,(0.$1.)Pmodel,$2.PK,$3.P,(4.(5.(6.&40.))(7.R2.)(8.(6.&40.)))P,(4.(0.(9.(6.&40.)(6.&40.)))(:.R3.)(;.(9.(6.&40.)(6.&40.))))(<.R5.Lst,$=.(>.R6.(?.R1.R5.)R4.))")
(* [comment removed for export] *).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply rz_msteps; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition J_main {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 av ev a_uid a_hwcap (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
              (Z_to_bv 64 0x3f09c) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x7d350)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x3f0a4)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x3f298)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x3f1e8)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x48358)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word) (rd : EntryDraw)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x3f2a8;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x5d0c8;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x1d24c;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  (* [comment removed for export] *)
  me_fits : entry_stack_fits sp0 av ev;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap rd) J (D_main sp0 av ev a_hwcap rd tid)
}.

Section Assembly.
  Context {AMB : Amb}.
  Variable sp : word.
  Variables argv envp : list (list byte).
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hvsp : valid_sp sp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable rd : EntryDraw.

  #[using="Hvsp"] Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  #[using="Hvsp"] Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  #[using="Hvsp"] Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  #[using="Hva Hve Hvsp Hfit J0"] Theorem ref_startup_sec : ltac2:(CDefT.buildp (gd_tbl_P_startup ()) "Pbrk,(6.&40.)Pmbase,(6.&40.)Plim,$10.Pfs0,$11.Pstdin0,$12.PK,$3.P,Ptid,(6.&40.)Pregs,(13.&5.(6.&40.))Pmem,P,(6.&40.)(5.(6.&8.))P,(14.(15.=(16.&40.R3.))(15.(16.&40.R3.)(17.+2.+16.)))P,(18.VAMB,Vsp,Vargv,Venvp,R4.Vrd,R3.R2.)(>.$19.(?.(1:.$1;.R4.(1<.&40.+1=24<.$1=.)R3.(1>.$19.))(1?.R5.(20.(21.$19.)R;.R:.Vsp,R9.(22.VAMB,Vargv,Venvp,R8.R7.))))R6.)(>.$19.(23.$19.$24.$25.Vsp,R7.R6.Vrd,R5.(22.VAMB,Vargv,Venvp,R4.R3.))R2.)")
(* [comment removed for export] *).
  Proof.
    intros brk mbase lim fs0 stdin0 K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model in_argv in_envp in_uid in_hwcap].
    set (model := init_model (segments_reserved rsegs) brk mbase sp lim (mkProcInputC argv envp fs0 stdin0)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => realizes rsegs (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)) with (0x1d100 : word) by (apply bv_eq; reflexivity).
    rewrite cmem_init. fold (regs_init sp).
    (* [comment removed for export] *)
    destruct (p1_run sp argv envp a_uid a_hwcap rd Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R1 |].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0x3efb8 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp a_uid a_hwcap rd) (J1 sp argv J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x3efb8 : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; apply wfJ_const | region_side | region_side]. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    (* [comment removed for export] *)
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (realizes SEGS (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run sp argv envp a_uid a_hwcap rd) with (G := RZ); try side Hva Hve HG.
    { unfold J1; repeat apply wfJ_wbytes; apply wfJ_const. }
    intros regs3 C1 C2 C10 C18 G3.
    carry G3 B3 (3:reg) C3. carry G3 B8 (8:reg) C8.
    assert (Cz : forall r : reg, In r [5; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
    { intros r Hr. rewrite (G3 r), (G2 r); [apply Az; exact Hr | |];
        clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
        repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
    pose proof (Cz 19 ltac:(in_list)) as Z19. pose proof (Cz 20 ltac:(in_list)) as Z20.
    pose proof (Cz 21 ltac:(in_list)) as Z21. pose proof (Cz 22 ltac:(in_list)) as Z22.
    pose proof (Cz 23 ltac:(in_list)) as Z23. pose proof (Cz 24 ltac:(in_list)) as Z24.
    pose proof (Cz 25 ltac:(in_list)) as Z25. pose proof (Cz 26 ltac:(in_list)) as Z26.
    pose proof (Cz 27 ltac:(in_list)) as Z27.
    (* [comment removed for export] *)
    change (J1 sp argv J0) with (J_lsm sp argv J0).
    eapply (tls_c1 sp J0 argv envp a_uid a_hwcap rd) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 sp J0 argv envp a_uid a_hwcap rd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 sp J0 argv envp a_uid a_hwcap rd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 sp J0 argv envp a_uid a_hwcap rd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (rz_set_tid SEGS regs4 (0x3f508 : word) _ (seg_rom SEGS) model K W_3bdbc F_3bdbc E_3bdbc);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x3f508 : word) 4) with (0x3f50c : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => realizes rsegs (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
    change (realizes SEGS (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 sp J0 argv envp a_uid a_hwcap rd) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 sp J0 argv envp a_uid a_hwcap rd) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 sp J0 argv envp a_uid a_hwcap rd) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 sp J0 argv envp a_uid a_hwcap rd) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 sp J0 argv envp a_uid a_hwcap rd) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - (* [comment removed for export] *)
      eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. apply wfJ_const.
      + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : ltac2:(CDefT.buildp (gd_tbl_P_startup ()) "Psp,(6.&40.)Pbrk,(6.&40.)Pmbase,(6.&40.)Prd,$26.Plim,$10.Pinp,$27.PK,$3.P,(28.R7.)P,(29.$19.R7.)P,(2:.(2;.R4.))P,(2<.(2=.R5.))P,(2>.R;.(2;.R6.)(2=.R6.))P,Ptid,(6.&40.)Pregs,(13.&5.(6.&40.))Pmem,P,(6.&40.)(5.(6.&8.))P,(14.(15.=(16.&40.R3.))(15.(16.&40.R3.)(17.+2.+16.)))P,(18.(2?.R;.)R10.(2;.R;.)(2=.R;.)R4.R=.R3.R2.)(>.$19.(?.(1:.$1;.R4.(1<.&40.+1=24<.$1=.)R3.(1>.$19.))(1?.R5.(20.(21.$19.)R10.R?.R11.R=.R<.)))R;.)(>.$19.(23.$19.$24.$25.R=.R<.R;.R:.R9.R8.)R7.)")
(* [comment removed for export] *).
Proof.
  intros sp brk mbase rd lim [argv envp fs0 stdin0 uid gid groups net nf sm hwc ab va ur tm] K Hsp Hbrk Hva Hve Hfit HK. cbn [in_argv in_envp] in *.
  exact (@ref_startup_sec (amb_of (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nf sm hwc ab va ur tm))
           sp argv envp Hva Hve Hsp Hfit rd brk mbase lim (fs_seed_tmp fs0 tm) stdin0 K HK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev tid rd regs mem.

  (* [comment removed for export] *)
  #[using="tid regs ME"] Lemma main_entry_rdn_above : ltac2:(CDefT.buildp (gd_tbl_P_startup ()) "Psegs,(0.$1.)Pa,(6.&40.)Pn,$30.P,(31.(16.&40.Vsp0,)(16.&40.R2.))P,(31.(32.(16.&40.R3.)(33.R2.))(17.+2.+40.))(4.(5.(0.(6.&8.)))(34.R5.Vmem,R4.R3.)(34.R5.(35.$25.Vsp0,Vav,Vev,(36.VAMB,)(37.VAMB,)Vrd,)R4.R3.))")
(* [comment removed for export] *).
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  
  (* [comment removed for export] *)
  
  #[using="AMB av ev tid rd regs ME"] Lemma main_entry_store_ok_win : ltac2:(CDefT.buildp (gd_tbl_P_startup ()) "Psegs,(0.$1.)Pa,(6.&40.)Pn,$30.P,(31.(38.(16.&40.Vsp0,)$39.)(16.&40.R2.))P,(31.(32.(16.&40.R3.)(33.R2.))(16.&40.Vsp0,))(4.$3:.(3;.R5.Vmem,R4.R3.)$3<.)")
(* [comment removed for export] *).
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="regs ME"] Lemma main_entry_mem_data : ltac2:(CDefT.buildp (gd_tbl_P_startup ()) "Pa,(6.&40.)P,(15.(16.&40.R1.)(38.(16.&40.Vsp0,)$39.))(4.(5.(6.&8.))A1.Vmem,R2.(3=.Vsp0,Vav,Vev,(37.VAMB,)Vrd,Vtid,R2.))")
(* [comment removed for export] *).
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  #[using="regs ME"] Lemma main_entry_rdn_data : ltac2:(CDefT.buildp (gd_tbl_P_startup ()) "Psegs,(0.$1.)Pa,(6.&40.)Pn,$30.P,(31.(32.(16.&40.R2.)(33.R1.))(38.(16.&40.Vsp0,)$39.))(4.(5.(0.(6.&8.)))(34.R4.Vmem,R3.R2.)(34.R4.(3=.Vsp0,Vav,Vev,(37.VAMB,)Vrd,Vtid,)R3.R2.))")
(* [comment removed for export] *).
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.

  (* [comment removed for export] *)
  #[using="tid regs mem ME"] Lemma main_entry_block_top : ltac2:(CDefT.buildp (gd_tbl_P_startup ()) "(31.(32.(16.&40.Vsp0,)(33.(3>.(6.&8.)(3?.$25.Vsp0,Vav,Vev,(36.VAMB,)(37.VAMB,)Vrd,))))$40.)")
(* [comment removed for export] *).
  Proof.
    pose proof (me_fits _ _ _ _ _ _ _ ME) as HF. unfold entry_stack_fits in HF.
    pose proof (build_stack_bytes_within_span RPH sp0 av ev a_uid a_hwcap rd) as HS. lia.
  Qed.
End Consumers.
