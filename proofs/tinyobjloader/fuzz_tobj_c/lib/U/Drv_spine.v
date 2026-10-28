(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "SLit"; "SVar"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "not"; "or"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "list"; "length"; "prod"; "cons"; "nil"; "nat"; "pair"; "app"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx"; "f_draw"; "f_inp"; "f_sp"; "f_F"; "f_md0"; "Fctx"; "f_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m"; "JD"; "Kd0"; "Dok"; "P0"; "DokS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_spine.SPINE.Ex"; "X0"; "HX0"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "event"; "in_fs"; "Model"; "FdEntry"; "with_fds"; "vm_reserved"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "add"; "of_nat"; "sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "w_tr"; "triple"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl"; "SIDEL"; "QN"; "hl_ex0"; "hl_ex2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states"; "T_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r"; "tv0"; "tvK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_spine.SPINE.Safe"; "XS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "die"; "calls"; "payload_len"; "MAX_INPUT"; "config_len"; "Spec"; "ex"; "msg_overrun"; "msg_read_error"; "msg_refused"; "msg_short"; "wr"; "zeros"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "dot_path"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ"; "DTrue"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "img_reserved"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht"; "TVc"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork"; "PID_MAX_ENVELOPE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "rnd1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "init_cost"; "vm_room"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "RI"; "ri_sec"; "ri_top"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h"; "KH"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states"; "NX0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl1_states"; "NX1"; "NX2"; "NX3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx"; "x1_ex"; "x2_ex"; "x3_ex"; "x4_ex"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rs"; "DG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rx"; "DG"; "r_exists_loop"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mkEntry"; "segments_reserved"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "ok_halted"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine"; "PRvm"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "malloc_contracts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS";
"vm_roomS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states"; "E_f0"; "F2"; "tvP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "imgU"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Top"; "md_main"; "spine_ex_stmt"; "spine_safe_stmt"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Strings.Ascii Strings.String.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLayout MallocIface MallocLaws Contract ContractDrv Pristine ClientLaws Glue RoomS ContractS.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymFrame SymEntail SymSummary SymCall SymExit Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import
  InitLayout InitState InitStrs InitArg1 SysOpen DrvGlue TobjJV DrvJ DrvPristine DrvLoop FuzzOneIface.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec SpecConsts SpecTop.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open_all OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rt_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl1_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx1_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx2_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx3_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx4_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_d__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open_all OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rt_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.Drv_hs_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl1_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx1_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx2_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx3_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx4_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G2.Drv_r_ref OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.Drv_hs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_d__G1.Drv_d_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_d__G1.Drv_d OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Top.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SPINE.
Variables sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
S6aS71S64Vsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Let argv := in_argv inp.
Let argv1 : list byte := nth 1 argv [].
Let fs := in_fs inp.
Let md0 (tid : word) : Model := ltac2:(tb__ "0|0|
S73Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7").

Let ri : run_init := ltac2:(tb__ "0|1|
S55ScQ40M0Vbrk;A2ScG0S51Vdraw;A1A2S31ScG0Vsp;A2Z800000A2A3").
Lemma Hsec : ltac2:(tb__ "0|0|
S5S4S56Vri;A1ScQ40S51Vdraw;A1A2A3"). Proof using . reflexivity. Qed.
Lemma Htop : ltac2:(tb__ "0|0|
S5S4S57Vri;A1S31ScQ40Vsp;A2Z800000A2A3"). Proof using . reflexivity. Qed.

Lemma img_reserved_U : ltac2:(tb__ "0|1|
S25S5SdSfSbQ40A1M0G0A2A1S2bR1A1S65S72A1A3S4eS4dR2A2F_;Fvmz;").
Proof using md0.
  intros vmz E. unfold img_reserved. rewrite E. cbn [mc_img_lo mc_img_hi C_U]. intros x Hx.
  assert (M : map (fun e => (bv_unsigned (fst e), bv_unsigned (snd e))) (segments_reserved segsU) = [(65536, 12288); (77824, 86016); (163840, 4096); (167936, 204800)]) by (vm_compute; reflexivity).
  destruct (segments_reserved segsU) as [|e1 [|e2 [|e3 [|e4 [|e5 l]]]]]; try discriminate M.
  cbn [map] in M. injection M as A1 N1 A2 N2 A3 N3 A4 N4.
  destruct (Z_lt_dec x 77824); [exists e1; split; [cbn; tauto | lia]|].
  destruct (Z_lt_dec x 163840); [exists e2; split; [cbn; tauto | lia]|].
  destruct (Z_lt_dec x 167936); [exists e3; split; [cbn; tauto | lia]|].
  exists e4; split; [cbn; tauto | lia].
Qed.

Lemma PRvm0 : ltac2:(tb__ "0|0|
SbQ40A1S69S4dVri;Vmd0;R1A1A3Ftid;").
Proof using Hent inp lim.
  intros tid. destruct Hent as (Hsp & Hbrk & Hmb & Hfits). destruct Hbrk as (B1 & B2 & B3). pose proof (bv_urange (rnd1 draw)) as UR.
  unfold PRvm, md0, Top.md_main. autorewrite with model. cbn -[Z.le Z.lt Z.add Z.sub Z.modulo alloc_top].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact B3|].
  split; [|split; [| apply img_reserved_U; reflexivity]].
  - unfold alloc_top. replace (bv_unsigned (vm_init_sp _)) with (bv_unsigned sp) by reflexivity.
    unfold valid_sp, sp_window_lo, sp_window_hi in Hsp. unfold stack_max_size. lia.
  - assert (RT : 0 < reserved_top (segments_reserved segsU) <= 0x5b000) by (vm_compute; split; [reflexivity | discriminate]).
    unfold brk_aslr_max in B2. unfold sp_window_lo, stack_max_size. lia.
Qed.

Lemma path_cases : ltac2:(tb__ "0|1|
S9S5SdSbQ8A1A1Vargv1;S4bA3M0S8G0A1A2").
Proof using argv.
  destruct (path_eqb argv1 dot_path) eqn:E; [left; apply path_eqb_eq; exact E | right].
  intros H. rewrite H, path_eqb_refl in E. discriminate.
Qed.

Definition dot_safe_stmt : Prop := ltac2:(tb__ "0|7|
SbQ40M0A1S33OF_;S0S0S6S2dZ0ScG0R4A2M1A2S2dG1S50A2A2SdS26A1S28OF_;F_;M2S67S43Vinp;A1M3R1A2M4S16SaR6R2A3F_;FK;G2G4S66SaR7R2A3F_;FK;S68R6G3A2S5S12SeSdSbQ8A1A1M5Vargv;A2U2A3S5G5Vargv1;S4bA3S21Vsp;Vdraw;Vinp;R8A4S35SaRaS15SaS1eVsp;Vdraw;Vinp;S1fVinp;Vmd0;RbA1A2R9S10SfS1S1A2M6S13S1S1S3P29A1S2Z10000A1A4S11G6A1A3S4cA7S3aR8A4S33S7L_;A4F_;F_;F_;F_;F_;F_;F_;Frho;Fr0;Fok;Ftid;").

Definition dot_ex_stmt : Prop := ltac2:(tb__ "0|4|
SbQ40M0A1S0S0S6S2dZ0ScG0R3A2M1A2S2dG1S50A2A2S5S12SeSdSbQ8A1A1M2Vargv;A2U2A3S5G2Vargv1;S4bA3S21Vsp;Vdraw;Vinp;R5A4S32SaS15SaS1eVsp;Vdraw;Vinp;S1fVinp;Vmd0;R7A1A2R6S10SfS1S1A2M3S13S1S1S3P29A1S2Z10000A1A4S11G3A1A3S4cA7S3aR5A4S33S5SdS26A1S34R1A1S3eVfs;S46Vargv1;A1A2A3Lw;A3F_;F_;F_;F_;Frho;Fr0;Ftid;").

Lemma dot_safe_ok : dot_safe_stmt.
Proof using Hent Hinp.
  intros tid ok r0 rho Htid HokK HokP Hokh Hargc Hdot HP0.
  exact (U.Drv_d__G1.Drv_d.dot_safe sp brk mb draw inp Hent Hinp Hargc (md0 tid) (Top.md_main_fds sp brk mb draw lim inp tid) ok HokK HokP Hokh Hdot r0 rho HP0).
Qed.
Lemma dot_ex_ok : dot_ex_stmt.
Proof using Hent Hinp.
  intros tid r0 rho Htid Hargc Hdot HP0.
  exact (U.Drv_d__G1.Drv_d.dot_ex sp brk mb draw inp Hent Hinp Hargc (md0 tid) (Top.md_main_fds sp brk mb draw lim inp tid) Hdot r0 rho HP0).
Qed.

Section Safe.

Hypothesis MCs : ltac2:(tb__ "0|0|
S6bSaS4dS6cA3").
Hypothesis MIS : malloc_init_S_U.
Hypothesis MBS : malloc_big_S_U.
Hypothesis FDS : free_drv_S_U.
Hypothesis MPS : malloc_payload_S_U.

Hypothesis FSUM : fuzz_one_sum_stmt_U.
Let DOT : dot_safe_stmt := dot_safe_ok.

Hypothesis Hlim : ltac2:(tb__ "0|1|
S6S2cS2eZ2M0Z1eA2Vlim;A2S2cVlim;S2eG0Z28A2A2A2").

Definition XS : Z := 2 ^ 29 - 2 ^ 20.
Lemma vm_roomS0 : ltac2:(tb__ "0|0|
SbQ40A1S6dVmd0;R1A1S3dA2Ftid;").
Proof using Hent Hlim brk inp mb sp.
  intros tid. pose proof (proj1 Hent) as Hsp. unfold valid_sp, sp_window_hi in Hsp.
  unfold md0, Top.md_main. apply vm_roomS_init_U; autorewrite with model; try reflexivity; unfold XS; [lia| | |unfold ROOMC; lia|].
  - replace (vm_limit _) with lim by reflexivity. lia.
  - replace (vm_limit _) with lim by reflexivity. lia.
  - replace (bv_unsigned (vm_init_sp _)) with (bv_unsigned sp) by reflexivity. unfold sp_window_lo in *. lia.
Qed.
Lemma HXS : ltac2:(tb__ "0|0|
S2cS2fS52S2eZ2Z1cA2A2S3dA2"). Proof using . unfold XS, init_cost. lia. Qed.
Lemma HXS' : init_cost <= XS. Proof using . unfold XS, init_cost. lia. Qed.

Lemma DGS_fds : ltac2:(tb__ "0|0|
S1cS4S4S54S28SdSfSbQ40A1S29A2A1S61S3dR5R4R3R2A5S61S3dR6R5R4S2aR2R3A2A5F_;Ff;Fmd;FA;Fg;Fcap;Fcx;").
Proof using . intros. apply Drv_rs.DG_fds. assumption. Qed.

Lemma file_safe : ltac2:(tb__ "0|1|
S1cS0S0S21S19R3A1S17R3A1S18R3A1R2A4S35SaS1dR4A1S15SaS1eS19R4A1S17R4A1S18R4A1M0S1fG0S1bR4A1A2R3S3bS22S3dA1A7S3aR2A4S33S7L_;A4F_;Frho;Fr0;Fcx;").
Proof using FDS FSUM MBS MCs MPS.
  intros cx r0 rho HP0.
  assert (DTvm : forall (A : MA) (m m' : Model), m_vmmaps m' = m_vmmaps m -> m_vm_materialized m' = m_vm_materialized m -> DTrue A m -> DTrue A m') by (intros; exact I).
  apply (Drv_rs.r_safe_loopS cx XS HXS MBS FDS); clear rho.
  -
    intros r1 rho1 cap g HX Hg HCG. refine (U.Drv_h__G1.Drv_h.xeh_safe cx r1 (Drv_rs.DG XS cap g) (DGS_fds cx cap g) _ _ _ rho1 cap HX).
    + intros rho2 HL. exact (U.Drv_hs__G1.Drv_hs.sh_safe cx r1 (Drv_rs.DG XS cap g) (Drv_rs.DG_vm XS cap g) MCs rho2 HL).
    + intros rho2 cap2 HX2 HL. exact (U.Drv_hs__G1.Drv_hs.ov_safe cx r1 (Drv_rs.DG XS cap g) (Drv_rs.DG_vm XS cap g) MCs rho2 cap2 HX2 HL).
    + intros rho2 cap2 HX2 HL6. pose proof HX2 as (_ & _ & _ & _ & HLM & _). pose proof HX as (_ & _ & _ & HLc & _ & HC).
      pose proof (CAP_facts cap HC) as (Cb & _ & _).
      refine (U.Drv_ht__G1.Drv_ht.ttr_safeS cx cap2 MPS _ (Drv_rs.kOf g) (Drv_rs.XOf XS cap g) ltac:(unfold Drv_rs.XOf, XS, init_cost; lia) _ r1 rho2 HX2 HL6).
      *
        intros r2 rho3 HT3 HP3.
        refine (Drv_hl.hl_safe2 cx FSUM HL6 HLM cap2 _ _ _ _ r2 rho3 HT3 HP3); intros rho4 g' vm mat HS HC'.
        -- exact (Drv_hx.x1_safe cx HL6 HLM cap2 HC' MCs rho4 g' vm mat HS).
        -- exact (Drv_hx.x2_safe cx HL6 HLM cap2 HC' MCs rho4 g' vm mat HS).
        -- exact (Drv_hx.x3_safe cx HL6 HLM cap2 HC' MCs rho4 g' vm mat HS).
        -- exact (Drv_hx.x4_safe cx HL6 HLM cap2 HC' MCs rho4 g' vm mat HS).
      *
        intros r2 rho3 HT3 HP3.
        refine (Drv_hl.hl_safe0 cx FSUM HL6 HLM cap2 _ _ _ _ r2 _ rho3 HT3 HP3); intros rho4 g' vm mat HS HC'.
        -- exact (Drv_hx.x1_safe cx HL6 HLM cap2 HC' MCs rho4 g' vm mat HS).
        -- exact (Drv_hx.x2_safe cx HL6 HLM cap2 HC' MCs rho4 g' vm mat HS).
        -- exact (Drv_hx.x3_safe cx HL6 HLM cap2 HC' MCs rho4 g' vm mat HS).
        -- exact (Drv_hx.x4_safe cx HL6 HLM cap2 HC' MCs rho4 g' vm mat HS).
  -
    intros r1 rho1 g H101 HL HH Hg. eapply triple_conseq; [| intros w Hw; exact Hw | exact (U.Drv_r__G2.Drv_r_ref.ref_safe cx ltac:(unfold MAX_INPUT; exact HL) r1 rho1)].
    intros w [Hsm HJ]. split; [exact Hsm|]. exact (JGD_mono segs C_U 31 _ r1 _ _ (Drv_rs.DG XS (2 ^ 26) g) DTrue _ _ _ (fun _ _ _ => I) HJ).
  -
    intros r1 rho1 H100 H101 HL. refine (U.Drv_h__G1.Drv_h.xe0_safe cx r1 _ _ _ rho1 H100 H101 HL).
    + intros A md f. apply Drv_rs.DX_fds.
    + intros rho2 HL2. exact (U.Drv_hs__G1.Drv_hs.sh0_safe cx r1 _ (Drv_rs.DX_vm (DRV_OPS - 2 * 0) (Drv_rs.XOf XS 65536 0)) MCs rho2 HL2).
Qed.

Theorem spine_safe_U : ltac2:(tb__ "0|0|
S75Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;A6").
Proof using DOT FDS FSUM Hlim MBS MCs MIS MPS.
  intros tid ok Htid HokK HokP Hokh Hargc Hmay rho HJM.
  apply (U.Drv_m__G1.Drv_m.m_safe_S sp brk mb draw inp Hent Hinp Hargc (md0 tid) (Top.md_main_fds sp brk mb draw lim inp tid) (Top.md_main_fs sp brk mb draw lim inp tid)
           ok HokK HokP Hokh ri Hsec Htop Hmay (PRvm0 tid) MIS XS (vm_roomS0 tid) HXS'); [|exact HJM].
  intros r0 rho' HP0.
  destruct path_cases as [Hdot|Hnd].
  - eapply triple_conseq; [| intros w Hw; exact Hw | exact (DOT tid ok r0 rho' Htid HokK HokP Hokh Hargc Hdot HP0)].
    intros w [Hsm HJ]. split; [exact Hsm|]. exact (JGD_mono segs C_U 31 _ r0 _ _ (U.Drv_m__G1.Drv_m.DokS XS) DTrue _ _ _ (fun _ _ _ => I) HJ).
  - destruct Hmay as (Hlen & Hne & [Hd|Hl]); [exfalso; exact (Hnd Hd)|].
    destruct (fs_lookup fs argv1) as [F|] eqn:HF; [|exfalso; exact (Hl HF)].
    exact (file_safe (mkFctx sp brk mb draw inp Hent Hinp Hargc (md0 tid) (Top.md_main_fds sp brk mb draw lim inp tid) (Top.md_main_fs sp brk mb draw lim inp tid)
                        ok HokK HokP Hokh (conj Hlen (conj Hne (or_intror Hl))) F HF Hnd) r0 rho' HP0).
Qed.
End Safe.

Section Ex.

Hypothesis MIX : malloc_init_ex_U true.
Hypothesis MBX : malloc_big_ex_U true.
Hypothesis FDX : free_drv_ex_U.
Hypothesis MPX : malloc_payload_ex_U true.
Hypothesis FCX : free_contract_ex_U.

Hypothesis FSUMX : fuzz_one_sum_ex_stmt_U.
Let DOTX : dot_ex_stmt := dot_ex_ok.

Hypothesis Hlim : ltac2:(tb__ "0|1|
S6S2cS2eZ2M0Z1eA2Vlim;A2S2cVlim;S2eG0Z28A2A2A2").

Definition X0 : Z := 2 ^ 30 - 2 ^ 20.
Lemma vm_room0 : ltac2:(tb__ "0|0|
SbQ40A1S53Vmd0;R1A1S23A2Ftid;").
Proof using Hent Hlim brk inp mb sp.
  intros tid. pose proof (proj1 Hent) as Hsp. unfold valid_sp, sp_window_hi in Hsp.
  unfold md0, Top.md_main. apply vm_room_init_U; autorewrite with model; try reflexivity; unfold X0; [lia| | |].
  - replace (vm_limit _) with lim by reflexivity. lia.
  - replace (vm_limit _) with lim by reflexivity. lia.
  - replace (bv_unsigned (vm_init_sp _)) with (bv_unsigned sp) by reflexivity. lia.
Qed.
Lemma HX0 : ltac2:(tb__ "0|0|
S2cS2fS52S2eZ2Z1dA2A2S23A2"). Proof using . unfold X0, init_cost. lia. Qed.
Lemma HX0' : init_cost <= X0. Proof using . unfold X0, init_cost. lia. Qed.

Section File.
Variable cx : Fctx.
Variable r0 : valuation.
Hypothesis HP0 : ltac2:(tb__ "0|0|
S21S19Vcx;A1S17Vcx;A1S18Vcx;A1Vr0;A4").
Local Notation F := (f_F cx).
Local Notation L := (Z.of_nat (length (f_F cx))).
Local Notation fsx := (in_fs (f_inp cx)).

Lemma DG_fds : ltac2:(tb__ "0|0|
S4S4S54S28SdSfSbQ40A1S29A2A1S62S23R5R4R3R2A5S62S23R6R5R4S2aR2R3A2A5F_;Ff;Fmd;FA;Fg;Fcap;").
Proof using . intros. apply Drv_rx.DG_fds. assumption. Qed.

Let LOOPX (Q : world -> Prop) EXEH EXref EXE0 : ltac2:(tb__ "0|1|
S0S32SaS15SaS1eS19Vcx;A1S17Vcx;A1S18Vcx;A1M0S1fG0S1bVcx;A1A2Vr0;S3bS20S23A1A7S3aR1A4VQ;A3Frho;") := ltac2:(tb__ "0|0|
S63Vcx;S23S24VMBX;VFDX;VQ;VEXEH;VEXref;VEXE0;Vr0;Aa").

Lemma ex_refused : ltac2:(tb__ "0|1|
S2cS41S30SeSbQ8A1S1aVcx;A1A2A1A2S0S32SaS15SaS1eS19Vcx;A1S17Vcx;A1S18Vcx;A1M0S1fG0S1bVcx;A1A2Vr0;S3bS20S23A1A7S3aR1A4S33S5SdS26A1S34R1A1S3eS27G0A1S47A2A3Lw;A3Frho;F_;").
Proof using HP0 LOOPX.
  intros HL rho. apply LOOPX; clear rho.
  - intros r1 rho1 cap g HX _ _. exfalso. destruct HX as (_ & _ & _ & _ & HLM & _). unfold MAX_INPUT in *. lia.
  - intros r1 rho1 g H101 HL' HH Hg. exact (U.Drv_r__G2.Drv_r_ref.ref_exists cx r1 _ rho1).
  - intros r1 rho1 _ _ HL4. exfalso. unfold MAX_INPUT in *. lia.
Qed.

Lemma ex_short : ltac2:(tb__ "0|1|
S2dS30SeSbQ8A1S1aVcx;A1A2A1Z6A2S0S32SaS15SaS1eS19Vcx;A1S17Vcx;A1S18Vcx;A1M0S1fG0S1bVcx;A1A2Vr0;S3bS20S23A1A7S3aR1A4S33S5SdS26A1S34R1A1S3eS27G0A1S48A2A3Lw;A3Frho;F_;").
Proof using LOOPX.
  intros HL rho. apply LOOPX; clear rho.
  - intros r1 rho1 cap g HX Hg HCG. refine (U.Drv_h__G1.Drv_h.xeh_exists cx r1 (Drv_rx.DG X0 cap g) (DG_fds cap g) _ _ _ _ rho1 cap HX).
    + intros rho2 _. exact (U.Drv_hs__G1.Drv_hs.sh_exists cx r1 (Drv_rx.kOf g) (Drv_rx.XOf X0 cap g) ltac:(unfold Drv_rx.kOf, DRV_OPS; lia) FDX rho2).
    + intros rho2 cap2 _ [H6 _]. exfalso. lia.
    + intros rho2 cap2 _ H6. exfalso. pose proof (config_len_range F). lia.
  - intros r1 rho1 g _ HL' _ _. exfalso. lia.
  - intros r1 rho1 H100 H101 HL4. refine (U.Drv_h__G1.Drv_h.xe0_exists cx r1 _ _ _ _ rho1 H100 H101 HL4).
    + intros A md f. apply Drv_rx.DX_fds.
    + intros rho2 _. exact (U.Drv_hs__G1.Drv_hs.sh0_exists cx r1 DRV_OPS (X0 - init_cost) ltac:(unfold DRV_OPS; lia) FDX rho2).
Qed.

Lemma ex_overrun : ltac2:(tb__ "0|4|
S6S2cZ6M0S30SeSbQ8A1S1aVcx;A1M1A2A1M2A2S2dG2S2fG0S42G1A1A2A2A2S0S32SaS15SaS1eS19Vcx;A1S17Vcx;A1S18Vcx;A1M3S1fG3S1bVcx;A1A2Vr0;S3bS20S23A1A7S3aR1A4S33S5SdS26A1S34R1A1S3eS27G3A1S45A2A3Lw;A3Frho;F_;").
Proof using LOOPX.
  intros [H6 Hov] rho. pose proof (config_len_range F) as CR. unfold CFG_COUNT_BIT in CR. apply LOOPX; clear rho.
  - intros r1 rho1 cap g HX Hg HCG. refine (U.Drv_h__G1.Drv_h.xeh_exists cx r1 (Drv_rx.DG X0 cap g) (DG_fds cap g) _ _ _ _ rho1 cap HX).
    + intros rho2 HL6'. exfalso. lia.
    + intros rho2 cap2 _ _. exact (U.Drv_hs__G1.Drv_hs.ov_exists cx r1 (Drv_rx.kOf g) (Drv_rx.XOf X0 cap g) ltac:(unfold Drv_rx.kOf, DRV_OPS; lia) FDX rho2).
    + intros rho2 cap2 _ H6'. exfalso. lia.
  - intros r1 rho1 g _ HL' _ _. exfalso. lia.
  - intros r1 rho1 _ _ HL4. exfalso. lia.
Qed.

Let HLX2 (cap : Z) (HL6 : 6 + config_len F <= L) (HLM : L < MAX_INPUT) : ltac2:(tb__ "0|0|
S0S0S4fVcx;Vcap;R1A3S2dZ0S40S1aVcx;A1A1A2S32SaS15SaS1eS19Vcx;A1S17Vcx;A1S18Vcx;A1S58Vcx;A1R4S70S4cA7S6fR3A4S37Vcx;A1A3F_;F_;Frho;Fr0;") := ltac2:(tb__ "0|2|
S39Vcx;VHL6;VHLM;Vcap;VFSUMX;S0S4S25SdSbQ40A1A1M0S36Vcx;Vcap;S59R4R3R2R1A7S5S4S3fS1aVcx;A1A1M1Z1A3S5dVcx;VHL6;VHLM;Vcap;R1VFCX;R6R5R4R3R2AbLHC;LHS;Lmat;Lvm;Lg;Lrho;S0S4S25G0S36Vcx;Vcap;S5aR4R3R2R1A7S5S4G1Z2A3S5eVcx;VHL6;VHLM;Vcap;R1VFCX;R6R5R4R3R2AbLHC;LHS;Lmat;Lvm;Lg;Lrho;S0S4S25G0S36Vcx;Vcap;S5bR4R3R2R1A7S5S4G1Z3A3S5fVcx;VHL6;VHLM;Vcap;R1VFCX;R6R5R4R3R2AbLHC;LHS;Lmat;Lvm;Lg;Lrho;S0S4S25G0S36Vcx;Vcap;S5cR4R3R2R1A7S5S4G1Z4A3S60Vcx;VHL6;VHLM;Vcap;R1VFCX;R6R5R4R3R2AbLHC;LHS;Lmat;Lvm;Lg;Lrho;A9").
Let HLX0 (cap : Z) (HL6 : 6 + config_len F <= L) (HLM : L < MAX_INPUT) (D : MA -> Model -> Prop) : ltac2:(tb__ "0|0|
S0S0S4fVcx;Vcap;R1A3S5S4S40S1aVcx;A1A1Z0A3S32SaS15SaS1eS19Vcx;A1S17Vcx;A1S18Vcx;A1S58Vcx;A1R4S3cVD;A7S6eR3A4S37Vcx;A1A3FHP;FHT;Frho;Fr1;") := ltac2:(tb__ "0|3|
S0S0S4fVcx;Vcap;R1A3S5S4S40S1aVcx;A1M0A1Z0A3S38Vcx;VHL6;VHLM;Vcap;VFSUMX;S0S4S25SdSbQ40A1A1M1S36Vcx;Vcap;S59R4R3R2R1A7S5S4S3fG0A1M2Z1A3S5dVcx;VHL6;VHLM;Vcap;R1VFCX;R6R5R4R3R2AbLHC;LHS;Lmat;Lvm;Lg;Lrho;S0S4S25G1S36Vcx;Vcap;S5aR4R3R2R1A7S5S4G2Z2A3S5eVcx;VHL6;VHLM;Vcap;R1VFCX;R6R5R4R3R2AbLHC;LHS;Lmat;Lvm;Lg;Lrho;S0S4S25G1S36Vcx;Vcap;S5bR4R3R2R1A7S5S4G2Z3A3S5fVcx;VHL6;VHLM;Vcap;R1VFCX;R6R5R4R3R2AbLHC;LHS;Lmat;Lvm;Lg;Lrho;S0S4S25G1S36Vcx;Vcap;S5cR4R3R2R1A7S5S4G2Z4A3S60Vcx;VHL6;VHLM;Vcap;R1VFCX;R6R5R4R3R2AbLHC;LHS;Lmat;Lvm;Lg;Lrho;R4VD;R3R2R1AeLHP;LHT;Lrho;Lr1;").

Lemma ex_normal : ltac2:(tb__ "0|3|
S2cS2fZ6S42S1aVcx;A1M0A1A2S30SeSbQ8A1G0A2A1M1A2S2dG1S41A2S0S32SaS15SaS1eS19Vcx;A1S17Vcx;A1S18Vcx;A1M2S1fG2S1bVcx;A1A2Vr0;S3bS20S23A1A7S3aR1A4S33S5SdS26A1S34R1A1S14S26S49Z1S4aS3fG0A1A1A2S10S26S44S27G2A1Z0A2S11S26A1A3A3A3Lw;A3Frho;F_;F_;").
Proof using HLX0 HLX2 LOOPX MPX.
  intros H6 HLM0 rho. pose proof (config_len_range F) as CR. unfold CFG_COUNT_BIT in CR. apply LOOPX; clear rho.
  - intros r1 rho1 cap g HX Hg HCG. refine (U.Drv_h__G1.Drv_h.xeh_exists cx r1 (Drv_rx.DG X0 cap g) (DG_fds cap g) _ _ _ _ rho1 cap HX).
    + intros rho2 HL6'. exfalso. lia.
    + intros rho2 cap2 _ [_ Hov]. exfalso. lia.
    + intros rho2 cap2 HX2 H6'. pose proof HX2 as (_ & _ & _ & _ & HLM & _). pose proof HX as (_ & _ & _ & HLc & _ & HC).
      pose proof (CAP_facts cap HC) as (Cb & _ & _).
      exact (U.Drv_ht__G1.Drv_ht.ttr_ex cx cap2 FCX (Drv_hl.QN cx) (HLX2 cap2 H6' HLM) (Drv_rx.kOf g) (Drv_rx.XOf X0 cap g) (HLX0 cap2 H6' HLM _)
               r1 rho2 MPX ltac:(unfold Drv_rx.XOf, X0, init_cost; lia) HX2 H6').
  - intros r1 rho1 g _ HL' _ _. exfalso. unfold MAX_INPUT in *. lia.
  - intros r1 rho1 _ _ HL4. exfalso. lia.
Qed.

End File.

Theorem spine_ex_U : ltac2:(tb__ "0|0|
S74Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;A6").
Proof using DOTX FCX FDX FSUMX Hlim MBX MIX MPX.
  intros tid t Htid Hargc Hmay Hin rho HJM.
  change (In t (post_open_traces argv1 fs)) in Hin.
  unfold post_open_traces in Hin.

  {
    assert (GO : forall Q : world -> Prop,
              (forall r0 rho', U.Drv_m__G1.Drv_m.P0 sp draw inp r0 -> etriple segs (SPJ segs (U.Drv_m__G1.Drv_m.JD sp draw inp (U.Drv_m__G1.Drv_m.Kd0 inp (md0 tid)) r0 U.Drv_r__G1.Drv_r.tv0 (Dok X0)) T_ok rho') Q) ->
              etriple segs (SP segs (Kx [] (md_open (md0 tid) argv1)) S_M rho) Q).
    { intros Q H. exact (U.Drv_m__G1.Drv_m.m_exists_ok sp brk mb draw inp Hent Hinp Hargc (md0 tid) (Top.md_main_fs sp brk mb draw lim inp tid)
                             ri Hsec Htop (PRvm0 tid) MIX X0 (vm_room0 tid) HX0' Q H rho HJM). }
    destruct path_cases as [Hdot|Hnd].
    +
      unfold is_dot in Hin. rewrite Hdot, path_eqb_refl in Hin. destruct Hin as [<-|[]].
      apply GO. intros r0 rho' HP0.
      eapply etriple_conseq; [| intros w Hw; exact Hw | ].
      2:{ rewrite <- Hdot. exact (DOTX tid r0 rho' Htid Hargc Hdot HP0). }
      intros w [Hsm HJ]. split; [exact Hsm|]. exact (JGD_mono segs C_U 31 _ r0 _ _ (Dok X0) DTrue _ _ _ (fun _ _ _ => I) HJ).
    +
      unfold is_dot in Hin. destruct (path_eqb argv1 dot_path) eqn:E; [exfalso; apply Hnd, path_eqb_eq; exact E|].
      destruct Hmay as (Hlen & Hne & [Hd|Hl]); [exfalso; exact (Hnd Hd)|].
      destruct (fs_lookup fs argv1) as [F|] eqn:HF; [|exfalso; exact (Hl HF)].
      set (cx := mkFctx sp brk mb draw inp Hent Hinp Hargc (md0 tid) (Top.md_main_fds sp brk mb draw lim inp tid) (Top.md_main_fs sp brk mb draw lim inp tid)
                        (ok_tgt segs (Spec inp)) (Top.HokK inp) (Top.HokP inp) (Top.Hokh inp)
                        (conj Hlen (conj Hne (or_intror Hl))) F HF Hnd).
      apply GO. intros r0 rho' HP0.
      destruct (file_traces_inv fs F t Hin) as [[HL ->]|[[HL ->]|[(HL & HLM & ->)|[HL ->]]]].
      * exact (ex_refused cx r0 HP0 HL rho').
      * exact (ex_short cx r0 (HL : Z.of_nat (length (f_F cx)) < 6) rho').
      * exact (ex_overrun cx r0 (HL : 6 <= Z.of_nat (length (f_F cx)) < 6 + config_len (f_F cx)) rho').
      * exact (ex_normal cx r0 (proj1 HL : 6 + config_len (f_F cx) <= Z.of_nat (length (f_F cx))) (proj2 HL : Z.of_nat (length (f_F cx)) < MAX_INPUT) rho').
  }
Qed.
End Ex.

End SPINE.

