(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sstate"; "sobj"; "ss_next"; "ss_objs"; "sv"; "rw"; "rl"; "rm"; "swf"; "agree_below"; "obj_range"; "smatch"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "False"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "bool"; "nil"; "true"; "app"; "prod"; "length"; "nat"; "cons"; "option"; "Some"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "LQ"; "ok_frame"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "Model"; "event"; "FdEntry"; "m_fds"; "m_fs"; "FdChannel"; "fd_lookup"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r"; "tvK"; "Ki"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "wz"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "payload_len"; "zeros"; "msg_zero"; "wr"; "config_len"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl"; "QN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx.HX"; "SIDEK"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "succ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ"; "DTrue"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "add"; "mul"; "pow"; "to_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out.WLoutS"; "Pre_wl2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states"; "NX0"; "X_1"; "O_payL"; "tvL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl1_states"; "NX1"; "NX2"; "NX3"; "X_2"; "X_3"; "X_4"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "rho_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "malloc_contracts"; "aceil"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "statics_objs"; "statics_view"; "static3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "ok_sideK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "snapJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx.HX.X2"; "bsf2"; "Kwf2"; "SIDEB2"; "PRf2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx.HX.X3"; "bsf3"; "Kwf3"; "SIDEB3"; "PRf3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx.HX.X4"; "bsf4"; "Kwf4"; "SIDEB4"; "PRf4"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx1_states"; "C_1"; "T_1Bt"; "T_1B"; "T_1f"; "T_1BS"; "XB12"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx2_states"; "C_2"; "T_2Bt"; "T_2B"; "T_2f"; "E_fl2"; "E_fl2c"; "T_2BS"; "T_2fS"; "XB22"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx3_states"; "C_3"; "T_3Bt"; "T_3B"; "T_3f"; "E_fl3"; "E_fl3c"; "T_3BS"; "T_3fS"; "XB32"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx4_states"; "C_4"; "T_4Bt"; "xs_xa"; "T_4B"; "T_4f"; "E_fl4"; "E_fl4c"; "T_4BS"; "T_4fS"; "XB42";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out.WLout"; "MSG"; "Posts_wl"; "Kw"; "chw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx.HX.X1"; "SIDEB1"; "@Corelib.Lists.ListDef"; "firstn"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open"; "std_fds"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Strings.Ascii Strings.String.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLayout MallocIface MallocLaws Contract ContractDrv Pristine ClientLaws Glue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require ReprGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall SymBytes SymExit Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import
  SumConv CfgGlue CursorGlue ObjXform ObjUnbase CallGlue ListObj StrBytes InitLayout InitState InitStrs InitArg1 MuslWL DrvGlue DrvGlue2 SysExtra SysRead
  DataWin TobjJV DrvJ DrvStatics DrvPristine DrvLoop FuzzOneIface DrvWins.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec SpecConsts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl1_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx1_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx2_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx3_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx4_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl1_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx1_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx2_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx3_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx4_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.Drv_hs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import MAddr RAddr HAddr TAddr LAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Section HX.
Variable cx : Fctx.
Let sp := f_sp cx. Let brk := f_brk cx. Let mb := f_mb cx. Let draw := f_draw cx. Let inp := f_inp cx.
Let Hent : valid_entry48 imgU (mkEntry sp brk mb draw) inp := f_ent cx.
Let Hinp : valid_input_either inp := f_inp_ok cx.
Let argv := in_argv inp.
Let argv1 : list byte := nth 1 argv [].
Let fs := in_fs inp.
Let Hargc : length argv = 2%nat := f_argc cx.
Let ok : world -> Prop := f_ok cx.
Let SpecT : list event -> Prop := Spec inp.
Let HokK : forall K, K_tcons SpecT K -> ok_frame segs ok K := f_okK cx.
Let HokP : forall K, K_tcons SpecT K -> ok_pframe segs ok K := f_okP cx.
Let Hokh : ok_halted ok SpecT := f_okh cx.
Let Hmay : open_may_succeed argv1 fs := f_may cx.
Let F : list byte := f_F cx.
Let HF : fs_lookup fs argv1 = Some F := f_HF cx.
Let Hnd : argv1 <> dot_path := f_nd cx.
Let L : Z := Z.of_nat (length F).

Let P0 := U.Drv_m__G1.Drv_m.P0 sp draw inp. Let P0_tp := U.Drv_m__G1.Drv_m.P0_tp sp draw inp.
Let P0_top := U.Drv_m__G1.Drv_m.P0_top sp draw inp.
Let wtop : word := U.Drv_m__G1.Drv_m.wtop sp.
Let JD := U.Drv_m__G1.Drv_m.JD sp draw inp.
Let P0_transport := U.Drv_hs__G1.Drv_hs.P0_transport cx.

Hypothesis HL6 : ltac2:(tb__ "0|0|
S43S44Z6S3bVF;A1A2VL;A2").
Hypothesis HLM : L < MAX_INPUT.
Variable cap : Z.

Let KL1 := Drv_hl.KL1 cx.
Let Ks := Drv_hl.Ks.
Let TL := Drv_hl.TL cx cap.
Let SIDEL := Drv_hl.SIDEL cx cap.
Let TR1 := Drv_hl.TR1.
Let KL1_tcons : K_tcons SpecT KL1 := Drv_hl.KL1_tcons cx HL6 HLM.
Let KL1_vmi : vm_insensitive KL1 := Drv_hl.KL1_vmi cx.
Let normal_in_spec : SpecT (wr 1 (zeros (calls F)) ++ [ex fs 0]) := Drv_hl.normal_in_spec cx HL6 HLM.

Lemma Ks_okf : ltac2:(tb__ "0|0|
S15S2aA1S29OF_;F_;S28S15S12Q40A1A1S93VSpecT;R3A2S27S0Vok;VKs;R4R3R2A3A3F_;Fmat;Fvm;FK;"). Proof using HokK. intros. apply HokK, (Drv_hl.Ks_tcons cx). assumption. Qed.
Lemma Ks_okp : ltac2:(tb__ "0|0|
S15S2aA1S29OF_;F_;S28S15S12Q40A1A1S93VSpecT;R3A2S9dS0Vok;VKs;R4R3R2A3A3F_;Fmat;Fvm;FK;"). Proof using HokP. intros. apply HokP, (Drv_hl.Ks_tcons cx). assumption. Qed.
Lemma okside_i : ltac2:(tb__ "0|0|
S48S5fS0Vok;S34VKL1;R1A2A3FAi;").
Proof using HokK HokP KL1_tcons KL1_vmi. intros Ai. split; [apply HokK, (U.Drv_r__G1.Drv_r.Ki_tcons cx), KL1_tcons|]. split; [apply HokP, (U.Drv_r__G1.Drv_r.Ki_tcons cx), KL1_tcons | apply U.Drv_r__G1.Drv_r.Ki_vmi, KL1_vmi]. Qed.

Definition SIDEK (rho : valuation) (vm : VmMaps) (mat : list word) : Prop := ltac2:(tb__ "0|0|
S60S0S35VP0;Vwtop;S33S40Vrho;Vvm;Vmat;A9").

Lemma snapJ_tail : ltac2:(tb__ "0|1|
S1aS6S6A2M0S15G0A1S48S29OF_;F_;S1S28S15S12Q40A1A1S60S0S35VP0;Vwtop;S1dG0R6R5A3R4R3R2R1A9S60S0S35VP0;Vwtop;R6R5R4R3R2A9F_;Fmat;Fvm;Frho;FD;Ftv;Ft;").
Proof using inp sp.
  intros t tv D rho vm mat (Ai & md & HM & Hi & (HN & HD & HZ) & HP & Hvm & Hmat & HDD).
  exists Ai, md. split; [exact HM|]. split; [exact Hi|]. split; [|auto]. split; [exact (Forall_inv_tail HN)|]. split; [exact (proj2 HD) | exact (Forall_inv_tail HZ)].
Qed.

Lemma SIDEK_transport : ltac2:(tb__ "0|6|
S1S1S28S15S12Q40A1M0A1S3dR4R2R1A3S23S3eR1P1fA2SeG0S7R6R2A2S7R7R2A2A3F_;Fi;SeG0S7R5P65M1A2S7R6G1A2A3SeG0S7R6P66M2A2S7R7G2A2A3G0SeS1eS12Q8A1A1M3S9aS0S9R8A1R1A3S9aS0S9R9A1M4R1A3A3Fa;G0SeS16S9bS0G4R1A3S9bS0S9RaA1R1A3A3Fa;S22SfS43S59R1A2S42R1S46Z2Z40A2A2A2SeG3S9RbS36R2A1M5A2S9RcG5A2A3F_;Fa;S3dRaR9R8A3F_;F_;F_;F_;F_;F_;F_;Fmat;Fvm;Frho';Frho;").
Proof using .
  intros rho rho' vm mat HS Hw R101 R102 RD WK Hm.
  apply (snapJ_transport segs C_U P0 malloc_laws_U wtop U.Drv_r__G1.Drv_r.tvK DTrue rho rho' vm mat HS).
  - apply U.Drv_hs__G1.Drv_hs.tv_eval_eq_K; assumption.
  - exact RD.
  - exact WK.
  - destruct HS as (Ai & md & _ & _ & _ & HP0 & _). apply (P0_transport rho rho' HP0); [exact Hw | exact Hm].
Qed.

Lemma tvK_sub : ltac2:(tb__ "0|4|
S54S1SeS16S57R2S33S33A3S18A3SfSeS12Q40A1M0S7S56R2R3A2M1P65M2A2S7R2G2A2A3SeG0S7G1P66M3A2S7R2G3A2A3A2F_;Frho;Fs;").
Proof using .
  intros s rho H. destruct (tv_sub_eqb_sound s U.Drv_r__G1.Drv_r.tvK U.Drv_r__G1.Drv_r.tvK rho H) as [M _]. cbn [map U.Drv_r__G1.Drv_r.tvK] in M.
  injection M as A B. split; apply bv_eq; [exact B | exact A].
Qed.

Lemma smatch_drop_nil : ltac2:(tb__ "0|2|
S1S2S1aS15S2aA1S9cA2S15S3A1M0S3SdS0R5R4R3A4SeG0S5R5A1S19S3R3S1dS3R2S17S3A1A3A3A3S43S21S22S22ScR7R3A2M1A3S20S22S22G1A3A2SeS16SaS41R7R5A2A1S18A3SdS0R9S41R8R6A2R7A4F_;F_;F_;F_;Fo;Fobjs;Fw;FS;Frho;").
Proof using Hargc JD KL1 L P0 SIDEL TL.
  intros rho S w objs o Hsm Hobjs He Hwf.
  apply (smatch_drop_last segs rho S w objs o (ss_next S) Hsm Hobjs Hwf).
  intros a Ha. exfalso. unfold in_rng in Ha. lia.
Qed.

Lemma pay_empty : ltac2:(tb__ "0|1|
S1VTL;R1A1SeS22S37VF;A1Z0A3S43S21S22S22ScR3S4cA2M0A3S20S22S22G0A3A2F_;F_;Frho;").
Proof using Hargc JD KL1 L P0 SIDEL.
  intros rho HT HP0. pose proof (Drv_hl.TL_plen cx cap rho HT) as V158.
  unfold obj_range, obj_lo_of, obj_hi_of, O_payL. cbn [ob_base ob_lo ob_hi eval fst snd].
  rewrite soff_lit_small by lia. rewrite (soff_var rho 158) by (rewrite V158; unfold F in *; lia). rewrite V158. unfold F in *. lia.
Qed.

Lemma static3_low : ltac2:(tb__ "0|0|
S22S5dS35R1A2S42R2S59A2F_;Fa;").
Proof using cx. exact (U.Drv_hs__G1.Drv_hs.static3_low cx). Qed.

Lemma KL1_fd1 : ltac2:(tb__ "0|0|
S15S2aA1S29VKL1;R2R1A2SeS1eS2bA1S2fS2cR2A1S92A2S1fS2bS2eS92A1A2A3F_;Fmd;Ftr;").
Proof using cx. intros tr md (_ & Hf & _). change WLout.chw with (Z_to_bv 64 1). rewrite Hf. reflexivity. Qed.

Lemma zeros_len : ltac2:(tb__ "0|0|
S22S43Z0R1A2SeS1cS1bS12Q8A1S38R2A1A2S47S45Z2R2A2A1A3F_;Fn;").
Proof using Hargc JD KL1 L. intros n Hn. pose proof (zeros_length n Hn). lia. Qed.

Section X1.
Hypothesis HC : calls F = 1.

Lemma LT1 : ltac2:(tb__ "0|1|
SfS3eS4aS4S4bA1A2SfS3ePf1S4aA2SfS3eP66S4S6eA1M0A2S3eG0S3fG0A1A2A2A2A2").
Proof using .
  split; [apply Pos.ltb_lt; reflexivity|]. split; [apply Pos.ltb_lt; reflexivity|]. split; [apply Pos.ltb_lt; reflexivity | apply Pos.lt_succ_diag_r].
Qed.

Lemma x1_exit_safe : ltac2:(tb__ "0|0|
S1S48S29OF_;F_;S1S32S0Vok;S25S0VJD;VKL1;R3S17S1aS6S6A2A1R2A4S70R1A4S30S11L_;A4Frho;FDf;Fr0';").
Proof using HC Hargc HokK HokP Hokh KL1_tcons P0 SIDEL TL normal_in_spec.
  intros r0' Df rho.
  apply (triple_from ok _ (fun r w => SP segs KL1 T_1fS r w)).
  { intros [tr [ms md]] [Hsm (Ai & HJi & _)]. pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & _).
    destruct (statics_view_of_MInvR segs C_U Ai _ md HM) as [g Vg].
    destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U _ T_1f (tr, mkCfg ms md) g (ss_next T_1f) (Pos.succ (ss_next T_1f)) Hsm
                ltac:(lia) Vg
                (robjs_missT_statics_sound C_U P0 (ss_facts T_1f) [] (ss_objs T_1f) _ ltac:(intros t Ht; destruct Ht) (smatch_facts_hold segs _ _ _ Hsm) missT_T1f)
                ltac:(rewrite T_1fS_eq; exact swf_T_1fS)) as [Hsm' _].
    eexists. split; [rewrite <- T_1fS_eq; exact Hsm' | exact Hk]. }
  intros rho1. destruct T_1fS_shape as [NX1 LN1].
  eapply (run_tr ok); [exact run_T1f | exact LN1 | apply HokK, KL1_tcons |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state]. destruct cert_x1 as (Hi & H17 & H10).
  apply (triple_exit_eval segs ok SpecT KL1 E_x1 rho2 0);
    [apply HokK, KL1_tcons | apply HokP, KL1_tcons | exact Hokh | exact Hi | left; exact H17 | rewrite H10; reflexivity |].
  intros tr md (-> & _ & ->). pose proof normal_in_spec as N. rewrite HC in N. exact N.
Qed.
Lemma x1_exit_ex : ltac2:(tb__ "0|0|
S1S48S29OF_;F_;S1S31S0S25S0VJD;VKL1;R3S17S1aS6S6A2A1R2A4S70R1A4S3cVcx;A1A3Frho;FDf;Fr0';").
Proof using HC SIDEL TL.
  intros r0' Df rho.
  apply (etriple_from _ (fun r w => SP segs KL1 T_1fS r w)).
  { intros [tr [ms md]] [Hsm (Ai & HJi & _)]. pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & _).
    destruct (statics_view_of_MInvR segs C_U Ai _ md HM) as [g Vg].
    destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U _ T_1f (tr, mkCfg ms md) g (ss_next T_1f) (Pos.succ (ss_next T_1f)) Hsm
                ltac:(lia) Vg
                (robjs_missT_statics_sound C_U P0 (ss_facts T_1f) [] (ss_objs T_1f) _ ltac:(intros t Ht; destruct Ht) (smatch_facts_hold segs _ _ _ Hsm) missT_T1f)
                ltac:(rewrite T_1fS_eq; exact swf_T_1fS)) as [Hsm' _].
    eexists. split; [rewrite <- T_1fS_eq; exact Hsm' | exact Hk]. }
  intros rho1. destruct T_1fS_shape as [NX1 LN1].
  eapply erun_tr; [exact run_T1f | exact LN1 |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state]. destruct cert_x1 as (Hi & H17 & H10).
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply (etriple_exit_eval segs KL1 E_x1 rho2 0 Hi (or_introl H17))].
  - intros w (tr & md & (Htr & _ & Hfs) & Hw). unfold Drv_hl.QN. rewrite Hw, Htr, Hfs, (HC : calls (f_F cx) = 1). reflexivity.
  - rewrite H10. reflexivity.
Qed.

Section Free1.
Hypothesis MCs : ltac2:(tb__ "0|0|
S58S0S35S5eA3").

Lemma x1_free_safe : ltac2:(tb__ "0|0|
S1S28S15S12Q40A1A1S3dR3R2R1A3S32S0Vok;S24S0VKs;VKL1;R3R2A3S6dR4A4S30S11L_;A4F_;Fmat;Fvm;Frho;").
Proof using HC KL1_tcons MCs SIDEL TL normal_in_spec.
  intros rho vm mat HSn.
  eapply triple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho C_1m 0 (-128) C_1x w unb_C1 (SPJ_xforms segs _ [XRebase 0; XRebase 1; XMerge 0] rho C_1 C_1m w xs_C1_ok Hw)) | intros w Hw; exact Hw |].
  eapply triple_conseq with (P := SPJ segs (JD KL1 rho U.Drv_r__G1.Drv_r.tvK DTrue) C_1x rho); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 U.Drv_r__G1.Drv_r.tvK DTrue rho vm mat tr md HSn Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_ff1_vals as (F12 & F13 & F10 & F15). destruct C_1x_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_ff1 as (CHK & RCHK & NZ).
  apply (dfree_call segs C_U EC_U 31 KL1 rho P0 malloc_laws_U ok C_1x s_ff1 R_ff1 rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (mc_free _ _ _ MCs). apply okside_i.
  - exact efr_ff1.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf NZ). }
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_1x) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) robj_inwi R_ff1 _ rho md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho Ai _ o a Ho Hr).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_1f_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply x1_exit_safe.
Qed.
End Free1.

Section FreeX1.
Hypothesis FCX : free_contract_ex_U.

Lemma x1_free_ex : ltac2:(tb__ "0|0|
S1S28S15S12Q40A1A1S3dR3R2R1A3S31S0S24S0VKs;VKL1;R3R2A3S6dR4A4S3cVcx;A1A3F_;Fmat;Fvm;Frho;").
Proof using FCX HC SIDEL TL.
  intros rho vm mat HSn.
  eapply etriple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho C_1m 0 (-128) C_1x w unb_C1 (SPJ_xforms segs _ [XRebase 0; XRebase 1; XMerge 0] rho C_1 C_1m w xs_C1_ok Hw)) | intros w Hw; exact Hw |].
  eapply etriple_conseq with (P := SPJ segs (JD KL1 rho U.Drv_r__G1.Drv_r.tvK DTrue) C_1x rho); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 U.Drv_r__G1.Drv_r.tvK DTrue rho vm mat tr md HSn Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_ff1_vals as (F12 & F13 & F10 & F15). destruct C_1x_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_ff1 as (CHK & RCHK & NZ).
  apply (dfree_call_ex segs C_U EC_U 31 KL1 rho P0 malloc_laws_U C_1x s_ff1 R_ff1 rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (FCX Ai). apply U.Drv_r__G1.Drv_r.Ki_vmi, KL1_vmi.
  - exact efr_ff1.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf NZ). }
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_1x) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) robj_inwi R_ff1 _ rho md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho Ai _ o a Ho Hr).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_1f_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply x1_exit_ex.
Qed.
End FreeX1.

Lemma x1_A_leaf : ltac2:(tb__ "0|5|
S2S2S2S2S2S54S1S22S28S15S12Q40A1A1S30SeS1eS2A1M0S95RbS87A2S1fS2RaA2M1A3SeG0S94RbU0Nd0A3G1A3SeS15S3A1M2S5RbA1S19S3S5RaA1S1dS3S4cS17S3A1A3A3A3SeS16SaRbA1S18A3SeS2RcS41RdS5RcA1M3A2A3SeG2S5RdA1M4S19S3G3S5bS35S4aA2A3A3SeS2RdS41ReG4A2A3SeS16S5aReS6dRdA3S18A3SeS16S55ReP1fA2S18A3SeS16S57RfS33S33A3S18A3VSIDEL;S4aRfReRdRcA5SeS22S37VF;A1Z0A3S24S0VKs;VKL1;RfReA3R17R11RdA5S10S1S1SfS3dR1R11R10A3S24S0VKs;VKL1;R11R10A3S6dR1RfA5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;Fs;Fn4;Fn3;Fn2;Fn1;Fn;").
Proof using TL.
  intros n n1 n2 n3 n4 s rho g vm mat [tr [ms md]] Hx Hu Ho2 Hwf3 Hn3 Ho3 Hn4 He Hid Htv (HSn & HG & HV & Hv & HT) HP0 [Hsm Hk].
  pose proof (smatch_unbase segs rho n1 0 (-208) n2 _ Hu (smatch_xforms segs xs_xa rho n n1 _ Hx Hsm)) as H2.
  assert (H3 : smatch segs rho n3 (tr, mkCfg ms md)).
  { rewrite Hn3. apply (smatch_drop_nil rho n2 _ (ss_objs n3) O_payL H2 Ho2 (pay_empty rho HT HP0)). rewrite <- Hn3. exact Hwf3. }
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho n3 (tr, mkCfg ms md) (ss_objs n4) g NX0 H3 Ho3 HV Hv) as (m' & H4 & Hout & RD & WK & _).
  rewrite <- Hn4 in H4.
  pose proof (entails_sound segs _ _ s _ _ He H4) as H5.
  exists (rho_sub (set_rm rho m') s). split; [|split; [exact H5 | exact Hk]].
  destruct (tvK_sub s (set_rm rho m') Htv) as [R101 R102].
  apply (SIDEK_transport rho); [exact (snapJ_tail _ _ _ _ _ _ HSn) | | exact R101 | exact R102 | | |].
  - intros i Hi. cbn [rho_sub rw]. rewrite (wsub_get_id s 31 i Hid ltac:(lia)). reflexivity.
  - intros a. cbn [rho_sub set_rm rm]. apply RD.
  - intros a. cbn [rho_sub set_rm rm]. apply WK.
  - intros a Ha. cbn [rho_sub set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Lemma x1_B2_intro : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1S30VSIDEL;S4aR5R4R3R2A5S42Z0S37VF;A1A2S24S0VKs;VKL1;R5R4A3S4bR7R3A5S10S1S1SfSfVTL;R1A1S60S0S35VP0;Vwtop;S4dS40R1R7R6A9A2S24S0VKs;VKL1;R7R6A3S72R1R5A5A2Lrho';A2F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;").
Proof using Hargc JD L P0_transport cap.
  intros rho g vm mat [tr [ms md]] (HSn & HG & HV & Hv & HT) HP [Hsm Hk].
  destruct X_1_objs as (OX & O2 & LnX & R10 & PcX).
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho X_1 (tr, mkCfg ms md) (firstn 13 (ss_objs X_1)) g NX0 Hsm OX HV Hv) as (m' & H1 & Hout & RD & WK & _).
  rewrite XB1r_eq in H1. set (rho' := set_rm rho m') in *.
  destruct XB10_eq as (RE & O2r & WF & NXr).
  pose proof HT as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  assert (H2 : smatch segs rho' XB10 (tr, mkCfg ms md)).
  { rewrite <- RE.
    apply (proj1 (SPJ_reshape segs (liftK (fun _ _ => True)) rho' XB1r 2 _ O_payB (tr, mkCfg ms md) O2r eq_refl eq_refl eq_refl WF
                              ltac:(intros _; unfold obj_lo_of, obj_hi_of, O_payB, O_payL; cbn [ob_base ob_lo ob_hi eval rho' set_rm rw]; rewrite E240; split; reflexivity)
                              (conj H1 I))). }
  pose proof (smatch_unbase segs rho' XB11 0 (-208) XB12 _ unb_fo1 (smatch_xforms segs xs_fo rho' XB10 XB11 _ xs_fo1_ok H2)) as H3.
  exists rho'. split; [split|split; [exact H3 | exact Hk]].
  - apply (Drv_hl.TL_rw cx cap rho rho'); [intros i _; reflexivity | exact HT].
  - apply (snapJ_transport segs C_U P0 malloc_laws_U wtop tvL DTrue rho rho' vm mat HSn).
    + apply (Drv_hl.tv_eval_eq_L); reflexivity.
    + exact RD.
    + exact WK.
    + destruct HSn as (Ai & md' & _ & _ & _ & HP0 & _). apply (P0_transport rho rho' HP0); [intros i _; reflexivity|].
      intros a Ha. cbn [rho' set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Definition SIDEB1 (rho : valuation) (g : Z) (vm : VmMaps) (mat : list word) : Prop := ltac2:(tb__ "0|1|
SfS3dVrho;Vvm;Vmat;A3SfS5cS0S35S9Vrho;A1Vg;A4SeS12Q40M0A1S7Vrho;S4S6eA1A2S14G0Vg;A2A3A2A2").

Lemma SIDEB1_agree : ltac2:(tb__ "0|0|
S23S1S1S22S28S15S12Q40A1A1S96R5R3R2R1A4SbR7R6R5A3S3eS4S6eA1R8A2S96R7R6R5R4A4F_;F_;F_;Fmat;Fvm;Fg;Frho';Frho;Fn;").
Proof using SIDEL TL.
  intros n rho rho' g vm mat (HS & HV & Hv) (Hw & _ & Hm) Hn. pose proof LT1 as (_ & _ & L102 & _).
  assert (Hm' : forall a, rm rho' a = rm rho a) by (intros a; symmetry; apply Hm).
  split; [|split].
  - apply (SIDEK_transport rho rho' vm mat HS).
    + intros i Hi. symmetry. apply Hw. lia.
    + symmetry. apply Hw. lia.
    + symmetry. apply Hw. lia.
    + intros a. unfold rd_of. rewrite Hm'. reflexivity.
    + intros a. unfold wok_of. rewrite Hm'. reflexivity.
    + intros a _. apply Hm'.
  - apply (statics_view_rm segs C_U statics_layout_U (rm rho) (rm rho') g); [intros a _; apply Hm' | exact HV].
  - rewrite <- Hw by lia. exact Hv.
Qed.

Lemma x1_BS_intro : ltac2:(tb__ "0|1|
S1S1S30S25S0VJD;VKL1;R3S33S40A4S6fR2R1A5S10S1S1S10S22S22S10S28S28S10S15S12Q40A1A1M0G0SfS96R4R3R2R1A4S24S0VKs;VKL1;R2R1A3S71R4R6A5A2Lmat;A2Lvm;A2Lg;A2Lrho1;A2F_;Fw;Frho;Fr0;").
Proof using SIDEL TL.
  intros r0 rho [tr [ms md]] [Hsm (Ai & HJi & _)]. destruct ent_T1Bt as [He NxBt]. pose proof LT1 as (_ & _ & L102 & _).
  pose proof (entails_sound segs _ _ [] _ _ He Hsm) as Hsm1. set (rho0 := rho_sub rho []) in Hsm1.
  assert (HJi0 : JGi segs C_U 31 KL1 r0 P0 [] U.Drv_r__G1.Drv_r.tvK Ai rho0 tr md).
  { apply (JGi_stable segs C_U 31 KL1 r0 P0 [] malloc_laws_U 104 U.Drv_r__G1.Drv_r.tvK Ai rho rho0 tr md ltac:(lia) (U.Drv_r__G1.Drv_r.tvK_below cx 104 ltac:(lia))); [|exact HJi].
    split; [intros i _; reflexivity|]. split; [intros l; reflexivity | intros a; reflexivity]. }
  pose proof HJi0 as (Hav & Hk & [HM [Hi HTPI]] & HP & HN & HKF & HP0').
  pose proof (U.Drv_hs__G1.Drv_hs.P0_now cx _ _ _ _ _ _ _ HJi0) as HP0.
  pose proof (tv_geo_of_JGi segs C_U 31 KL1 r0 P0 U.Drv_r__G1.Drv_r.tvK Ai rho0 tr md HJi0) as HG.
  destruct (statics_view_of_MInvR segs C_U Ai rho0 md HM) as [g Vg].
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U rho0 T_1Bt (tr, mkCfg ms md) g (ss_next T_1Bt) (Pos.succ (ss_next T_1Bt)) Hsm1
              ltac:(lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts T_1Bt) U.Drv_r__G1.Drv_r.tvK (ss_objs T_1Bt) rho0 HG (smatch_facts_hold segs _ _ _ Hsm1) missT_T1B)
              ltac:(rewrite T_1BS_eq; exact swf_T_1BS)) as [Hsm' Hag].
  set (rho1 := rho_set_rw rho0 (ss_next T_1Bt) (Z_to_bv 64 g)) in *.
  assert (RW : forall i, i <> ss_next T_1Bt -> rw rho1 i = rw rho0 i) by (intros i Hi'; subst rho1; apply rho_set_rw_other; exact Hi').
  exists rho1, g, (m_vmmaps md), (m_vm_materialized md). split; [|split; [rewrite <- T_1BS_eq; exact Hsm' | apply (Drv_hl.Ks_intro); exact Hk]].
  destruct (deJ segs C_U 31 P0 wtop P0_top KL1 r0 U.Drv_r__G1.Drv_r.tvK DTrue Ai rho0 tr md HJi0 I HP0) as [HSn _].
  split; [|split; [exact Vg | subst rho1; apply rho_set_rw_at]].
  apply (SIDEK_transport rho0 rho1 _ _ HSn).
  - intros i Hi'. apply RW. lia.
  - apply RW. lia.
  - apply RW. lia.
  - intros a; reflexivity.
  - intros a; reflexivity.
  - intros a _; reflexivity.
Qed.

Lemma x1_B_leaf : ltac2:(tb__ "0|1|
S2S2S54S1S22S28S15S12Q40A1A1S30SeS15S3A1S5R8A1M0S19S3S5R7A1S5bS35S4S6eA1A2A3A3SeS2R8S41R9G0A2A3SeS16S5aR9S6dR8A3S18A3SeS16S55R9P1fA2S18A3SeS16S57RaS33S33A3S18A3S96RaR9R8R7A4S24S0VKs;VKL1;R9R8A3ReRbR7A5S10S1S1SfS3dR1RbRaA3S24S0VKs;VKL1;RbRaA3S6dR1R9A5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;Fs;Fn4;Fn;").
Proof using SIDEL TL.
  intros n n4 s rho g vm mat [tr [ms md]] Ho Hn4 He Hid Htv (HSn & HV & Hv) [Hsm Hk].
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho n (tr, mkCfg ms md) (ss_objs n4) g (ss_next T_1Bt) Hsm Ho HV Hv) as (m' & H4 & Hout & RD & WK & _).
  rewrite <- Hn4 in H4.
  pose proof (entails_sound segs _ _ s _ _ He H4) as H5.
  exists (rho_sub (set_rm rho m') s). split; [|split; [exact H5 | exact Hk]].
  destruct (tvK_sub s (set_rm rho m') Htv) as [R101 R102].
  apply (SIDEK_transport rho); [exact HSn | | exact R101 | exact R102 | | |].
  - intros i Hi. cbn [rho_sub rw]. rewrite (wsub_get_id s 31 i Hid ltac:(lia)). reflexivity.
  - intros a. cbn [rho_sub set_rm rm]. apply RD.
  - intros a. cbn [rho_sub set_rm rm]. apply WK.
  - intros a Ha. cbn [rho_sub set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Section Safe1.
Hypothesis MCs : ltac2:(tb__ "0|0|
S58S0S35S5eA3").

Lemma x1_A_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4aR4R3R2R1A5SeS22S37VF;A1Z0A3S32S0Vok;S24S0VKs;VKL1;R4R3A3S4bR6A4S30S11L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS HP0. pose proof HS as (HSn & HG & HV & Hv & HT). pose proof HT as [_ [_ P2]]. pose proof (P2 HP0) as Z241.
  pose proof LT1 as (L1 & L2 & _). destruct diff_XA10 as (Hd & Hwf & Hln & Hnx).
  apply (triple_restate segs ok _ rho X_1 XA10 _ _ Hwf Hd).
  { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite Z241. reflexivity. }
  eapply (run_tr ok); [exact run_XA10 | exact Hln | apply Ks_okf, KL1_tcons |].
  rewrite Hnx. destruct ent_C1 as (E1 & E2 & _ & _). destruct ent_C1_props as (I1 & I2 & _ & _ & T1 & T2 & _ & _).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (Drv_hl.SIDEL_agree cx cap NX0 _ rho rho2 g vm mat HS Hag2 L1 L2) as HS2.
  - destruct XA1a_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_1 r w)); [intros w Hw; exact (x1_A_leaf XA1a XA1a1 XA1a2 XA1a3 XA1a4 s_CAa1 rho2 g vm mat w xs_XA1a_ok unb_XA1a O2 W3 N3 O3 N4 E1 I1 T1 HS2 HP0 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x1_free_safe MCs rho3 vm mat HS3).
  - destruct XA1b_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_1 r w)); [intros w Hw; exact (x1_A_leaf XA1b XA1b1 XA1b2 XA1b3 XA1b4 s_CAb1 rho2 g vm mat w xs_XA1b_ok unb_XA1b O2 W3 N3 O3 N4 E2 I2 T2 HS2 HP0 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x1_free_safe MCs rho3 vm mat HS3).
Qed.

Lemma x1_Bt_safe : ltac2:(tb__ "0|0|
S1S1S32S0Vok;S25S0VJD;VKL1;R2S33S40A4S6fR1A4S30S11L_;A4Frho;Fr0;").
Proof using HC Hargc HokK HokP Hokh KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport SIDEL TL normal_in_spec.
  intros r0 rho. pose proof LT1 as (_ & _ & _ & L4).
  apply (triple_from ok _ (fun r w => exists g vm mat, SIDEB1 r g vm mat /\ SP segs (Ks KL1 vm mat) T_1BS r w)).
  { intros w Hw. destruct (x1_BS_intro r0 rho w Hw) as (rho1 & g & vm & mat & HS & HP'). exists rho1, g, vm, mat. split; assumption. }
  intros rho1. apply triple_ex. intros g. apply triple_ex. intros vm. apply triple_ex. intros mat. apply triple_pure. intros HS1.
  destruct T_1BS_shape as [NxS LnS].
  eapply (run_tr ok); [exact run_T1B | exact LnS | apply Ks_okf, KL1_tcons |].
  rewrite NxS. destruct ent_C1 as (_ & _ & E3 & E4). destruct ent_C1_props as (_ & _ & I3 & I4 & _ & _ & T3 & T4).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (SIDEB1_agree _ rho1 rho2 g vm mat HS1 Hag2 L4) as HS2.
  - destruct XB1a_sets as (O4 & _ & N4).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_1 r w)); [intros w Hw; exact (x1_B_leaf XB1a XB1a4 s_CBa1 rho2 g vm mat w O4 N4 E3 I3 T3 HS2 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x1_free_safe MCs rho3 vm mat HS3).
  - destruct XB1b_sets as (O4 & _ & N4).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_1 r w)); [intros w Hw; exact (x1_B_leaf XB1b XB1b4 s_CBb1 rho2 g vm mat w O4 N4 E4 I4 T4 HS2 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x1_free_safe MCs rho3 vm mat HS3).
Qed.

Lemma x1_B_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4aR4R3R2R1A5S42Z0S37VF;A1A2S32S0Vok;S24S0VKs;VKL1;R4R3A3S4bR6A4S30S11L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS HP.
  apply (triple_from ok _ (fun r w => (TL r /\ snapJ segs C_U P0 wtop tvL DTrue r vm mat) /\ SP segs (Ks KL1 vm mat) XB12 r w)); [intros w Hw; exact (x1_B2_intro rho g vm mat w HS HP Hw)|].
  intros rho1. apply triple_pure. intros [HT1 HSn1].
  eapply triple_conseq with (P := SPJ segs (JD KL1 rho1 tvL DTrue) XB12 rho1); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 tvL DTrue rho1 vm mat tr md HSn1 Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_fb1_vals as (F12 & F13 & F10 & F15). destruct XB12_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_fb1 as [CHK RCHK].
  pose proof HT1 as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  apply (dfree_call segs C_U EC_U 31 KL1 rho1 P0 malloc_laws_U ok XB12 s_fb1 R_fb1 rho1 tvL 0%nat (SVar 241, SVar 158) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho2. apply (mc_free _ _ _ MCs). apply okside_i.
  - exact efr_fb1.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (Drv_hl.tvL_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP' & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho1 (SVar 241, SVar 158)) by (unfold tnz; cbn [fst eval]; exact NZ241).
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho1 (ss_facts XB12) tvL (Some 0%nat) robj_inwi R_fb1 _ rho1 md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho1 Ai _ o a Ho Hr).
      * exists (SVar 241, SVar 158). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_1B_eq. change (remove_nth 0 tvL) with U.Drv_r__G1.Drv_r.tvK. apply x1_Bt_safe.
Qed.

Theorem x1_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4aR4R3R2R1A5S32S0Vok;S24S0VKs;VKL1;R3R2A3S4bR5A4S30S11L_;A4F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS. pose proof (Drv_hl.plen_range cx HL6 HLM) as PR.
  destruct (Z.eq_dec (payload_len F) 0) as [Z0|NZ]; [exact (x1_A_safe rho g vm mat HS Z0) | apply (x1_B_safe rho g vm mat HS ltac:(unfold F in *; lia))].
Qed.
End Safe1.

Section Ex1.
Hypothesis FCX : free_contract_ex_U.

Lemma x1_A_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4aR4R3R2R1A5SeS22S37VF;A1Z0A3S31S0S24S0VKs;VKL1;R4R3A3S4bR6A4S3cVcx;A1A3F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC TL.
  intros rho g vm mat HS HP0. pose proof HS as (HSn & HG & HV & Hv & HT). pose proof HT as [_ [_ P2]]. pose proof (P2 HP0) as Z241.
  pose proof LT1 as (L1 & L2 & _). destruct diff_XA10 as (Hd & Hwf & Hln & Hnx).
  apply (etriple_restate segs _ rho X_1 XA10 _ _ Hwf Hd).
  { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite Z241. reflexivity. }
  eapply erun_tr; [exact run_XA10 | exact Hln |].
  rewrite Hnx. destruct ent_C1 as (E1 & E2 & _ & _). destruct ent_C1_props as (I1 & I2 & _ & _ & T1 & T2 & _ & _).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (Drv_hl.SIDEL_agree cx cap NX0 _ rho rho2 g vm mat HS Hag2 L1 L2) as HS2.
  - destruct XA1a_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_1 r w)); [intros w Hw; exact (x1_A_leaf XA1a XA1a1 XA1a2 XA1a3 XA1a4 s_CAa1 rho2 g vm mat w xs_XA1a_ok unb_XA1a O2 W3 N3 O3 N4 E1 I1 T1 HS2 HP0 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x1_free_ex FCX rho3 vm mat HS3 w0 Hw0).
  - destruct XA1b_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_1 r w)); [intros w Hw; exact (x1_A_leaf XA1b XA1b1 XA1b2 XA1b3 XA1b4 s_CAb1 rho2 g vm mat w xs_XA1b_ok unb_XA1b O2 W3 N3 O3 N4 E2 I2 T2 HS2 HP0 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x1_free_ex FCX rho3 vm mat HS3 w0 Hw0).
Qed.

Lemma x1_Bt_ex : ltac2:(tb__ "0|0|
S1S1S31S0S25S0VJD;VKL1;R2S33S40A4S6fR1A4S3cVcx;A1A3Frho;Fr0;").
Proof using FCX HC SIDEL TL.
  intros r0 rho. pose proof LT1 as (_ & _ & _ & L4).
  apply (etriple_from _ (fun r w => exists g vm mat, SIDEB1 r g vm mat /\ SP segs (Ks KL1 vm mat) T_1BS r w)).
  { intros w Hw. destruct (x1_BS_intro r0 rho w Hw) as (rho1 & g & vm & mat & HS & HP'). exists rho1, g, vm, mat. split; assumption. }
  intros rho1. apply etriple_ex. intros g. apply etriple_ex. intros vm. apply etriple_ex. intros mat. apply etriple_pure. intros HS1.
  destruct T_1BS_shape as [NxS LnS].
  eapply erun_tr; [exact run_T1B | exact LnS |].
  rewrite NxS. destruct ent_C1 as (_ & _ & E3 & E4). destruct ent_C1_props as (_ & _ & I3 & I4 & _ & _ & T3 & T4).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (SIDEB1_agree _ rho1 rho2 g vm mat HS1 Hag2 L4) as HS2.
  - destruct XB1a_sets as (O4 & _ & N4).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_1 r w)); [intros w Hw; exact (x1_B_leaf XB1a XB1a4 s_CBa1 rho2 g vm mat w O4 N4 E3 I3 T3 HS2 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x1_free_ex FCX rho3 vm mat HS3 w0 Hw0).
  - destruct XB1b_sets as (O4 & _ & N4).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_1 r w)); [intros w Hw; exact (x1_B_leaf XB1b XB1b4 s_CBb1 rho2 g vm mat w O4 N4 E4 I4 T4 HS2 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x1_free_ex FCX rho3 vm mat HS3 w0 Hw0).
Qed.

Lemma x1_B_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4aR4R3R2R1A5S42Z0S37VF;A1A2S31S0S24S0VKs;VKL1;R4R3A3S4bR6A4S3cVcx;A1A3F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC TL.
  intros rho g vm mat HS HP.
  apply (etriple_from _ (fun r w => (TL r /\ snapJ segs C_U P0 wtop tvL DTrue r vm mat) /\ SP segs (Ks KL1 vm mat) XB12 r w)); [intros w Hw; exact (x1_B2_intro rho g vm mat w HS HP Hw)|].
  intros rho1 w0 [[HT1 HSn1] Hw0]. revert w0 Hw0.
  eapply etriple_conseq with (P := SPJ segs (JD KL1 rho1 tvL DTrue) XB12 rho1); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 tvL DTrue rho1 vm mat tr md HSn1 Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_fb1_vals as (F12 & F13 & F10 & F15). destruct XB12_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_fb1 as [CHK RCHK].
  pose proof HT1 as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  apply (dfree_call_ex segs C_U EC_U 31 KL1 rho1 P0 malloc_laws_U XB12 s_fb1 R_fb1 rho1 tvL 0%nat (SVar 241, SVar 158) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho2. apply (FCX Ai). apply U.Drv_r__G1.Drv_r.Ki_vmi, KL1_vmi.
  - exact efr_fb1.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (Drv_hl.tvL_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP' & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho1 (SVar 241, SVar 158)) by (unfold tnz; cbn [fst eval]; exact NZ241).
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho1 (ss_facts XB12) tvL (Some 0%nat) robj_inwi R_fb1 _ rho1 md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho1 Ai _ o a Ho Hr).
      * exists (SVar 241, SVar 158). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_1B_eq. change (remove_nth 0 tvL) with U.Drv_r__G1.Drv_r.tvK. apply x1_Bt_ex.
Qed.

Theorem x1_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4aR4R3R2R1A5S31S0S24S0VKs;VKL1;R3R2A3S4bR5A4S3cVcx;A1A3F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC HL6 HLM TL.
  intros rho g vm mat HS. pose proof (Drv_hl.plen_range cx HL6 HLM) as PR.
  destruct (Z.eq_dec (payload_len F) 0) as [Z0|NZ]; [exact (x1_A_ex rho g vm mat HS Z0) | apply (x1_B_ex rho g vm mat HS ltac:(unfold F in *; lia))].
Qed.
End Ex1.

End X1.

Section X2.
Hypothesis HC : calls F = 2.

Lemma LT2 : ltac2:(tb__ "0|1|
SfS3eS4eS4S51A1A2SfS3ePf1S4eA2SfS3eP66S4S74A1M0A2S3eG0S3fG0A1A2A2A2A2").
Proof using .
  split; [apply Pos.ltb_lt; reflexivity|]. split; [apply Pos.ltb_lt; reflexivity|]. split; [apply Pos.ltb_lt; reflexivity | apply Pos.lt_succ_diag_r].
Qed.

Definition bsf2 : list byte := zeros 1.
Definition PRf2 (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
SfSeS15S12Q8A1M0A1M1S8Vrho1;P5A2S61A3SfSeG1S8Vrho1;P6A2S17G0A1A3SfSeS22S13Q40M2S7Vrho1;PdA2A2Z2A3SeS22S13G2S7Vrho1;PfA2A2Z0A3A2A2A2").
Definition Kwf2 (k : nat) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S91VKL1;S61S17S12Q8A1A1Vk;A4").

Lemma bsf2_len : length bsf2 = 2%nat. Proof using . reflexivity. Qed.
Lemma zeros2_eq : ltac2:(tb__ "0|1|
SeS15S12Q8A1M0A1S38Z2A1S19G0S39S61A3A3"). Proof using . reflexivity. Qed.
Lemma Kwf2_trace : ltac2:(tb__ "0|1|
S1cS15S2aA1M0S29S62R3R2R1A3SfSeG0R3S19S2aVTR1;S3aZ1S97S12Q8A1R4S61A3A2A3A3SfSeS15S1aS12Q40A1S2bA2A1S2cR2A1S99A3SeS98S2dR2A1Vfs;A3A2A2F_;Fmd;Ftr;Fk;").
Proof using .
  intros k tr md (tr0 & (-> & Hf & Hs) & ->). split; [|auto]. unfold WLout.TRk, WLout.MSG, wr. rewrite app_nil_r. reflexivity.
Qed.
Lemma Kwf2_tcons : ltac2:(tb__ "0|0|
S1cS93VSpecT;S62R1A1A2Fk;").
Proof using HC normal_in_spec.
  intros k tr md HK. destruct (Kwf2_trace k tr md HK) as (-> & _ & _). exists (wr 1 (zeros (calls F)) ++ [ex fs 0]). split; [exact normal_in_spec|].
  rewrite HC, zeros2_eq. unfold TR1, Drv_hl.TR1. rewrite <- (firstn_skipn k bsf2) at 2. rewrite !Drv_hl.wr_app, <- !app_assoc.
  rewrite (app_assoc (wr 1 msg_zero) (wr 1 (firstn k bsf2))). apply is_prefix_app.
Qed.
Lemma wl2f2_call : ltac2:(tb__ "0|1|
S1S64R1A1S32S0Vok;S24S0VKL1;S49R2A4S26S0S62S1bS12Q8A1M0S8fS61S17G0A1A2A2A1S4S49A1R2S90A5A4F_;Frho1;").
Proof using HC SIDEL TL normal_in_spec.
  intros rho1 (H5 & H6 & H13 & H15).
  apply (WLout.wl2_sum ok KL1 rho1 bsf2 [] H5 H6 ltac:(rewrite H13, bsf2_len; reflexivity) ltac:(rewrite H15; reflexivity)).
  - unfold WLout.MSG, max_write_total. rewrite app_nil_r, bsf2_len. cbn. lia.
  - intros k. apply HokK, Kwf2_tcons.
  - intros k. apply HokP, Kwf2_tcons.
  - apply KL1_fd1.
  - rewrite bsf2_len. cbn. lia.
Qed.
Lemma wl2f2_ecall : ltac2:(tb__ "0|1|
S1S64R1A1S31S0S24S0VKL1;S49R2A4S26S0S62S1bS12Q8A1M0S8fS61S17G0A1A2A2A1S4S49A1R2S90A5A3F_;Frho1;").
Proof using SIDEL TL.
  intros rho1 (H5 & H6 & H13 & H15).
  apply (WLout.wl2_sum_ex KL1 rho1 bsf2 [] H5 H6 ltac:(rewrite H13, bsf2_len; reflexivity) ltac:(rewrite H15; reflexivity)).
  - unfold WLout.MSG, max_write_total. rewrite app_nil_r, bsf2_len. cbn. lia.
  - apply KL1_fd1.
  - rewrite bsf2_len. cbn. lia.
Qed.

Lemma fl2_intro : ltac2:(tb__ "0|2|
S1S30S24S0VKL1;S77R2R1A5S10S1S1SfSfSeS15S12Q8A1M0A1M1S8R1P5A2S61A3SeG1S8R1P6A2S17G0A1A3A2S24S0VKL1;S78R1R3A5A2Lrho';A2F_;Fw;Frho;").
Proof using Hargc JD L P0 SIDEL TL.
  intros rho [tr [ms md]] [Hsm Hk]. destruct norl_fl2 as [N5 N6]. destruct obj10_fl2 as (O10 & Lo & Hi & Wr & Ar & CB & BL).
  pose proof (smatch_xforms segs xs_fl2 rho E_fl2 E_fl21 _ xs_fl2_ok Hsm) as H1.
  pose proof (smatch_unbase segs rho E_fl21 1 (-64) E_fl22 _ unb_fl2 H1) as H2.
  pose proof (smatch_obj_to_list segs rho E_fl22 _ 12 5 _ stdout_buf (stdout_buf + 2) BL_fl2 H2 O10 Lo Hi ltac:(unfold stdout_buf; lia) ltac:(unfold stdout_buf; lia) Wr Ar CB N5) as H3.
  rewrite E_fl23_eq, BL in H3.
  set (rho' := rho_set_rl (rho_set_rl rho 5 (zeros 1)) 6 (@nil byte)).
  assert (H3' : smatch segs rho' E_fl23 (tr, mkCfg ms md)) by (apply smatch_set_rl; [exact N6 | exact H3]).
  exists rho'. split; [split; reflexivity|]. split; [|exact Hk].
  rewrite <- E_fl2c_eq. unfold app_objs.
  apply (ReprGlue.smatch_carve_rom segs rho' E_fl23 _ 0 0 6 (ss_next E_fl23) H3').
  - exact swf_E_fl2c.
  - lia. - lia. - lia.
  - reflexivity.
  - intros k Hk0. exfalso. lia.
  - apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd]. lia.
Qed.

Lemma x2_fS_intro : ltac2:(tb__ "0|0|
S1S48S29OF_;F_;S1S30S25S0VJD;VKL1;R4S17S1aS6S6A2A1R3A4S76R2R1A5S10S1S1S24S0VKL1;S7aR1R3A5Lr;A2F_;Fw;Frho;FDf;Fr0';").
Proof using Hargc L P0 SIDEL TL.
  intros r0' Df rho [tr [ms md]] [Hsm (Ai & HJi & _)]. pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & _).
  destruct (statics_view_of_MInvR segs C_U Ai _ md HM) as [g Vg].
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U _ T_2f (tr, mkCfg ms md) g (ss_next T_2f) (Pos.succ (ss_next T_2f)) Hsm
              ltac:(lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts T_2f) [] (ss_objs T_2f) _ ltac:(intros t Ht; destruct Ht) (smatch_facts_hold segs _ _ _ Hsm) missT_T2f)
              ltac:(rewrite T_2fS_eq; exact swf_T_2fS)) as [Hsm' _].
  eexists. split; [rewrite <- T_2fS_eq; exact Hsm' | exact Hk].
Qed.

Lemma x2_exit_safe : ltac2:(tb__ "0|0|
S1S48S29OF_;F_;S1S32S0Vok;S25S0VJD;VKL1;R3S17S1aS6S6A2A1R2A4S76R1A4S30S11L_;A4Frho;FDf;Fr0';").
Proof using HC Hargc HokK HokP Hokh KL1_tcons P0 SIDEL TL normal_in_spec.
  intros r0' Df rho.
  apply (triple_from ok _ (fun r w => SP segs KL1 T_2fS r w)); [intros w Hw; exact (x2_fS_intro r0' Df rho w Hw)|].
  intros rho1. destruct T_2fS_shape as [NX1 LN1].
  eapply (run_tr ok); [exact run_T2f | exact LN1 | apply HokK, KL1_tcons |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  apply (triple_from ok _ (fun r w => (rl r 5 = bsf2 /\ rl r 6 = []) /\ SP segs KL1 E_fl2c r w)); [intros w Hw; exact (fl2_intro rho2 w Hw)|].
  intros rho3. apply triple_pure. intros [H5 H6].
  destruct s_fl2_vals as (S12 & S13 & S14 & S15). destruct E_fl2_facts as (Fc & F3 & Nc & N3 & N2 & NT).
  apply (call_path segs PRf2 ok KL1 (Kwf2 (length (WLout.MSG bsf2 []))) E_fl2c E_fl2c WLoutS.Pre_wl2 [] s_fl2 R_fl2 WLout.Posts_wl _ rho3 eq_refl efr_fl2 chk_fl2 ltac:(rewrite Fc; exact fb_fl2)).
  - apply wl2f2_call.
  - intros ms _. unfold PRf2. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. change (ss_next WLoutS.Pre_wl2) with 92%positive. rewrite T_fl2D_eq.
    destruct T_fl2E_eq as (TE & FbE & LnE & _).
    eapply triple_conseq with (P := SP segs (Kwf2 (length (WLout.MSG bsf2 []))) T_fl2E rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [|exact HK]. rewrite <- TE. apply smatch_add_facts; [exact Hsm | exact HF4 | exact FbE]. }
    eapply (run_tr ok); [exact run_fl2 | exact LnE | apply HokK, Kwf2_tcons |].
    intros Lf rho5 [<-|[]] Hag5. cbn [lf_state]. destruct cert_x2 as (Hi & H17 & H10).
    apply (triple_exit_eval segs ok SpecT (Kwf2 (length (WLout.MSG bsf2 []))) E_x2 rho5 0);
      [apply HokK, Kwf2_tcons | apply HokP, Kwf2_tcons | exact Hokh | exact Hi | left; exact H17 | rewrite H10; reflexivity |].
    intros tr md HK. destruct (Kwf2_trace _ tr md HK) as (-> & _ & ->).
    unfold WLout.MSG. rewrite app_nil_r, firstn_all. unfold TR1, Drv_hl.TR1. rewrite <- Drv_hl.wr_app, <- zeros2_eq. pose proof normal_in_spec as N. rewrite HC in N. exact N.
Qed.

Lemma x2_exit_ex : ltac2:(tb__ "0|0|
S1S48S29OF_;F_;S1S31S0S25S0VJD;VKL1;R3S17S1aS6S6A2A1R2A4S76R1A4S3cVcx;A1A3Frho;FDf;Fr0';").
Proof using HC SIDEL TL.
  intros r0' Df rho.
  apply (etriple_from _ (fun r w => SP segs KL1 T_2fS r w)); [intros w Hw; exact (x2_fS_intro r0' Df rho w Hw)|].
  intros rho1. destruct T_2fS_shape as [NX1 LN1].
  eapply erun_tr; [exact run_T2f | exact LN1 |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  apply (etriple_from _ (fun r w => (rl r 5 = bsf2 /\ rl r 6 = []) /\ SP segs KL1 E_fl2c r w)); [intros w Hw; exact (fl2_intro rho2 w Hw)|].
  intros rho3 w0 [[H5 H6] Hw0]. revert w0 Hw0.
  destruct s_fl2_vals as (S12 & S13 & S14 & S15). destruct E_fl2_facts as (Fc & F3 & Nc & N3 & N2 & NT).
  apply (ecall_path segs PRf2 KL1 (Kwf2 (length (WLout.MSG bsf2 []))) E_fl2c E_fl2c WLoutS.Pre_wl2 [] s_fl2 R_fl2 WLout.Posts_wl _ rho3 eq_refl efr_fl2 chk_fl2 ltac:(rewrite Fc; exact fb_fl2)).
  - apply wl2f2_ecall.
  - intros ms _. unfold PRf2. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. change (ss_next WLoutS.Pre_wl2) with 92%positive. rewrite T_fl2D_eq.
    destruct T_fl2E_eq as (TE & FbE & LnE & _).
    eapply etriple_conseq with (P := SP segs (Kwf2 (length (WLout.MSG bsf2 []))) T_fl2E rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [|exact HK]. rewrite <- TE. apply smatch_add_facts; [exact Hsm | exact HF4 | exact FbE]. }
    eapply erun_tr; [exact run_fl2 | exact LnE |].
    intros Lf rho5 [<-|[]] Hag5. cbn [lf_state]. destruct cert_x2 as (Hi & H17 & H10).
    eapply etriple_conseq; [intros w Hw; exact Hw | | apply (etriple_exit_eval segs (Kwf2 (length (WLout.MSG bsf2 []))) E_x2 rho5 0 Hi (or_introl H17))].
    + intros w (tr & md & HK & Hw). destruct (Kwf2_trace _ tr md HK) as (Htr & _ & Hfs). unfold Drv_hl.QN. rewrite Hw, Htr, Hfs.
      unfold WLout.MSG. rewrite app_nil_r, firstn_all. unfold TR1, Drv_hl.TR1. rewrite <- Drv_hl.wr_app, <- zeros2_eq, (HC : calls (f_F cx) = 2). reflexivity.
    + rewrite H10. reflexivity.
Qed.

Section Free2.
Hypothesis MCs : ltac2:(tb__ "0|0|
S58S0S35S5eA3").

Lemma x2_free_safe : ltac2:(tb__ "0|0|
S1S28S15S12Q40A1A1S3dR3R2R1A3S32S0Vok;S24S0VKs;VKL1;R3R2A3S73R4A4S30S11L_;A4F_;Fmat;Fvm;Frho;").
Proof using HC KL1_tcons MCs SIDEL TL normal_in_spec.
  intros rho vm mat HSn.
  eapply triple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho C_2m 0 (-128) C_2x w unb_C2 (SPJ_xforms segs _ [XRebase 0; XRebase 1; XMerge 0] rho C_2 C_2m w xs_C2_ok Hw)) | intros w Hw; exact Hw |].
  eapply triple_conseq with (P := SPJ segs (JD KL1 rho U.Drv_r__G1.Drv_r.tvK DTrue) C_2x rho); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 U.Drv_r__G1.Drv_r.tvK DTrue rho vm mat tr md HSn Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_ff2_vals as (F12 & F13 & F10 & F15). destruct C_2x_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_ff2 as (CHK & RCHK & NZ).
  apply (dfree_call segs C_U EC_U 31 KL1 rho P0 malloc_laws_U ok C_2x s_ff2 R_ff2 rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (mc_free _ _ _ MCs). apply okside_i.
  - exact efr_ff2.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf NZ). }
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_2x) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) robj_inwi R_ff2 _ rho md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho Ai _ o a Ho Hr).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_2f_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply x2_exit_safe.
Qed.
End Free2.

Section FreeX2.
Hypothesis FCX : free_contract_ex_U.

Lemma x2_free_ex : ltac2:(tb__ "0|0|
S1S28S15S12Q40A1A1S3dR3R2R1A3S31S0S24S0VKs;VKL1;R3R2A3S73R4A4S3cVcx;A1A3F_;Fmat;Fvm;Frho;").
Proof using FCX HC SIDEL TL.
  intros rho vm mat HSn.
  eapply etriple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho C_2m 0 (-128) C_2x w unb_C2 (SPJ_xforms segs _ [XRebase 0; XRebase 1; XMerge 0] rho C_2 C_2m w xs_C2_ok Hw)) | intros w Hw; exact Hw |].
  eapply etriple_conseq with (P := SPJ segs (JD KL1 rho U.Drv_r__G1.Drv_r.tvK DTrue) C_2x rho); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 U.Drv_r__G1.Drv_r.tvK DTrue rho vm mat tr md HSn Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_ff2_vals as (F12 & F13 & F10 & F15). destruct C_2x_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_ff2 as (CHK & RCHK & NZ).
  apply (dfree_call_ex segs C_U EC_U 31 KL1 rho P0 malloc_laws_U C_2x s_ff2 R_ff2 rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (FCX Ai). apply U.Drv_r__G1.Drv_r.Ki_vmi, KL1_vmi.
  - exact efr_ff2.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf NZ). }
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_2x) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) robj_inwi R_ff2 _ rho md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho Ai _ o a Ho Hr).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_2f_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply x2_exit_ex.
Qed.
End FreeX2.

Lemma x2_A_leaf : ltac2:(tb__ "0|5|
S2S2S2S2S2S54S1S22S28S15S12Q40A1A1S30SeS1eS2A1M0S95RbS87A2S1fS2RaA2M1A3SeG0S94RbU0Nd0A3G1A3SeS15S3A1M2S5RbA1S19S3S5RaA1S1dS3S4cS17S3A1A3A3A3SeS16SaRbA1S18A3SeS2RcS41RdS5RcA1M3A2A3SeG2S5RdA1M4S19S3G3S5bS35S4eA2A3A3SeS2RdS41ReG4A2A3SeS16S5aReS73RdA3S18A3SeS16S55ReP1fA2S18A3SeS16S57RfS33S33A3S18A3VSIDEL;S4eRfReRdRcA5SeS22S37VF;A1Z0A3S24S0VKs;VKL1;RfReA3R17R11RdA5S10S1S1SfS3dR1R11R10A3S24S0VKs;VKL1;R11R10A3S73R1RfA5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;Fs;Fn4;Fn3;Fn2;Fn1;Fn;").
Proof using TL.
  intros n n1 n2 n3 n4 s rho g vm mat [tr [ms md]] Hx Hu Ho2 Hwf3 Hn3 Ho3 Hn4 He Hid Htv (HSn & HG & HV & Hv & HT) HP0 [Hsm Hk].
  pose proof (smatch_unbase segs rho n1 0 (-208) n2 _ Hu (smatch_xforms segs xs_xa rho n n1 _ Hx Hsm)) as H2.
  assert (H3 : smatch segs rho n3 (tr, mkCfg ms md)).
  { rewrite Hn3. apply (smatch_drop_nil rho n2 _ (ss_objs n3) O_payL H2 Ho2 (pay_empty rho HT HP0)). rewrite <- Hn3. exact Hwf3. }
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho n3 (tr, mkCfg ms md) (ss_objs n4) g NX1 H3 Ho3 HV Hv) as (m' & H4 & Hout & RD & WK & _).
  rewrite <- Hn4 in H4.
  pose proof (entails_sound segs _ _ s _ _ He H4) as H5.
  exists (rho_sub (set_rm rho m') s). split; [|split; [exact H5 | exact Hk]].
  destruct (tvK_sub s (set_rm rho m') Htv) as [R101 R102].
  apply (SIDEK_transport rho); [exact (snapJ_tail _ _ _ _ _ _ HSn) | | exact R101 | exact R102 | | |].
  - intros i Hi. cbn [rho_sub rw]. rewrite (wsub_get_id s 31 i Hid ltac:(lia)). reflexivity.
  - intros a. cbn [rho_sub set_rm rm]. apply RD.
  - intros a. cbn [rho_sub set_rm rm]. apply WK.
  - intros a Ha. cbn [rho_sub set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Lemma x2_B2_intro : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1S30VSIDEL;S4eR5R4R3R2A5S42Z0S37VF;A1A2S24S0VKs;VKL1;R5R4A3S51R7R3A5S10S1S1SfSfVTL;R1A1S60S0S35VP0;Vwtop;S4dS40R1R7R6A9A2S24S0VKs;VKL1;R7R6A3S7bR1R5A5A2Lrho';A2F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;").
Proof using Hargc JD L P0_transport cap.
  intros rho g vm mat [tr [ms md]] (HSn & HG & HV & Hv & HT) HP [Hsm Hk].
  destruct X_2_objs as (OX & O2 & LnX & R10 & PcX).
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho X_2 (tr, mkCfg ms md) (firstn 13 (ss_objs X_2)) g NX1 Hsm OX HV Hv) as (m' & H1 & Hout & RD & WK & _).
  rewrite XB2r_eq in H1. set (rho' := set_rm rho m') in *.
  destruct XB20_eq as (RE & O2r & WF & NXr).
  pose proof HT as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  assert (H2 : smatch segs rho' XB20 (tr, mkCfg ms md)).
  { rewrite <- RE.
    apply (proj1 (SPJ_reshape segs (liftK (fun _ _ => True)) rho' XB2r 2 _ O_payB (tr, mkCfg ms md) O2r eq_refl eq_refl eq_refl WF
                              ltac:(intros _; unfold obj_lo_of, obj_hi_of, O_payB, O_payL; cbn [ob_base ob_lo ob_hi eval rho' set_rm rw]; rewrite E240; split; reflexivity)
                              (conj H1 I))). }
  pose proof (smatch_unbase segs rho' XB21 0 (-208) XB22 _ unb_fo2 (smatch_xforms segs xs_fo rho' XB20 XB21 _ xs_fo2_ok H2)) as H3.
  exists rho'. split; [split|split; [exact H3 | exact Hk]].
  - apply (Drv_hl.TL_rw cx cap rho rho'); [intros i _; reflexivity | exact HT].
  - apply (snapJ_transport segs C_U P0 malloc_laws_U wtop tvL DTrue rho rho' vm mat HSn).
    + apply (Drv_hl.tv_eval_eq_L); reflexivity.
    + exact RD.
    + exact WK.
    + destruct HSn as (Ai & md' & _ & _ & _ & HP0 & _). apply (P0_transport rho rho' HP0); [intros i _; reflexivity|].
      intros a Ha. cbn [rho' set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Definition SIDEB2 (rho : valuation) (g : Z) (vm : VmMaps) (mat : list word) : Prop := ltac2:(tb__ "0|1|
SfS3dVrho;Vvm;Vmat;A3SfS5cS0S35S9Vrho;A1Vg;A4SeS12Q40M0A1S7Vrho;S4S74A1A2S14G0Vg;A2A3A2A2").

Lemma SIDEB2_agree : ltac2:(tb__ "0|0|
S23S1S1S22S28S15S12Q40A1A1S63R5R3R2R1A4SbR7R6R5A3S3eS4S74A1R8A2S63R7R6R5R4A4F_;F_;F_;Fmat;Fvm;Fg;Frho';Frho;Fn;").
Proof using SIDEL TL.
  intros n rho rho' g vm mat (HS & HV & Hv) (Hw & _ & Hm) Hn. pose proof LT2 as (_ & _ & L102 & _).
  assert (Hm' : forall a, rm rho' a = rm rho a) by (intros a; symmetry; apply Hm).
  split; [|split].
  - apply (SIDEK_transport rho rho' vm mat HS).
    + intros i Hi. symmetry. apply Hw. lia.
    + symmetry. apply Hw. lia.
    + symmetry. apply Hw. lia.
    + intros a. unfold rd_of. rewrite Hm'. reflexivity.
    + intros a. unfold wok_of. rewrite Hm'. reflexivity.
    + intros a _. apply Hm'.
  - apply (statics_view_rm segs C_U statics_layout_U (rm rho) (rm rho') g); [intros a _; apply Hm' | exact HV].
  - rewrite <- Hw by lia. exact Hv.
Qed.

Lemma x2_BS_intro : ltac2:(tb__ "0|1|
S1S1S30S25S0VJD;VKL1;R3S33S40A4S75R2R1A5S10S1S1S10S22S22S10S28S28S10S15S12Q40A1A1M0G0SfS63R4R3R2R1A4S24S0VKs;VKL1;R2R1A3S79R4R6A5A2Lmat;A2Lvm;A2Lg;A2Lrho1;A2F_;Fw;Frho;Fr0;").
Proof using SIDEL TL.
  intros r0 rho [tr [ms md]] [Hsm (Ai & HJi & _)]. destruct ent_T2Bt as [He NxBt]. pose proof LT2 as (_ & _ & L102 & _).
  pose proof (entails_sound segs _ _ [] _ _ He Hsm) as Hsm1. set (rho0 := rho_sub rho []) in Hsm1.
  assert (HJi0 : JGi segs C_U 31 KL1 r0 P0 [] U.Drv_r__G1.Drv_r.tvK Ai rho0 tr md).
  { apply (JGi_stable segs C_U 31 KL1 r0 P0 [] malloc_laws_U 104 U.Drv_r__G1.Drv_r.tvK Ai rho rho0 tr md ltac:(lia) (U.Drv_r__G1.Drv_r.tvK_below cx 104 ltac:(lia))); [|exact HJi].
    split; [intros i _; reflexivity|]. split; [intros l; reflexivity | intros a; reflexivity]. }
  pose proof HJi0 as (Hav & Hk & [HM [Hi HTPI]] & HP & HN & HKF & HP0').
  pose proof (U.Drv_hs__G1.Drv_hs.P0_now cx _ _ _ _ _ _ _ HJi0) as HP0.
  pose proof (tv_geo_of_JGi segs C_U 31 KL1 r0 P0 U.Drv_r__G1.Drv_r.tvK Ai rho0 tr md HJi0) as HG.
  destruct (statics_view_of_MInvR segs C_U Ai rho0 md HM) as [g Vg].
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U rho0 T_2Bt (tr, mkCfg ms md) g (ss_next T_2Bt) (Pos.succ (ss_next T_2Bt)) Hsm1
              ltac:(lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts T_2Bt) U.Drv_r__G1.Drv_r.tvK (ss_objs T_2Bt) rho0 HG (smatch_facts_hold segs _ _ _ Hsm1) missT_T2B)
              ltac:(rewrite T_2BS_eq; exact swf_T_2BS)) as [Hsm' Hag].
  set (rho1 := rho_set_rw rho0 (ss_next T_2Bt) (Z_to_bv 64 g)) in *.
  assert (RW : forall i, i <> ss_next T_2Bt -> rw rho1 i = rw rho0 i) by (intros i Hi'; subst rho1; apply rho_set_rw_other; exact Hi').
  exists rho1, g, (m_vmmaps md), (m_vm_materialized md). split; [|split; [rewrite <- T_2BS_eq; exact Hsm' | apply (Drv_hl.Ks_intro); exact Hk]].
  destruct (deJ segs C_U 31 P0 wtop P0_top KL1 r0 U.Drv_r__G1.Drv_r.tvK DTrue Ai rho0 tr md HJi0 I HP0) as [HSn _].
  split; [|split; [exact Vg | subst rho1; apply rho_set_rw_at]].
  apply (SIDEK_transport rho0 rho1 _ _ HSn).
  - intros i Hi'. apply RW. lia.
  - apply RW. lia.
  - apply RW. lia.
  - intros a; reflexivity.
  - intros a; reflexivity.
  - intros a _; reflexivity.
Qed.

Lemma x2_B_leaf : ltac2:(tb__ "0|1|
S2S2S54S1S22S28S15S12Q40A1A1S30SeS15S3A1S5R8A1M0S19S3S5R7A1S5bS35S4S74A1A2A3A3SeS2R8S41R9G0A2A3SeS16S5aR9S73R8A3S18A3SeS16S55R9P1fA2S18A3SeS16S57RaS33S33A3S18A3S63RaR9R8R7A4S24S0VKs;VKL1;R9R8A3ReRbR7A5S10S1S1SfS3dR1RbRaA3S24S0VKs;VKL1;RbRaA3S73R1R9A5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;Fs;Fn4;Fn;").
Proof using SIDEL TL.
  intros n n4 s rho g vm mat [tr [ms md]] Ho Hn4 He Hid Htv (HSn & HV & Hv) [Hsm Hk].
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho n (tr, mkCfg ms md) (ss_objs n4) g (ss_next T_2Bt) Hsm Ho HV Hv) as (m' & H4 & Hout & RD & WK & _).
  rewrite <- Hn4 in H4.
  pose proof (entails_sound segs _ _ s _ _ He H4) as H5.
  exists (rho_sub (set_rm rho m') s). split; [|split; [exact H5 | exact Hk]].
  destruct (tvK_sub s (set_rm rho m') Htv) as [R101 R102].
  apply (SIDEK_transport rho); [exact HSn | | exact R101 | exact R102 | | |].
  - intros i Hi. cbn [rho_sub rw]. rewrite (wsub_get_id s 31 i Hid ltac:(lia)). reflexivity.
  - intros a. cbn [rho_sub set_rm rm]. apply RD.
  - intros a. cbn [rho_sub set_rm rm]. apply WK.
  - intros a Ha. cbn [rho_sub set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Section Safe2.
Hypothesis MCs : ltac2:(tb__ "0|0|
S58S0S35S5eA3").

Lemma x2_A_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4eR4R3R2R1A5SeS22S37VF;A1Z0A3S32S0Vok;S24S0VKs;VKL1;R4R3A3S51R6A4S30S11L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS HP0. pose proof HS as (HSn & HG & HV & Hv & HT). pose proof HT as [_ [_ P2]]. pose proof (P2 HP0) as Z241.
  pose proof LT2 as (L1 & L2 & _). destruct diff_XA20 as (Hd & Hwf & Hln & Hnx).
  apply (triple_restate segs ok _ rho X_2 XA20 _ _ Hwf Hd).
  { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite Z241. reflexivity. }
  eapply (run_tr ok); [exact run_XA20 | exact Hln | apply Ks_okf, KL1_tcons |].
  rewrite Hnx. destruct ent_C2 as (E1 & E2 & _ & _). destruct ent_C2_props as (I1 & I2 & _ & _ & T1 & T2 & _ & _).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (Drv_hl.SIDEL_agree cx cap NX1 _ rho rho2 g vm mat HS Hag2 L1 L2) as HS2.
  - destruct XA2a_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_2 r w)); [intros w Hw; exact (x2_A_leaf XA2a XA2a1 XA2a2 XA2a3 XA2a4 s_CAa2 rho2 g vm mat w xs_XA2a_ok unb_XA2a O2 W3 N3 O3 N4 E1 I1 T1 HS2 HP0 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x2_free_safe MCs rho3 vm mat HS3).
  - destruct XA2b_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_2 r w)); [intros w Hw; exact (x2_A_leaf XA2b XA2b1 XA2b2 XA2b3 XA2b4 s_CAb2 rho2 g vm mat w xs_XA2b_ok unb_XA2b O2 W3 N3 O3 N4 E2 I2 T2 HS2 HP0 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x2_free_safe MCs rho3 vm mat HS3).
Qed.

Lemma x2_Bt_safe : ltac2:(tb__ "0|0|
S1S1S32S0Vok;S25S0VJD;VKL1;R2S33S40A4S75R1A4S30S11L_;A4Frho;Fr0;").
Proof using HC Hargc HokK HokP Hokh KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport SIDEL TL normal_in_spec.
  intros r0 rho. pose proof LT2 as (_ & _ & _ & L4).
  apply (triple_from ok _ (fun r w => exists g vm mat, SIDEB2 r g vm mat /\ SP segs (Ks KL1 vm mat) T_2BS r w)).
  { intros w Hw. destruct (x2_BS_intro r0 rho w Hw) as (rho1 & g & vm & mat & HS & HP'). exists rho1, g, vm, mat. split; assumption. }
  intros rho1. apply triple_ex. intros g. apply triple_ex. intros vm. apply triple_ex. intros mat. apply triple_pure. intros HS1.
  destruct T_2BS_shape as [NxS LnS].
  eapply (run_tr ok); [exact run_T2B | exact LnS | apply Ks_okf, KL1_tcons |].
  rewrite NxS. destruct ent_C2 as (_ & _ & E3 & E4). destruct ent_C2_props as (_ & _ & I3 & I4 & _ & _ & T3 & T4).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (SIDEB2_agree _ rho1 rho2 g vm mat HS1 Hag2 L4) as HS2.
  - destruct XB2a_sets as (O4 & _ & N4).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_2 r w)); [intros w Hw; exact (x2_B_leaf XB2a XB2a4 s_CBa2 rho2 g vm mat w O4 N4 E3 I3 T3 HS2 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x2_free_safe MCs rho3 vm mat HS3).
  - destruct XB2b_sets as (O4 & _ & N4).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_2 r w)); [intros w Hw; exact (x2_B_leaf XB2b XB2b4 s_CBb2 rho2 g vm mat w O4 N4 E4 I4 T4 HS2 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x2_free_safe MCs rho3 vm mat HS3).
Qed.

Lemma x2_B_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4eR4R3R2R1A5S42Z0S37VF;A1A2S32S0Vok;S24S0VKs;VKL1;R4R3A3S51R6A4S30S11L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS HP.
  apply (triple_from ok _ (fun r w => (TL r /\ snapJ segs C_U P0 wtop tvL DTrue r vm mat) /\ SP segs (Ks KL1 vm mat) XB22 r w)); [intros w Hw; exact (x2_B2_intro rho g vm mat w HS HP Hw)|].
  intros rho1. apply triple_pure. intros [HT1 HSn1].
  eapply triple_conseq with (P := SPJ segs (JD KL1 rho1 tvL DTrue) XB22 rho1); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 tvL DTrue rho1 vm mat tr md HSn1 Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_fb2_vals as (F12 & F13 & F10 & F15). destruct XB22_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_fb2 as [CHK RCHK].
  pose proof HT1 as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  apply (dfree_call segs C_U EC_U 31 KL1 rho1 P0 malloc_laws_U ok XB22 s_fb2 R_fb2 rho1 tvL 0%nat (SVar 241, SVar 158) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho2. apply (mc_free _ _ _ MCs). apply okside_i.
  - exact efr_fb2.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (Drv_hl.tvL_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP' & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho1 (SVar 241, SVar 158)) by (unfold tnz; cbn [fst eval]; exact NZ241).
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho1 (ss_facts XB22) tvL (Some 0%nat) robj_inwi R_fb2 _ rho1 md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho1 Ai _ o a Ho Hr).
      * exists (SVar 241, SVar 158). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_2B_eq. change (remove_nth 0 tvL) with U.Drv_r__G1.Drv_r.tvK. apply x2_Bt_safe.
Qed.

Theorem x2_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4eR4R3R2R1A5S32S0Vok;S24S0VKs;VKL1;R3R2A3S51R5A4S30S11L_;A4F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS. pose proof (Drv_hl.plen_range cx HL6 HLM) as PR.
  destruct (Z.eq_dec (payload_len F) 0) as [Z0|NZ]; [exact (x2_A_safe rho g vm mat HS Z0) | apply (x2_B_safe rho g vm mat HS ltac:(unfold F in *; lia))].
Qed.
End Safe2.

Section Ex2.
Hypothesis FCX : free_contract_ex_U.

Lemma x2_A_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4eR4R3R2R1A5SeS22S37VF;A1Z0A3S31S0S24S0VKs;VKL1;R4R3A3S51R6A4S3cVcx;A1A3F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC TL.
  intros rho g vm mat HS HP0. pose proof HS as (HSn & HG & HV & Hv & HT). pose proof HT as [_ [_ P2]]. pose proof (P2 HP0) as Z241.
  pose proof LT2 as (L1 & L2 & _). destruct diff_XA20 as (Hd & Hwf & Hln & Hnx).
  apply (etriple_restate segs _ rho X_2 XA20 _ _ Hwf Hd).
  { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite Z241. reflexivity. }
  eapply erun_tr; [exact run_XA20 | exact Hln |].
  rewrite Hnx. destruct ent_C2 as (E1 & E2 & _ & _). destruct ent_C2_props as (I1 & I2 & _ & _ & T1 & T2 & _ & _).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (Drv_hl.SIDEL_agree cx cap NX1 _ rho rho2 g vm mat HS Hag2 L1 L2) as HS2.
  - destruct XA2a_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_2 r w)); [intros w Hw; exact (x2_A_leaf XA2a XA2a1 XA2a2 XA2a3 XA2a4 s_CAa2 rho2 g vm mat w xs_XA2a_ok unb_XA2a O2 W3 N3 O3 N4 E1 I1 T1 HS2 HP0 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x2_free_ex FCX rho3 vm mat HS3 w0 Hw0).
  - destruct XA2b_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_2 r w)); [intros w Hw; exact (x2_A_leaf XA2b XA2b1 XA2b2 XA2b3 XA2b4 s_CAb2 rho2 g vm mat w xs_XA2b_ok unb_XA2b O2 W3 N3 O3 N4 E2 I2 T2 HS2 HP0 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x2_free_ex FCX rho3 vm mat HS3 w0 Hw0).
Qed.

Lemma x2_Bt_ex : ltac2:(tb__ "0|0|
S1S1S31S0S25S0VJD;VKL1;R2S33S40A4S75R1A4S3cVcx;A1A3Frho;Fr0;").
Proof using FCX HC SIDEL TL.
  intros r0 rho. pose proof LT2 as (_ & _ & _ & L4).
  apply (etriple_from _ (fun r w => exists g vm mat, SIDEB2 r g vm mat /\ SP segs (Ks KL1 vm mat) T_2BS r w)).
  { intros w Hw. destruct (x2_BS_intro r0 rho w Hw) as (rho1 & g & vm & mat & HS & HP'). exists rho1, g, vm, mat. split; assumption. }
  intros rho1. apply etriple_ex. intros g. apply etriple_ex. intros vm. apply etriple_ex. intros mat. apply etriple_pure. intros HS1.
  destruct T_2BS_shape as [NxS LnS].
  eapply erun_tr; [exact run_T2B | exact LnS |].
  rewrite NxS. destruct ent_C2 as (_ & _ & E3 & E4). destruct ent_C2_props as (_ & _ & I3 & I4 & _ & _ & T3 & T4).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (SIDEB2_agree _ rho1 rho2 g vm mat HS1 Hag2 L4) as HS2.
  - destruct XB2a_sets as (O4 & _ & N4).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_2 r w)); [intros w Hw; exact (x2_B_leaf XB2a XB2a4 s_CBa2 rho2 g vm mat w O4 N4 E3 I3 T3 HS2 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x2_free_ex FCX rho3 vm mat HS3 w0 Hw0).
  - destruct XB2b_sets as (O4 & _ & N4).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_2 r w)); [intros w Hw; exact (x2_B_leaf XB2b XB2b4 s_CBb2 rho2 g vm mat w O4 N4 E4 I4 T4 HS2 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x2_free_ex FCX rho3 vm mat HS3 w0 Hw0).
Qed.

Lemma x2_B_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4eR4R3R2R1A5S42Z0S37VF;A1A2S31S0S24S0VKs;VKL1;R4R3A3S51R6A4S3cVcx;A1A3F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC TL.
  intros rho g vm mat HS HP.
  apply (etriple_from _ (fun r w => (TL r /\ snapJ segs C_U P0 wtop tvL DTrue r vm mat) /\ SP segs (Ks KL1 vm mat) XB22 r w)); [intros w Hw; exact (x2_B2_intro rho g vm mat w HS HP Hw)|].
  intros rho1 w0 [[HT1 HSn1] Hw0]. revert w0 Hw0.
  eapply etriple_conseq with (P := SPJ segs (JD KL1 rho1 tvL DTrue) XB22 rho1); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 tvL DTrue rho1 vm mat tr md HSn1 Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_fb2_vals as (F12 & F13 & F10 & F15). destruct XB22_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_fb2 as [CHK RCHK].
  pose proof HT1 as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  apply (dfree_call_ex segs C_U EC_U 31 KL1 rho1 P0 malloc_laws_U XB22 s_fb2 R_fb2 rho1 tvL 0%nat (SVar 241, SVar 158) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho2. apply (FCX Ai). apply U.Drv_r__G1.Drv_r.Ki_vmi, KL1_vmi.
  - exact efr_fb2.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (Drv_hl.tvL_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP' & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho1 (SVar 241, SVar 158)) by (unfold tnz; cbn [fst eval]; exact NZ241).
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho1 (ss_facts XB22) tvL (Some 0%nat) robj_inwi R_fb2 _ rho1 md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho1 Ai _ o a Ho Hr).
      * exists (SVar 241, SVar 158). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_2B_eq. change (remove_nth 0 tvL) with U.Drv_r__G1.Drv_r.tvK. apply x2_Bt_ex.
Qed.

Theorem x2_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4eR4R3R2R1A5S31S0S24S0VKs;VKL1;R3R2A3S51R5A4S3cVcx;A1A3F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC HL6 HLM TL.
  intros rho g vm mat HS. pose proof (Drv_hl.plen_range cx HL6 HLM) as PR.
  destruct (Z.eq_dec (payload_len F) 0) as [Z0|NZ]; [exact (x2_A_ex rho g vm mat HS Z0) | apply (x2_B_ex rho g vm mat HS ltac:(unfold F in *; lia))].
Qed.
End Ex2.

End X2.

Section X3.
Hypothesis HC : calls F = 3.

Lemma LT3 : ltac2:(tb__ "0|1|
SfS3eS4fS4S52A1A2SfS3ePf1S4fA2SfS3eP66S4S7dA1M0A2S3eG0S3fG0A1A2A2A2A2").
Proof using .
  split; [apply Pos.ltb_lt; reflexivity|]. split; [apply Pos.ltb_lt; reflexivity|]. split; [apply Pos.ltb_lt; reflexivity | apply Pos.lt_succ_diag_r].
Qed.

Definition bsf3 : list byte := zeros 2.
Definition PRf3 (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
SfSeS15S12Q8A1M0A1M1S8Vrho1;P5A2S65A3SfSeG1S8Vrho1;P6A2S17G0A1A3SfSeS22S13Q40M2S7Vrho1;PdA2A2Z4A3SeS22S13G2S7Vrho1;PfA2A2Z0A3A2A2A2").
Definition Kwf3 (k : nat) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S91VKL1;S65S17S12Q8A1A1Vk;A4").

Lemma bsf3_len : length bsf3 = 4%nat. Proof using . reflexivity. Qed.
Lemma zeros3_eq : ltac2:(tb__ "0|1|
SeS15S12Q8A1M0A1S38Z3A1S19G0S39S65A3A3"). Proof using . reflexivity. Qed.
Lemma Kwf3_trace : ltac2:(tb__ "0|1|
S1cS15S2aA1M0S29S66R3R2R1A3SfSeG0R3S19S2aVTR1;S3aZ1S97S12Q8A1R4S65A3A2A3A3SfSeS15S1aS12Q40A1S2bA2A1S2cR2A1S99A3SeS98S2dR2A1Vfs;A3A2A2F_;Fmd;Ftr;Fk;").
Proof using .
  intros k tr md (tr0 & (-> & Hf & Hs) & ->). split; [|auto]. unfold WLout.TRk, WLout.MSG, wr. rewrite app_nil_r. reflexivity.
Qed.
Lemma Kwf3_tcons : ltac2:(tb__ "0|0|
S1cS93VSpecT;S66R1A1A2Fk;").
Proof using HC normal_in_spec.
  intros k tr md HK. destruct (Kwf3_trace k tr md HK) as (-> & _ & _). exists (wr 1 (zeros (calls F)) ++ [ex fs 0]). split; [exact normal_in_spec|].
  rewrite HC, zeros3_eq. unfold TR1, Drv_hl.TR1. rewrite <- (firstn_skipn k bsf3) at 2. rewrite !Drv_hl.wr_app, <- !app_assoc.
  rewrite (app_assoc (wr 1 msg_zero) (wr 1 (firstn k bsf3))). apply is_prefix_app.
Qed.
Lemma wl2f3_call : ltac2:(tb__ "0|1|
S1S68R1A1S32S0Vok;S24S0VKL1;S49R2A4S26S0S66S1bS12Q8A1M0S8fS65S17G0A1A2A2A1S4S49A1R2S90A5A4F_;Frho1;").
Proof using HC SIDEL TL normal_in_spec.
  intros rho1 (H5 & H6 & H13 & H15).
  apply (WLout.wl2_sum ok KL1 rho1 bsf3 [] H5 H6 ltac:(rewrite H13, bsf3_len; reflexivity) ltac:(rewrite H15; reflexivity)).
  - unfold WLout.MSG, max_write_total. rewrite app_nil_r, bsf3_len. cbn. lia.
  - intros k. apply HokK, Kwf3_tcons.
  - intros k. apply HokP, Kwf3_tcons.
  - apply KL1_fd1.
  - rewrite bsf3_len. cbn. lia.
Qed.
Lemma wl2f3_ecall : ltac2:(tb__ "0|1|
S1S68R1A1S31S0S24S0VKL1;S49R2A4S26S0S66S1bS12Q8A1M0S8fS65S17G0A1A2A2A1S4S49A1R2S90A5A3F_;Frho1;").
Proof using SIDEL TL.
  intros rho1 (H5 & H6 & H13 & H15).
  apply (WLout.wl2_sum_ex KL1 rho1 bsf3 [] H5 H6 ltac:(rewrite H13, bsf3_len; reflexivity) ltac:(rewrite H15; reflexivity)).
  - unfold WLout.MSG, max_write_total. rewrite app_nil_r, bsf3_len. cbn. lia.
  - apply KL1_fd1.
  - rewrite bsf3_len. cbn. lia.
Qed.

Lemma fl3_intro : ltac2:(tb__ "0|2|
S1S30S24S0VKL1;S80R2R1A5S10S1S1SfSfSeS15S12Q8A1M0A1M1S8R1P5A2S65A3SeG1S8R1P6A2S17G0A1A3A2S24S0VKL1;S81R1R3A5A2Lrho';A2F_;Fw;Frho;").
Proof using Hargc JD L P0 SIDEL TL.
  intros rho [tr [ms md]] [Hsm Hk]. destruct norl_fl3 as [N5 N6]. destruct obj10_fl3 as (O10 & Lo & Hi & Wr & Ar & CB & BL).
  pose proof (smatch_xforms segs xs_fl3 rho E_fl3 E_fl31 _ xs_fl3_ok Hsm) as H1.
  pose proof (smatch_unbase segs rho E_fl31 1 (-64) E_fl32 _ unb_fl3 H1) as H2.
  pose proof (smatch_obj_to_list segs rho E_fl32 _ 12 5 _ stdout_buf (stdout_buf + 4) BL_fl3 H2 O10 Lo Hi ltac:(unfold stdout_buf; lia) ltac:(unfold stdout_buf; lia) Wr Ar CB N5) as H3.
  rewrite E_fl33_eq, BL in H3.
  set (rho' := rho_set_rl (rho_set_rl rho 5 (zeros 2)) 6 (@nil byte)).
  assert (H3' : smatch segs rho' E_fl33 (tr, mkCfg ms md)) by (apply smatch_set_rl; [exact N6 | exact H3]).
  exists rho'. split; [split; reflexivity|]. split; [|exact Hk].
  rewrite <- E_fl3c_eq. unfold app_objs.
  apply (ReprGlue.smatch_carve_rom segs rho' E_fl33 _ 0 0 6 (ss_next E_fl33) H3').
  - exact swf_E_fl3c.
  - lia. - lia. - lia.
  - reflexivity.
  - intros k Hk0. exfalso. lia.
  - apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd]. lia.
Qed.

Lemma x3_fS_intro : ltac2:(tb__ "0|0|
S1S48S29OF_;F_;S1S30S25S0VJD;VKL1;R4S17S1aS6S6A2A1R3A4S7fR2R1A5S10S1S1S24S0VKL1;S83R1R3A5Lr;A2F_;Fw;Frho;FDf;Fr0';").
Proof using Hargc L P0 SIDEL TL.
  intros r0' Df rho [tr [ms md]] [Hsm (Ai & HJi & _)]. pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & _).
  destruct (statics_view_of_MInvR segs C_U Ai _ md HM) as [g Vg].
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U _ T_3f (tr, mkCfg ms md) g (ss_next T_3f) (Pos.succ (ss_next T_3f)) Hsm
              ltac:(lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts T_3f) [] (ss_objs T_3f) _ ltac:(intros t Ht; destruct Ht) (smatch_facts_hold segs _ _ _ Hsm) missT_T3f)
              ltac:(rewrite T_3fS_eq; exact swf_T_3fS)) as [Hsm' _].
  eexists. split; [rewrite <- T_3fS_eq; exact Hsm' | exact Hk].
Qed.

Lemma x3_exit_safe : ltac2:(tb__ "0|0|
S1S48S29OF_;F_;S1S32S0Vok;S25S0VJD;VKL1;R3S17S1aS6S6A2A1R2A4S7fR1A4S30S11L_;A4Frho;FDf;Fr0';").
Proof using HC Hargc HokK HokP Hokh KL1_tcons P0 SIDEL TL normal_in_spec.
  intros r0' Df rho.
  apply (triple_from ok _ (fun r w => SP segs KL1 T_3fS r w)); [intros w Hw; exact (x3_fS_intro r0' Df rho w Hw)|].
  intros rho1. destruct T_3fS_shape as [NX1 LN1].
  eapply (run_tr ok); [exact run_T3f | exact LN1 | apply HokK, KL1_tcons |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  apply (triple_from ok _ (fun r w => (rl r 5 = bsf3 /\ rl r 6 = []) /\ SP segs KL1 E_fl3c r w)); [intros w Hw; exact (fl3_intro rho2 w Hw)|].
  intros rho3. apply triple_pure. intros [H5 H6].
  destruct s_fl3_vals as (S12 & S13 & S14 & S15). destruct E_fl3_facts as (Fc & F3 & Nc & N3 & N2 & NT).
  apply (call_path segs PRf3 ok KL1 (Kwf3 (length (WLout.MSG bsf3 []))) E_fl3c E_fl3c WLoutS.Pre_wl2 [] s_fl3 R_fl3 WLout.Posts_wl _ rho3 eq_refl efr_fl3 chk_fl3 ltac:(rewrite Fc; exact fb_fl3)).
  - apply wl2f3_call.
  - intros ms _. unfold PRf3. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. change (ss_next WLoutS.Pre_wl2) with 92%positive. rewrite T_fl3D_eq.
    destruct T_fl3E_eq as (TE & FbE & LnE & _).
    eapply triple_conseq with (P := SP segs (Kwf3 (length (WLout.MSG bsf3 []))) T_fl3E rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [|exact HK]. rewrite <- TE. apply smatch_add_facts; [exact Hsm | exact HF4 | exact FbE]. }
    eapply (run_tr ok); [exact run_fl3 | exact LnE | apply HokK, Kwf3_tcons |].
    intros Lf rho5 [<-|[]] Hag5. cbn [lf_state]. destruct cert_x3 as (Hi & H17 & H10).
    apply (triple_exit_eval segs ok SpecT (Kwf3 (length (WLout.MSG bsf3 []))) E_x3 rho5 0);
      [apply HokK, Kwf3_tcons | apply HokP, Kwf3_tcons | exact Hokh | exact Hi | left; exact H17 | rewrite H10; reflexivity |].
    intros tr md HK. destruct (Kwf3_trace _ tr md HK) as (-> & _ & ->).
    unfold WLout.MSG. rewrite app_nil_r, firstn_all. unfold TR1, Drv_hl.TR1. rewrite <- Drv_hl.wr_app, <- zeros3_eq. pose proof normal_in_spec as N. rewrite HC in N. exact N.
Qed.

Lemma x3_exit_ex : ltac2:(tb__ "0|0|
S1S48S29OF_;F_;S1S31S0S25S0VJD;VKL1;R3S17S1aS6S6A2A1R2A4S7fR1A4S3cVcx;A1A3Frho;FDf;Fr0';").
Proof using HC SIDEL TL.
  intros r0' Df rho.
  apply (etriple_from _ (fun r w => SP segs KL1 T_3fS r w)); [intros w Hw; exact (x3_fS_intro r0' Df rho w Hw)|].
  intros rho1. destruct T_3fS_shape as [NX1 LN1].
  eapply erun_tr; [exact run_T3f | exact LN1 |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  apply (etriple_from _ (fun r w => (rl r 5 = bsf3 /\ rl r 6 = []) /\ SP segs KL1 E_fl3c r w)); [intros w Hw; exact (fl3_intro rho2 w Hw)|].
  intros rho3 w0 [[H5 H6] Hw0]. revert w0 Hw0.
  destruct s_fl3_vals as (S12 & S13 & S14 & S15). destruct E_fl3_facts as (Fc & F3 & Nc & N3 & N2 & NT).
  apply (ecall_path segs PRf3 KL1 (Kwf3 (length (WLout.MSG bsf3 []))) E_fl3c E_fl3c WLoutS.Pre_wl2 [] s_fl3 R_fl3 WLout.Posts_wl _ rho3 eq_refl efr_fl3 chk_fl3 ltac:(rewrite Fc; exact fb_fl3)).
  - apply wl2f3_ecall.
  - intros ms _. unfold PRf3. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. change (ss_next WLoutS.Pre_wl2) with 92%positive. rewrite T_fl3D_eq.
    destruct T_fl3E_eq as (TE & FbE & LnE & _).
    eapply etriple_conseq with (P := SP segs (Kwf3 (length (WLout.MSG bsf3 []))) T_fl3E rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [|exact HK]. rewrite <- TE. apply smatch_add_facts; [exact Hsm | exact HF4 | exact FbE]. }
    eapply erun_tr; [exact run_fl3 | exact LnE |].
    intros Lf rho5 [<-|[]] Hag5. cbn [lf_state]. destruct cert_x3 as (Hi & H17 & H10).
    eapply etriple_conseq; [intros w Hw; exact Hw | | apply (etriple_exit_eval segs (Kwf3 (length (WLout.MSG bsf3 []))) E_x3 rho5 0 Hi (or_introl H17))].
    + intros w (tr & md & HK & Hw). destruct (Kwf3_trace _ tr md HK) as (Htr & _ & Hfs). unfold Drv_hl.QN. rewrite Hw, Htr, Hfs.
      unfold WLout.MSG. rewrite app_nil_r, firstn_all. unfold TR1, Drv_hl.TR1. rewrite <- Drv_hl.wr_app, <- zeros3_eq, (HC : calls (f_F cx) = 3). reflexivity.
    + rewrite H10. reflexivity.
Qed.

Section Free3.
Hypothesis MCs : ltac2:(tb__ "0|0|
S58S0S35S5eA3").

Lemma x3_free_safe : ltac2:(tb__ "0|0|
S1S28S15S12Q40A1A1S3dR3R2R1A3S32S0Vok;S24S0VKs;VKL1;R3R2A3S7cR4A4S30S11L_;A4F_;Fmat;Fvm;Frho;").
Proof using HC KL1_tcons MCs SIDEL TL normal_in_spec.
  intros rho vm mat HSn.
  eapply triple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho C_3m 0 (-128) C_3x w unb_C3 (SPJ_xforms segs _ [XRebase 0; XRebase 1; XMerge 0] rho C_3 C_3m w xs_C3_ok Hw)) | intros w Hw; exact Hw |].
  eapply triple_conseq with (P := SPJ segs (JD KL1 rho U.Drv_r__G1.Drv_r.tvK DTrue) C_3x rho); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 U.Drv_r__G1.Drv_r.tvK DTrue rho vm mat tr md HSn Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_ff3_vals as (F12 & F13 & F10 & F15). destruct C_3x_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_ff3 as (CHK & RCHK & NZ).
  apply (dfree_call segs C_U EC_U 31 KL1 rho P0 malloc_laws_U ok C_3x s_ff3 R_ff3 rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (mc_free _ _ _ MCs). apply okside_i.
  - exact efr_ff3.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf NZ). }
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_3x) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) robj_inwi R_ff3 _ rho md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho Ai _ o a Ho Hr).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_3f_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply x3_exit_safe.
Qed.
End Free3.

Section FreeX3.
Hypothesis FCX : free_contract_ex_U.

Lemma x3_free_ex : ltac2:(tb__ "0|0|
S1S28S15S12Q40A1A1S3dR3R2R1A3S31S0S24S0VKs;VKL1;R3R2A3S7cR4A4S3cVcx;A1A3F_;Fmat;Fvm;Frho;").
Proof using FCX HC SIDEL TL.
  intros rho vm mat HSn.
  eapply etriple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho C_3m 0 (-128) C_3x w unb_C3 (SPJ_xforms segs _ [XRebase 0; XRebase 1; XMerge 0] rho C_3 C_3m w xs_C3_ok Hw)) | intros w Hw; exact Hw |].
  eapply etriple_conseq with (P := SPJ segs (JD KL1 rho U.Drv_r__G1.Drv_r.tvK DTrue) C_3x rho); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 U.Drv_r__G1.Drv_r.tvK DTrue rho vm mat tr md HSn Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_ff3_vals as (F12 & F13 & F10 & F15). destruct C_3x_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_ff3 as (CHK & RCHK & NZ).
  apply (dfree_call_ex segs C_U EC_U 31 KL1 rho P0 malloc_laws_U C_3x s_ff3 R_ff3 rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (FCX Ai). apply U.Drv_r__G1.Drv_r.Ki_vmi, KL1_vmi.
  - exact efr_ff3.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf NZ). }
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_3x) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) robj_inwi R_ff3 _ rho md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho Ai _ o a Ho Hr).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_3f_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply x3_exit_ex.
Qed.
End FreeX3.

Lemma x3_A_leaf : ltac2:(tb__ "0|5|
S2S2S2S2S2S54S1S22S28S15S12Q40A1A1S30SeS1eS2A1M0S95RbS87A2S1fS2RaA2M1A3SeG0S94RbU0Nd0A3G1A3SeS15S3A1M2S5RbA1S19S3S5RaA1S1dS3S4cS17S3A1A3A3A3SeS16SaRbA1S18A3SeS2RcS41RdS5RcA1M3A2A3SeG2S5RdA1M4S19S3G3S5bS35S4fA2A3A3SeS2RdS41ReG4A2A3SeS16S5aReS7cRdA3S18A3SeS16S55ReP1fA2S18A3SeS16S57RfS33S33A3S18A3VSIDEL;S4fRfReRdRcA5SeS22S37VF;A1Z0A3S24S0VKs;VKL1;RfReA3R17R11RdA5S10S1S1SfS3dR1R11R10A3S24S0VKs;VKL1;R11R10A3S7cR1RfA5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;Fs;Fn4;Fn3;Fn2;Fn1;Fn;").
Proof using TL.
  intros n n1 n2 n3 n4 s rho g vm mat [tr [ms md]] Hx Hu Ho2 Hwf3 Hn3 Ho3 Hn4 He Hid Htv (HSn & HG & HV & Hv & HT) HP0 [Hsm Hk].
  pose proof (smatch_unbase segs rho n1 0 (-208) n2 _ Hu (smatch_xforms segs xs_xa rho n n1 _ Hx Hsm)) as H2.
  assert (H3 : smatch segs rho n3 (tr, mkCfg ms md)).
  { rewrite Hn3. apply (smatch_drop_nil rho n2 _ (ss_objs n3) O_payL H2 Ho2 (pay_empty rho HT HP0)). rewrite <- Hn3. exact Hwf3. }
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho n3 (tr, mkCfg ms md) (ss_objs n4) g NX2 H3 Ho3 HV Hv) as (m' & H4 & Hout & RD & WK & _).
  rewrite <- Hn4 in H4.
  pose proof (entails_sound segs _ _ s _ _ He H4) as H5.
  exists (rho_sub (set_rm rho m') s). split; [|split; [exact H5 | exact Hk]].
  destruct (tvK_sub s (set_rm rho m') Htv) as [R101 R102].
  apply (SIDEK_transport rho); [exact (snapJ_tail _ _ _ _ _ _ HSn) | | exact R101 | exact R102 | | |].
  - intros i Hi. cbn [rho_sub rw]. rewrite (wsub_get_id s 31 i Hid ltac:(lia)). reflexivity.
  - intros a. cbn [rho_sub set_rm rm]. apply RD.
  - intros a. cbn [rho_sub set_rm rm]. apply WK.
  - intros a Ha. cbn [rho_sub set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Lemma x3_B2_intro : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1S30VSIDEL;S4fR5R4R3R2A5S42Z0S37VF;A1A2S24S0VKs;VKL1;R5R4A3S52R7R3A5S10S1S1SfSfVTL;R1A1S60S0S35VP0;Vwtop;S4dS40R1R7R6A9A2S24S0VKs;VKL1;R7R6A3S84R1R5A5A2Lrho';A2F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;").
Proof using Hargc JD L P0_transport cap.
  intros rho g vm mat [tr [ms md]] (HSn & HG & HV & Hv & HT) HP [Hsm Hk].
  destruct X_3_objs as (OX & O2 & LnX & R10 & PcX).
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho X_3 (tr, mkCfg ms md) (firstn 13 (ss_objs X_3)) g NX2 Hsm OX HV Hv) as (m' & H1 & Hout & RD & WK & _).
  rewrite XB3r_eq in H1. set (rho' := set_rm rho m') in *.
  destruct XB30_eq as (RE & O2r & WF & NXr).
  pose proof HT as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  assert (H2 : smatch segs rho' XB30 (tr, mkCfg ms md)).
  { rewrite <- RE.
    apply (proj1 (SPJ_reshape segs (liftK (fun _ _ => True)) rho' XB3r 2 _ O_payB (tr, mkCfg ms md) O2r eq_refl eq_refl eq_refl WF
                              ltac:(intros _; unfold obj_lo_of, obj_hi_of, O_payB, O_payL; cbn [ob_base ob_lo ob_hi eval rho' set_rm rw]; rewrite E240; split; reflexivity)
                              (conj H1 I))). }
  pose proof (smatch_unbase segs rho' XB31 0 (-208) XB32 _ unb_fo3 (smatch_xforms segs xs_fo rho' XB30 XB31 _ xs_fo3_ok H2)) as H3.
  exists rho'. split; [split|split; [exact H3 | exact Hk]].
  - apply (Drv_hl.TL_rw cx cap rho rho'); [intros i _; reflexivity | exact HT].
  - apply (snapJ_transport segs C_U P0 malloc_laws_U wtop tvL DTrue rho rho' vm mat HSn).
    + apply (Drv_hl.tv_eval_eq_L); reflexivity.
    + exact RD.
    + exact WK.
    + destruct HSn as (Ai & md' & _ & _ & _ & HP0 & _). apply (P0_transport rho rho' HP0); [intros i _; reflexivity|].
      intros a Ha. cbn [rho' set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Definition SIDEB3 (rho : valuation) (g : Z) (vm : VmMaps) (mat : list word) : Prop := ltac2:(tb__ "0|1|
SfS3dVrho;Vvm;Vmat;A3SfS5cS0S35S9Vrho;A1Vg;A4SeS12Q40M0A1S7Vrho;S4S7dA1A2S14G0Vg;A2A3A2A2").

Lemma SIDEB3_agree : ltac2:(tb__ "0|0|
S23S1S1S22S28S15S12Q40A1A1S67R5R3R2R1A4SbR7R6R5A3S3eS4S7dA1R8A2S67R7R6R5R4A4F_;F_;F_;Fmat;Fvm;Fg;Frho';Frho;Fn;").
Proof using SIDEL TL.
  intros n rho rho' g vm mat (HS & HV & Hv) (Hw & _ & Hm) Hn. pose proof LT3 as (_ & _ & L102 & _).
  assert (Hm' : forall a, rm rho' a = rm rho a) by (intros a; symmetry; apply Hm).
  split; [|split].
  - apply (SIDEK_transport rho rho' vm mat HS).
    + intros i Hi. symmetry. apply Hw. lia.
    + symmetry. apply Hw. lia.
    + symmetry. apply Hw. lia.
    + intros a. unfold rd_of. rewrite Hm'. reflexivity.
    + intros a. unfold wok_of. rewrite Hm'. reflexivity.
    + intros a _. apply Hm'.
  - apply (statics_view_rm segs C_U statics_layout_U (rm rho) (rm rho') g); [intros a _; apply Hm' | exact HV].
  - rewrite <- Hw by lia. exact Hv.
Qed.

Lemma x3_BS_intro : ltac2:(tb__ "0|1|
S1S1S30S25S0VJD;VKL1;R3S33S40A4S7eR2R1A5S10S1S1S10S22S22S10S28S28S10S15S12Q40A1A1M0G0SfS67R4R3R2R1A4S24S0VKs;VKL1;R2R1A3S82R4R6A5A2Lmat;A2Lvm;A2Lg;A2Lrho1;A2F_;Fw;Frho;Fr0;").
Proof using SIDEL TL.
  intros r0 rho [tr [ms md]] [Hsm (Ai & HJi & _)]. destruct ent_T3Bt as [He NxBt]. pose proof LT3 as (_ & _ & L102 & _).
  pose proof (entails_sound segs _ _ [] _ _ He Hsm) as Hsm1. set (rho0 := rho_sub rho []) in Hsm1.
  assert (HJi0 : JGi segs C_U 31 KL1 r0 P0 [] U.Drv_r__G1.Drv_r.tvK Ai rho0 tr md).
  { apply (JGi_stable segs C_U 31 KL1 r0 P0 [] malloc_laws_U 104 U.Drv_r__G1.Drv_r.tvK Ai rho rho0 tr md ltac:(lia) (U.Drv_r__G1.Drv_r.tvK_below cx 104 ltac:(lia))); [|exact HJi].
    split; [intros i _; reflexivity|]. split; [intros l; reflexivity | intros a; reflexivity]. }
  pose proof HJi0 as (Hav & Hk & [HM [Hi HTPI]] & HP & HN & HKF & HP0').
  pose proof (U.Drv_hs__G1.Drv_hs.P0_now cx _ _ _ _ _ _ _ HJi0) as HP0.
  pose proof (tv_geo_of_JGi segs C_U 31 KL1 r0 P0 U.Drv_r__G1.Drv_r.tvK Ai rho0 tr md HJi0) as HG.
  destruct (statics_view_of_MInvR segs C_U Ai rho0 md HM) as [g Vg].
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U rho0 T_3Bt (tr, mkCfg ms md) g (ss_next T_3Bt) (Pos.succ (ss_next T_3Bt)) Hsm1
              ltac:(lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts T_3Bt) U.Drv_r__G1.Drv_r.tvK (ss_objs T_3Bt) rho0 HG (smatch_facts_hold segs _ _ _ Hsm1) missT_T3B)
              ltac:(rewrite T_3BS_eq; exact swf_T_3BS)) as [Hsm' Hag].
  set (rho1 := rho_set_rw rho0 (ss_next T_3Bt) (Z_to_bv 64 g)) in *.
  assert (RW : forall i, i <> ss_next T_3Bt -> rw rho1 i = rw rho0 i) by (intros i Hi'; subst rho1; apply rho_set_rw_other; exact Hi').
  exists rho1, g, (m_vmmaps md), (m_vm_materialized md). split; [|split; [rewrite <- T_3BS_eq; exact Hsm' | apply (Drv_hl.Ks_intro); exact Hk]].
  destruct (deJ segs C_U 31 P0 wtop P0_top KL1 r0 U.Drv_r__G1.Drv_r.tvK DTrue Ai rho0 tr md HJi0 I HP0) as [HSn _].
  split; [|split; [exact Vg | subst rho1; apply rho_set_rw_at]].
  apply (SIDEK_transport rho0 rho1 _ _ HSn).
  - intros i Hi'. apply RW. lia.
  - apply RW. lia.
  - apply RW. lia.
  - intros a; reflexivity.
  - intros a; reflexivity.
  - intros a _; reflexivity.
Qed.

Lemma x3_B_leaf : ltac2:(tb__ "0|1|
S2S2S54S1S22S28S15S12Q40A1A1S30SeS15S3A1S5R8A1M0S19S3S5R7A1S5bS35S4S7dA1A2A3A3SeS2R8S41R9G0A2A3SeS16S5aR9S7cR8A3S18A3SeS16S55R9P1fA2S18A3SeS16S57RaS33S33A3S18A3S67RaR9R8R7A4S24S0VKs;VKL1;R9R8A3ReRbR7A5S10S1S1SfS3dR1RbRaA3S24S0VKs;VKL1;RbRaA3S7cR1R9A5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;Fs;Fn4;Fn;").
Proof using SIDEL TL.
  intros n n4 s rho g vm mat [tr [ms md]] Ho Hn4 He Hid Htv (HSn & HV & Hv) [Hsm Hk].
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho n (tr, mkCfg ms md) (ss_objs n4) g (ss_next T_3Bt) Hsm Ho HV Hv) as (m' & H4 & Hout & RD & WK & _).
  rewrite <- Hn4 in H4.
  pose proof (entails_sound segs _ _ s _ _ He H4) as H5.
  exists (rho_sub (set_rm rho m') s). split; [|split; [exact H5 | exact Hk]].
  destruct (tvK_sub s (set_rm rho m') Htv) as [R101 R102].
  apply (SIDEK_transport rho); [exact HSn | | exact R101 | exact R102 | | |].
  - intros i Hi. cbn [rho_sub rw]. rewrite (wsub_get_id s 31 i Hid ltac:(lia)). reflexivity.
  - intros a. cbn [rho_sub set_rm rm]. apply RD.
  - intros a. cbn [rho_sub set_rm rm]. apply WK.
  - intros a Ha. cbn [rho_sub set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Section Safe3.
Hypothesis MCs : ltac2:(tb__ "0|0|
S58S0S35S5eA3").

Lemma x3_A_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4fR4R3R2R1A5SeS22S37VF;A1Z0A3S32S0Vok;S24S0VKs;VKL1;R4R3A3S52R6A4S30S11L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS HP0. pose proof HS as (HSn & HG & HV & Hv & HT). pose proof HT as [_ [_ P2]]. pose proof (P2 HP0) as Z241.
  pose proof LT3 as (L1 & L2 & _). destruct diff_XA30 as (Hd & Hwf & Hln & Hnx).
  apply (triple_restate segs ok _ rho X_3 XA30 _ _ Hwf Hd).
  { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite Z241. reflexivity. }
  eapply (run_tr ok); [exact run_XA30 | exact Hln | apply Ks_okf, KL1_tcons |].
  rewrite Hnx. destruct ent_C3 as (E1 & E2 & _ & _). destruct ent_C3_props as (I1 & I2 & _ & _ & T1 & T2 & _ & _).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (Drv_hl.SIDEL_agree cx cap NX2 _ rho rho2 g vm mat HS Hag2 L1 L2) as HS2.
  - destruct XA3a_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_3 r w)); [intros w Hw; exact (x3_A_leaf XA3a XA3a1 XA3a2 XA3a3 XA3a4 s_CAa3 rho2 g vm mat w xs_XA3a_ok unb_XA3a O2 W3 N3 O3 N4 E1 I1 T1 HS2 HP0 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x3_free_safe MCs rho3 vm mat HS3).
  - destruct XA3b_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_3 r w)); [intros w Hw; exact (x3_A_leaf XA3b XA3b1 XA3b2 XA3b3 XA3b4 s_CAb3 rho2 g vm mat w xs_XA3b_ok unb_XA3b O2 W3 N3 O3 N4 E2 I2 T2 HS2 HP0 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x3_free_safe MCs rho3 vm mat HS3).
Qed.

Lemma x3_Bt_safe : ltac2:(tb__ "0|0|
S1S1S32S0Vok;S25S0VJD;VKL1;R2S33S40A4S7eR1A4S30S11L_;A4Frho;Fr0;").
Proof using HC Hargc HokK HokP Hokh KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport SIDEL TL normal_in_spec.
  intros r0 rho. pose proof LT3 as (_ & _ & _ & L4).
  apply (triple_from ok _ (fun r w => exists g vm mat, SIDEB3 r g vm mat /\ SP segs (Ks KL1 vm mat) T_3BS r w)).
  { intros w Hw. destruct (x3_BS_intro r0 rho w Hw) as (rho1 & g & vm & mat & HS & HP'). exists rho1, g, vm, mat. split; assumption. }
  intros rho1. apply triple_ex. intros g. apply triple_ex. intros vm. apply triple_ex. intros mat. apply triple_pure. intros HS1.
  destruct T_3BS_shape as [NxS LnS].
  eapply (run_tr ok); [exact run_T3B | exact LnS | apply Ks_okf, KL1_tcons |].
  rewrite NxS. destruct ent_C3 as (_ & _ & E3 & E4). destruct ent_C3_props as (_ & _ & I3 & I4 & _ & _ & T3 & T4).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (SIDEB3_agree _ rho1 rho2 g vm mat HS1 Hag2 L4) as HS2.
  - destruct XB3a_sets as (O4 & _ & N4).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_3 r w)); [intros w Hw; exact (x3_B_leaf XB3a XB3a4 s_CBa3 rho2 g vm mat w O4 N4 E3 I3 T3 HS2 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x3_free_safe MCs rho3 vm mat HS3).
  - destruct XB3b_sets as (O4 & _ & N4).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_3 r w)); [intros w Hw; exact (x3_B_leaf XB3b XB3b4 s_CBb3 rho2 g vm mat w O4 N4 E4 I4 T4 HS2 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x3_free_safe MCs rho3 vm mat HS3).
Qed.

Lemma x3_B_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4fR4R3R2R1A5S42Z0S37VF;A1A2S32S0Vok;S24S0VKs;VKL1;R4R3A3S52R6A4S30S11L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS HP.
  apply (triple_from ok _ (fun r w => (TL r /\ snapJ segs C_U P0 wtop tvL DTrue r vm mat) /\ SP segs (Ks KL1 vm mat) XB32 r w)); [intros w Hw; exact (x3_B2_intro rho g vm mat w HS HP Hw)|].
  intros rho1. apply triple_pure. intros [HT1 HSn1].
  eapply triple_conseq with (P := SPJ segs (JD KL1 rho1 tvL DTrue) XB32 rho1); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 tvL DTrue rho1 vm mat tr md HSn1 Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_fb3_vals as (F12 & F13 & F10 & F15). destruct XB32_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_fb3 as [CHK RCHK].
  pose proof HT1 as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  apply (dfree_call segs C_U EC_U 31 KL1 rho1 P0 malloc_laws_U ok XB32 s_fb3 R_fb3 rho1 tvL 0%nat (SVar 241, SVar 158) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho2. apply (mc_free _ _ _ MCs). apply okside_i.
  - exact efr_fb3.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (Drv_hl.tvL_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP' & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho1 (SVar 241, SVar 158)) by (unfold tnz; cbn [fst eval]; exact NZ241).
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho1 (ss_facts XB32) tvL (Some 0%nat) robj_inwi R_fb3 _ rho1 md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho1 Ai _ o a Ho Hr).
      * exists (SVar 241, SVar 158). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_3B_eq. change (remove_nth 0 tvL) with U.Drv_r__G1.Drv_r.tvK. apply x3_Bt_safe.
Qed.

Theorem x3_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4fR4R3R2R1A5S32S0Vok;S24S0VKs;VKL1;R3R2A3S52R5A4S30S11L_;A4F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS. pose proof (Drv_hl.plen_range cx HL6 HLM) as PR.
  destruct (Z.eq_dec (payload_len F) 0) as [Z0|NZ]; [exact (x3_A_safe rho g vm mat HS Z0) | apply (x3_B_safe rho g vm mat HS ltac:(unfold F in *; lia))].
Qed.
End Safe3.

Section Ex3.
Hypothesis FCX : free_contract_ex_U.

Lemma x3_A_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4fR4R3R2R1A5SeS22S37VF;A1Z0A3S31S0S24S0VKs;VKL1;R4R3A3S52R6A4S3cVcx;A1A3F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC TL.
  intros rho g vm mat HS HP0. pose proof HS as (HSn & HG & HV & Hv & HT). pose proof HT as [_ [_ P2]]. pose proof (P2 HP0) as Z241.
  pose proof LT3 as (L1 & L2 & _). destruct diff_XA30 as (Hd & Hwf & Hln & Hnx).
  apply (etriple_restate segs _ rho X_3 XA30 _ _ Hwf Hd).
  { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite Z241. reflexivity. }
  eapply erun_tr; [exact run_XA30 | exact Hln |].
  rewrite Hnx. destruct ent_C3 as (E1 & E2 & _ & _). destruct ent_C3_props as (I1 & I2 & _ & _ & T1 & T2 & _ & _).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (Drv_hl.SIDEL_agree cx cap NX2 _ rho rho2 g vm mat HS Hag2 L1 L2) as HS2.
  - destruct XA3a_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_3 r w)); [intros w Hw; exact (x3_A_leaf XA3a XA3a1 XA3a2 XA3a3 XA3a4 s_CAa3 rho2 g vm mat w xs_XA3a_ok unb_XA3a O2 W3 N3 O3 N4 E1 I1 T1 HS2 HP0 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x3_free_ex FCX rho3 vm mat HS3 w0 Hw0).
  - destruct XA3b_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_3 r w)); [intros w Hw; exact (x3_A_leaf XA3b XA3b1 XA3b2 XA3b3 XA3b4 s_CAb3 rho2 g vm mat w xs_XA3b_ok unb_XA3b O2 W3 N3 O3 N4 E2 I2 T2 HS2 HP0 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x3_free_ex FCX rho3 vm mat HS3 w0 Hw0).
Qed.

Lemma x3_Bt_ex : ltac2:(tb__ "0|0|
S1S1S31S0S25S0VJD;VKL1;R2S33S40A4S7eR1A4S3cVcx;A1A3Frho;Fr0;").
Proof using FCX HC SIDEL TL.
  intros r0 rho. pose proof LT3 as (_ & _ & _ & L4).
  apply (etriple_from _ (fun r w => exists g vm mat, SIDEB3 r g vm mat /\ SP segs (Ks KL1 vm mat) T_3BS r w)).
  { intros w Hw. destruct (x3_BS_intro r0 rho w Hw) as (rho1 & g & vm & mat & HS & HP'). exists rho1, g, vm, mat. split; assumption. }
  intros rho1. apply etriple_ex. intros g. apply etriple_ex. intros vm. apply etriple_ex. intros mat. apply etriple_pure. intros HS1.
  destruct T_3BS_shape as [NxS LnS].
  eapply erun_tr; [exact run_T3B | exact LnS |].
  rewrite NxS. destruct ent_C3 as (_ & _ & E3 & E4). destruct ent_C3_props as (_ & _ & I3 & I4 & _ & _ & T3 & T4).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (SIDEB3_agree _ rho1 rho2 g vm mat HS1 Hag2 L4) as HS2.
  - destruct XB3a_sets as (O4 & _ & N4).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_3 r w)); [intros w Hw; exact (x3_B_leaf XB3a XB3a4 s_CBa3 rho2 g vm mat w O4 N4 E3 I3 T3 HS2 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x3_free_ex FCX rho3 vm mat HS3 w0 Hw0).
  - destruct XB3b_sets as (O4 & _ & N4).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_3 r w)); [intros w Hw; exact (x3_B_leaf XB3b XB3b4 s_CBb3 rho2 g vm mat w O4 N4 E4 I4 T4 HS2 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x3_free_ex FCX rho3 vm mat HS3 w0 Hw0).
Qed.

Lemma x3_B_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4fR4R3R2R1A5S42Z0S37VF;A1A2S31S0S24S0VKs;VKL1;R4R3A3S52R6A4S3cVcx;A1A3F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC TL.
  intros rho g vm mat HS HP.
  apply (etriple_from _ (fun r w => (TL r /\ snapJ segs C_U P0 wtop tvL DTrue r vm mat) /\ SP segs (Ks KL1 vm mat) XB32 r w)); [intros w Hw; exact (x3_B2_intro rho g vm mat w HS HP Hw)|].
  intros rho1 w0 [[HT1 HSn1] Hw0]. revert w0 Hw0.
  eapply etriple_conseq with (P := SPJ segs (JD KL1 rho1 tvL DTrue) XB32 rho1); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 tvL DTrue rho1 vm mat tr md HSn1 Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_fb3_vals as (F12 & F13 & F10 & F15). destruct XB32_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_fb3 as [CHK RCHK].
  pose proof HT1 as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  apply (dfree_call_ex segs C_U EC_U 31 KL1 rho1 P0 malloc_laws_U XB32 s_fb3 R_fb3 rho1 tvL 0%nat (SVar 241, SVar 158) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho2. apply (FCX Ai). apply U.Drv_r__G1.Drv_r.Ki_vmi, KL1_vmi.
  - exact efr_fb3.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (Drv_hl.tvL_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP' & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho1 (SVar 241, SVar 158)) by (unfold tnz; cbn [fst eval]; exact NZ241).
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho1 (ss_facts XB32) tvL (Some 0%nat) robj_inwi R_fb3 _ rho1 md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho1 Ai _ o a Ho Hr).
      * exists (SVar 241, SVar 158). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_3B_eq. change (remove_nth 0 tvL) with U.Drv_r__G1.Drv_r.tvK. apply x3_Bt_ex.
Qed.

Theorem x3_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S4fR4R3R2R1A5S31S0S24S0VKs;VKL1;R3R2A3S52R5A4S3cVcx;A1A3F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC HL6 HLM TL.
  intros rho g vm mat HS. pose proof (Drv_hl.plen_range cx HL6 HLM) as PR.
  destruct (Z.eq_dec (payload_len F) 0) as [Z0|NZ]; [exact (x3_A_ex rho g vm mat HS Z0) | apply (x3_B_ex rho g vm mat HS ltac:(unfold F in *; lia))].
Qed.
End Ex3.

End X3.

Section X4.
Hypothesis HC : calls F = 4.

Lemma LT4 : ltac2:(tb__ "0|1|
SfS3eS50S4S53A1A2SfS3ePf1S50A2SfS3eP66S4S86A1M0A2S3eG0S3fG0A1A2A2A2A2").
Proof using .
  split; [apply Pos.ltb_lt; reflexivity|]. split; [apply Pos.ltb_lt; reflexivity|]. split; [apply Pos.ltb_lt; reflexivity | apply Pos.lt_succ_diag_r].
Qed.

Definition bsf4 : list byte := zeros 3.
Definition PRf4 (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
SfSeS15S12Q8A1M0A1M1S8Vrho1;P5A2S69A3SfSeG1S8Vrho1;P6A2S17G0A1A3SfSeS22S13Q40M2S7Vrho1;PdA2A2Z6A3SeS22S13G2S7Vrho1;PfA2A2Z0A3A2A2A2").
Definition Kwf4 (k : nat) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S91VKL1;S69S17S12Q8A1A1Vk;A4").

Lemma bsf4_len : length bsf4 = 6%nat. Proof using . reflexivity. Qed.
Lemma zeros4_eq : ltac2:(tb__ "0|1|
SeS15S12Q8A1M0A1S38Z4A1S19G0S39S69A3A3"). Proof using . reflexivity. Qed.
Lemma Kwf4_trace : ltac2:(tb__ "0|1|
S1cS15S2aA1M0S29S6aR3R2R1A3SfSeG0R3S19S2aVTR1;S3aZ1S97S12Q8A1R4S69A3A2A3A3SfSeS15S1aS12Q40A1S2bA2A1S2cR2A1S99A3SeS98S2dR2A1Vfs;A3A2A2F_;Fmd;Ftr;Fk;").
Proof using .
  intros k tr md (tr0 & (-> & Hf & Hs) & ->). split; [|auto]. unfold WLout.TRk, WLout.MSG, wr. rewrite app_nil_r. reflexivity.
Qed.
Lemma Kwf4_tcons : ltac2:(tb__ "0|0|
S1cS93VSpecT;S6aR1A1A2Fk;").
Proof using HC normal_in_spec.
  intros k tr md HK. destruct (Kwf4_trace k tr md HK) as (-> & _ & _). exists (wr 1 (zeros (calls F)) ++ [ex fs 0]). split; [exact normal_in_spec|].
  rewrite HC, zeros4_eq. unfold TR1, Drv_hl.TR1. rewrite <- (firstn_skipn k bsf4) at 2. rewrite !Drv_hl.wr_app, <- !app_assoc.
  rewrite (app_assoc (wr 1 msg_zero) (wr 1 (firstn k bsf4))). apply is_prefix_app.
Qed.
Lemma wl2f4_call : ltac2:(tb__ "0|1|
S1S6cR1A1S32S0Vok;S24S0VKL1;S49R2A4S26S0S6aS1bS12Q8A1M0S8fS69S17G0A1A2A2A1S4S49A1R2S90A5A4F_;Frho1;").
Proof using HC SIDEL TL normal_in_spec.
  intros rho1 (H5 & H6 & H13 & H15).
  apply (WLout.wl2_sum ok KL1 rho1 bsf4 [] H5 H6 ltac:(rewrite H13, bsf4_len; reflexivity) ltac:(rewrite H15; reflexivity)).
  - unfold WLout.MSG, max_write_total. rewrite app_nil_r, bsf4_len. cbn. lia.
  - intros k. apply HokK, Kwf4_tcons.
  - intros k. apply HokP, Kwf4_tcons.
  - apply KL1_fd1.
  - rewrite bsf4_len. cbn. lia.
Qed.
Lemma wl2f4_ecall : ltac2:(tb__ "0|1|
S1S6cR1A1S31S0S24S0VKL1;S49R2A4S26S0S6aS1bS12Q8A1M0S8fS69S17G0A1A2A2A1S4S49A1R2S90A5A3F_;Frho1;").
Proof using SIDEL TL.
  intros rho1 (H5 & H6 & H13 & H15).
  apply (WLout.wl2_sum_ex KL1 rho1 bsf4 [] H5 H6 ltac:(rewrite H13, bsf4_len; reflexivity) ltac:(rewrite H15; reflexivity)).
  - unfold WLout.MSG, max_write_total. rewrite app_nil_r, bsf4_len. cbn. lia.
  - apply KL1_fd1.
  - rewrite bsf4_len. cbn. lia.
Qed.

Lemma fl4_intro : ltac2:(tb__ "0|2|
S1S30S24S0VKL1;S8aR2R1A5S10S1S1SfSfSeS15S12Q8A1M0A1M1S8R1P5A2S69A3SeG1S8R1P6A2S17G0A1A3A2S24S0VKL1;S8bR1R3A5A2Lrho';A2F_;Fw;Frho;").
Proof using Hargc JD L P0 SIDEL TL.
  intros rho [tr [ms md]] [Hsm Hk]. destruct norl_fl4 as [N5 N6]. destruct obj10_fl4 as (O10 & Lo & Hi & Wr & Ar & CB & BL).
  pose proof (smatch_xforms segs xs_fl4 rho E_fl4 E_fl41 _ xs_fl4_ok Hsm) as H1.
  pose proof (smatch_unbase segs rho E_fl41 1 (-64) E_fl42 _ unb_fl4 H1) as H2.
  pose proof (smatch_obj_to_list segs rho E_fl42 _ 12 5 _ stdout_buf (stdout_buf + 6) BL_fl4 H2 O10 Lo Hi ltac:(unfold stdout_buf; lia) ltac:(unfold stdout_buf; lia) Wr Ar CB N5) as H3.
  rewrite E_fl43_eq, BL in H3.
  set (rho' := rho_set_rl (rho_set_rl rho 5 (zeros 3)) 6 (@nil byte)).
  assert (H3' : smatch segs rho' E_fl43 (tr, mkCfg ms md)) by (apply smatch_set_rl; [exact N6 | exact H3]).
  exists rho'. split; [split; reflexivity|]. split; [|exact Hk].
  rewrite <- E_fl4c_eq. unfold app_objs.
  apply (ReprGlue.smatch_carve_rom segs rho' E_fl43 _ 0 0 6 (ss_next E_fl43) H3').
  - exact swf_E_fl4c.
  - lia. - lia. - lia.
  - reflexivity.
  - intros k Hk0. exfalso. lia.
  - apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd]. lia.
Qed.

Lemma x4_fS_intro : ltac2:(tb__ "0|0|
S1S48S29OF_;F_;S1S30S25S0VJD;VKL1;R4S17S1aS6S6A2A1R3A4S89R2R1A5S10S1S1S24S0VKL1;S8dR1R3A5Lr;A2F_;Fw;Frho;FDf;Fr0';").
Proof using Hargc L P0 SIDEL TL.
  intros r0' Df rho [tr [ms md]] [Hsm (Ai & HJi & _)]. pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & _).
  destruct (statics_view_of_MInvR segs C_U Ai _ md HM) as [g Vg].
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U _ T_4f (tr, mkCfg ms md) g (ss_next T_4f) (Pos.succ (ss_next T_4f)) Hsm
              ltac:(lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts T_4f) [] (ss_objs T_4f) _ ltac:(intros t Ht; destruct Ht) (smatch_facts_hold segs _ _ _ Hsm) missT_T4f)
              ltac:(rewrite T_4fS_eq; exact swf_T_4fS)) as [Hsm' _].
  eexists. split; [rewrite <- T_4fS_eq; exact Hsm' | exact Hk].
Qed.

Lemma x4_exit_safe : ltac2:(tb__ "0|0|
S1S48S29OF_;F_;S1S32S0Vok;S25S0VJD;VKL1;R3S17S1aS6S6A2A1R2A4S89R1A4S30S11L_;A4Frho;FDf;Fr0';").
Proof using HC Hargc HokK HokP Hokh KL1_tcons P0 SIDEL TL normal_in_spec.
  intros r0' Df rho.
  apply (triple_from ok _ (fun r w => SP segs KL1 T_4fS r w)); [intros w Hw; exact (x4_fS_intro r0' Df rho w Hw)|].
  intros rho1. destruct T_4fS_shape as [NX1 LN1].
  eapply (run_tr ok); [exact run_T4f | exact LN1 | apply HokK, KL1_tcons |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  apply (triple_from ok _ (fun r w => (rl r 5 = bsf4 /\ rl r 6 = []) /\ SP segs KL1 E_fl4c r w)); [intros w Hw; exact (fl4_intro rho2 w Hw)|].
  intros rho3. apply triple_pure. intros [H5 H6].
  destruct s_fl4_vals as (S12 & S13 & S14 & S15). destruct E_fl4_facts as (Fc & F3 & Nc & N3 & N2 & NT).
  apply (call_path segs PRf4 ok KL1 (Kwf4 (length (WLout.MSG bsf4 []))) E_fl4c E_fl4c WLoutS.Pre_wl2 [] s_fl4 R_fl4 WLout.Posts_wl _ rho3 eq_refl efr_fl4 chk_fl4 ltac:(rewrite Fc; exact fb_fl4)).
  - apply wl2f4_call.
  - intros ms _. unfold PRf4. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. change (ss_next WLoutS.Pre_wl2) with 92%positive. rewrite T_fl4D_eq.
    destruct T_fl4E_eq as (TE & FbE & LnE & _).
    eapply triple_conseq with (P := SP segs (Kwf4 (length (WLout.MSG bsf4 []))) T_fl4E rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [|exact HK]. rewrite <- TE. apply smatch_add_facts; [exact Hsm | exact HF4 | exact FbE]. }
    eapply (run_tr ok); [exact run_fl4 | exact LnE | apply HokK, Kwf4_tcons |].
    intros Lf rho5 [<-|[]] Hag5. cbn [lf_state]. destruct cert_x4 as (Hi & H17 & H10).
    apply (triple_exit_eval segs ok SpecT (Kwf4 (length (WLout.MSG bsf4 []))) E_x4 rho5 0);
      [apply HokK, Kwf4_tcons | apply HokP, Kwf4_tcons | exact Hokh | exact Hi | left; exact H17 | rewrite H10; reflexivity |].
    intros tr md HK. destruct (Kwf4_trace _ tr md HK) as (-> & _ & ->).
    unfold WLout.MSG. rewrite app_nil_r, firstn_all. unfold TR1, Drv_hl.TR1. rewrite <- Drv_hl.wr_app, <- zeros4_eq. pose proof normal_in_spec as N. rewrite HC in N. exact N.
Qed.

Lemma x4_exit_ex : ltac2:(tb__ "0|0|
S1S48S29OF_;F_;S1S31S0S25S0VJD;VKL1;R3S17S1aS6S6A2A1R2A4S89R1A4S3cVcx;A1A3Frho;FDf;Fr0';").
Proof using HC SIDEL TL.
  intros r0' Df rho.
  apply (etriple_from _ (fun r w => SP segs KL1 T_4fS r w)); [intros w Hw; exact (x4_fS_intro r0' Df rho w Hw)|].
  intros rho1. destruct T_4fS_shape as [NX1 LN1].
  eapply erun_tr; [exact run_T4f | exact LN1 |].
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  apply (etriple_from _ (fun r w => (rl r 5 = bsf4 /\ rl r 6 = []) /\ SP segs KL1 E_fl4c r w)); [intros w Hw; exact (fl4_intro rho2 w Hw)|].
  intros rho3 w0 [[H5 H6] Hw0]. revert w0 Hw0.
  destruct s_fl4_vals as (S12 & S13 & S14 & S15). destruct E_fl4_facts as (Fc & F3 & Nc & N3 & N2 & NT).
  apply (ecall_path segs PRf4 KL1 (Kwf4 (length (WLout.MSG bsf4 []))) E_fl4c E_fl4c WLoutS.Pre_wl2 [] s_fl4 R_fl4 WLout.Posts_wl _ rho3 eq_refl efr_fl4 chk_fl4 ltac:(rewrite Fc; exact fb_fl4)).
  - apply wl2f4_ecall.
  - intros ms _. unfold PRf4. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. change (ss_next WLoutS.Pre_wl2) with 92%positive. rewrite T_fl4D_eq.
    destruct T_fl4E_eq as (TE & FbE & LnE & _).
    eapply etriple_conseq with (P := SP segs (Kwf4 (length (WLout.MSG bsf4 []))) T_fl4E rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [|exact HK]. rewrite <- TE. apply smatch_add_facts; [exact Hsm | exact HF4 | exact FbE]. }
    eapply erun_tr; [exact run_fl4 | exact LnE |].
    intros Lf rho5 [<-|[]] Hag5. cbn [lf_state]. destruct cert_x4 as (Hi & H17 & H10).
    eapply etriple_conseq; [intros w Hw; exact Hw | | apply (etriple_exit_eval segs (Kwf4 (length (WLout.MSG bsf4 []))) E_x4 rho5 0 Hi (or_introl H17))].
    + intros w (tr & md & HK & Hw). destruct (Kwf4_trace _ tr md HK) as (Htr & _ & Hfs). unfold Drv_hl.QN. rewrite Hw, Htr, Hfs.
      unfold WLout.MSG. rewrite app_nil_r, firstn_all. unfold TR1, Drv_hl.TR1. rewrite <- Drv_hl.wr_app, <- zeros4_eq, (HC : calls (f_F cx) = 4). reflexivity.
    + rewrite H10. reflexivity.
Qed.

Section Free4.
Hypothesis MCs : ltac2:(tb__ "0|0|
S58S0S35S5eA3").

Lemma x4_free_safe : ltac2:(tb__ "0|0|
S1S28S15S12Q40A1A1S3dR3R2R1A3S32S0Vok;S24S0VKs;VKL1;R3R2A3S85R4A4S30S11L_;A4F_;Fmat;Fvm;Frho;").
Proof using HC KL1_tcons MCs SIDEL TL normal_in_spec.
  intros rho vm mat HSn.
  eapply triple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho C_4m 0 (-128) C_4x w unb_C4 (SPJ_xforms segs _ [XRebase 0; XRebase 1; XMerge 0] rho C_4 C_4m w xs_C4_ok Hw)) | intros w Hw; exact Hw |].
  eapply triple_conseq with (P := SPJ segs (JD KL1 rho U.Drv_r__G1.Drv_r.tvK DTrue) C_4x rho); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 U.Drv_r__G1.Drv_r.tvK DTrue rho vm mat tr md HSn Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_ff4_vals as (F12 & F13 & F10 & F15). destruct C_4x_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_ff4 as (CHK & RCHK & NZ).
  apply (dfree_call segs C_U EC_U 31 KL1 rho P0 malloc_laws_U ok C_4x s_ff4 R_ff4 rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (mc_free _ _ _ MCs). apply okside_i.
  - exact efr_ff4.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf NZ). }
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_4x) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) robj_inwi R_ff4 _ rho md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho Ai _ o a Ho Hr).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_4f_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply x4_exit_safe.
Qed.
End Free4.

Section FreeX4.
Hypothesis FCX : free_contract_ex_U.

Lemma x4_free_ex : ltac2:(tb__ "0|0|
S1S28S15S12Q40A1A1S3dR3R2R1A3S31S0S24S0VKs;VKL1;R3R2A3S85R4A4S3cVcx;A1A3F_;Fmat;Fvm;Frho;").
Proof using FCX HC SIDEL TL.
  intros rho vm mat HSn.
  eapply etriple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho C_4m 0 (-128) C_4x w unb_C4 (SPJ_xforms segs _ [XRebase 0; XRebase 1; XMerge 0] rho C_4 C_4m w xs_C4_ok Hw)) | intros w Hw; exact Hw |].
  eapply etriple_conseq with (P := SPJ segs (JD KL1 rho U.Drv_r__G1.Drv_r.tvK DTrue) C_4x rho); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 U.Drv_r__G1.Drv_r.tvK DTrue rho vm mat tr md HSn Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_ff4_vals as (F12 & F13 & F10 & F15). destruct C_4x_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_ff4 as (CHK & RCHK & NZ).
  apply (dfree_call_ex segs C_U EC_U 31 KL1 rho P0 malloc_laws_U C_4x s_ff4 R_ff4 rho U.Drv_r__G1.Drv_r.tvK 0%nat (SVar 102, SVar 101) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (FCX Ai). apply U.Drv_r__G1.Drv_r.Ki_vmi, KL1_vmi.
  - exact efr_ff4.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (U.Drv_r__G1.Drv_r.tvK_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho _ _ HFf NZ). }
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho (ss_facts C_4x) U.Drv_r__G1.Drv_r.tvK (Some 0%nat) robj_inwi R_ff4 _ rho md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho Ai _ o a Ho Hr).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_4f_eq. change (remove_nth 0 U.Drv_r__G1.Drv_r.tvK) with (@nil (sv * sv)). apply x4_exit_ex.
Qed.
End FreeX4.

Lemma x4_A_leaf : ltac2:(tb__ "0|5|
S2S2S2S2S2S54S1S22S28S15S12Q40A1A1S30SeS1eS2A1M0S95RbS87A2S1fS2RaA2M1A3SeG0S94RbU0Nd0A3G1A3SeS15S3A1M2S5RbA1S19S3S5RaA1S1dS3S4cS17S3A1A3A3A3SeS16SaRbA1S18A3SeS2RcS41RdS5RcA1M3A2A3SeG2S5RdA1M4S19S3G3S5bS35S50A2A3A3SeS2RdS41ReG4A2A3SeS16S5aReS85RdA3S18A3SeS16S55ReP1fA2S18A3SeS16S57RfS33S33A3S18A3VSIDEL;S50RfReRdRcA5SeS22S37VF;A1Z0A3S24S0VKs;VKL1;RfReA3R17R11RdA5S10S1S1SfS3dR1R11R10A3S24S0VKs;VKL1;R11R10A3S85R1RfA5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;Fs;Fn4;Fn3;Fn2;Fn1;Fn;").
Proof using TL.
  intros n n1 n2 n3 n4 s rho g vm mat [tr [ms md]] Hx Hu Ho2 Hwf3 Hn3 Ho3 Hn4 He Hid Htv (HSn & HG & HV & Hv & HT) HP0 [Hsm Hk].
  pose proof (smatch_unbase segs rho n1 0 (-208) n2 _ Hu (smatch_xforms segs xs_xa rho n n1 _ Hx Hsm)) as H2.
  assert (H3 : smatch segs rho n3 (tr, mkCfg ms md)).
  { rewrite Hn3. apply (smatch_drop_nil rho n2 _ (ss_objs n3) O_payL H2 Ho2 (pay_empty rho HT HP0)). rewrite <- Hn3. exact Hwf3. }
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho n3 (tr, mkCfg ms md) (ss_objs n4) g NX3 H3 Ho3 HV Hv) as (m' & H4 & Hout & RD & WK & _).
  rewrite <- Hn4 in H4.
  pose proof (entails_sound segs _ _ s _ _ He H4) as H5.
  exists (rho_sub (set_rm rho m') s). split; [|split; [exact H5 | exact Hk]].
  destruct (tvK_sub s (set_rm rho m') Htv) as [R101 R102].
  apply (SIDEK_transport rho); [exact (snapJ_tail _ _ _ _ _ _ HSn) | | exact R101 | exact R102 | | |].
  - intros i Hi. cbn [rho_sub rw]. rewrite (wsub_get_id s 31 i Hid ltac:(lia)). reflexivity.
  - intros a. cbn [rho_sub set_rm rm]. apply RD.
  - intros a. cbn [rho_sub set_rm rm]. apply WK.
  - intros a Ha. cbn [rho_sub set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Lemma x4_B2_intro : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1S30VSIDEL;S50R5R4R3R2A5S42Z0S37VF;A1A2S24S0VKs;VKL1;R5R4A3S53R7R3A5S10S1S1SfSfVTL;R1A1S60S0S35VP0;Vwtop;S4dS40R1R7R6A9A2S24S0VKs;VKL1;R7R6A3S8eR1R5A5A2Lrho';A2F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;").
Proof using Hargc JD L P0_transport cap.
  intros rho g vm mat [tr [ms md]] (HSn & HG & HV & Hv & HT) HP [Hsm Hk].
  destruct X_4_objs as (OX & O2 & LnX & R10 & PcX).
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho X_4 (tr, mkCfg ms md) (firstn 13 (ss_objs X_4)) g NX3 Hsm OX HV Hv) as (m' & H1 & Hout & RD & WK & _).
  rewrite XB4r_eq in H1. set (rho' := set_rm rho m') in *.
  destruct XB40_eq as (RE & O2r & WF & NXr).
  pose proof HT as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  assert (H2 : smatch segs rho' XB40 (tr, mkCfg ms md)).
  { rewrite <- RE.
    apply (proj1 (SPJ_reshape segs (liftK (fun _ _ => True)) rho' XB4r 2 _ O_payB (tr, mkCfg ms md) O2r eq_refl eq_refl eq_refl WF
                              ltac:(intros _; unfold obj_lo_of, obj_hi_of, O_payB, O_payL; cbn [ob_base ob_lo ob_hi eval rho' set_rm rw]; rewrite E240; split; reflexivity)
                              (conj H1 I))). }
  pose proof (smatch_unbase segs rho' XB41 0 (-208) XB42 _ unb_fo4 (smatch_xforms segs xs_fo rho' XB40 XB41 _ xs_fo4_ok H2)) as H3.
  exists rho'. split; [split|split; [exact H3 | exact Hk]].
  - apply (Drv_hl.TL_rw cx cap rho rho'); [intros i _; reflexivity | exact HT].
  - apply (snapJ_transport segs C_U P0 malloc_laws_U wtop tvL DTrue rho rho' vm mat HSn).
    + apply (Drv_hl.tv_eval_eq_L); reflexivity.
    + exact RD.
    + exact WK.
    + destruct HSn as (Ai & md' & _ & _ & _ & HP0 & _). apply (P0_transport rho rho' HP0); [intros i _; reflexivity|].
      intros a Ha. cbn [rho' set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Definition SIDEB4 (rho : valuation) (g : Z) (vm : VmMaps) (mat : list word) : Prop := ltac2:(tb__ "0|1|
SfS3dVrho;Vvm;Vmat;A3SfS5cS0S35S9Vrho;A1Vg;A4SeS12Q40M0A1S7Vrho;S4S86A1A2S14G0Vg;A2A3A2A2").

Lemma SIDEB4_agree : ltac2:(tb__ "0|0|
S23S1S1S22S28S15S12Q40A1A1S6bR5R3R2R1A4SbR7R6R5A3S3eS4S86A1R8A2S6bR7R6R5R4A4F_;F_;F_;Fmat;Fvm;Fg;Frho';Frho;Fn;").
Proof using SIDEL TL.
  intros n rho rho' g vm mat (HS & HV & Hv) (Hw & _ & Hm) Hn. pose proof LT4 as (_ & _ & L102 & _).
  assert (Hm' : forall a, rm rho' a = rm rho a) by (intros a; symmetry; apply Hm).
  split; [|split].
  - apply (SIDEK_transport rho rho' vm mat HS).
    + intros i Hi. symmetry. apply Hw. lia.
    + symmetry. apply Hw. lia.
    + symmetry. apply Hw. lia.
    + intros a. unfold rd_of. rewrite Hm'. reflexivity.
    + intros a. unfold wok_of. rewrite Hm'. reflexivity.
    + intros a _. apply Hm'.
  - apply (statics_view_rm segs C_U statics_layout_U (rm rho) (rm rho') g); [intros a _; apply Hm' | exact HV].
  - rewrite <- Hw by lia. exact Hv.
Qed.

Lemma x4_BS_intro : ltac2:(tb__ "0|1|
S1S1S30S25S0VJD;VKL1;R3S33S40A4S88R2R1A5S10S1S1S10S22S22S10S28S28S10S15S12Q40A1A1M0G0SfS6bR4R3R2R1A4S24S0VKs;VKL1;R2R1A3S8cR4R6A5A2Lmat;A2Lvm;A2Lg;A2Lrho1;A2F_;Fw;Frho;Fr0;").
Proof using SIDEL TL.
  intros r0 rho [tr [ms md]] [Hsm (Ai & HJi & _)]. destruct ent_T4Bt as [He NxBt]. pose proof LT4 as (_ & _ & L102 & _).
  pose proof (entails_sound segs _ _ [] _ _ He Hsm) as Hsm1. set (rho0 := rho_sub rho []) in Hsm1.
  assert (HJi0 : JGi segs C_U 31 KL1 r0 P0 [] U.Drv_r__G1.Drv_r.tvK Ai rho0 tr md).
  { apply (JGi_stable segs C_U 31 KL1 r0 P0 [] malloc_laws_U 104 U.Drv_r__G1.Drv_r.tvK Ai rho rho0 tr md ltac:(lia) (U.Drv_r__G1.Drv_r.tvK_below cx 104 ltac:(lia))); [|exact HJi].
    split; [intros i _; reflexivity|]. split; [intros l; reflexivity | intros a; reflexivity]. }
  pose proof HJi0 as (Hav & Hk & [HM [Hi HTPI]] & HP & HN & HKF & HP0').
  pose proof (U.Drv_hs__G1.Drv_hs.P0_now cx _ _ _ _ _ _ _ HJi0) as HP0.
  pose proof (tv_geo_of_JGi segs C_U 31 KL1 r0 P0 U.Drv_r__G1.Drv_r.tvK Ai rho0 tr md HJi0) as HG.
  destruct (statics_view_of_MInvR segs C_U Ai rho0 md HM) as [g Vg].
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U rho0 T_4Bt (tr, mkCfg ms md) g (ss_next T_4Bt) (Pos.succ (ss_next T_4Bt)) Hsm1
              ltac:(lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts T_4Bt) U.Drv_r__G1.Drv_r.tvK (ss_objs T_4Bt) rho0 HG (smatch_facts_hold segs _ _ _ Hsm1) missT_T4B)
              ltac:(rewrite T_4BS_eq; exact swf_T_4BS)) as [Hsm' Hag].
  set (rho1 := rho_set_rw rho0 (ss_next T_4Bt) (Z_to_bv 64 g)) in *.
  assert (RW : forall i, i <> ss_next T_4Bt -> rw rho1 i = rw rho0 i) by (intros i Hi'; subst rho1; apply rho_set_rw_other; exact Hi').
  exists rho1, g, (m_vmmaps md), (m_vm_materialized md). split; [|split; [rewrite <- T_4BS_eq; exact Hsm' | apply (Drv_hl.Ks_intro); exact Hk]].
  destruct (deJ segs C_U 31 P0 wtop P0_top KL1 r0 U.Drv_r__G1.Drv_r.tvK DTrue Ai rho0 tr md HJi0 I HP0) as [HSn _].
  split; [|split; [exact Vg | subst rho1; apply rho_set_rw_at]].
  apply (SIDEK_transport rho0 rho1 _ _ HSn).
  - intros i Hi'. apply RW. lia.
  - apply RW. lia.
  - apply RW. lia.
  - intros a; reflexivity.
  - intros a; reflexivity.
  - intros a _; reflexivity.
Qed.

Lemma x4_B_leaf : ltac2:(tb__ "0|1|
S2S2S54S1S22S28S15S12Q40A1A1S30SeS15S3A1S5R8A1M0S19S3S5R7A1S5bS35S4S86A1A2A3A3SeS2R8S41R9G0A2A3SeS16S5aR9S85R8A3S18A3SeS16S55R9P1fA2S18A3SeS16S57RaS33S33A3S18A3S6bRaR9R8R7A4S24S0VKs;VKL1;R9R8A3ReRbR7A5S10S1S1SfS3dR1RbRaA3S24S0VKs;VKL1;RbRaA3S85R1R9A5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;Fw;Fmat;Fvm;Fg;Frho;Fs;Fn4;Fn;").
Proof using SIDEL TL.
  intros n n4 s rho g vm mat [tr [ms md]] Ho Hn4 He Hid Htv (HSn & HV & Hv) [Hsm Hk].
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho n (tr, mkCfg ms md) (ss_objs n4) g (ss_next T_4Bt) Hsm Ho HV Hv) as (m' & H4 & Hout & RD & WK & _).
  rewrite <- Hn4 in H4.
  pose proof (entails_sound segs _ _ s _ _ He H4) as H5.
  exists (rho_sub (set_rm rho m') s). split; [|split; [exact H5 | exact Hk]].
  destruct (tvK_sub s (set_rm rho m') Htv) as [R101 R102].
  apply (SIDEK_transport rho); [exact HSn | | exact R101 | exact R102 | | |].
  - intros i Hi. cbn [rho_sub rw]. rewrite (wsub_get_id s 31 i Hid ltac:(lia)). reflexivity.
  - intros a. cbn [rho_sub set_rm rm]. apply RD.
  - intros a. cbn [rho_sub set_rm rm]. apply WK.
  - intros a Ha. cbn [rho_sub set_rm rm]. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Section Safe4.
Hypothesis MCs : ltac2:(tb__ "0|0|
S58S0S35S5eA3").

Lemma x4_A_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S50R4R3R2R1A5SeS22S37VF;A1Z0A3S32S0Vok;S24S0VKs;VKL1;R4R3A3S53R6A4S30S11L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS HP0. pose proof HS as (HSn & HG & HV & Hv & HT). pose proof HT as [_ [_ P2]]. pose proof (P2 HP0) as Z241.
  pose proof LT4 as (L1 & L2 & _). destruct diff_XA40 as (Hd & Hwf & Hln & Hnx).
  apply (triple_restate segs ok _ rho X_4 XA40 _ _ Hwf Hd).
  { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite Z241. reflexivity. }
  eapply (run_tr ok); [exact run_XA40 | exact Hln | apply Ks_okf, KL1_tcons |].
  rewrite Hnx. destruct ent_C4 as (E1 & E2 & _ & _). destruct ent_C4_props as (I1 & I2 & _ & _ & T1 & T2 & _ & _).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (Drv_hl.SIDEL_agree cx cap NX3 _ rho rho2 g vm mat HS Hag2 L1 L2) as HS2.
  - destruct XA4a_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_4 r w)); [intros w Hw; exact (x4_A_leaf XA4a XA4a1 XA4a2 XA4a3 XA4a4 s_CAa4 rho2 g vm mat w xs_XA4a_ok unb_XA4a O2 W3 N3 O3 N4 E1 I1 T1 HS2 HP0 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x4_free_safe MCs rho3 vm mat HS3).
  - destruct XA4b_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_4 r w)); [intros w Hw; exact (x4_A_leaf XA4b XA4b1 XA4b2 XA4b3 XA4b4 s_CAb4 rho2 g vm mat w xs_XA4b_ok unb_XA4b O2 W3 N3 O3 N4 E2 I2 T2 HS2 HP0 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x4_free_safe MCs rho3 vm mat HS3).
Qed.

Lemma x4_Bt_safe : ltac2:(tb__ "0|0|
S1S1S32S0Vok;S25S0VJD;VKL1;R2S33S40A4S88R1A4S30S11L_;A4Frho;Fr0;").
Proof using HC Hargc HokK HokP Hokh KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport SIDEL TL normal_in_spec.
  intros r0 rho. pose proof LT4 as (_ & _ & _ & L4).
  apply (triple_from ok _ (fun r w => exists g vm mat, SIDEB4 r g vm mat /\ SP segs (Ks KL1 vm mat) T_4BS r w)).
  { intros w Hw. destruct (x4_BS_intro r0 rho w Hw) as (rho1 & g & vm & mat & HS & HP'). exists rho1, g, vm, mat. split; assumption. }
  intros rho1. apply triple_ex. intros g. apply triple_ex. intros vm. apply triple_ex. intros mat. apply triple_pure. intros HS1.
  destruct T_4BS_shape as [NxS LnS].
  eapply (run_tr ok); [exact run_T4B | exact LnS | apply Ks_okf, KL1_tcons |].
  rewrite NxS. destruct ent_C4 as (_ & _ & E3 & E4). destruct ent_C4_props as (_ & _ & I3 & I4 & _ & _ & T3 & T4).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (SIDEB4_agree _ rho1 rho2 g vm mat HS1 Hag2 L4) as HS2.
  - destruct XB4a_sets as (O4 & _ & N4).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_4 r w)); [intros w Hw; exact (x4_B_leaf XB4a XB4a4 s_CBa4 rho2 g vm mat w O4 N4 E3 I3 T3 HS2 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x4_free_safe MCs rho3 vm mat HS3).
  - destruct XB4b_sets as (O4 & _ & N4).
    apply (triple_from ok _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_4 r w)); [intros w Hw; exact (x4_B_leaf XB4b XB4b4 s_CBb4 rho2 g vm mat w O4 N4 E4 I4 T4 HS2 Hw)|].
    intros rho3. apply triple_pure. intros HS3. exact (x4_free_safe MCs rho3 vm mat HS3).
Qed.

Lemma x4_B_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S50R4R3R2R1A5S42Z0S37VF;A1A2S32S0Vok;S24S0VKs;VKL1;R4R3A3S53R6A4S30S11L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS HP.
  apply (triple_from ok _ (fun r w => (TL r /\ snapJ segs C_U P0 wtop tvL DTrue r vm mat) /\ SP segs (Ks KL1 vm mat) XB42 r w)); [intros w Hw; exact (x4_B2_intro rho g vm mat w HS HP Hw)|].
  intros rho1. apply triple_pure. intros [HT1 HSn1].
  eapply triple_conseq with (P := SPJ segs (JD KL1 rho1 tvL DTrue) XB42 rho1); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 tvL DTrue rho1 vm mat tr md HSn1 Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_fb4_vals as (F12 & F13 & F10 & F15). destruct XB42_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_fb4 as [CHK RCHK].
  pose proof HT1 as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  apply (dfree_call segs C_U EC_U 31 KL1 rho1 P0 malloc_laws_U ok XB42 s_fb4 R_fb4 rho1 tvL 0%nat (SVar 241, SVar 158) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho2. apply (mc_free _ _ _ MCs). apply okside_i.
  - exact efr_fb4.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (Drv_hl.tvL_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP' & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho1 (SVar 241, SVar 158)) by (unfold tnz; cbn [fst eval]; exact NZ241).
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho1 (ss_facts XB42) tvL (Some 0%nat) robj_inwi R_fb4 _ rho1 md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho1 Ai _ o a Ho Hr).
      * exists (SVar 241, SVar 158). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_4B_eq. change (remove_nth 0 tvL) with U.Drv_r__G1.Drv_r.tvK. apply x4_Bt_safe.
Qed.

Theorem x4_safe : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S50R4R3R2R1A5S32S0Vok;S24S0VKs;VKL1;R3R2A3S53R5A4S30S11L_;A4F_;Fmat;Fvm;Fg;Frho;").
Proof using HC Hargc HokK HokP Hokh JD KL1_tcons KL1_vmi MCs P0 P0_tp P0_transport TL normal_in_spec.
  intros rho g vm mat HS. pose proof (Drv_hl.plen_range cx HL6 HLM) as PR.
  destruct (Z.eq_dec (payload_len F) 0) as [Z0|NZ]; [exact (x4_A_safe rho g vm mat HS Z0) | apply (x4_B_safe rho g vm mat HS ltac:(unfold F in *; lia))].
Qed.
End Safe4.

Section Ex4.
Hypothesis FCX : free_contract_ex_U.

Lemma x4_A_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S50R4R3R2R1A5SeS22S37VF;A1Z0A3S31S0S24S0VKs;VKL1;R4R3A3S53R6A4S3cVcx;A1A3F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC TL.
  intros rho g vm mat HS HP0. pose proof HS as (HSn & HG & HV & Hv & HT). pose proof HT as [_ [_ P2]]. pose proof (P2 HP0) as Z241.
  pose proof LT4 as (L1 & L2 & _). destruct diff_XA40 as (Hd & Hwf & Hln & Hnx).
  apply (etriple_restate segs _ rho X_4 XA40 _ _ Hwf Hd).
  { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite Z241. reflexivity. }
  eapply erun_tr; [exact run_XA40 | exact Hln |].
  rewrite Hnx. destruct ent_C4 as (E1 & E2 & _ & _). destruct ent_C4_props as (I1 & I2 & _ & _ & T1 & T2 & _ & _).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (Drv_hl.SIDEL_agree cx cap NX3 _ rho rho2 g vm mat HS Hag2 L1 L2) as HS2.
  - destruct XA4a_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_4 r w)); [intros w Hw; exact (x4_A_leaf XA4a XA4a1 XA4a2 XA4a3 XA4a4 s_CAa4 rho2 g vm mat w xs_XA4a_ok unb_XA4a O2 W3 N3 O3 N4 E1 I1 T1 HS2 HP0 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x4_free_ex FCX rho3 vm mat HS3 w0 Hw0).
  - destruct XA4b_sets as (O2 & W3 & O3 & _ & _ & _ & N4 & N3).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_4 r w)); [intros w Hw; exact (x4_A_leaf XA4b XA4b1 XA4b2 XA4b3 XA4b4 s_CAb4 rho2 g vm mat w xs_XA4b_ok unb_XA4b O2 W3 N3 O3 N4 E2 I2 T2 HS2 HP0 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x4_free_ex FCX rho3 vm mat HS3 w0 Hw0).
Qed.

Lemma x4_Bt_ex : ltac2:(tb__ "0|0|
S1S1S31S0S25S0VJD;VKL1;R2S33S40A4S88R1A4S3cVcx;A1A3Frho;Fr0;").
Proof using FCX HC SIDEL TL.
  intros r0 rho. pose proof LT4 as (_ & _ & _ & L4).
  apply (etriple_from _ (fun r w => exists g vm mat, SIDEB4 r g vm mat /\ SP segs (Ks KL1 vm mat) T_4BS r w)).
  { intros w Hw. destruct (x4_BS_intro r0 rho w Hw) as (rho1 & g & vm & mat & HS & HP'). exists rho1, g, vm, mat. split; assumption. }
  intros rho1. apply etriple_ex. intros g. apply etriple_ex. intros vm. apply etriple_ex. intros mat. apply etriple_pure. intros HS1.
  destruct T_4BS_shape as [NxS LnS].
  eapply erun_tr; [exact run_T4B | exact LnS |].
  rewrite NxS. destruct ent_C4 as (_ & _ & E3 & E4). destruct ent_C4_props as (_ & _ & I3 & I4 & _ & _ & T3 & T4).
  intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (SIDEB4_agree _ rho1 rho2 g vm mat HS1 Hag2 L4) as HS2.
  - destruct XB4a_sets as (O4 & _ & N4).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_4 r w)); [intros w Hw; exact (x4_B_leaf XB4a XB4a4 s_CBa4 rho2 g vm mat w O4 N4 E3 I3 T3 HS2 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x4_free_ex FCX rho3 vm mat HS3 w0 Hw0).
  - destruct XB4b_sets as (O4 & _ & N4).
    apply (etriple_from _ (fun r w => SIDEK r vm mat /\ SP segs (Ks KL1 vm mat) C_4 r w)); [intros w Hw; exact (x4_B_leaf XB4b XB4b4 s_CBb4 rho2 g vm mat w O4 N4 E4 I4 T4 HS2 Hw)|].
    intros rho3 w0 [HS3 Hw0]. exact (x4_free_ex FCX rho3 vm mat HS3 w0 Hw0).
Qed.

Lemma x4_B_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S50R4R3R2R1A5S42Z0S37VF;A1A2S31S0S24S0VKs;VKL1;R4R3A3S53R6A4S3cVcx;A1A3F_;F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC TL.
  intros rho g vm mat HS HP.
  apply (etriple_from _ (fun r w => (TL r /\ snapJ segs C_U P0 wtop tvL DTrue r vm mat) /\ SP segs (Ks KL1 vm mat) XB42 r w)); [intros w Hw; exact (x4_B2_intro rho g vm mat w HS HP Hw)|].
  intros rho1 w0 [[HT1 HSn1] Hw0]. revert w0 Hw0.
  eapply etriple_conseq with (P := SPJ segs (JD KL1 rho1 tvL DTrue) XB42 rho1); [| intros w Hw; exact Hw |].
  { intros [tr [ms md]] [Hsm (Hk & Hvm & Hmat)]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
    exact (reJ segs C_U 31 P0 wtop P0_top P0_tp KL1 tvL DTrue rho1 vm mat tr md HSn1 Hvm Hmat ltac:(intros; exact I) Hk). }
  destruct s_fb4_vals as (F12 & F13 & F10 & F15). destruct XB42_shape as (Cpc & Cnx & Cfa & Cln). destruct chk_fb4 as [CHK RCHK].
  pose proof HT1 as [_ [P1 _]]. destruct (P1 HP) as [E240 NZ241].
  apply (dfree_call_ex segs C_U EC_U 31 KL1 rho1 P0 malloc_laws_U XB42 s_fb4 R_fb4 rho1 tvL 0%nat (SVar 241, SVar 158) _ DTrue
           (fun Ai => J_free_pre segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) (fun Ai => JL_free segs C_U Ai (U.Drv_r__G1.Drv_r.Ki KL1 Ai)) DTrue).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho2. apply (FCX Ai). apply U.Drv_r__G1.Drv_r.Ki_vmi, KL1_vmi.
  - exact efr_fb4.
  - exact CHK.
  - rewrite Cnx. reflexivity.
  - reflexivity.
  - rewrite Cnx. apply (Drv_hl.tvL_below cx). apply Pos.leb_le. reflexivity.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ _. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP' & (HN & HD & HZ) & HKF & HP0').
    pose proof (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx _ _ _ _ _ _ _ HJ) as HT.
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho1 (SVar 241, SVar 158)) by (unfold tnz; cbn [fst eval]; exact NZ241).
    split; [|split; [exact Hnz|split]].
    + intros (A1' & A2' & A3' & A4' & A5' & A6'). split; [exact A1'|]. split; [exact A2'|]. split; [split; [exact A3' | exact Hi] | split; [exact A4' | split; [exact A5' | exact A6']]].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho1 (ss_facts XB42) tvL (Some 0%nat) robj_inwi R_fb4 _ rho1 md HM HT HFf HN HD HZ RCHK).
      * intros o a _ Ho Hr. exact (robj_inwi_caddr rho1 Ai _ o a Ho Hr).
      * exists (SVar 241, SVar 158). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & HbA & HbA' & Hkept & Hik & [Hk Hi]).
    exists A', l1, l2. split; [exact HM'|]. split; [split; [exact (init_kept_init _ _ Hik Hi) | exact (init_kept_top _ _ Hik)]|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
  - intros rho5 Hag5. rewrite T_4B_eq. change (remove_nth 0 tvL) with U.Drv_r__G1.Drv_r.tvK. apply x4_Bt_ex.
Qed.

Theorem x4_ex : ltac2:(tb__ "0|0|
S1S22S28S15S12Q40A1A1VSIDEL;S50R4R3R2R1A5S31S0S24S0VKs;VKL1;R3R2A3S53R5A4S3cVcx;A1A3F_;Fmat;Fvm;Fg;Frho;").
Proof using FCX HC HL6 HLM TL.
  intros rho g vm mat HS. pose proof (Drv_hl.plen_range cx HL6 HLM) as PR.
  destruct (Z.eq_dec (payload_len F) 0) as [Z0|NZ]; [exact (x4_A_ex rho g vm mat HS Z0) | apply (x4_B_ex rho g vm mat HS ltac:(unfold F in *; lia))].
Qed.
End Ex4.

End X4.

End HX.
