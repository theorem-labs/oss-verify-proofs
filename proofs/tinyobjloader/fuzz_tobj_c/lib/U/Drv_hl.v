(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "not"; "ex"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sstate"; "sobj"; "rw"; "ss_next"; "sv"; "sprop"; "ss_facts"; "SVar"; "ss_objs"; "rm"; "SLit"; "SPNot"; "swf"; "rl"; "ss_lenient"; "SAlu"; "SPBranch"; "agree_below"; "holds"; "obj_range"; "ranges_disjoint"; "eval"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "app"; "Some"; "option"; "pair"; "prod"; "nil"; "fst"; "None"; "nat"; "andb"; "false"; "snd"; "length"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "event"; "Model"; "FdEntry"; "m_vm_materialized"; "m_vmmaps"; "m_fds"; "m_fs"; "FdChannel"; "fd_lookup"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states"; "tvL"; "PreFZ"; "PDfz"; "NX0"; "O_payL"; "S_0"; "X_1"; "LCUTS"; "N_1"; "robj_inwi"; "E_io"; "E_w"; "E_wc"; "T_w"; "T_wDi"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl.HL"; "Ks"; "TL"; "SIDEL"; "KL1"; "bs1"; "bs2"; "fork_ne"; "PRw"; "TR1"; "PAY"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "mc_img_hi"; "mc_img_lo"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "LQ"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "w_tr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ"; "DTrue"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "calls"; "payload_len"; "wr"; "zeros"; "ex"; "msg_zero"; "MAX_INPUT"; "config_len"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "opp"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsCut"; "mkLeaf"; "sym_run"; "set_objs"; "@Stdlib.PArith.BinPos.Pos"; "le"; "succ"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl.HL.Ex"; "QN"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "map"; "Forall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface"; "FZ_U"; "L_fuzz"; "fz_rets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "statics_objs"; "app_objs"; "a_got"; "a_guard"; "a_nl"; "statics_disjoint"; "static3"; "statics_view"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "robjs_missT_statics"; "tv_geo"; "CAP"; "snapJ"; "tv_eval_eq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out.WLout"; "Kw"; "MSG"; "Posts_wl"; "chw"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "is_prefix"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "wsub_dom_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_afterN"; "call_checkT";
"new_objs_tv"; "robjs_check"; "tvL_ok"; "T_ok"; "T0"; "aceil"; "tv_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states"; "E_f0"; "F2"; "tvP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r"; "tvK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "FUEL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out.WLoutS"; "Pre_wl2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "vm_insensitive"; "ok_sideK"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states.LAddr"; "nl_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl1_states"; "NX1"; "NX2"; "NX3"; "S_1"; "S_2"; "S_3"; "X_2"; "X_3"; "X_4"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open"; "std_fds"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"].
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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec SpecConsts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl1_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl1_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hs__G1.Drv_hs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import MAddr RAddr HAddr TAddr LAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Section HL.
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
Let KH := U.Drv_h__G1.Drv_h.KH cx.
Let TVc := U.Drv_ht__G1.Drv_ht.TVc cx.

Lemma NUsp : 0x7fff80000000 <= bv_unsigned sp <= 0x800000000000.
Proof using Hargc Hent Hinp JD KH L TVc. pose proof (U.Drv_m__G1.Drv_m.NU sp brk mb draw inp Hent Hinp Hargc) as N. lia. Qed.

Lemma T_ok_T0_31 : ltac2:(tb__ "0|0|
S6S6S1dS9dP1fR3R2A3Sa4R3R2A2Sa4R4Sa5R5A1A2F_;F_;FT;Frho;Fr0;").
Proof using .
  intros r0 rho T [Hw _] [E Rg]. unfold TobjJV.T_ok, TobjJV.T0, V_TOP in *. rewrite (Hw 30%positive ltac:(reflexivity)).
  split; [reflexivity|]. rewrite E. exact Rg.
Qed.

Definition TR1 : list event := wr 1 msg_zero.
Definition KL1 : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S1fS34A1M0S35S1S0G0R2S54A3S1S0S1fS27S30Q40A1S36A2A1S39R1A1SbeA3S0Sb0S3aR1A1Vfs;A3A2A2Lmd;Ltr;").

Definition Ks (K : list event -> Model -> Prop) (vm : VmMaps) (mat : list word) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S1fS34A1S35S1VK;R2R1A2S1S0S33S38R1A1Vvm;A3S0S1fS30Q40A1A1S37R1A1Vmat;A3A2A2Lmd;Ltr;").

Lemma zeros_succ : ltac2:(tb__ "0|1|
S1dS6bZ0R1A2S0S1fS30Q8A1M0A1S66S6dR2Z1A2A1S23G0S68S66R2A1A3A3F_;Fn;").
Proof using Hargc JD KH L TVc.
  intros n Hn. unfold zeros. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_comm. reflexivity.
Qed.
Lemma wr_app : ltac2:(tb__ "0|2|
S1dS1fS30Q8A1M0A1M1G1S0S1fS34A1S65R3S23G0R2R1A3A2S23S34S65R3R2A2S65R3R1A2A3A3Fb;Fa;Fch;").
Proof using . intros ch a b. unfold wr. apply map_app. Qed.

Lemma KL1_vmi : vm_insensitive KL1.
Proof using . split; [intros tr md vm (A & B & C) | intros tr md lz mt (A & B & C)]; (split; [exact A|]; split; autorewrite with model; assumption). Qed.
Lemma KH_tcons : K_tcons SpecT KH. Proof using inp. exact (U.Drv_h__G1.Drv_h.KH_tcons cx). Qed.
Lemma KH_vmi : vm_insensitive KH. Proof using cx. exact (U.Drv_h__G1.Drv_h.KH_vmi cx). Qed.
Lemma Ks_tcons : ltac2:(tb__ "0|0|
S1fS34A1S35OF_;F_;S33S1fS30Q40A1A1S7dVSpecT;R3A2S7dVSpecT;S4cR4R3R2A3A2F_;Fmat;Fvm;FK;").
Proof using inp. intros K vm mat HK tr md [H _]. exact (HK tr md H). Qed.
Lemma Ks_okf : ltac2:(tb__ "0|0|
S1fS34A1S35OF_;F_;S33S1fS30Q40A1A1S7dVSpecT;R3A2S5cS5Vok;S4cR4R3R2A3A3F_;Fmat;Fvm;FK;"). Proof using HokK. intros. apply HokK, Ks_tcons. assumption. Qed.
Lemma Ks_okp : ltac2:(tb__ "0|0|
S1fS34A1S35OF_;F_;S33S1fS30Q40A1A1S7dVSpecT;R3A2SbfS5Vok;S4cR4R3R2A3A3F_;Fmat;Fvm;FK;"). Proof using HokP. intros. apply HokP, Ks_tcons. assumption. Qed.
Lemma Ks_intro : ltac2:(tb__ "0|1|
S1fS34A1M0S35OF_;F_;G0S35R3R2R1A2S4cR4S38R2A1S37R2A1R3R2A5F_;Fmd;Ftr;FK;").
Proof using . intros K tr md H. split; [exact H | split; reflexivity]. Qed.
Lemma okside_K : ltac2:(tb__ "0|0|
S1fS34A1S35OF_;F_;S7dVSpecT;R1A2SaeR2A1SafS5Vok;R3A3F_;F_;FK;").
Proof using HokK HokP. intros K HK HV. split; [apply HokK, HK|]. split; [apply HokP, HK | exact HV]. Qed.

Lemma tvL_below : ltac2:(tb__ "0|0|
S1eS74Pf2R1A2S0S20Sa7R2S3dA2S21A3F_;Fn;").
Proof using Hargc JD KH L TVc.
  intros n Hn. cbn.
  replace (241 <? n)%positive with true by (symmetry; apply Pos.ltb_lt; lia). replace (158 <? n)%positive with true by (symmetry; apply Pos.ltb_lt; lia).
  replace (102 <? n)%positive with true by (symmetry; apply Pos.ltb_lt; lia). replace (101 <? n)%positive with true by (symmetry; apply Pos.ltb_lt; lia).
  reflexivity.
Qed.
Lemma tv_eval_eq_L : ltac2:(tb__ "0|5|
S6S6S0S30Q40A1M0S9R1Pf1M1A2S9R2G1A2A3S0G0S9R2P9eM2A2S9R3G2A2A3S0G0S9R3P66M3A2S9R4G3A2A3S0G0S9R4P65M4A2S9R5G4A2A3S92R6R5S3dA3F_;F_;F_;F_;Frho';Frho;").
Proof using . intros rho rho' H1 H2 H3 H4 t Ht. destruct Ht as [<-|[<-|[]]]; cbn [fst snd eval]; rewrite ?H1, ?H2, ?H3, ?H4; split; reflexivity. Qed.
Lemma tv_geo_L : ltac2:(tb__ "0|6|
S6S6S0S30Q40A1M0S9R1Pf1M1A2S9R2G1A2A3S0G0S9R2P9eM2A2S9R3G2A2A3S0G0S9R3P66M3A2S9R4G3A2A3S0G0S9R4P65M4A2S9R5G4A2A3S8fS56R6S3dA3M5G5F_;F_;F_;F_;F_;Frho';Frho;").
Proof using .
  intros rho rho' H1 H2 H3 H4 HG t Ht. pose proof (HG t Ht) as G. unfold tvv in *.
  destruct Ht as [<-|[<-|[]]]; cbn [fst snd eval] in *; rewrite ?H1, ?H2, ?H3, ?H4; exact G.
Qed.

Lemma statics_img : ltac2:(tb__ "0|5|
S1dS1dS8bS27S1dS1dA2M0S26S1dS1dR2R1A4S22G0S26S1dS1dS85S56A1M1S6dG1Z8M2A2A4S22G0S26S1dS1dS86S56A1M3S6dG3G2A2A4S22G0S26S1dS1dS87S56A1M4S6dG4Z1A2A4S28G0A1A3A3A3A3S1S6bS58S56A1R3A2S6bR2S57S56A1A2A2F_;Fhi;Flo;").
Proof using . intros lo hi [H|[H|[H|[]]]]; injection H as <- <-; cbv; split; congruence. Qed.

Lemma statics_disjoint_ins : ltac2:(tb__ "0|6|
S6S1fS8A1M0S8G0S88S56R4S23S8R3R1A3A3S1dS1dS8bS27S1dS1dA2M1S26S1dS1dR2R1A4S22G1S26S1dS1dS85S56A1M2S6dG2Z8M3A2A4S22G1S26S1dS1dS86S56A1M4S6dG4G3A2A4S22G1S26S1dS1dS87S56A1M5S6dG5Z1A2A4S28G1A1A3A3A3A3S1bS1aR8R6A2S26S1dS1dR3R2A4A2F_;Fhi;Flo;S88S56R6S23S8R5S22S8R4R3A3A3A3F_;F_;Fl2;Fo;Fl1;Frho;").
Proof using .
  intros rho l1 o l2 (D1 & D2 & D3) Ho.
  apply Forall_app in D1 as [A1 B1]. apply Forall_app in D2 as [A2 B2]. apply Forall_app in D3 as [A3 B3].
  split; [|split]; apply Forall_app; split; try assumption; constructor; try assumption; apply Ho; cbn; auto.
Qed.

Lemma static3_low : ltac2:(tb__ "0|0|
S1dS89S56R1A2S6cR2Sa6A2F_;Fa;").
Proof using cx. exact (U.Drv_hs__G1.Drv_hs.static3_low cx). Qed.

Definition fork_ne (j : Z) : sprop := ltac2:(tb__ "0|0|
S17Sb3S16Sb2SeP9fA1S11S6eVj;A1A1A3S11Z0A1A3").

Lemma JD_add_null : ltac2:(tb__ "0|4|
S1fS34A1M0S35OF_;M1F_;S6S1fS27SbSbA2M2A1S93G1F_;S6G0S35SbS0S1dS31Q40S1cR4R1A2A2Z0M3A3VJD;R9R8R7R6R5R4R3A7VJD;RaR9S22G2S26SbSbS11G3A1R3A4R8A3R7R6R5R4A7F_;F_;Fe;Fmd;Ftr;Frho;FD;Ftv;Fr0;FK;").
Proof using Hargc KH L P0 TVc.
  intros K r0 tv D rho tr md e He (Ai & (Hav & Hk & HM & HP & (HN & HD & HZ) & HKF & HP0') & HDD). exists Ai. split; [|exact HDD].
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HP|]. split; [|split; [exact HKF | exact HP0']].
  assert (Z0 : ~ tnz rho (SLit 0, e)) by (unfold tnz; cbn [fst eval]; rewrite U_addr by lia; lia).
  split; [|split].
  - constructor; [intros Hnz; exfalso; exact (Z0 Hnz) | exact HN].
  - split; [intros t' _ Hnz _; exfalso; exact (Z0 Hnz) | exact HD].
  - constructor; [intros _; unfold tvv; cbn [fst snd]; exact He | exact HZ].
Qed.

Definition bs1 : list byte := [b8 48].
Definition bs2 : list byte := [b8 10].
Lemma msg_zero_eq : ltac2:(tb__ "0|1|
S0S1fS30Q8A1M0A1S68S23G0S50S51A3A3"). Proof using . reflexivity. Qed.

Lemma Ks_fd1 : ltac2:(tb__ "0|0|
S33S1fS30Q40A1A1S1fS34A1S35S4cVKH;R4R3R2R1A5S0S25S36A1S3cS39R2A1S97A2S24S36S3bS97A1A2A3F_;Fmd;Ftr;Fmat;Fvm;").
Proof using cx. intros vm mat tr md ((_ & Hf & _) & _). change WLout.chw with (Z_to_bv 64 1). rewrite Hf. reflexivity. Qed.

Hypothesis FSUM : fuzz_one_sum_stmt_U.

Hypothesis HL6 : ltac2:(tb__ "0|0|
S6bS6dZ6S6aVF;A1A2VL;A2").
Hypothesis HLM : L < MAX_INPUT.

Lemma normal_in_spec : ltac2:(tb__ "0|0|
VSpecT;S23S34S65Z1S66S63VF;A1A1A2S22S34S67Vfs;Z0A2S28S34A1A3A3A1").
Proof using HL6 HLM inp. exact (U.Drv_r__G1.Drv_r.normal_in_spec cx (conj HL6 HLM)). Qed.

Lemma TR1_prefix : ltac2:(tb__ "0|0|
S9aS34S54S23S34S65Z1S66S63VF;A1A1A2S22S34S67Vfs;Z0A2S28S34A1A3A3A3").
Proof using Hargc JD KH L TVc.
  pose proof (calls_range F) as CR. unfold TR1.
  replace (calls F) with ((calls F - 1) + 1) by lia. rewrite zeros_succ by lia. rewrite wr_app, <- app_assoc. apply is_prefix_app.
Qed.
Lemma KL1_tcons : K_tcons SpecT KL1.
Proof using HL6 HLM. intros tr md (-> & _ & _). exists (wr 1 (zeros (calls F)) ++ [ex fs 0]). split; [exact normal_in_spec | exact TR1_prefix]. Qed.
Lemma plen_range : ltac2:(tb__ "0|1|
S1S6bZ0S64VF;A1M0A2S6cG0S69A2A2").
Proof using HL6 HLM Hargc JD KH TVc. pose proof (config_len_range F). unfold payload_len, HDR_MIN, L, F in *. lia. Qed.

Variable cap : Z.

Definition PAY (rho : valuation) : Prop := ltac2:(tb__ "0|5|
S1S6cZ0M0S64VF;A1M1A2S1S0S30Q40M2A1S9Vrho;Pf0A2S9Vrho;Pf1A2M3A3S3S0S1dS31G2G3A2G0A3M4A1A2F_;S0S1dG1G0A3G4F_;A2").
Definition TL (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S1VTVc;Vcap;Vrho;A2S55Vrho;A1A2").

Lemma TL_rw : ltac2:(tb__ "0|1|
S6S6S1eS74R1Pf1A2S0S30Q40A1S9R3R2A2S9R4R2A2A3F_;Fi;S4dR3A1M0G0F_;F_;Frho';Frho;").
Proof using .
  intros rho rho' Hw [[[(I1 & I2 & I3 & I4 & I5 & I6) [A [B C]]] D] [P1 P2]].
  unfold TL, TVc, U.Drv_ht__G1.Drv_ht.TVc, U.Drv_ht__G1.Drv_ht.TV, PAY, U.Drv_r__G1.Drv_r.INVX, U.Drv_r__G1.Drv_r.UV in *.
  rewrite !Hw by lia.
  split; [split; [split; [exact (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 I6)))))|split; [exact A|split; [exact B|exact C]]]|exact D]|split; [exact P1 | exact P2]].
Qed.
Lemma TL_agree : ltac2:(tb__ "0|1|
S6S6S1eS74Pf2R1A2S18R2R4R3A3S4dR5A1M0G0F_;F_;F_;Fn;Frho';Frho;").
Proof using . intros rho rho' n Hn (Hw & _ & _) HT. apply (TL_rw rho rho'); [intros i Hi; symmetry; apply Hw; lia | exact HT]. Qed.
Lemma TL_vagree : ltac2:(tb__ "0|1|
S6S6S1eS74Pf2R1A2S9dR2R4R3A3S4dR5A1M0G0F_;F_;F_;Fn;Frho';Frho;").
Proof using . intros rho rho' n Hn [Hw _] HT. apply (TL_rw rho rho'); [intros i Hi; symmetry; apply Hw; lia | exact HT]. Qed.

Lemma TL_plen : ltac2:(tb__ "0|0|
S6S4dR1A1S0S1dS31Q40S9R2P9eA2A2S64VF;A1A3F_;Frho;").
Proof using . intros rho [[(_ & _ & B & _) _] _]. exact B. Qed.
Lemma TL_calls : ltac2:(tb__ "0|0|
S6S4dR1A1S0S1dS31Q40S9R2P9fA2A2S63VF;A1A3F_;Frho;").
Proof using . intros rho [[_ D] _]. exact D. Qed.
Lemma TL_cap : ltac2:(tb__ "0|0|
S6S4dR1A1S1S0S1dS31Q40S9R2P65A2A2Vcap;A3S90Vcap;A1A2F_;Frho;").
Proof using . intros rho [[((I1 & I2 & I3 & I4 & I5 & I6) & _) _] _]. split; [exact I2 | exact I6]. Qed.

Let P0_now := U.Drv_hs__G1.Drv_hs.P0_now cx.
Let P0_transport := U.Drv_hs__G1.Drv_hs.P0_transport cx.

Definition SIDEL (v : positive) (rho : valuation) (g : Z) (vm : VmMaps) (mat : list word) : Prop := ltac2:(tb__ "0|1|
S1S91S5S56VP0;Vwtop;S3dS62Vrho;Vvm;Vmat;A9S1S8fS56Vrho;S3dA3S1S8aS5S56S10Vrho;A1Vg;A4S1S0S30Q40M0A1S9Vrho;Vv;A2S32G0Vg;A2A3S4dVrho;A1A2A2A2A2").

Lemma SIDEL_transport : ltac2:(tb__ "0|1|
S1eS6S6S1dS33S1fS30Q40A1M0A1S4eR6R5R3R2R1A5S1eS74R1R8A2S0G0S9R7R2A2S9R8R2A2A3F_;Fi;S76Pf1R8A2G0S0S25S30Q8A1A1S10R8R1A2S10R9R1A2A3Fa;S4eRaR8R7R6R5A5F_;F_;F_;F_;Fmat;Fvm;Fg;Frho';Frho;Fv;").
Proof using .
  intros v rho rho' g vm mat (HS & HG & HV & Hv & HT) Hw Hv' Hm.
  assert (RD : forall a, rd_of segs (rm rho') a = rd_of segs (rm rho) a) by (intros a; unfold rd_of; rewrite Hm; reflexivity).
  assert (WK : forall a, wok_of segs (rm rho') a = wok_of segs (rm rho) a) by (intros a; unfold wok_of; rewrite Hm; reflexivity).
  split; [|split; [|split; [|split]]].
  - apply (snapJ_transport segs C_U P0 malloc_laws_U wtop tvL DTrue rho rho' vm mat HS).
    + apply tv_eval_eq_L; apply Hw; lia.
    + exact RD.
    + exact WK.
    + destruct HS as (Ai & md & _ & _ & _ & HP0 & _). apply (P0_transport rho rho' HP0); [intros i Hi; apply Hw; lia | intros a _; apply Hm].
  - apply (tv_geo_L rho rho'); [apply Hw; lia | apply Hw; lia | apply Hw; lia | apply Hw; lia | exact HG].
  - apply (statics_view_rm segs C_U statics_layout_U (rm rho) (rm rho') g); [intros a _; apply Hm | exact HV].
  - rewrite Hw by lia. exact Hv.
  - apply (TL_rw rho rho'); [intros i Hi; apply Hw; lia | exact HT].
Qed.
Lemma SIDEL_agree : ltac2:(tb__ "0|0|
S1eS1eS6S6S1dS33S1fS30Q40A1A1S4eR7R5R3R2R1A5S18R7R6R5A3S76R9R8A2S76Pf1RaA2S4eRbR8R7R6R5A5F_;F_;F_;F_;Fmat;Fvm;Fg;Frho';Frho;Fn;Fv;").
Proof using .
  intros v n rho rho' g vm mat HS (Hw & _ & Hm) Hn Hv.
  apply (SIDEL_transport v rho rho' g vm mat HS); [intros i Hi; symmetry; apply Hw; lia | exact Hv | intros a; symmetry; apply Hm].
Qed.

Lemma pay_disjoint : ltac2:(tb__ "0|0|
S6S1dS1dS4dR3A1S8fS56R4S3dA3S6bS58S56A1R4A2S6bR4S57S56A1A2S1bS1aR7S41A2S26S1dS1dR6R5A4A2F_;F_;F_;F_;Fhi;Flo;Frho;").
Proof using HL6 HLM.
  intros rho lo hi HT HG Hlo Hhi. pose proof (TL_plen rho HT) as V158. destruct HT as [_ [P1 P2]]. pose proof plen_range as PR.
  unfold obj_range, obj_lo_of, obj_hi_of, O_payL. cbn [ob_base ob_lo ob_hi eval].
  rewrite soff_lit_small by lia. rewrite (soff_var rho 158) by (rewrite V158; unfold MAX_INPUT in PR; lia). rewrite V158.
  unfold ranges_disjoint. cbn [fst snd].
  destruct (Z.eq_dec (payload_len F) 0) as [Z0|NZ]; [lia|].
  destruct (P1 ltac:(lia)) as [E240 NZ241].
  destruct (HG (SVar 241, SVar 158) ltac:(left; reflexivity)) as [_ G2]. cbn [fst snd eval] in G2. unfold tvv in G2. cbn [fst snd eval] in G2.
  rewrite E240. pose proof (G2 NZ241) as G. rewrite V158 in G. unfold IB, UNIT in G. lia.
Qed.

Lemma fz_call : ltac2:(tb__ "0|5|
S1fS34A1S35OF_;F_;S6S7S7fS1fS8A1M0S6S60S7dVSpecT;R7A2SaeR8A1S0S25G0A1S9bR7S3eR6A3S24G0R5A2A3S0S20Sa0S56P1fR8S3eR7R6S7bS27S7S1fS27SbSbA2A1M1A2M2S7S29S7G1A2S3fA4A7S21A3S0S20S9eR8S77A2S21A3S0S20S8cG2G2S2cSa3S77RaSaRbA1S29S7G1R1A3M3S2eS7G1R1A3M4A5Sa1S3eG3G4A3A2Ld;S3fA3S21A3S0S20Sa2SdRbA1S3dS2aS2bA1S46R9A5S21A3S74Pf2SaRcA1A2S0SbS7eRcPcA2SePf0A1A3S0SbS7eRdPdA2SeP9eA1A3S4dRcA1S1dS6S8bS1dR2S82S80A1A3S9dSaR13A1R10R2A3S5eS5Vok;S5aS5VJD;R16R15S3dS62A4S9fS77R14R13R12S81S80R4A2A5R3A4R10A4F_;F_;Frho';Fr;S5eS5Vok;S5aS5VJD;R13R12S3dS62A4R11ReA4RdA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Frho;FR;Fs;FCl;Fr0;FK;").
Proof using FSUM HL6 HLM.
  intros K r0 Cl s R rho Q HK HV He Hchk Hdom Hpd Hrchk Hnx Hs12 Hs13 HT CONT.
  pose proof (TL_plen rho HT) as V158. destruct HT as [_ [P1 P2]].
  eapply triple_conseq with (P := SPJ segs (JG segs C_U 31 K r0 P0 [] (tvL ++ [])) Cl rho); [| intros w Hw; exact Hw |].
  { intros w [Hsm HJ]. split; [exact Hsm|]. rewrite app_nil_r. exact (JGD_JG segs C_U 31 K r0 P0 tvL DTrue _ _ _ HJ). }
  apply (client_callJ segs C_U 31 K r0 P0 [] malloc_laws_U P0_fz PreFZ [] PDfz NF eq_refl
           (fun ok' FBc rho1 Hok' => FSUM ok' K FBc rho1 Hok') ok Cl s R rho tvL [] Q).
  - exact (okside_K K HK HV).
  - exact He.
  - exact Hchk.
  - exact Hdom.
  - apply Pos.leb_le. lia.
  - rewrite app_nil_r. apply tvL_below. lia.
  - reflexivity.
  - exact Hpd.
  -
    intros Ai ms HFa _ Hav _ _ _ HZ _ HT. rewrite app_nil_r in HZ. split.
    + apply (robjs_checkF_sound segs C_U r0 [] rho (ss_facts Cl) tvL robj_inwi R HFa (T_ok_T0_31 r0 rho _ Hav HT) HZ Hrchk).
      intros o a _ Hr Ha. right; left. exact (robj_inwi_img rho o a Hr Ha).
    + unfold P0_fz, payload_cov. rewrite !rw_call', Hs12, Hs13. cbn [eval]. rewrite V158.
      destruct (Z.eq_dec (payload_len F) 0) as [Z0|NZ]; [left; exact Z0 | right].
      pose proof plen_range as PR. destruct (P1 ltac:(lia)) as [E240 NZ241].
      exists (bv_unsigned (rw rho 241)), (bv_unsigned (rw rho 158)). split; [|rewrite E240, V158; lia].
      apply (proj2 (In_FBx [] rho tvL _)). right. exists (SVar 241, SVar 158).
      split; [left; reflexivity|]. split; [exact NZ241 | reflexivity].
  -
    intros d rho' Hd Hag. unfold PDfz, PD_fuzz in Hd. apply in_map_iff in Hd as (r & <- & Hr). cbn [fst snd import_tv map]. rewrite app_nil_r.
    eapply triple_conseq; [| intros w Hw; exact Hw | exact (CONT r rho' Hr Hag)].
    intros w [Hsm HJ]. split; [exact Hsm|]. exact (JG_JGD segs C_U 31 K r0 P0 tvL _ _ _ HJ).
Qed.

Lemma toS : ltac2:(tb__ "0|8|
S1fS34A1M0S35OF_;F_;S6S7S7S6G0Sb1S35S0S7S84R6S83S56SaR6A1M1A2S75G1A1A3R5A3S0S20S13R6A1S21A3S0S20S8eS56SdR8A1S3dS23S8S79S8U2M2SfR8A1M3A3S7aS8U3M4G3A3A3A4S21A3S0S1fS8A1SfR9A1M5S23S8S79S8G2G5A3S22S8S41S7aS8G4G5A3A3A3A3S74Pf2SaRaA1A2S4dR9A1S5aS5VJD;ReRdS3dS62A4RcRaS26G0S98R9S99R8R7A2A4A5S4S6S6S4S1dS1dS1S4eSaRfA1R2R1S38RaA1M6S37RaA1M7A5S59S5S4cR11G6G7A3ReR2S26G0S98RcS99RbRaA2A4A5A2Lg;A2Lrho1;A2F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;FPS;FP;Fr0;FK;").
Proof using HL6 HLM.
  intros K r0 P PS rho tr ms md HPS Hwf Hmiss Hobjs Hnx HT [Hsm (Ai & HJi & _)].
  pose proof HJi as (Hav & Hk & [HM [Hi HTPI]] & HP & HN & HKF & HP0').
  pose proof (P0_now _ _ _ _ _ _ _ HJi) as HP0.
  pose proof (tv_geo_of_JGi segs C_U 31 K r0 P0 tvL Ai rho tr md HJi) as HG.
  destruct (statics_view_of_MInvR segs C_U Ai rho md HM) as [g Vg].
  assert (HD : statics_disjoint C_U rho (ss_objs P)).
  { rewrite Hobjs. apply statics_disjoint_ins.
    - exact (robjs_missT_statics_sound C_U P0 (ss_facts P) tvL (firstn 2 (ss_objs P) ++ skipn 3 (ss_objs P)) rho HG (smatch_facts_hold segs _ _ _ Hsm) Hmiss).
    - intros lo hi Hin. destruct (statics_img lo hi Hin) as [H1 H2]. exact (pay_disjoint rho lo hi HT HG H1 H2). }
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U rho P (tr, mkCfg ms md) g (ss_next P) (Pos.succ (ss_next P)) Hsm
              ltac:(lia) Vg HD ltac:(rewrite HPS; exact Hwf)) as [Hsm' Hag].
  set (rho1 := rho_set_rw rho (ss_next P) (Z_to_bv 64 g)) in *.
  assert (RW : forall i, i <> ss_next P -> rw rho1 i = rw rho i) by (intros i Hi'; subst rho1; apply rho_set_rw_other; exact Hi').
  exists rho1, g. split.
  - destruct (deJ segs C_U 31 P0 wtop P0_top K r0 tvL DTrue Ai rho tr md HJi I HP0) as [HSn _].
    split; [|split; [|split; [|split]]].
    + apply (snapJ_transport segs C_U P0 malloc_laws_U wtop tvL DTrue rho rho1 _ _ HSn).
      * apply tv_eval_eq_L; apply RW; lia.
      * intros a; reflexivity.
      * intros a; reflexivity.
      * apply (P0_transport rho rho1 HP0); [intros i Hi'; apply RW; lia | intros a _; reflexivity].
    + apply (tv_geo_L rho rho1); [apply RW; lia | apply RW; lia | apply RW; lia | apply RW; lia | exact HG].
    + exact Vg.
    + subst rho1. apply rho_set_rw_at.
    + apply (TL_rw rho rho1); [intros i Hi'; apply RW; lia | exact HT].
  - split; [rewrite <- HPS; exact Hsm' | apply Ks_intro; exact Hk].
Qed.

Lemma fromN : ltac2:(tb__ "0|2|
S1fS34A1M0S35OF_;F_;S7S7S1eS6S1dS33S1fS30Q40A1A1G0Sb1S35S0S1fS8A1SfRaA1M1S23S8SfR9A1S83S56R8A2A3A3S0S20S9cS73RbG1A2RaS28S27S1eSbA2A1A3S21A3S76Pf1RaA2S4eRbRaR9R8R7A5S59S5S4cRfR9R8A3ReRbS26G0S98R7S99R6R5A2A4A5S4S6S6S1S4dR1A1S5aS5VJD;R11R1S3dS62A4RfR1S26G0S98R9S99R8R7A2A4A5A2Lrho';A2F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Fmat;Fvm;Fg;Frho;Fv;FS;FN;FK;").
Proof using .
  intros K N S v rho g vm mat tr ms md HN He Hv (HSn & HG & HV & Hvv & HT) [Hsm (Hk & Hvm & Hmat)].
  destruct (release_statics segs C_U statics_layout_U statics_wseg_U rho N (tr, mkCfg ms md) (ss_objs S) g v Hsm HN HV Hvv)
    as (m' & Hsm1 & Hout & RD & WK & _).
  pose proof (entails_sound segs _ _ [] _ _ He Hsm1) as Hsm2.
  set (rho' := rho_sub (set_rm rho m') []) in *.
  assert (RW : forall i, rw rho' i = rw rho i) by (intros i; reflexivity).
  assert (RM : rm rho' = m') by reflexivity.
  exists rho'. split; [exact (TL_rw rho rho' (fun i _ => RW i) HT)|]. split; [exact Hsm2|].
  unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
  apply (reJ segs C_U 31 P0 wtop P0_top P0_tp K tvL DTrue rho' vm mat tr md); [| exact Hvm | exact Hmat | intros; exact I | exact Hk].
  apply (snapJ_transport segs C_U P0 malloc_laws_U wtop tvL DTrue rho rho' vm mat HSn).
  - apply tv_eval_eq_L; apply RW.
  - intros a. rewrite RM. apply RD.
  - intros a. rewrite RM. apply WK.
  - destruct HSn as (Ai & md' & _ & _ & _ & HP0 & _). apply (P0_transport rho rho' HP0); [intros i _; apply RW|].
    intros a Ha. rewrite RM. apply Hout. intros Hs3. apply static3_low in Hs3. unfold wz in Hs3. rewrite U_addr in Hs3 by (unfold aceil in Ha; lia). lia.
Qed.

Lemma fork_val : ltac2:(tb__ "0|2|
S6S1dScS4dR3A1S1S6bZ1R3A2S6bR3Z4A2A2S19R5R3A2S1S0ScR4S17Sb3S16Sb2SeP9fA1S11S6eR5A1A1A3S11Z0A1A3M0A3S3S0S1dS63VF;A1R6A3M1A1F_;S0ScR4S12G0A1A3G1F_;A2F_;F_;F_;Fp;Fj;Frho;").
Proof using .
  intros rho j p HT Hj Hp. pose proof (TL_calls rho HT) as V159. pose proof (calls_range F) as CR.
  assert (E : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 159) (SLit (- j)))) = (calls F - j) mod M64v).
  { rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite V159. unfold M64v.
    replace ((- j) mod 18446744073709551616) with (18446744073709551616 - j)
      by (apply (Zmod_unique (- j) 18446744073709551616 (-1)); lia).
    replace (calls F + (18446744073709551616 - j)) with ((calls F - j) + 1 * 18446744073709551616) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  assert (Z0 : (calls F - j) mod M64v = 0 <-> calls F = j).
  { unfold M64v. split; [|intros ->; rewrite Z.sub_diag; reflexivity]. intros Hm.
    destruct (Z_lt_le_dec (calls F - j) 0).
    - exfalso. rewrite <- (Zmod_unique (calls F - j) 18446744073709551616 (-1) (calls F - j + 18446744073709551616)) in Hm; lia.
    - rewrite Z.mod_small in Hm; lia. }
  split; intros ->.
  - apply holds_bne in Hp. rewrite E, CursorGlue.U_lit in Hp. change (0 mod M64v) with 0 in Hp. intros Hc. apply Hp. apply (proj2 Z0). exact Hc.
  - apply holds_nbne in Hp. rewrite E, CursorGlue.U_lit in Hp. change (0 mod M64v) with 0 in Hp. apply (proj1 Z0). exact Hp.
Qed.

Lemma post_go : ltac2:(tb__ "0|c|
S1dS1fS34A1S35OF_;F_;S6S7S7S7S7S1eS6S7dVSpecT;R8A2S0S7S84R7S83S56SaR7A1M0A2S75G0A1A3R6A3S0S20S13R7A1S21A3S0S20S8eS56SdR9A1S3dS23S8S79S8U2M1SfR9A1M2A3S7aS8U3M3G2A3A3A4S21A3S0S1fS8A1SfRaA1M4S23S8S79S8G1G4A3S22S8S41S7aS8G3G4A3A3A3A3S0S1eSaRbA1M5R7A3S0S1eG5S75R8A1A3S0S20S15RcA1S2dA3S74Pf2RaA2S0S25S1fS6fA1M6A1S72S5SacS44ReS21A5S24G6S22S6fS71RdS70A2S22S6fS71RcS70A2S28S6fA1A3A3A2A3S0S25ScA1M7S8dScSdReA1U0A3M8S24ScS52R13A1A2A3S0G7G8S24ScS12S52R14A1A1A2A3S1S6bZ1R15A2S6bR15Z4A2A2S4dReA1S6S1dS33S1fS30Q40A1A1M9S4eR14R4R3R2R1A5S3S0S1dS63VF;A1MaR1cA3A1S5eS5Vok;S59S5S4cR1cR4R3A3R18R6A4S5fS2L_;MbA4F_;F_;Fmat;Fvm;Fg;Frho2;S6S1dS33G9S4eR15R4R3R2R1A5S0S1dGaR1dA3S5eS5Vok;S59S5S4cR1dR4R3A3R18R6A4GbA4F_;F_;Fmat;Fvm;Fg;Frho2;S5eS5Vok;S5aS5VJD;R18R17S3dS62A4R16R11A4GbA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;FNX;FXn;FNn;FPS;FP;Fr0;FK;Fj;").
Proof using HL6 HLM.
  intros j K r0 P PS Nn Xn NX rho HK HPS Hwf Hmiss Hobjs HnxP HnxPS HlnPS Hnx Hrun HfN HfX Hj HT HN HX.
  apply (triple_from ok _ (fun r w => exists g vm mat, SIDEL NX r g vm mat /\ SP segs (Ks K vm mat) PS r w)).
  { intros [tr [ms md]] Hw. destruct (toS K r0 P PS rho tr ms md HPS Hwf Hmiss Hobjs ltac:(rewrite HnxP; exact Hnx) HT Hw) as (rho1 & g & HS & HP').
    exists rho1, g, (m_vmmaps md), (m_vm_materialized md). rewrite <- HnxP. split; assumption. }
  intros rho1. apply triple_ex. intros g. apply triple_ex. intros vm. apply triple_ex. intros mat. apply triple_pure. intros HS1.
  eapply (run_tr ok); [exact Hrun | exact HlnPS | apply Ks_okf; exact HK |].
  rewrite HnxPS. intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state];
    pose proof (SIDEL_agree NX (Pos.succ NX) rho1 rho2 g vm mat HS1 Hag2 ltac:(lia) ltac:(lia)) as HS2;
    apply triple_facts; intros HF2.
  - pose proof (Forall_nth_error _ _ _ _ HF2 HfN) as Hf.
    apply (HN rho2 g vm mat HS2). exact (proj1 (fork_val rho2 j _ (proj2 (proj2 (proj2 (proj2 HS2)))) Hj Hf) eq_refl).
  - pose proof (Forall_nth_error _ _ _ _ HF2 HfX) as Hf.
    apply (HX rho2 g vm mat HS2). exact (proj2 (fork_val rho2 j _ (proj2 (proj2 (proj2 (proj2 HS2)))) Hj Hf) eq_refl).
Qed.

Lemma iter_gen : ltac2:(tb__ "0|10|
S1dS6S7S7S7S7fS1fS8A1M0S1eS6S0S25G0A1S9bR7S3eR4A3S24G0R3A2A3S1S0S20Sa0S56P1fR8S3eR5R4S7bS27S7S1fS27SbSbA2A1M1A2M2S7S29S7G1A2S3fA4A7S21A3S1S0S20S9eR5S77A2S21A3S1S0S20S8cG2G2S2cSa3S77R6SaR9A1S29S7G1R1A3M3S2eS7G1R1A3M4A5Sa1S3eG3G4A3A2Ld;S3fA3S21A3S0S20Sa2SdR8A1S3dS2aS2bA1S46R4A5S21A3A2A2A2S0SbS7eR6PcA2SePf0A1A3S0SbS7eR7PdA2SeP9eA1A3S74Pf2SaRbA1A2S1dS8bS1dR1S82S80A1A3S4S7S7S4S7S7S1S0S7S9fS77R10RdRcS81S80R4A2A5R2A3S1S0S7S84R2S83S56SaR2A1M5A2S75G5A1A3R1A3S1S0S20S13R1A1S21A3S1S0S20S8eS56SdR2A1S3dS23S8S79S8U2SfR2A1M6A3M7S7aS8U3G6A3M8A3A4S21A3S1S0G0G6S23S8G7S22S8S41G8A3A3A3S1S0S1eG5RbA3S1S0S1eSaR1A1S75RbA1A3S1S0S20S15R1A1S2dA3S0S25S1fS6fA1M9A1S72S5SacS44R1S21A5S24G9S22S6fS71RfS70A2S22S6fS71ReS70A2S28S6fA1A3A3A2A3A2A2A2A2A2A2A2A2LPS;A2LP;A2F_;Fr;S74SaRdA1R8A2S0S25ScA1MaS8dScSdRdA1U0A3MbS24ScS52R10A1A2A3S0GaGbS24ScS12S52R11A1A1A2A3S1S6bZ1R12A2S6bR12Z4A2A2S4dRbA1S6S1dS33S1fS30Q40A1A1McS4eR11R4R3R2R1A5S3S0S1dS63VF;A1MdR19A3A1S5eS5Vok;S59S5S4cS4fR4R3A3R17R6A4S5fS2L_;MeA4MfF_;F_;Fmat;Fvm;Fg;Frho2;S6S1dS33GcS4eR12R4R3R2R1A5S0S1dGdR1aA3GfF_;F_;Fmat;Fvm;Fg;Frho2;S5eS5Vok;S5aS5VJD;S4fR15S3dS62A4R14ReA4GeA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;FNX;FR;Fs;FXn;FNn;FS;Fr0;Fj;").
Proof using FSUM HL6 HLM.
  intros j r0 S Nn Xn s R NX rho He (Hchk & Hdom & Hpd & Hrchk) Hs12 Hs13 HnxS POSTS HSN HfN HfX Hj HT HN HX.
  apply (fz_call KL1 r0 S s R rho _ KL1_tcons KL1_vmi He Hchk Hdom Hpd Hrchk HnxS Hs12 Hs13 HT).
  intros r rho' Hr Hag. destruct (POSTS r Hr) as (P & PS & HP & HPS & Hwf & Hmiss & Hobjs & HnxP & HnxPS & HlnPS & Hrun). rewrite HP.
  apply (post_go j KL1 r0 P PS Nn Xn NX rho' KL1_tcons HPS Hwf Hmiss Hobjs HnxP HnxPS HlnPS ltac:(lia) Hrun HfN HfX Hj); [|exact HN|exact HX].
  exact (TL_vagree rho rho' (ss_next S) HnxS Hag HT).
Qed.

Lemma Kw_trace : ltac2:(tb__ "0|3|
S33S1fS30Q40A1M0A1M1S2bS1fS34A1M2S35S94S4cVKH;R5R4A3S50S51R3R2R1A6S1S0G2R3S65Z1S79S30Q8A1R4S68A3A2A3S1S0S1fS27G0S36A2A1S39R2A1SbeA3S1S0Sb0S3aR2A1Vfs;A3S1S0S33S38R2A1R6A3S0G1S37R2A1R5A3A2A2A2A2F_;Fmd;Ftr;Fk;Fmat;Fvm;").
Proof using inp.
  intros vm mat k tr md (tr0 & ((-> & Hf & Hs) & Hv & Hm) & ->). split; [|auto]. unfold WLout.TRk, WLout.MSG, wr. rewrite msg_zero_eq. reflexivity.
Qed.
Lemma Kw_tcons : ltac2:(tb__ "0|0|
S33S1fS30Q40A1A1S2bS7dVSpecT;S94S4cVKH;R3R2A3S50S51R1A4A2Fk;Fmat;Fvm;").
Proof using HL6 HLM Hargc JD TVc cap fs.
  intros vm mat k tr md HK. destruct (Kw_trace vm mat k tr md HK) as (-> & _). exists (wr 1 (zeros (calls F)) ++ [ex fs 0]). split; [exact normal_in_spec|].
  pose proof (calls_range F) as CR. replace (calls F) with ((calls F - 1) + 1) by lia. rewrite zeros_succ by lia.
  rewrite <- (firstn_skipn k msg_zero) at 2. rewrite !wr_app, <- !app_assoc. apply is_prefix_app.
Qed.
Lemma Kw_KL1 : ltac2:(tb__ "0|0|
S33S1fS30Q40A1A1S1fS34A1S35S94S4cVKH;R4R3A3S50S51S2fS30Q8A1S95S50S51A2A2R2R1A6S4cS4fR5R4R3R2A5F_;Fmd;Ftr;Fmat;Fvm;").
Proof using .
  intros vm mat tr md HK. destruct (Kw_trace vm mat _ tr md HK) as (-> & Hf & Hs & Hv & Hm).
  split; [|split; [exact Hv | exact Hm]]. split; [|split; [exact Hf | exact Hs]]. unfold WLout.MSG, bs1, bs2. reflexivity.
Qed.
Definition PRw (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S1S0S1fS30Q8A1A1M0S14Vrho1;P5A2S50A3S1S0G0S14Vrho1;P6A2S51A3S1S0S1dS31Q40M1S9Vrho1;PdA2A2Z1M2A3S0S1dS31G1S9Vrho1;PfA2A2G2A3A2A2A2").

Lemma wl2_call : ltac2:(tb__ "0|1|
S33S1fS30Q40A1A1S6S53R1A1S5eS5Vok;S59S5S4cVKH;R4R3A3M0SadR2A4S5bS5S94G0S50S51S2fS30Q8A1S95S50S51A2A2A4SaSadA1R2S96A5A4F_;Frho1;Fmat;Fvm;").
Proof using HL6 HLM Hargc HokK HokP JD P0 TVc cap fs.
  intros vm mat rho1 (H5 & H6 & H13 & H15).
  apply (WLout.wl2_sum ok (Ks KH vm mat) rho1 bs1 bs2 H5 H6 H13 H15).
  - unfold WLout.MSG, max_write_total. cbn. lia.
  - intros k. apply HokK, Kw_tcons.
  - intros k. apply HokP, Kw_tcons.
  - apply Ks_fd1.
  - cbn. lia.
Qed.

Lemma wc_intro : ltac2:(tb__ "0|5|
S33S1fS30Q40M0A1M1A1S6S5fS4dR2A1S8fS56R3S3dA3S59S5S4cVKH;R6R5A3S48R4R3A5S4S6S6S1S1S0S1fS30Q8A1M2A1M3S14R1P5A2S50A3S0G3S14R1P6A2S51A3A2S1S1eS0G1S9R2R1A2S9R7R1A2A3Fi;S1G1S0S25G2A1M4S10R2R1A2S10R7R1A2A3Fa;S1S1dS1S6bZ0R1A2S6cR1Z1A2A2S0G4S10R3S32G0S6dSb4R2A2A2A2S2aG2A1A3F_;Fk;S59S5S4cVKH;R8R7A3S49R1R5A5A2A2A2A2Lrho';A2F_;F_;F_;Fw;Frho;Fmat;Fvm;").
Proof using HL6 HLM.
  intros vm mat rho [tr [ms md]] HT HG [Hsm Hk]. destruct norl_w as [N5 N6]. destruct E_w_facts as (Fc & F3 & F2 & Nc & N3 & N2 & _).
  destruct obj14_w as (O14 & CB & BL). destruct E_w_shape as (_ & _ & R13 & R12 & _).
  pose proof (smatch_xforms segs xs_w rho E_w E_w1 _ xs_w_ok Hsm) as H1.
  pose proof (smatch_unbase segs rho E_w1 2 _ E_w2 _ unb_w H1) as H2.
  pose proof (smatch_obj_to_list segs rho E_w2 _ 16 5 _ stdout_buf (stdout_buf + 1) BL_w H2 O14 eq_refl eq_refl ltac:(unfold stdout_buf; lia) ltac:(unfold stdout_buf; lia) eq_refl eq_refl CB N5) as H3.
  rewrite E_w3_eq, BL in H3. set (rho5 := rho_set_rl rho 5 [Z_to_bv 8 48]) in H3.
  set (rho' := rho_set_rl rho5 6 bs2).
  assert (H3' : smatch segs rho' E_w3 (tr, mkCfg ms md)) by (apply smatch_set_rl; [exact N6 | exact H3]).
  assert (RW : forall i, rw rho' i = rw rho i) by (intros i; reflexivity).
  assert (RM : forall a, rm rho' a = rm rho a) by (intros a; reflexivity).
  assert (HT' : TL rho') by (apply (TL_rw rho rho' (fun i _ => RW i) HT)).
  assert (HG' : tv_geo C_U rho' tvL).
  { subst rho' rho5. apply tv_geo_set_rl; [reflexivity|]. apply tv_geo_set_rl; [reflexivity|]. exact HG. }
  pose proof (robjs_missT_sound C_U P0 (ss_facts E_w) tvL nl_addr (nl_addr + 1) (firstn 4 (ss_objs E_w3) ++ skipn 5 (ss_objs E_w3)) rho' HG'
                ltac:(rewrite <- F3; exact (smatch_facts_hold segs _ _ _ H3')) missT_nl) as Hdisj0.
  assert (Hdisj : Forall (fun o' => ranges_disjoint (obj_range rho' o') (nl_addr, nl_addr + 1)) (ss_objs E_w3)).
  { assert (EO : ss_objs E_w3 = firstn 4 (ss_objs E_w3) ++ O_payL :: skipn 5 (ss_objs E_w3)) by reflexivity.
    rewrite EO. apply Forall_app in Hdisj0 as [D1 D2]. apply Forall_app. split; [exact D1|]. constructor; [|exact D2].
    apply (pay_disjoint rho' nl_addr (nl_addr + 1) HT' HG'); cbv; congruence. }
  assert (RO : forall k, 0 <= k < 1 -> ro_addr segs (Z_to_bv 64 (nl_addr + k)) = true).
  { intros k Hk'. apply (U.Drv_hs__G1.Drv_hs.rom_ro nl_addr bs2 rom_nl). cbn. lia. }
  assert (RN : forall k, 0 <= k < 1 -> rm rho' (Z_to_bv 64 (nl_addr + k)) = None).
  { apply (U.Drv_hs__G1.Drv_hs.rom_rm_none cx rho' E_w3 tr ms md nl_addr 1 H3' Hdisj); [unfold nl_addr; lia | unfold nl_addr; lia | exact RO]. }
  exists rho'. split; [|split; [exact RW | split; [exact RM | split; [exact RN|]]]].
  { split; reflexivity. }
  split; [|exact Hk].
  rewrite <- E_wc_eq. unfold app_objs.
  apply (ReprGlue.smatch_carve_rom segs rho' E_w3 _ nl_addr 1 6 (ss_next E_w3) H3').
  - exact swf_E_wc.
  - unfold nl_addr. lia.
  - lia.
  - unfold nl_addr. lia.
  - reflexivity.
  - intros k Hk0. apply (rom_bytes_ok_sound segs nl_addr bs2 rom_nl). cbn. lia.
  - exact Hdisj.
Qed.

Lemma tw_intro : ltac2:(tb__ "0|1|
S1fS34A1S35OF_;F_;S6S5fS7cScS19R2A1SdS48A1A3S1dS1S6bZ0R1A2S6cR1Z1A2A2S0S25S30Q8A1M0A1S10R5S32Q40S6dSb4R2A2A2A2S2aG0A1A3F_;Fk;S59S5R5S4bR4R3A5S59S5R6S4aR5R4A5F_;F_;F_;Fw;Frho;FK;").
Proof using Hargc JD KH L P0 TVc cap.
  intros K rho [tr [ms md]] HFw RN [Hsm Hk]. split; [|exact Hk].
  pose proof (smatch_xforms segs xs_wd rho (add_facts (ss_facts E_w) T_wDi) T_wDm _ xs_wd_ok (smatch_add_facts segs rho (ss_facts E_w) T_wDi _ Hsm HFw fb_wd)) as H1.
  pose proof (smatch_unbase segs rho T_wDm 1 _ T_wDu _ unb_wd H1) as H2.
  pose proof (smatch_obj_forget segs rho T_wDu _ 12 H2) as H3. rewrite T_wDf_eq in H3.
  destruct T_wDr_eq as (RE & O10 & WF).
  assert (H4 : SPJ segs (liftK K) T_wDr rho (tr, mkCfg ms md)).
  { rewrite <- RE. apply (SPJ_reshape segs (liftK K) rho T_wDf 12 _ O_b1z _ O10 eq_refl eq_refl eq_refl WF); [|split; [exact H3 | exact Hk]].
    intros _. unfold obj_range, obj_lo_of, obj_hi_of, O_b1z. cbn [ob_base ob_lo ob_hi eval]. rewrite !U_addr by (unfold stdout_buf; lia). rewrite !soff_lit_small by (unfold stdout_buf; lia). lia. }
  destruct H4 as [H4 _].
  pose proof (smatch_xforms segs [XMerge 12] rho T_wDr T_wM _ xs_wm_ok H4) as H5.
  destruct T_wM_objs as [OM WT]. rewrite <- T_w_eq.
  apply (U.Drv_hs__G1.Drv_hs.smatch_drop_rom cx rho T_wM _ (ss_objs T_w) nl_addr 1 6 _ H5 OM); [unfold nl_addr; lia | lia | unfold nl_addr; lia | | exact RN | rewrite T_w_eq; exact WT].
  intros k Hk'. apply (U.Drv_hs__G1.Drv_hs.rom_ro nl_addr bs2 rom_nl). cbn. lia.
Qed.

Lemma printf0_safe : ltac2:(tb__ "0|5|
S6S1dS33S1fS30Q40A1A1M0S4eS40R4R3R2R1A5M1S6S1dS33G0G1S3S0S1dS63VF;A1Z1A3M2A1S5eS5Vok;S59S5S4cS4fR4R3A3M3S45R6A4S5fS2L_;M4A4F_;F_;Fmat;Fvm;Fg;Frho2;S6S1dS33G0G1G2S5eS5Vok;S59S5G3S43R6A4G4A4F_;F_;Fmat;Fvm;Fg;Frho2;S5eS5Vok;S59S5S4cVKH;R5R4A3S47R7A4G4A4F_;F_;F_;Fmat;Fvm;Fg;Frho1;").
Proof using HL6 HLM.
  intros rho1 g vm mat HS1 HN HX. destruct nexts_w as (NxIo & NxPio & NxW & NxWc & LtDi & NxTw & Lt241). apply Pos.ltb_lt in LtDi. apply Pos.ltb_lt in Lt241.
  pose proof (Pos.lt_succ_diag_r NX0) as LtS.
  destruct cert_io as (Hi & _ & H17 & H10 & H11). destruct P_io_shape as [_ LnPio].

  eapply triple_seq.
  { apply triple1_triple. apply (triple1_ioctl_example segs ok (Ks KH vm mat) E_io rho1); [apply Ks_okf, KH_tcons | apply Ks_okp, KH_tcons | exact Hi | rewrite H17; reflexivity | | rewrite H11; reflexivity].
    intros tr md ((_ & Hf & _) & _). rewrite H10, Hf. eexists. reflexivity. }
  rewrite P_io_eq.

  eapply (run_tr ok); [exact run_Pio | exact LnPio | apply Ks_okf, KH_tcons |].
  rewrite NxPio. intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  pose proof (SIDEL_agree NX0 _ rho1 rho2 g vm mat HS1 Hag2 LtS Lt241) as HS2.
  apply (triple_from ok _ (fun r w => (SIDEL NX0 r g vm mat /\ rl r 5 = bs1 /\ rl r 6 = bs2 /\ (forall k, 0 <= k < 1 -> rm r (Z_to_bv 64 (nl_addr + k)) = None)) /\ SP segs (Ks KH vm mat) E_wc r w)).
  { intros w Hw. destruct (wc_intro vm mat rho2 w (proj2 (proj2 (proj2 (proj2 HS2)))) (proj1 (proj2 HS2)) Hw) as (r & [A B] & Hrw & Hrm & RN & HS).
    exists r. split; [|exact HS]. split; [exact (SIDEL_transport NX0 rho2 r g vm mat HS2 (fun i _ => Hrw i) Lt241 Hrm)|]. auto. }
  intros rho3. apply triple_pure. intros (HS3 & H5 & H6 & RN3).
  destruct s_w_vals as (S12 & S13 & S14 & S15). destruct E_w_facts as (Fc & F3 & F2 & Nc & N3 & N2 & _).
  apply (call_path segs PRw ok (Ks KH vm mat) (WLout.Kw (Ks KH vm mat) bs1 bs2 (length (WLout.MSG bs1 bs2)))
           E_wc E_wc WLoutS.Pre_wl2 [] s_w R_w WLout.Posts_wl _ rho3 eq_refl efr_w chk_w ltac:(rewrite Fc; exact fb_w)).
  - apply wl2_call.
  - intros ms _. unfold PRw. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. rewrite Nc, NxW in Hag4.
    change (ss_next WLoutS.Pre_wl2) with 92%positive. rewrite T_wDi_eq.
    eapply triple_conseq with (P := SP segs (Ks KL1 vm mat) T_w rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. apply (tw_intro (Ks KL1 vm mat) rho4 w HF4).
      - intros k Hk. destruct Hag4 as (_ & _ & Hm). rewrite <- Hm. exact (RN3 k Hk).
      - split; [exact Hsm|]. exact (Kw_KL1 vm mat _ _ HK). }
    pose proof (SIDEL_agree NX0 _ rho3 rho4 g vm mat HS3 Hag4 LtS Lt241) as HS4.
    destruct T_w_shape as (NxT & LnT & _). destruct fork_1 as (FfN & FfX & _).
    eapply (run_tr ok); [exact run_Tw | exact LnT | apply Ks_okf, KL1_tcons |].
    rewrite NxT. intros Lf rho5 [<-|[<-|[]]] Hag5; cbn [lf_state];
      pose proof (SIDEL_agree NX0 _ rho4 rho5 g vm mat HS4 Hag5 LtDi Lt241) as HS5;
      apply triple_facts; intros HF5.
    + pose proof (Forall_nth_error _ _ _ _ HF5 FfN) as Hf.
      apply (HN rho5 g vm mat HS5). exact (proj1 (fork_val rho5 1 _ (proj2 (proj2 (proj2 (proj2 HS5)))) ltac:(lia) Hf) eq_refl).
    + pose proof (Forall_nth_error _ _ _ _ HF5 FfX) as Hf.
      apply (HX rho5 g vm mat HS5). exact (proj2 (fork_val rho5 1 _ (proj2 (proj2 (proj2 (proj2 HS5)))) ltac:(lia) Hf) eq_refl).
Qed.

Lemma iter0 : ltac2:(tb__ "0|5|
S6S6S4dR1A1S6S1dS33S1fS30Q40A1A1M0S4eS40R4R3R2R1A5M1S3S0S1dS63VF;A1Z1A3M2A1S5eS5Vok;S59S5S4cS4fR4R3A3M3S45R6A4S5fS2L_;M4A4F_;F_;Fmat;Fvm;Fg;Frho2;S6S1dS33G0G1G2S5eS5Vok;S59S5G3S43R6A4G4A4F_;F_;Fmat;Fvm;Fg;Frho2;S5eS5Vok;S5aS5VJD;VKH;R5S3dS62A4S42R4A4G4A4F_;F_;F_;Frho;Fr0;").
Proof using FSUM HL6 HLM.
  intros r0 rho HT HN HX. destruct nexts_w as (_ & _ & _ & _ & _ & _ & Lt241). apply Pos.ltb_lt in Lt241.
  assert (Nx : ss_next S_0x = 248%positive) by reflexivity.
  eapply triple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho S_01 0 _ S_0x w unb_S_0x (SPJ_xforms segs _ _ rho S_0 S_01 w xs_S_01_ok Hw)) | intros w Hw; exact Hw |].
  destruct s_fz0_vals as (S12 & S13 & _). destruct chk_fz0 as (C1 & C2 & C3 & C4).
  apply (fz_call KH r0 S_0x s_fz0 R_fz0 rho _ KH_tcons KH_vmi efr_fz0 C1 C2 C3 C4 ltac:(rewrite Nx; lia) S12 S13 HT).
  intros r rho' Hr Hag. destruct (posts_0 r Hr) as (P & PS & HP & HPS & Hwf & Hmiss & Hobjs & HnxP & HnxPS & HlnPS & Hrun). rewrite HP.
  pose proof (TL_vagree rho rho' (ss_next S_0x) ltac:(rewrite Nx; lia) Hag HT) as HT'.
  apply (triple_from ok _ (fun r w => exists g vm mat, SIDEL NX0 r g vm mat /\ SP segs (Ks KH vm mat) PS r w)).
  { intros [tr [ms md]] Hw. destruct (toS KH r0 P PS rho' tr ms md HPS Hwf Hmiss Hobjs ltac:(rewrite HnxP; lia) HT' Hw) as (rho1 & g & HS & HP').
    exists rho1, g, (m_vmmaps md), (m_vm_materialized md). rewrite <- HnxP. split; assumption. }
  intros rho1. apply triple_ex. intros g. apply triple_ex. intros vm. apply triple_ex. intros mat. apply triple_pure. intros HS1.
  eapply (run_tr ok); [exact Hrun | exact HlnPS | apply Ks_okf, KH_tcons |].
  rewrite HnxPS. intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  exact (printf0_safe rho2 g vm mat (SIDEL_agree NX0 _ rho1 rho2 g vm mat HS1 Hag2 (Pos.lt_succ_diag_r _) Lt241) HN HX).
Qed.

Section Entries.
Hypothesis LOOP : ltac2:(tb__ "0|0|
S6S6S4dR1A1S5eS5Vok;S5aS5VJD;VKH;R3S3dS62A4S42R2A4S5fS2L_;A4F_;Frho;Fr0;").

Lemma ent2_safe : ltac2:(tb__ "0|0|
S6S6VTVc;Vcap;R1A2S6cZ0S64VF;A1A2S5eS5Vok;S5aS5VJD;VKH;R4SaaS62A4Sa9R3A4S5fS2L_;A4F_;F_;Frho;Fr0;").
Proof using Hargc L LOOP P0.
  intros r0 rho HTV HP. pose proof HTV as [[HX [V157 [V158 HL6']]] V159]. unfold U.Drv_r__G1.Drv_r.UV in *.
  apply triple_factsJ. intros HFa.
  assert (Hnz : bv_unsigned (rw rho 170) <> 0).
  { assert (Hx : existsb (sprop_eqb (SPNot (SPBranch BC_EQ (SVar 170) (SLit 0)))) (ss_facts F2) = true) by (vm_cast_no_check (@eq_refl bool true)).
    pose proof (holds_of_existsb rho _ _ HFa Hx) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  clear HFa.
  eapply triple_conseq; [intros w Hw; exact (SPJ_obj_forget segs _ rho F2w 11 w (SPJ_xforms segs _ [XSplit 10 (SLit stdout_buf)] rho F2 F2w w xs_F2_ok Hw)) | intros w Hw; exact Hw |].
  rewrite F2f_eq. destruct s_F2_props as [Id2 Tv2]. destruct s_F2_vals as (S240 & S241 & S158 & S159 & S157 & S100 & S101 & S102 & S103).
  apply (U.Drv_r__G1.Drv_r.reenter cx r0 KH tvP tvL DTrue F2f S_0 s_F2 rho _ 171 ent_F2 Id2 ltac:(lia) eq_refl Tv2).
  apply LOOP.
  assert (RW : forall i, (i < 31)%positive -> rw (rho_sub rho s_F2) i = rw rho i).
  { intros i Hi. cbn [rho_sub rw]. rewrite (wsub_get_id s_F2 31 i Id2 Hi). reflexivity. }
  split; [split; [split; [|split; [|split; [|exact HL6']]]|]|].
  - unfold U.Drv_r__G1.Drv_r.INVX, U.Drv_r__G1.Drv_r.UV in *. cbn [rho_sub rw]. rewrite S100, S101, S103. exact HX.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S157. exact V157.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S158. exact V158.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S159. exact V159.
  - split; [|intros H0; exfalso; lia]. intros _. cbn [rho_sub rw]. rewrite S240, S241. split; [reflexivity | exact Hnz].
Qed.

Lemma ent0_safe : ltac2:(tb__ "0|0|
S6S93S35OF_;F_;S6VTVc;Vcap;R1A2S0S1dS64VF;A1Z0A3S5eS5Vok;S5aS5VJD;VKH;R5SabR4A4Sa8R3A4S5fS2L_;A4F_;F_;Frho;FD;Fr0;").
Proof using Hargc L LOOP P0.
  intros r0 D rho HTV HP0. pose proof HTV as [[HX [V157 [V158 HL6']]] V159]. unfold U.Drv_r__G1.Drv_r.UV in *.
  assert (Z158 : bv_unsigned (rw rho 158) = 0) by (unfold L, F in *; lia).

  eapply triple_conseq with (P := SPJ segs (JD KH r0 ((SLit 0, SVar 158) :: U.Drv_r__G1.Drv_r.tvK) DTrue) E_f0 rho); [| intros w Hw; exact Hw |].
  { intros w [Hsm HJ]. split; [exact Hsm|]. apply JD_add_null; [cbn [eval]; exact Z158|].
    exact (JGD_mono segs C_U 31 KH r0 P0 _ D DTrue _ _ _ (fun _ _ _ => I) HJ). }

  apply (triple_restate segs ok _ rho E_f0 E_f0r _ _ swf_E_f0r diff_E_f0r).
  { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite Z158. reflexivity. }

  eapply triple_conseq; [intros w Hw; exact (SPJ_obj_forget segs _ rho E_f03 10 w (SPJ_xforms segs _ [XSplit 9 (SLit stdout_buf)] rho E_f02 E_f03 w xs_E_f03_ok
                                        (SPJ_unbase segs _ rho E_f01 0 (-80) E_f02 w unb_E_f02 (SPJ_xforms segs _ [XSplit 0 (SLit (-80))] rho E_f0r E_f01 w xs_E_f01_ok Hw)))) | intros w Hw; exact Hw |].
  rewrite E_f0x_eq. destruct swf_E_f0a as (WFa & Len9 & NxX & FaX).

  eapply triple_conseq with (P := SPJ segs (JD KH r0 ((SLit 0, SVar 158) :: U.Drv_r__G1.Drv_r.tvK) DTrue) E_f0e rho); [| intros w Hw; exact Hw |].
  { intros w [Hsm HJ]. split; [|exact HJ]. apply (smatch_xforms segs xs_f0e rho E_f0a E_f0e _ xs_f0e_ok). rewrite <- E_f0a_eq.
    apply (TobjJVA.smatch_carve_plain segs rho E_f0x w (SLit empty_addr) (SVar 158) (ss_next E_f0x) Hsm).
    - rewrite E_f0a_eq. exact WFa.
    - cbn [eval]. rewrite Z158. lia.
    - cbn [eval]. rewrite Z158, U_addr by (unfold empty_addr; lia). unfold empty_addr. lia.
    - apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd eval]. rewrite Z158. lia.
    - intros z Hz. exfalso. cbn [eval] in Hz. rewrite Z158 in Hz. lia. }
  destruct s_F0_props as [Id0 Tv0]. destruct s_F0_vals as (S240 & S241 & S158 & S159 & S157 & S100 & S101 & S102 & S103).
  apply (U.Drv_r__G1.Drv_r.reenter cx r0 KH ((SLit 0, SVar 158) :: U.Drv_r__G1.Drv_r.tvK) tvL DTrue E_f0e S_0 s_F0 rho _ 171 ent_F0 Id0 ltac:(lia) eq_refl Tv0).
  apply LOOP.
  split; [split; [split; [|split; [|split; [|exact HL6']]]|]|].
  - unfold U.Drv_r__G1.Drv_r.INVX, U.Drv_r__G1.Drv_r.UV in *. cbn [rho_sub rw]. rewrite S100, S101, S103. exact HX.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S157. exact V157.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S158. exact V158.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S159. exact V159.
  - split; [intros Hp; exfalso; lia|]. intros _. cbn [rho_sub rw]. rewrite S241. reflexivity.
Qed.
End Entries.

Section Chain.

Hypothesis EX1 : ltac2:(tb__ "0|0|
S6S1dS33S1fS30Q40A1A1S4eS40R4R3R2R1A5S0S1dS63VF;A1Z1A3S5eS5Vok;S59S5S4cS4fR4R3A3S43R6A4S5fS2L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").
Hypothesis EX2 : ltac2:(tb__ "0|0|
S6S1dS33S1fS30Q40A1A1S4eSb5R4R3R2R1A5S0S1dS63VF;A1Z2A3S5eS5Vok;S59S5S4cS4fR4R3A3SbbR6A4S5fS2L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").
Hypothesis EX3 : ltac2:(tb__ "0|0|
S6S1dS33S1fS30Q40A1A1S4eSb6R4R3R2R1A5S0S1dS63VF;A1Z3A3S5eS5Vok;S59S5S4cS4fR4R3A3SbcR6A4S5fS2L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").
Hypothesis EX4 : ltac2:(tb__ "0|0|
S6S1dS33S1fS30Q40A1A1S4eSb7R4R3R2R1A5S0S1dS63VF;A1Z4A3S5eS5Vok;S59S5S4cS4fR4R3A3SbdR6A4S5fS2L_;A4F_;F_;Fmat;Fvm;Fg;Frho;").

Lemma iter3 : ltac2:(tb__ "0|0|
S6S6S4dR1A1S6cZ3S63VF;A1A2S5eS5Vok;S5aS5VJD;S4fR4S3dS62A4SbaR3A4S5fS2L_;A4F_;F_;Frho;Fr0;").
Proof using EX4 FSUM HL6 HLM.
  intros r0 rho HT Hlt. destruct s_fz3_vals as (S12 & S13 & _). destruct fork_4 as (FfN & FfX & _). pose proof (calls_range F) as CR.
  assert (A : (242 <=? ss_next S_3)%positive = true) by reflexivity. apply Pos.leb_le in A.
  assert (B : (ss_next S_3 <=? NX3)%positive = true) by reflexivity. apply Pos.leb_le in B.
  apply (iter_gen 4 r0 S_3 N_4 X_4 s_fz3 R_fz3 NX3 rho efr_fz3 chk_fz3 S12 S13 A posts_3 B FfN FfX ltac:(lia) HT).
  - intros rho2 g vm mat _ Hne. exfalso. lia.
  - exact EX4.
Qed.

Lemma iter2 : ltac2:(tb__ "0|0|
S6S6S4dR1A1S6cZ2S63VF;A1A2S5eS5Vok;S5aS5VJD;S4fR4S3dS62A4Sb9R3A4S5fS2L_;A4F_;F_;Frho;Fr0;").
Proof using EX3 EX4 FSUM HL6 HLM.
  intros r0 rho HT Hlt. destruct s_fz2_vals as (S12 & S13 & _). destruct fork_3 as (FfN & FfX & _). pose proof (calls_range F) as CR.
  assert (A : (242 <=? ss_next S_2)%positive = true) by reflexivity. apply Pos.leb_le in A.
  assert (B : (ss_next S_2 <=? NX2)%positive = true) by reflexivity. apply Pos.leb_le in B.
  assert (C : (241 <? NX2)%positive = true) by reflexivity. apply Pos.ltb_lt in C.
  apply (iter_gen 3 r0 S_2 N_3 X_3 s_fz2 R_fz2 NX2 rho efr_fz2 chk_fz2 S12 S13 A posts_2 B FfN FfX ltac:(lia) HT).
  - intros rho2 g vm mat HS2 Hne.
    apply (triple_from ok _ (fun r w => TL r /\ SPJ segs (JD KL1 r tvL DTrue) S_3 r w)).
    { intros [tr [ms md]] Hw. destruct (fromN KL1 N_3 S_3 NX2 rho2 g vm mat tr ms md (proj1 N_3_objs) ent_S3 C HS2 Hw) as (rho' & HT' & HS'). exists rho'. split; assumption. }
    intros rho'. apply triple_pure. intros HT'. apply (iter3 rho' rho' HT'). lia.
  - exact EX3.
Qed.

Lemma iter1 : ltac2:(tb__ "0|0|
S6S6S4dR1A1S6cZ1S63VF;A1A2S5eS5Vok;S5aS5VJD;S4fR4S3dS62A4Sb8R3A4S5fS2L_;A4F_;F_;Frho;Fr0;").
Proof using EX2 EX3 EX4 FSUM HL6 HLM.
  intros r0 rho HT Hlt. destruct s_fz1_vals as (S12 & S13 & _). destruct fork_2 as (FfN & FfX & _). pose proof (calls_range F) as CR.
  assert (A : (242 <=? ss_next S_1)%positive = true) by reflexivity. apply Pos.leb_le in A.
  assert (B : (ss_next S_1 <=? NX1)%positive = true) by reflexivity. apply Pos.leb_le in B.
  assert (C : (241 <? NX1)%positive = true) by reflexivity. apply Pos.ltb_lt in C.
  apply (iter_gen 2 r0 S_1 N_2 X_2 s_fz1 R_fz1 NX1 rho efr_fz1 chk_fz1 S12 S13 A posts_1 B FfN FfX ltac:(lia) HT).
  - intros rho2 g vm mat HS2 Hne.
    apply (triple_from ok _ (fun r w => TL r /\ SPJ segs (JD KL1 r tvL DTrue) S_2 r w)).
    { intros [tr [ms md]] Hw. destruct (fromN KL1 N_2 S_2 NX1 rho2 g vm mat tr ms md (proj1 N_2_objs) ent_S2 C HS2 Hw) as (rho' & HT' & HS'). exists rho'. split; assumption. }
    intros rho'. apply triple_pure. intros HT'. apply (iter2 rho' rho' HT'). lia.
  - exact EX2.
Qed.

Lemma loop_safe : ltac2:(tb__ "0|0|
S6S6S4dR1A1S5eS5Vok;S5aS5VJD;VKH;R3S3dS62A4S42R2A4S5fS2L_;A4F_;Frho;Fr0;").
Proof using EX1 EX2 EX3 EX4 FSUM HL6 HLM.
  intros r0 rho HT. pose proof (calls_range F) as CR.
  assert (C : (241 <? NX0)%positive = true) by reflexivity. apply Pos.ltb_lt in C.
  apply (iter0 r0 rho HT).
  - intros rho2 g vm mat HS2 Hne.
    apply (triple_from ok _ (fun r w => TL r /\ SPJ segs (JD KL1 r tvL DTrue) S_1 r w)).
    { intros [tr [ms md]] Hw. destruct (fromN KL1 N_1 S_1 NX0 rho2 g vm mat tr ms md (proj1 N_1_objs) ent_S1 C HS2 Hw) as (rho' & HT' & HS'). exists rho'. split; assumption. }
    intros rho'. apply triple_pure. intros HT'. apply (iter1 rho' rho' HT'). lia.
  - exact EX1.
Qed.

Theorem hl_safe2 : ltac2:(tb__ "0|0|
S6S6VTVc;Vcap;R1A2S6cZ0S64VF;A1A2S5eS5Vok;S5aS5VJD;VKH;R4SaaS62A4Sa9R3A4S5fS2L_;A4F_;F_;Frho;Fr0;").
Proof using EX1 EX2 EX3 EX4 FSUM HL6 HLM Hargc HokK HokP P0_now P0_tp P0_transport. exact (ent2_safe loop_safe). Qed.

Theorem hl_safe0 : ltac2:(tb__ "0|0|
S6S93S35OF_;F_;S6VTVc;Vcap;R1A2S0S1dS64VF;A1Z0A3S5eS5Vok;S5aS5VJD;VKH;R5SabR4A4Sa8R3A4S5fS2L_;A4F_;F_;Frho;FD;Fr0;").
Proof using EX1 EX2 EX3 EX4 FSUM HL6 HLM Hargc HokK HokP P0_now P0_tp P0_transport. exact (ent0_safe loop_safe). Qed.
End Chain.

Section Ex.
Hypothesis FSUMX : fuzz_one_sum_ex_stmt_U.

Definition QN : world -> Prop := ltac2:(tb__ "0|0|
S5fS0S1fS34A1S61R1A1S23S34S65Z1S66S63VF;A1A1A2S22S34S67Vfs;Z0A2S28S34A1A3A3A3Lw;").

Lemma efz_call : ltac2:(tb__ "0|5|
S1fS34A1S35OF_;F_;S6S7S7fS1fS8A1M0S6S5fOF_;SaeR7A1S0S25G0A1S9bR6S3eR5A3S24G0R4A2A3S0S20Sa0S56P1fR7S3eR6R5S7bS27S7S1fS27SbSbA2A1M1A2M2S7S29S7G1A2S3fA4A7S21A3S0S20S9eR7S77A2S21A3S0S20S8cG2G2S2cSa3S77R9SaRaA1S29S7G1R1A3M3S2eS7G1R1A3M4A5Sa1S3eG3G4A3A2Ld;S3fA3S21A3S0S20Sa2SdRaA1S3dS2aS2bA1S46R8A5S21A3S74Pf2SaRbA1A2S0SbS7eRbPcA2SePf0A1A3S0SbS7eRcPdA2SeP9eA1A3S4dRbA1S1dS6S8bS1dR2S82S80A1A3S9dSaR12A1RfR2A3S5dS5S5aS5VJD;R15R14S3dS62A4S9fS77R13R12R11S81S80R4A2A5R3A4RfA3F_;F_;Frho';Fr;S5dS5S5aS5VJD;R12R11S3dS62A4R10RdA4RcA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Frho;FR;Fs;FCl;Fr0;FK;").
Proof using FSUMX HL6 HLM.
  intros K r0 Cl s R rho Q HV He Hchk Hdom Hpd Hrchk Hnx Hs12 Hs13 HT CONT.
  pose proof (TL_plen rho HT) as V158. destruct HT as [_ [P1 P2]].
  eapply etriple_conseq with (P := SPJ segs (JG segs C_U 31 K r0 P0 [] (tvL ++ [])) Cl rho); [| intros w Hw; exact Hw |].
  { intros w [Hsm HJ]. split; [exact Hsm|]. rewrite app_nil_r. exact (JGD_JG segs C_U 31 K r0 P0 tvL DTrue _ _ _ HJ). }
  apply (client_callJ_ex segs C_U 31 K r0 P0 [] malloc_laws_U P0_fz PreFZ [] PDfz NF eq_refl
           (fun FBc rho1 HV' => FSUMX K FBc rho1 HV') Cl s R rho tvL [] Q).
  - exact HV.
  - exact He.
  - exact Hchk.
  - exact Hdom.
  - apply Pos.leb_le. lia.
  - rewrite app_nil_r. apply tvL_below. lia.
  - reflexivity.
  - exact Hpd.
  - intros Ai ms HFa _ Hav _ _ _ HZ _ HT. rewrite app_nil_r in HZ. split.
    + apply (robjs_checkF_sound segs C_U r0 [] rho (ss_facts Cl) tvL robj_inwi R HFa (T_ok_T0_31 r0 rho _ Hav HT) HZ Hrchk).
      intros o a _ Hr Ha. right; left. exact (robj_inwi_img rho o a Hr Ha).
    + unfold P0_fz, payload_cov. rewrite !rw_call', Hs12, Hs13. cbn [eval]. rewrite V158.
      destruct (Z.eq_dec (payload_len F) 0) as [Z0|NZ]; [left; exact Z0 | right].
      pose proof plen_range as PR. destruct (P1 ltac:(lia)) as [E240 NZ241].
      exists (bv_unsigned (rw rho 241)), (bv_unsigned (rw rho 158)). split; [|rewrite E240, V158; lia].
      apply (proj2 (In_FBx [] rho tvL _)). right. exists (SVar 241, SVar 158).
      split; [left; reflexivity|]. split; [exact NZ241 | reflexivity].
  - intros d rho' Hd Hag. unfold PDfz, PD_fuzz in Hd. apply in_map_iff in Hd as (r & <- & Hr). cbn [fst snd import_tv map]. rewrite app_nil_r.
    eapply etriple_conseq; [| intros w Hw; exact Hw | exact (CONT r rho' Hr Hag)].
    intros w [Hsm HJ]. split; [exact Hsm|]. exact (JG_JGD segs C_U 31 K r0 P0 tvL _ _ _ HJ).
Qed.

Lemma epost_go : ltac2:(tb__ "0|b|
S1dS1fS34A1S35OF_;F_;S6S7S7S7S7S1eS6S5fOF_;S0S7S84R7S83S56SaR7A1M0A2S75G0A1A3R6A3S0S20S13R7A1S21A3S0S20S8eS56SdR9A1S3dS23S8S79S8U2M1SfR9A1M2A3S7aS8U3M3G2A3A3A4S21A3S0S1fS8A1SfRaA1M4S23S8S79S8G1G4A3S22S8S41S7aS8G3G4A3A3A3A3S0S1eSaRbA1M5R7A3S0S1eG5S75R8A1A3S0S20S15RcA1S2dA3S74Pf2RaA2S0S25S1fS6fA1M6A1S72S5SacS44ReS21A5S24G6S22S6fS71RdS70A2S22S6fS71RcS70A2S28S6fA1A3A3A2A3S0S25ScA1M7S8dScSdReA1U0A3M8S24ScS52R13A1A2A3S0G7G8S24ScS12S52R14A1A1A2A3S1S6bZ1R15A2S6bR15Z4A2A2S4dReA1S6S1dS33S1fS30Q40A1A1M9S4eR14R4R3R2R1A5S3S0S1dS63VF;A1MaR1cA3A1S5dS5S59S5S4cR1cR4R3A3R18R6A4R14A3F_;F_;Fmat;Fvm;Fg;Frho2;S6S1dS33G9S4eR15R4R3R2R1A5S0S1dGaR1dA3S5dS5S59S5S4cR1dR4R3A3R18R6A4R15A3F_;F_;Fmat;Fvm;Fg;Frho2;S5dS5S5aS5VJD;R18R17S3dS62A4R16R11A4R10A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Frho;FNX;FXn;FNn;FPS;FP;Fr0;FK;Fj;").
Proof using HL6 HLM.
  intros j K r0 P PS Nn Xn NX rho Q HPS Hwf Hmiss Hobjs HnxP HnxPS HlnPS Hnx Hrun HfN HfX Hj HT HN HX.
  apply (etriple_from _ (fun r w => exists g vm mat, SIDEL NX r g vm mat /\ SP segs (Ks K vm mat) PS r w)).
  { intros [tr [ms md]] Hw. destruct (toS K r0 P PS rho tr ms md HPS Hwf Hmiss Hobjs ltac:(rewrite HnxP; exact Hnx) HT Hw) as (rho1 & g & HS & HP').
    exists rho1, g, (m_vmmaps md), (m_vm_materialized md). rewrite <- HnxP. split; assumption. }
  intros rho1. apply etriple_ex. intros g. apply etriple_ex. intros vm. apply etriple_ex. intros mat. apply etriple_pure. intros HS1.
  eapply erun_tr; [exact Hrun | exact HlnPS |].
  rewrite HnxPS. intros Lf rho2 [<-|[<-|[]]] Hag2; cbn [lf_state];
    pose proof (SIDEL_agree NX (Pos.succ NX) rho1 rho2 g vm mat HS1 Hag2 ltac:(lia) ltac:(lia)) as HS2;
    apply etriple_facts; intros HF2.
  - pose proof (Forall_nth_error _ _ _ _ HF2 HfN) as Hf.
    apply (HN rho2 g vm mat HS2). exact (proj1 (fork_val rho2 j _ (proj2 (proj2 (proj2 (proj2 HS2)))) Hj Hf) eq_refl).
  - pose proof (Forall_nth_error _ _ _ _ HF2 HfX) as Hf.
    apply (HX rho2 g vm mat HS2). exact (proj2 (fork_val rho2 j _ (proj2 (proj2 (proj2 (proj2 HS2)))) Hj Hf) eq_refl).
Qed.

Lemma eiter_gen : ltac2:(tb__ "0|f|
S1dS6S7S7S7S7fS1fS8A1M0S1eS6S5fOF_;S0S25G0A1S9bR8S3eR5A3S24G0R4A2A3S1S0S20Sa0S56P1fR9S3eR6R5S7bS27S7S1fS27SbSbA2A1M1A2M2S7S29S7G1A2S3fA4A7S21A3S1S0S20S9eR6S77A2S21A3S1S0S20S8cG2G2S2cSa3S77R7SaRaA1S29S7G1R1A3M3S2eS7G1R1A3M4A5Sa1S3eG3G4A3A2Ld;S3fA3S21A3S0S20Sa2SdR9A1S3dS2aS2bA1S46R5A5S21A3A2A2A2S0SbS7eR7PcA2SePf0A1A3S0SbS7eR8PdA2SeP9eA1A3S74Pf2SaRcA1A2S1dS8bS1dR1S82S80A1A3S4S7S7S4S7S7S1S0S7S9fS77R11ReRdS81S80R4A2A5R2A3S1S0S7S84R2S83S56SaR2A1M5A2S75G5A1A3R1A3S1S0S20S13R1A1S21A3S1S0S20S8eS56SdR2A1S3dS23S8S79S8U2SfR2A1M6A3M7S7aS8U3G6A3M8A3A4S21A3S1S0G0G6S23S8G7S22S8S41G8A3A3A3S1S0S1eG5RcA3S1S0S1eSaR1A1S75RcA1A3S1S0S20S15R1A1S2dA3S0S25S1fS6fA1M9A1S72S5SacS44R1S21A5S24G9S22S6fS71R10S70A2S22S6fS71RfS70A2S28S6fA1A3A3A2A3A2A2A2A2A2A2A2A2LPS;A2LP;A2F_;Fr;S74SaReA1R9A2S0S25ScA1MaS8dScSdReA1U0A3MbS24ScS52R11A1A2A3S0GaGbS24ScS12S52R12A1A1A2A3S1S6bZ1R13A2S6bR13Z4A2A2S4dRcA1S6S1dS33S1fS30Q40A1A1McS4eR12R4R3R2R1A5S3S0S1dS63VF;A1MdR1aA3A1S5dS5S59S5S4cS4fR4R3A3R18R6A4MeR12A3F_;F_;Fmat;Fvm;Fg;Frho2;S6S1dS33GcS4eR13R4R3R2R1A5S0S1dGdR1bA3S5dS5GeR13A3F_;F_;Fmat;Fvm;Fg;Frho2;S5dS5S5aS5VJD;S4fR16S3dS62A4R15RfA4ReA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Frho;FNX;FR;Fs;FXn;FNn;FS;Fr0;Fj;").
Proof using FSUMX HL6 HLM.
  intros j r0 S Nn Xn s R NX rho Q He (Hchk & Hdom & Hpd & Hrchk) Hs12 Hs13 HnxS POSTS HSN HfN HfX Hj HT HN HX.
  apply (efz_call KL1 r0 S s R rho _ KL1_vmi He Hchk Hdom Hpd Hrchk HnxS Hs12 Hs13 HT).
  intros r rho' Hr Hag. destruct (POSTS r Hr) as (P & PS & HP & HPS & Hwf & Hmiss & Hobjs & HnxP & HnxPS & HlnPS & Hrun). rewrite HP.
  apply (epost_go j KL1 r0 P PS Nn Xn NX rho' Q HPS Hwf Hmiss Hobjs HnxP HnxPS HlnPS ltac:(lia) Hrun HfN HfX Hj); [|exact HN|exact HX].
  exact (TL_vagree rho rho' (ss_next S) HnxS Hag HT).
Qed.

Lemma wl2_ecall : ltac2:(tb__ "0|1|
S33S1fS30Q40A1A1S6S53R1A1S5dS5S59S5S4cVKH;R4R3A3M0SadR2A4S5bS5S94G0S50S51S2fS30Q8A1S95S50S51A2A2A4SaSadA1R2S96A5A3F_;Frho1;Fmat;Fvm;").
Proof using Hargc JD L P0 TVc cap.
  intros vm mat rho1 (H5 & H6 & H13 & H15).
  apply (WLout.wl2_sum_ex (Ks KH vm mat) rho1 bs1 bs2 H5 H6 H13 H15).
  - unfold WLout.MSG, max_write_total. cbn. lia.
  - apply Ks_fd1.
  - cbn. lia.
Qed.

Lemma eprintf0 : ltac2:(tb__ "0|4|
S6S1dS33S1fS30Q40A1A1M0S5fOF_;S4eS40R5R4R3R2A5S6S1dS33G0S4eS40R4R3R2R1A5M1S3S0S1dS63VF;A1Z1A3M2A1S5dS5S59S5S4cS4fR4R3A3M3S45R6A4R8A3F_;F_;Fmat;Fvm;Fg;Frho2;S6S1dS33G0G1G2S5dS5S59S5G3S43R6A4R9A3F_;F_;Fmat;Fvm;Fg;Frho2;S5dS5S59S5S4cVKH;R6R5A3S47R8A4R4A3F_;F_;F_;FQ;Fmat;Fvm;Fg;Frho1;").
Proof using HL6 HLM.
  intros rho1 g vm mat Q HS1 HN HX. destruct nexts_w as (NxIo & NxPio & NxW & NxWc & LtDi & NxTw & Lt241). apply Pos.ltb_lt in LtDi. apply Pos.ltb_lt in Lt241.
  pose proof (Pos.lt_succ_diag_r NX0) as LtS.
  destruct cert_io as (Hi & _ & H17 & H10 & H11). destruct P_io_shape as [_ LnPio].
  eapply etriple_seq.
  { apply (etriple_ioctl segs (Ks KH vm mat) E_io rho1); [exact Hi | rewrite H17; reflexivity | | rewrite H11; reflexivity].
    intros tr md ((_ & Hf & _) & _). rewrite H10, Hf. eexists. reflexivity. }
  rewrite P_io_eq.
  eapply erun_tr; [exact run_Pio | exact LnPio |].
  rewrite NxPio. intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  pose proof (SIDEL_agree NX0 _ rho1 rho2 g vm mat HS1 Hag2 LtS Lt241) as HS2.
  apply (etriple_from _ (fun r w => (SIDEL NX0 r g vm mat /\ rl r 5 = bs1 /\ rl r 6 = bs2 /\ (forall k, 0 <= k < 1 -> rm r (Z_to_bv 64 (nl_addr + k)) = None)) /\ SP segs (Ks KH vm mat) E_wc r w)).
  { intros w Hw. destruct (wc_intro vm mat rho2 w (proj2 (proj2 (proj2 (proj2 HS2)))) (proj1 (proj2 HS2)) Hw) as (r & [A B] & Hrw & Hrm & RN & HS).
    exists r. split; [|exact HS]. split; [exact (SIDEL_transport NX0 rho2 r g vm mat HS2 (fun i _ => Hrw i) Lt241 Hrm)|]. auto. }
  intros rho3 w0 [(HS3 & H5 & H6 & RN3) Hw0]. revert w0 Hw0.
  destruct s_w_vals as (S12 & S13 & S14 & S15). destruct E_w_facts as (Fc & F3 & F2 & Nc & N3 & N2 & _).
  apply (ecall_path segs PRw (Ks KH vm mat) (WLout.Kw (Ks KH vm mat) bs1 bs2 (length (WLout.MSG bs1 bs2)))
           E_wc E_wc WLoutS.Pre_wl2 [] s_w R_w WLout.Posts_wl _ rho3 eq_refl efr_w chk_w ltac:(rewrite Fc; exact fb_w)).
  - apply wl2_ecall.
  - intros ms _. unfold PRw. rewrite !rw_call', S13, S15. cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho4 [<-|[]] Hag4 HF4. cbn [lf_state]. rewrite Fc in HF4. rewrite Nc, NxW in Hag4.
    change (ss_next WLoutS.Pre_wl2) with 92%positive. rewrite T_wDi_eq.
    eapply etriple_conseq with (P := SP segs (Ks KL1 vm mat) T_w rho4); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. apply (tw_intro (Ks KL1 vm mat) rho4 w HF4).
      - intros k Hk. destruct Hag4 as (_ & _ & Hm). rewrite <- Hm. exact (RN3 k Hk).
      - split; [exact Hsm|]. exact (Kw_KL1 vm mat _ _ HK). }
    pose proof (SIDEL_agree NX0 _ rho3 rho4 g vm mat HS3 Hag4 LtS Lt241) as HS4.
    destruct T_w_shape as (NxT & LnT & _). destruct fork_1 as (FfN & FfX & _).
    eapply erun_tr; [exact run_Tw | exact LnT |].
    rewrite NxT. intros Lf rho5 [<-|[<-|[]]] Hag5; cbn [lf_state];
      pose proof (SIDEL_agree NX0 _ rho4 rho5 g vm mat HS4 Hag5 LtDi Lt241) as HS5;
      apply etriple_facts; intros HF5.
    + pose proof (Forall_nth_error _ _ _ _ HF5 FfN) as Hf.
      apply (HN rho5 g vm mat HS5). exact (proj1 (fork_val rho5 1 _ (proj2 (proj2 (proj2 (proj2 HS5)))) ltac:(lia) Hf) eq_refl).
    + pose proof (Forall_nth_error _ _ _ _ HF5 FfX) as Hf.
      apply (HX rho5 g vm mat HS5). exact (proj2 (fork_val rho5 1 _ (proj2 (proj2 (proj2 (proj2 HS5)))) ltac:(lia) Hf) eq_refl).
Qed.

Lemma eiter0 : ltac2:(tb__ "0|4|
S6S6S5fOF_;S4dR2A1S6S1dS33S1fS30Q40A1A1M0S4eS40R4R3R2R1A5M1S3S0S1dS63VF;A1Z1A3M2A1S5dS5S59S5S4cS4fR4R3A3M3S45R6A4R8A3F_;F_;Fmat;Fvm;Fg;Frho2;S6S1dS33G0G1G2S5dS5S59S5G3S43R6A4R9A3F_;F_;Fmat;Fvm;Fg;Frho2;S5dS5S5aS5VJD;VKH;R6S3dS62A4S42R5A4R4A3F_;F_;F_;FQ;Frho;Fr0;").
Proof using FSUMX HL6 HLM.
  intros r0 rho Q HT HN HX. destruct nexts_w as (_ & _ & _ & _ & _ & _ & Lt241). apply Pos.ltb_lt in Lt241.
  assert (Nx : ss_next S_0x = 248%positive) by reflexivity.
  eapply etriple_conseq; [intros w Hw; exact (SPJ_unbase segs _ rho S_01 0 _ S_0x w unb_S_0x (SPJ_xforms segs _ _ rho S_0 S_01 w xs_S_01_ok Hw)) | intros w Hw; exact Hw |].
  destruct s_fz0_vals as (S12 & S13 & _). destruct chk_fz0 as (C1 & C2 & C3 & C4).
  apply (efz_call KH r0 S_0x s_fz0 R_fz0 rho _ KH_vmi efr_fz0 C1 C2 C3 C4 ltac:(rewrite Nx; lia) S12 S13 HT).
  intros r rho' Hr Hag. destruct (posts_0 r Hr) as (P & PS & HP & HPS & Hwf & Hmiss & Hobjs & HnxP & HnxPS & HlnPS & Hrun). rewrite HP.
  pose proof (TL_vagree rho rho' (ss_next S_0x) ltac:(rewrite Nx; lia) Hag HT) as HT'.
  apply (etriple_from _ (fun r w => exists g vm mat, SIDEL NX0 r g vm mat /\ SP segs (Ks KH vm mat) PS r w)).
  { intros [tr [ms md]] Hw. destruct (toS KH r0 P PS rho' tr ms md HPS Hwf Hmiss Hobjs ltac:(rewrite HnxP; lia) HT' Hw) as (rho1 & g & HS & HP').
    exists rho1, g, (m_vmmaps md), (m_vm_materialized md). rewrite <- HnxP. split; assumption. }
  intros rho1. apply etriple_ex. intros g. apply etriple_ex. intros vm. apply etriple_ex. intros mat. apply etriple_pure. intros HS1.
  eapply erun_tr; [exact Hrun | exact HlnPS |].
  rewrite HnxPS. intros Lf rho2 [<-|[]] Hag2. cbn [lf_state].
  exact (eprintf0 rho2 g vm mat Q (SIDEL_agree NX0 _ rho1 rho2 g vm mat HS1 Hag2 (Pos.lt_succ_diag_r _) Lt241) HN HX).
Qed.

Section EEntries.
Variable Q : world -> Prop.
Hypothesis ELOOP : ltac2:(tb__ "0|0|
S6S6S4dR1A1S5dS5S5aS5VJD;VKH;R3S3dS62A4S42R2A4VQ;A3F_;Frho;Fr0;").

Lemma ent2_ex : ltac2:(tb__ "0|0|
S6S6VTVc;Vcap;R1A2S6cZ0S64VF;A1A2S5dS5S5aS5VJD;VKH;R4SaaS62A4Sa9R3A4VQ;A3F_;F_;Frho;Fr0;").
Proof using ELOOP Hargc L P0.
  intros r0 rho HTV HP. pose proof HTV as [[HX [V157 [V158 HL6']]] V159]. unfold U.Drv_r__G1.Drv_r.UV in *.
  apply etriple_factsJ. intros HFa.
  assert (Hnz : bv_unsigned (rw rho 170) <> 0).
  { assert (Hx : existsb (sprop_eqb (SPNot (SPBranch BC_EQ (SVar 170) (SLit 0)))) (ss_facts F2) = true) by (vm_cast_no_check (@eq_refl bool true)).
    pose proof (holds_of_existsb rho _ _ HFa Hx) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  clear HFa.
  eapply etriple_conseq; [intros w Hw; exact (SPJ_obj_forget segs _ rho F2w 11 w (SPJ_xforms segs _ [XSplit 10 (SLit stdout_buf)] rho F2 F2w w xs_F2_ok Hw)) | intros w Hw; exact Hw |].
  rewrite F2f_eq. destruct s_F2_props as [Id2 Tv2]. destruct s_F2_vals as (S240 & S241 & S158 & S159 & S157 & S100 & S101 & S102 & S103).
  apply (U.Drv_r__G1.Drv_r.ereenter cx r0 KH tvP tvL DTrue F2f S_0 s_F2 rho _ 171 ent_F2 Id2 ltac:(lia) eq_refl Tv2).
  apply ELOOP.
  split; [split; [split; [|split; [|split; [|exact HL6']]]|]|].
  - unfold U.Drv_r__G1.Drv_r.INVX, U.Drv_r__G1.Drv_r.UV in *. cbn [rho_sub rw]. rewrite S100, S101, S103. exact HX.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S157. exact V157.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S158. exact V158.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S159. exact V159.
  - split; [|intros H0; exfalso; lia]. intros _. cbn [rho_sub rw]. rewrite S240, S241. split; [reflexivity | exact Hnz].
Qed.

Lemma ent0_ex : ltac2:(tb__ "0|0|
S6S93S35OF_;F_;S6VTVc;Vcap;R1A2S0S1dS64VF;A1Z0A3S5dS5S5aS5VJD;VKH;R5SabR4A4Sa8R3A4VQ;A3F_;F_;Frho;FD;Fr0;").
Proof using ELOOP Hargc L P0.
  intros r0 D rho HTV HP0. pose proof HTV as [[HX [V157 [V158 HL6']]] V159]. unfold U.Drv_r__G1.Drv_r.UV in *.
  assert (Z158 : bv_unsigned (rw rho 158) = 0) by (unfold L, F in *; lia).
  eapply etriple_conseq with (P := SPJ segs (JD KH r0 ((SLit 0, SVar 158) :: U.Drv_r__G1.Drv_r.tvK) DTrue) E_f0 rho); [| intros w Hw; exact Hw |].
  { intros w [Hsm HJ]. split; [exact Hsm|]. apply JD_add_null; [cbn [eval]; exact Z158|].
    exact (JGD_mono segs C_U 31 KH r0 P0 _ D DTrue _ _ _ (fun _ _ _ => I) HJ). }
  apply (etriple_restate segs _ rho E_f0 E_f0r _ _ swf_E_f0r diff_E_f0r).
  { constructor; [|constructor]. cbn [fst snd eval]. apply bv_eq. rewrite Z158. reflexivity. }
  eapply etriple_conseq; [intros w Hw; exact (SPJ_obj_forget segs _ rho E_f03 10 w (SPJ_xforms segs _ [XSplit 9 (SLit stdout_buf)] rho E_f02 E_f03 w xs_E_f03_ok
                                        (SPJ_unbase segs _ rho E_f01 0 (-80) E_f02 w unb_E_f02 (SPJ_xforms segs _ [XSplit 0 (SLit (-80))] rho E_f0r E_f01 w xs_E_f01_ok Hw)))) | intros w Hw; exact Hw |].
  rewrite E_f0x_eq. destruct swf_E_f0a as (WFa & Len9 & NxX & FaX).
  eapply etriple_conseq with (P := SPJ segs (JD KH r0 ((SLit 0, SVar 158) :: U.Drv_r__G1.Drv_r.tvK) DTrue) E_f0e rho); [| intros w Hw; exact Hw |].
  { intros w [Hsm HJ]. split; [|exact HJ]. apply (smatch_xforms segs xs_f0e rho E_f0a E_f0e _ xs_f0e_ok). rewrite <- E_f0a_eq.
    apply (TobjJVA.smatch_carve_plain segs rho E_f0x w (SLit empty_addr) (SVar 158) (ss_next E_f0x) Hsm).
    - rewrite E_f0a_eq. exact WFa.
    - cbn [eval]. rewrite Z158. lia.
    - cbn [eval]. rewrite Z158, U_addr by (unfold empty_addr; lia). unfold empty_addr. lia.
    - apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd eval]. rewrite Z158. lia.
    - intros z Hz. exfalso. cbn [eval] in Hz. rewrite Z158 in Hz. lia. }
  destruct s_F0_props as [Id0 Tv0]. destruct s_F0_vals as (S240 & S241 & S158 & S159 & S157 & S100 & S101 & S102 & S103).
  apply (U.Drv_r__G1.Drv_r.ereenter cx r0 KH ((SLit 0, SVar 158) :: U.Drv_r__G1.Drv_r.tvK) tvL DTrue E_f0e S_0 s_F0 rho _ 171 ent_F0 Id0 ltac:(lia) eq_refl Tv0).
  apply ELOOP.
  split; [split; [split; [|split; [|split; [|exact HL6']]]|]|].
  - unfold U.Drv_r__G1.Drv_r.INVX, U.Drv_r__G1.Drv_r.UV in *. cbn [rho_sub rw]. rewrite S100, S101, S103. exact HX.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S157. exact V157.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S158. exact V158.
  - unfold U.Drv_r__G1.Drv_r.UV. cbn [rho_sub rw]. rewrite S159. exact V159.
  - split; [intros Hp; exfalso; lia|]. intros _. cbn [rho_sub rw]. rewrite S241. reflexivity.
Qed.
End EEntries.

Section EChain.
Hypothesis EEX1 : ltac2:(tb__ "0|0|
S6S1dS33S1fS30Q40A1A1S4eS40R4R3R2R1A5S0S1dS63VF;A1Z1A3S5dS5S59S5S4cS4fR4R3A3S43R6A4S78A3F_;F_;Fmat;Fvm;Fg;Frho;").
Hypothesis EEX2 : ltac2:(tb__ "0|0|
S6S1dS33S1fS30Q40A1A1S4eSb5R4R3R2R1A5S0S1dS63VF;A1Z2A3S5dS5S59S5S4cS4fR4R3A3SbbR6A4S78A3F_;F_;Fmat;Fvm;Fg;Frho;").
Hypothesis EEX3 : ltac2:(tb__ "0|0|
S6S1dS33S1fS30Q40A1A1S4eSb6R4R3R2R1A5S0S1dS63VF;A1Z3A3S5dS5S59S5S4cS4fR4R3A3SbcR6A4S78A3F_;F_;Fmat;Fvm;Fg;Frho;").
Hypothesis EEX4 : ltac2:(tb__ "0|0|
S6S1dS33S1fS30Q40A1A1S4eSb7R4R3R2R1A5S0S1dS63VF;A1Z4A3S5dS5S59S5S4cS4fR4R3A3SbdR6A4S78A3F_;F_;Fmat;Fvm;Fg;Frho;").

Lemma eiter3 : ltac2:(tb__ "0|0|
S6S6S4dR1A1S6cZ3S63VF;A1A2S5dS5S5aS5VJD;S4fR4S3dS62A4SbaR3A4S78A3F_;F_;Frho;Fr0;").
Proof using EEX4 FSUMX HL6 HLM.
  intros r0 rho HT Hlt. destruct s_fz3_vals as (S12 & S13 & _). destruct fork_4 as (FfN & FfX & _). pose proof (calls_range F) as CR.
  assert (A : (242 <=? ss_next S_3)%positive = true) by reflexivity. apply Pos.leb_le in A.
  assert (B : (ss_next S_3 <=? NX3)%positive = true) by reflexivity. apply Pos.leb_le in B.
  apply (eiter_gen 4 r0 S_3 N_4 X_4 s_fz3 R_fz3 NX3 rho QN efr_fz3 chk_fz3 S12 S13 A posts_3 B FfN FfX ltac:(lia) HT).
  - intros rho2 g vm mat _ Hne. exfalso. lia.
  - exact EEX4.
Qed.

Lemma eiter2 : ltac2:(tb__ "0|0|
S6S6S4dR1A1S6cZ2S63VF;A1A2S5dS5S5aS5VJD;S4fR4S3dS62A4Sb9R3A4S78A3F_;F_;Frho;Fr0;").
Proof using EEX3 EEX4 FSUMX HL6 HLM.
  intros r0 rho HT Hlt. destruct s_fz2_vals as (S12 & S13 & _). destruct fork_3 as (FfN & FfX & _). pose proof (calls_range F) as CR.
  assert (A : (242 <=? ss_next S_2)%positive = true) by reflexivity. apply Pos.leb_le in A.
  assert (B : (ss_next S_2 <=? NX2)%positive = true) by reflexivity. apply Pos.leb_le in B.
  assert (C : (241 <? NX2)%positive = true) by reflexivity. apply Pos.ltb_lt in C.
  apply (eiter_gen 3 r0 S_2 N_3 X_3 s_fz2 R_fz2 NX2 rho QN efr_fz2 chk_fz2 S12 S13 A posts_2 B FfN FfX ltac:(lia) HT).
  - intros rho2 g vm mat HS2 Hne.
    apply (etriple_from _ (fun r w => TL r /\ SPJ segs (JD KL1 r tvL DTrue) S_3 r w)).
    { intros [tr [ms md]] Hw. destruct (fromN KL1 N_3 S_3 NX2 rho2 g vm mat tr ms md (proj1 N_3_objs) ent_S3 C HS2 Hw) as (rho' & HT' & HS'). exists rho'. split; assumption. }
    intros rho'. apply etriple_pure. intros HT'. apply (eiter3 rho' rho' HT'). lia.
  - exact EEX3.
Qed.

Lemma eiter1 : ltac2:(tb__ "0|0|
S6S6S4dR1A1S6cZ1S63VF;A1A2S5dS5S5aS5VJD;S4fR4S3dS62A4Sb8R3A4S78A3F_;F_;Frho;Fr0;").
Proof using EEX2 EEX3 EEX4 FSUMX HL6 HLM.
  intros r0 rho HT Hlt. destruct s_fz1_vals as (S12 & S13 & _). destruct fork_2 as (FfN & FfX & _). pose proof (calls_range F) as CR.
  assert (A : (242 <=? ss_next S_1)%positive = true) by reflexivity. apply Pos.leb_le in A.
  assert (B : (ss_next S_1 <=? NX1)%positive = true) by reflexivity. apply Pos.leb_le in B.
  assert (C : (241 <? NX1)%positive = true) by reflexivity. apply Pos.ltb_lt in C.
  apply (eiter_gen 2 r0 S_1 N_2 X_2 s_fz1 R_fz1 NX1 rho QN efr_fz1 chk_fz1 S12 S13 A posts_1 B FfN FfX ltac:(lia) HT).
  - intros rho2 g vm mat HS2 Hne.
    apply (etriple_from _ (fun r w => TL r /\ SPJ segs (JD KL1 r tvL DTrue) S_2 r w)).
    { intros [tr [ms md]] Hw. destruct (fromN KL1 N_2 S_2 NX1 rho2 g vm mat tr ms md (proj1 N_2_objs) ent_S2 C HS2 Hw) as (rho' & HT' & HS'). exists rho'. split; assumption. }
    intros rho'. apply etriple_pure. intros HT'. apply (eiter2 rho' rho' HT'). lia.
  - exact EEX2.
Qed.

Lemma loop_ex : ltac2:(tb__ "0|0|
S6S6S4dR1A1S5dS5S5aS5VJD;VKH;R3S3dS62A4S42R2A4S78A3F_;Frho;Fr0;").
Proof using EEX1 EEX2 EEX3 EEX4 FSUMX HL6 HLM.
  intros r0 rho HT. pose proof (calls_range F) as CR.
  assert (C : (241 <? NX0)%positive = true) by reflexivity. apply Pos.ltb_lt in C.
  apply (eiter0 r0 rho QN HT).
  - intros rho2 g vm mat HS2 Hne.
    apply (etriple_from _ (fun r w => TL r /\ SPJ segs (JD KL1 r tvL DTrue) S_1 r w)).
    { intros [tr [ms md]] Hw. destruct (fromN KL1 N_1 S_1 NX0 rho2 g vm mat tr ms md (proj1 N_1_objs) ent_S1 C HS2 Hw) as (rho' & HT' & HS'). exists rho'. split; assumption. }
    intros rho'. apply etriple_pure. intros HT'. apply (eiter1 rho' rho' HT'). lia.
  - exact EEX1.
Qed.

Theorem hl_ex2 : ltac2:(tb__ "0|0|
S6S6VTVc;Vcap;R1A2S6cZ0S64VF;A1A2S5dS5S5aS5VJD;VKH;R4SaaS62A4Sa9R3A4S78A3F_;F_;Frho;Fr0;").
Proof using EEX1 EEX2 EEX3 EEX4 FSUMX HL6 HLM. exact (ent2_ex QN loop_ex). Qed.

Theorem hl_ex0 : ltac2:(tb__ "0|0|
S6S93S35OF_;F_;S6VTVc;Vcap;R1A2S0S1dS64VF;A1Z0A3S5dS5S5aS5VJD;VKH;R5SabR4A4Sa8R3A4S78A3F_;F_;Frho;FD;Fr0;").
Proof using EEX1 EEX2 EEX3 EEX4 FSUMX HL6 HLM. exact (ent0_ex QN loop_ex). Qed.
End EChain.
End Ex.

End HL.
