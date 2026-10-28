(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "sub"; "mul"; "of_nat"; "pow"; "lt"; "opp"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_next"; "SVar"; "sprop"; "SLit"; "sstate"; "ss_facts"; "SAlu"; "reg_sv"; "DUnknown"; "mkObj"; "rw"; "sobj"; "ss_lenient"; "cell"; "SPUle"; "obj_wf"; "sprop_below"; "ss_objs"; "eval"; "rl"; "SPBranch"; "ss_pc"; "SPNot"; "SPUlt"; "holds"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "cons"; "nil"; "Some"; "option"; "length"; "false"; "prod"; "pair"; "None"; "app"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rs"; "QF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsCut"; "sym_run"; "RsEcall"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rs.RS.SX"; "DG"; "CAPG"; "DX"; "XOf"; "kOf"; "DM"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r"; "UV"; "tv0"; "tvK"; "KdR"; "KB"; "BR"; "HDR"; "INVG"; "INVK"; "INVX"; "chunk"; "tvG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx"; "f_F"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "instr"; "ALU_SUB"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "sv_subst"; "wsub_id_below"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "Model"; "FdEntry"; "m_vm_materialized"; "m_vmmaps"; "with_fds"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "rs"; "read_ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyRS"; "Eb"; "E3c"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "tv_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "NX0"; "CUTS"; "FUEL"; "K"; "KG"; "ES0mA"; "XE0"; "XEH"; "Cx_0g"; "Cx_0m"; "Cx_0s"; "ES0sA"; "IRS"; "K0"; "R0g"; "X_ref"; "ES0gA"; "ES0gB"; "ES0mB"; "ES0sB"; "O_rsU"; "O_src0t"; "P_E_rdA"; "R0m"; "R0s"; "T0gA"; "T0gB"; "T0mA"; "T0mB"; "T0sA"; "T0sB"; "T_gok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "snapJ"; "CAP"; "ALIGNED"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "tl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rs.RS.SX.LoopS"; "LoopIHs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "init_cost"; "malloc_cost"; "DRV_OPS"; "drvN"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "succ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m"; "DokS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states"; "T_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rs.RS"; "Dvm"; "@Corelib.Init.Peano"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue2"; "obj_forget"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.HdrPack"; "pack4_at"; "pack4_vals"; "pack4_word"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead"; "S_after_var"; "hdr_val"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List Bool.Bool PArith.PArith micromega.Lia.
From Stdlib Require Import Strings.Ascii Strings.String.
From stdpp Require Import bitvector.bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLayout MallocIface MallocLaws Contract ContractDrv Pristine ClientLaws Glue RoomS ContractS.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall SymBytes SymExit Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import
  SumConv CfgGlue CursorGlue ObjXform ObjUnbase CallGlue ListObj StrBytes InitLayout InitState InitStrs InitArg1 MuslWL MuslMemcpyHdr MuslMemcpy MuslMemcpyRS HdrPack ImgList
  DrvGlue DrvGlue2 SysExtra SysRead SysReadList DataWin TobjJV DrvJ DrvStatics DrvPristine DrvLoop DrvTail1 DrvWins.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec SpecConsts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy_rs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy_hdr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy_rs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import MAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import XLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac lia := slia.
Local Ltac nia := snia.

Definition QF : world -> Prop := fun _ => False.

Section RS.
Variable cx : Fctx.
Let sp := f_sp cx. Let brk := f_brk cx. Let mb := f_mb cx. Let draw := f_draw cx. Let inp := f_inp cx.
Let Hent : valid_entry48 imgU (mkEntry sp brk mb draw) inp := f_ent cx.
Let Hinp : valid_input_either inp := f_inp_ok cx.
Let argv := in_argv inp.
Let envp := in_envp inp.
Let argv0 : list byte := nth 0 argv [].
Let argv1 : list byte := nth 1 argv [].
Let fs := in_fs inp.
Let Hargc : length argv = 2%nat := f_argc cx.

Let md0 : Model := f_md0 cx.
Let Hfds0 : m_fds md0 = std_fds := f_fds0 cx.
Let Hfs : m_fs md0 = fs := f_fs0 cx.
Let mdo : Model := md_open md0 argv1.
Let ok : world -> Prop := f_ok cx.
Let SpecT : list event -> Prop := Spec inp.
Let HokK : forall K, K_tcons SpecT K -> ok_frame segs ok K := f_okK cx.
Let HokP : forall K, K_tcons SpecT K -> ok_pframe segs ok K := f_okP cx.
Let Hokh : ok_halted ok SpecT := f_okh cx.
Let Hmay : open_may_succeed argv1 fs := f_may cx.

Local Notation F := (f_F cx).
Let HF : fs_lookup fs argv1 = Some F := f_HF cx.
Let Hnd : argv1 <> dot_path := f_nd cx.
Local Notation L := (Z.of_nat (length (f_F cx))).

Let P0 := U.Drv_m__G1.Drv_m.P0 sp draw inp. Let P0_tp := U.Drv_m__G1.Drv_m.P0_tp sp draw inp.
Let P0_top := U.Drv_m__G1.Drv_m.P0_top sp draw inp.
Let wtop : word := U.Drv_m__G1.Drv_m.wtop sp.
Let JD := U.Drv_m__G1.Drv_m.JD sp draw inp.
Let Kd0 := U.Drv_m__G1.Drv_m.Kd0 inp md0.

Local Notation KdR := (U.Drv_r__G1.Drv_r.KdR cx).
Local Notation Kd0_KdR := (U.Drv_r__G1.Drv_r.Kd0_KdR cx).
Local Notation KdR_vmi := (U.Drv_r__G1.Drv_r.KdR_vmi cx).
Local Notation JD_stable := (U.Drv_r__G1.Drv_r.JD_stable cx).
Local Notation KB := (U.Drv_r__G1.Drv_r.KB cx).
Local Notation chunk := (U.Drv_r__G1.Drv_r.chunk cx).
Local Notation chunk_length := (U.Drv_r__G1.Drv_r.chunk_length cx).
Local Notation jread_rs := (U.Drv_r__G1.Drv_r.jread_rs cx).
Local Notation kread_rs := (U.Drv_r__G1.Drv_r.kread_rs cx).
Local Notation kread_list := (U.Drv_r__G1.Drv_r.kread_list cx).
Local Notation JD_okf := (U.Drv_r__G1.Drv_r.JD_okf cx).
Local Notation KdR_tcons := (U.Drv_r__G1.Drv_r.KdR_tcons cx).
Local Notation KB_okf := (U.Drv_r__G1.Drv_r.KB_okf cx).
Local Notation KB_okp := (U.Drv_r__G1.Drv_r.KB_okp cx).
Local Notation okside := (U.Drv_r__G1.Drv_r.okside cx).
Local Notation okside_i := (U.Drv_r__G1.Drv_r.okside_i cx).
Local Notation HDRW := (U.Drv_r__G1.Drv_r.HDRW cx).
Local Notation HDR := (U.Drv_r__G1.Drv_r.HDR cx).
Local Notation INVK := (U.Drv_r__G1.Drv_r.INVK cx).
Local Notation INVG := (U.Drv_r__G1.Drv_r.INVG cx).
Local Notation INVX := (U.Drv_r__G1.Drv_r.INVX cx).
Local Notation INVK_agree := (U.Drv_r__G1.Drv_r.INVK_agree cx).
Local Notation INVG_agree := (U.Drv_r__G1.Drv_r.INVG_agree cx).
Local Notation tvK_below := (U.Drv_r__G1.Drv_r.tvK_below cx).
Local Notation tvb_0 := (U.Drv_r__G1.Drv_r.tvb_0 cx).
Local Notation JD_geom := (U.Drv_r__G1.Drv_r.JD_geom cx).
Local Notation JD_monoK := (U.Drv_r__G1.Drv_r.JD_monoK cx).
Local Notation reenter := (U.Drv_r__G1.Drv_r.reenter cx).
Local Notation pure_callD := (U.Drv_r__G1.Drv_r.pure_callD cx).
Local Notation HDR_sext := (U.Drv_r__G1.Drv_r.HDR_sext cx).
Local Notation hdr_chunk0 := (U.Drv_r__G1.Drv_r.hdr_chunk0 cx).
Local Notation T_ok_of_JGi := (U.Drv_r__G1.Drv_r.T_ok_of_JGi cx).

Definition Dvm (D : MA -> Model -> Prop) : Prop := ltac2:(tb__ "0|0|
S71S65S65S0S64S68R1A1S68R2A1A3S0S2eS39Q40A1A1S67R2A1S67R3A1A3VD;R5R4A2VD;R6R4A2F_;F_;F_;Fm';Fm;FA;").

Section SX.

Variable X0 : Z.
Hypothesis HX0 : ltac2:(tb__ "0|0|
S8S9S9cSdZ2Z1cA2A2VX0;A2").
Hypothesis MBX : malloc_big_S_U.
Hypothesis FDX : free_drv_S_U.

Definition DX (k X : Z) : MA -> Model -> Prop := ltac2:(tb__ "0|0|
S71S65S1S9fS72Vk;R2A3Sb0R1VX;A2A2Lmd;LA;").

Definition kOf (g : Z) : Z := DRV_OPS - 2 * g.
Definition XOf (cap g : Z) : Z := ltac2:(tb__ "0|1|
SaSaSaVX0;S9cA2SaSbZ2M0Vcap;A2SdG0Z11A2A2A2SbVg;SdG0Z15A2A2A2").
Definition DG (cap g : Z) : MA -> Model -> Prop := ltac2:(tb__ "0|0|
S49S4bVg;A1S4aVcap;Vg;A2A2").

Definition CAPG (cap g : Z) : Prop := ltac2:(tb__ "0|0|
S0S5Vcap;SbZ10000SdZ2Vg;A2A2A3").

Lemma DX_fds : ltac2:(tb__ "0|0|
S5S5S71S65S2eS35S39Q40A1S66A2A1S49R5R4R3R2A4S49R6R5R4S69R2R3A2A4F_;Ff;Fmd;FA;FX;Fk;").
Proof using . clear. intros k X A md f [Hd Hv]. split; [exact Hd | exact (vm_roomS_frame md (with_fds f md) X eq_refl eq_refl Hv)]. Qed.
Lemma DG_fds : ltac2:(tb__ "0|0|
S5S5S71S65S2eS35S39Q40A1S66A2A1S47R5R4R3R2A4S47R6R5R4S69R2R3A2A4F_;Ff;Fmd;FA;Fg;Fcap;").
Proof using . intros cap g. exact (DX_fds (kOf g) (XOf cap g)). Qed.
Lemma DX_vm : ltac2:(tb__ "0|0|
S5S5Sa7S49R2R1A2A1FX;Fk;").
Proof using . clear. intros k X A m m' Hv Hm [Hd Hr]. split; [exact Hd | exact (vm_roomS_frame m m' X Hv Hm Hr)]. Qed.
Lemma DG_vm : ltac2:(tb__ "0|0|
S5S5Sa7S47R2R1A2A1Fg;Fcap;").
Proof using . intros cap g. exact (DX_vm (kOf g) (XOf cap g)). Qed.
Lemma DX0 : ltac2:(tb__ "0|0|
S71S65S3Sa5VX0;R2R1A3S49S9eSaVX0;S9cA2R2R1A4A2Fmd;FA;").
Proof using . clear. intros A md. split; intros H; exact H. Qed.
Lemma DG0 : ltac2:(tb__ "0|0|
S71S65S3S47Z10000Z0R2R1A4S49S9eSaVX0;S9cA2R2R1A4A2Fmd;FA;").
Proof using . clear. intros A md. unfold DG, kOf, XOf. replace (DRV_OPS - 2 * 0) with DRV_OPS by lia. replace (X0 - init_cost - (2 * 65536 - 2 ^ 17) - 0 * 2 ^ 21) with (X0 - init_cost) by lia. split; intros H; exact H. Qed.
Lemma pow_g_bound : ltac2:(tb__ "0|1|
S5S8Z0R1A2S8SbZ10000SdZ2M0R2A2A2SdG0Z1aA2A2S8R3ZaA2F_;F_;Fg;").
Proof using .
  clear. intros g Hg H. destruct (Z_lt_le_dec 10 g) as [Hl|Hl]; [|exact Hl]. exfalso.
  assert (2 ^ 11 <= 2 ^ g) by (apply Z.pow_le_mono_r; lia). change (2 ^ 26) with (65536 * 2 ^ 10) in H.
  assert (2 ^ 10 < 2 ^ 11) by (apply Z.pow_lt_mono_r; lia). nia.
Qed.

Lemma g_lt_bound : ltac2:(tb__ "0|1|
S5S5S8Z0R1A2S48R3R2A2SeR4SdZ2M0Z1aA2A2S1S8R4Z9A2S8R5SdG0Z19A2A2A2F_;F_;F_;Fg;Fcap;").
Proof using .
  clear. intros cap g Hg -> Hlt. destruct (Z_lt_le_dec 9 g) as [Hl|Hl].
  - exfalso. assert (2 ^ 10 <= 2 ^ g) by (apply Z.pow_le_mono_r; lia). change (2 ^ 26) with (65536 * 2 ^ 10) in Hlt. nia.
  - split; [exact Hl|]. assert (2 ^ g <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 25) with (65536 * 2 ^ 9). nia.
Qed.
Lemma init_cost_val : init_cost = 2 ^ 25. Proof using . reflexivity. Qed.
Lemma DRV_OPS_val : DRV_OPS = 40. Proof using . reflexivity. Qed.
Lemma malloc_cost_val : ltac2:(tb__ "0|0|
S5S0S5S9dR1A1S9R1SdZ2Z15A2A2A3Fn;"). Proof using . reflexivity. Qed.
Lemma MMAP_THRESHOLD_val : MMAP_THRESHOLD = 131052. Proof using . reflexivity. Qed.

Definition DM (cap g : Z) : MA -> Model -> Prop := ltac2:(tb__ "0|0|
S49SaS4bVg;A1Z1A2SaS4aVcap;Vg;A2S9dSbZ2Vcap;A2A1A2A2").
Lemma DG_next : ltac2:(tb__ "0|2|
S5S5S71S65S49SaSaS4bR3A1Z1M0A2G0A2SaS4aR4R3A2S9dSbZ2M1R4A2A1A2R2R1A4S47SbG1R5A2S9R4G0A2R3R2A4F_;Fmd;FA;Fg;Fcap;").
Proof using .
  clear. intros cap g A md [Hd Hv]. unfold DG, DX, kOf, XOf in *. rewrite malloc_cost_val in Hv.
  split; [replace (DRV_OPS - 2 * (g + 1)) with (DRV_OPS - 2 * g - 1 - 1) by lia; exact Hd|].
  eapply vm_roomS_mono; [|exact Hv]. pose proof (vm_roomS_nonneg _ _ Hv). lia.
Qed.

Section LoopS.
Variable r0 : valuation.
Let JS (off cap g : Z) : jpred := ltac2:(tb__ "0|0|
VJD;S50Vcx;Voff;A2Vr0;S4fS47Vcap;Vg;A2A4").

Hypothesis TXEH : ltac2:(tb__ "0|0|
S11S5S5S56Vcx;R2R3A3S1S8Z0R2A2S8R2ZaA2A2S48R4R3A2S3cS7Vok;S3fS7VJS;ScS33S39Q8A1S59Vcx;A1A2A1R5R4A3S7aR6A4S3eA4F_;F_;F_;Fg;Fcap;Frho;").
Hypothesis TXref : ltac2:(tb__ "0|1|
S11S5S0S5S4dR2P65A2SdZ2Z1aA2M0A3S8G0ScS33S39Q8A1S59Vcx;A1A2A1A2S53Vcx;S1cR4P67A2A2S1S8Z0R4A2S8R4ZaA2A2S3cS7Vok;S3fS7VJS;G0G0R5A3S82R6A4S3eA4F_;F_;F_;F_;Fg;Frho;").

Definition LoopIHs (m : Z) : Prop := ltac2:(tb__ "0|3|
S1S11S5S5S5SeSbZ2M0SaScS33S39Q8A1S59Vcx;A1A2A1M1R3A2A2Vm;A2S55Vcx;R4R3R5A4S1S8Z0R3A2S48R4R3A2A2M2S3cS7Vok;S3fS7VJS;R6R5R4A3S76R7A4S3eA4F_;F_;F_;Fg;Fcap;Flen;Frho;S11S5S5SeS9SbG0SaG1R2A2A2Z1A2Vm;A2S54Vcx;R3R4A3G2S3cS7Vok;S3fS7VJS;R5R5R4A3S77R6A4S3eA4F_;F_;F_;Fg;Fcap;Frho;A2").

Lemma exit_viaS : ltac2:(tb__ "0|e|
S16S16S16S16S63S2eS35S10S10A2M0A1M1S11S6S5S5S0S2cS2bR9A1S2dA3S0S32S35G1S2eS14A1M2A2M3A1Sa3RbRaA2S31G3S36G1G2S2fG0S36S10S10S13R4A1S15Z0M4A1A4S30G0A1A3S30S14A1M5A4A2A3S0S32S2eS41A1M6A1S44S7S75S74RbS2dA5S31G6S2fS41S42RaS43A2S30S41A1A3A2A3S0S2cS1eRcA1S34A3S0S16S9aS2fS14S20S60RaS13P65M7A1M8A2S15Z4000000A1M9A2G5A3RcA2RbA3S0S2cS6cRcS7aRbA3S2dA3S0S2cS61RcP1fMaA2S2dA3S0S2cS6fRdRcS4fA3S2dA3Sa0GaS12R11A1A2S0S2cS70S12R12A1MbReA2S2dA3S0S2cS97S14S22GbA1S2fS14S20S60R10G8A2G9A2G5A3A3S2dA3S0S39Q40McA1MdS1cRfReA2S3bGcG4A2A3S8G4RdA2S48RfReA2S11S6Sa1R1S12R19A1A2S0GdS1cR3R2A2S1cR15R2A2A3F_;Fi;S1S8S3aGcS24R2S5fR16G7A2A2A2SdZ2Z1aA2A2S56Vcx;R12S62R2R16A2A3A2F_;Fr;S3cS7Vok;S3fS7VJD;S50Vcx;ScS33S39Q8A1S59Vcx;A1A2A1A2Vr0;R14S47R11R10A2A4R19R13A4S3eA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fg;Fcap;Fv;Frho;FtvL;Fsx;FXK;FX;FPZ;FP;").
Proof using TXEH.
  intros P PZ X XK sx tvL rho v cap g Hwf Hd Hrun Hlen HXK He Hid Htv Hn Hb Hfb Hz Hg Hcap HI.
  apply (triple_restate segs ok _ rho P PZ _ _ Hwf Hd).
  { constructor; [|constructor]. cbn [fst snd eval]. rewrite Hz. apply bv_eq. reflexivity. }
  eapply (run_trJ segs ok FUEL CUTS PZ _ _ rho _ Hrun Hlen); [apply JD_okf, KdR_tcons | apply JD_stable; [lia|exact Hb] |].
  intros Lf rho1 [<-|[]] Hag. cbn [lf_state].
  destruct (HI rho1 ltac:(intros i Hi; destruct Hag as (Hw & _); symmetry; apply Hw; exact Hi)) as (H26 & HX).
  apply (triple_add_facts segs ok _ rho1 _ X XK _ HXK Hfb).
  { constructor; [|constructor]. apply holds_ule. change (sv_subst sx (SVar 101)) with (wsub_get sx 101).
    rewrite CursorGlue.U_lit. unfold M64v. rewrite Z.mod_small by lia. exact H26. }
  apply (reenter r0 (KdR L) tvL tvK (DG cap g) XK XEH sx rho1 _ (ss_next PZ) He Hid Hn Hb Htv).
  apply (TXEH _ cap g HX); [|exact Hcap]. split; [exact Hg|]. apply pow_g_bound; [exact Hg|]. unfold CAPG in Hcap. rewrite <- Hcap. destruct HX as (_ & _ & _ & _ & _ & [_ HC]). exact HC.
Qed.

Section SCopyTail.
Variables (T Tr Tm G H GR GK HK : sstate) (sh sg : wsub) (xs : list xform) (FKl FGl : list sprop).
Hypothesis Tr_eq : ltac2:(tb__ "0|4|
S0S16S9bS9bVT;U0S1bS13P66A1S13P64A1M0S18S5aG0S13P99A1M1A3S30S1fA1M2S1aA5A3U1S1bS15Z0A1S15S6aA1M3S18S5aG1G3A3G2S1aA5A3VTr;A3").
Hypothesis T_objs : ltac2:(tb__ "0|8|
S1S0S32S1dA1M0S96S1dS23VT;A1U0M1A3S31S1dS1bS18S5aS13P66A1M2S13P64A1M3A3S15Z0A1M4S13P99A1M5S30S1fA1M6S1aA5A2A3S1S0G0S96S1dS23S9bVT;G1S1bG2G3S18S5aG3G5A3G6S1aA5A3A1U1A3S31S1dS1bS15S6aA1G4G5G6S1aA5A2A3S1S0S6S12VT;A1M7S12VTr;A1A3S1S0S2eS14A1S17VTr;A1S17VT;A1A3S1S0S6S12VTm;A1G7A3S1S0S6S12VH;A1G7A3S1S0S6S12VG;A1G7A3S0S2cS1eVTm;A1S34A3A2A2A2A2A2A2A2").
Hypothesis T_next : ss_next T = 194%positive.
Hypothesis xs_ok : ltac2:(tb__ "0|0|
S0S32S16A1Sa4VTr;Vxs;A2S31S16VTm;A2A3").
Hypothesis run_t : ltac2:(tb__ "0|1|
S0S32S2eS41A1M0A1S44S7S75S74VTm;S2dA5S31G0S2fS41S42VG;S43A2S2fS41S42VH;S43A2S30S41A1A3A3A2A3").
Hypothesis HG_regs : ltac2:(tb__ "0|4|
S1S0S10S19VH;Z13M0A2S18S5aS13P99A1S13P64A1A3M1A3S1S0S10S19VH;Z15M2A2S13P65A1M3A3S1S0S10S19VG;G0A2G1A3S1S0S10S19VG;G2A2G3A3S0S32S14A1S96S14S17VH;A1U0A3S31S14S28S26S5bG1G3A3A1A2A3A2A2A2A2").
Hypothesis FKl_eq : ltac2:(tb__ "0|2|
S0S2eS14A1VFKl;S2fS14S29S60Vsh;S13P64A1A2M0S60Vsh;S13P65A1A2M1A2S2fS14S20S15Z4A1G0A2S2fS14S20G1S15Z4000000A1A2S30S14A1A3A3A3A3").
Hypothesis HK_eq : ltac2:(tb__ "0|0|
S0S16S9aVFKl;VH;A2VHK;A3").
Hypothesis ent_h : ltac2:(tb__ "0|0|
S0S2cS6cVHK;S76Vsh;A3S2dA3").
Hypothesis sh_vals : ltac2:(tb__ "0|4|
S1S0S10S5fVsh;P64M0A2S60Vsh;S13G0A1A2A3S1S0S10S5fVsh;P65M1A2S13G1A1A3S1S0S10S5fVsh;P66M2A2S13G2A1A3S0S10S5fVsh;P67M3A2S13G3A1A3A2A2A2").
Hypothesis sh_100 : ltac2:(tb__ "0|1|
S0S10S60Vsh;S13P64A1M0A2S18S5aS13P99A1G0A3A3").
Hypothesis G_fact : ltac2:(tb__ "0|0|
S0S32S14A1S96S14S17VG;A1U0A3S31S14S26S5bS19VG;Z13A2S19VG;Z15A2A3A2A3").
Hypothesis diff_GR : ltac2:(tb__ "0|4|
S0S32S35S2eS35S10S10A2M0A1M1S2eS14A1M2A2M3A1Sa3VG;VGR;A2S31G3S36G1G2S2fG0S36S10S10S19VG;Z13A2S19VG;Z15A2A4S30G0A1A3S30S14A1A4A2A3").
Hypothesis swf_GR : swf GR = true.
Hypothesis GR_next : ltac2:(tb__ "0|0|
S0S6S12VGR;A1S12VT;A1A3").
Hypothesis FGl_eq : ltac2:(tb__ "0|0|
S0S2eS14A1VFGl;S2fS14S20S60Vsg;S13P65A1A2S15Z4000000A1A2S30S14A1A3A3").
Hypothesis GK_eq : ltac2:(tb__ "0|0|
S0S16S9aVFGl;VGR;A2VGK;A3").
Hypothesis ent_g : ltac2:(tb__ "0|0|
S0S2cS6cVGK;S77Vsg;A3S2dA3").
Hypothesis sg_vals : ltac2:(tb__ "0|3|
S1S0S10S5fVsg;P65M0A2S13G0A1A3S1S0S10S5fVsg;P66M1A2S13G1A1A3S0S10S5fVsg;P67M2A2S13G2A1A3A2A2").
Hypothesis ids : ltac2:(tb__ "0|1|
S1S0S2cS61Vsh;P1fM0A2S2dA3S0S2cS61Vsg;G0A2S2dA3A2").
Hypothesis tvs : ltac2:(tb__ "0|0|
S1S0S2cS6fVsh;S4fS4fA3S2dA3S0S2cS6fVsg;S4fS4fA3S2dA3A2").
Hypothesis wf_back : ltac2:(tb__ "0|5|
S1S0S2cS21S12VT;A1M0S1bS13P66A1S13P64A1M1S18S5aG1S13P99A1M2A3S30S1fA1M3S1aA5A2S2dA3S0S2cS21G0S1bS15Z0A1S15S6aA1M4S18S5aG2G4A3G3S1aA5A2S2dA3A2").

Lemma copy_tailS : ltac2:(tb__ "0|4|
S5S11S5S5S5S5S5S99R7A1S8SbZ2SaScS33S39Q8A1S59Vcx;A1A2A1M0R6A2A2R8A2S0S5S4dR8P64A2R7A3S0S5S4dR9P65A2R7A3S0S5S4dRaP66A2R6A3S0S5S4dRbP99A2R8A3S53Vcx;S1cRcP67A2A2S8Z4M1RcA2SeZ0M2RbA2S8S9ReRcA2RdA2S8S9RfRdA2G0A2S4S95S9R10ReA2M3A1S0S5G3G0A3A2S94R10A1S8S9S9RfR11A2G1A2Z7fffff800000A2S8G2RfA2S48R13R10A2S3cS7Vok;S3fS7VJS;S9R15R13A2R14R11A3VT;R16A4S3eA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fg;Fb;Fgot;Fcap;Flen;Frho;Fm;").
Proof using FGl_eq FKl_eq GK_eq G_fact GR_next HG_regs HK_eq T_next T_objs Tr_eq diff_GR ent_g ent_h ids run_t sg_vals sh_100 sh_vals swf_GR tvs wf_back xs_ok.
  intros m rho len cap got b g [IHK IHG] Hm U100 U101 U102 U153 I3 H4 Hgp Hlc HlL Hal I7 Gb Hg Hcap.
  pose proof (CAP_facts cap I7) as (C1 & C2 & _). pose proof rs_range as RR. unfold UV in U100, U101, U102, U153.
  pose proof (bv_urange (rw rho 102)) as R102. pose proof (bv_urange (rw rho 153)) as R153.
  destruct T_objs as (To0 & To1 & NxTr & FTr & NxTm & NxH & NxG & LnTm). destruct HG_regs as (RH19 & RH21 & RG19 & RG21 & Hf0).
  destruct sh_vals as (Sh0 & Sh1 & Sh2 & Sh3). destruct sg_vals as (Sg1 & Sg2 & Sg3). destruct ids as [Idh Idg]. destruct tvs as [Th Tg]. destruct wf_back as [Wb1 Wb2].
  assert (E100 : bv_unsigned (eval rho (SVar 100)) = len) by exact U100.
  assert (E153 : bv_unsigned (eval rho (SVar 153)) = got) by exact U153.
  assert (E102 : bv_unsigned (eval rho (SVar 102)) = b) by exact U102.
  assert (Edst : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 102) (SVar 100))) = b + len) by (apply (Uadd rho (SVar 102) (SVar 100) _ _ E102 E100); lia).
  assert (Elg : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 100) (SVar 153))) = len + got) by (apply (Uadd rho (SVar 100) (SVar 153) _ _ E100 E153); lia).
  assert (Egr : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 153) (SLit rs))) = got + rs) by (apply (Uadd rho (SVar 153) (SLit rs) _ _ E153 (Ulit rho rs ltac:(lia))); lia).

  set (Obk := mkObj (SVar 102) (SVar 100) (SAlu ALU_ADD (SVar 100) (SVar 153)) [] DUnknown) in *.
  set (Osb := mkObj (SLit 0) (SLit rs) (SAlu ALU_ADD (SVar 153) (SLit rs)) [] DUnknown) in *.
  eapply triple_conseq with (P := SPJ segs (JS (len + got) cap g) Tr rho); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- Tr_eq.
    apply (SPJ_reshape segs _ rho (reshape_obj_at T 0 Obk) 1 _ Osb w To1 eq_refl eq_refl eq_refl); [| |].
    { cbn [ss_next reshape_obj_at set_objs]. exact Wb2. }
    { intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi Osb]. rewrite (Ulit rho 0), (Ulit rho rs) by lia.
      rewrite !soff_lit_small by lia. rewrite (soff_small rho _ _ Egr) by lia. rewrite (soff_small rho _ _ E153) by lia. lia. }
    apply (SPJ_reshape segs _ rho T 0 _ Obk w To0 eq_refl eq_refl eq_refl Wb1); [|exact Hw].
    intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi Obk]. rewrite Edst, E102. rewrite !soff_lit_small by lia.
    rewrite (soff_small rho _ _ E100) by lia. rewrite (soff_small rho _ _ Elg) by lia. rewrite (soff_small rho _ _ E153) by lia. lia. }
  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs rho Tr Tm w xs_ok Hw) | intros w Hw; exact Hw |].
  eapply (run_trJ segs ok FUEL CUTS Tm _ _ rho _ run_t LnTm); [apply JD_okf, KdR_tcons | apply JD_stable; [rewrite NxTm, T_next; lia | rewrite NxTm, T_next; apply tvK_below; lia] |].
  rewrite NxTm, T_next. intros Lf rho3 [<-|[<-|[]]] Hag3; cbn [lf_state].
  -
    apply triple_factsJ. intros HFG.
    pose proof (Forall_nth_error _ _ _ _ HFG G_fact) as Hf. clear HFG. apply holds_beq in Hf. rewrite RG19, RG21 in Hf.
    assert (T153 : bv_unsigned (rw rho3 153) = got) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U153).
    assert (T100 : bv_unsigned (rw rho3 100) = len) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U100).
    assert (T101 : bv_unsigned (rw rho3 101) = cap) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U101).
    assert (T103 : rw rho3 103 = rw rho 103) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; reflexivity).
    rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) in Hf by lia. cbn [eval] in Hf. rewrite T101 in Hf.
    apply (triple_restate segs ok _ rho3 G GR _ _ swf_GR diff_GR).
    { constructor; [|constructor]. cbn [fst snd]. rewrite RG19, RG21. apply bv_eq. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. cbn [eval]. lia. }
    apply (triple_add_facts segs ok _ rho3 FGl GR GK _ GK_eq).
    { rewrite FGl_eq. change (sv_subst sg (SVar 101)) with (wsub_get sg 101). rewrite Sg1. cbn -[Pos.ltb]. rewrite GR_next, T_next. reflexivity. }
    { rewrite FGl_eq. change (sv_subst sg (SVar 101)) with (wsub_get sg 101). rewrite Sg1.
      constructor; [|constructor]. apply holds_ule. cbn [eval]. rewrite T101, lit_unsigned. cbn. lia. }
    apply (reenter r0 (KdR (len + got)) tvK tvK (DG cap g) GK KG sg rho3 _ 194 ent_g Idg ltac:(lia) (tvK_below 194 ltac:(lia)) Tg).
    replace (len + got) with cap by lia. apply (IHG _ cap g); [lia| |split; [exact Hg|exact Hcap]].
    unfold INVG, UV. cbn [rho_sub rw]. rewrite Sg1, Sg3. cbn [eval]. rewrite T101, T103.
    split; [reflexivity|]. split; [exact I3|]. split; [lia | exact I7].
  -
    apply triple_factsJ. intros HFH.
    pose proof (Forall_nth_error _ _ _ _ HFH Hf0) as Hf. clear HFH. apply holds_nbeq in Hf.
    assert (T153 : bv_unsigned (rw rho3 153) = got) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U153).
    assert (T100 : bv_unsigned (rw rho3 100) = len) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U100).
    assert (T101 : bv_unsigned (rw rho3 101) = cap) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U101).
    assert (T103 : rw rho3 103 = rw rho 103) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; reflexivity).
    rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) in Hf by lia. cbn [eval] in Hf. rewrite T101 in Hf.
    apply (triple_add_facts segs ok _ rho3 FKl H HK _ HK_eq).
    { rewrite FKl_eq, sh_100. change (sv_subst sh (SVar 101)) with (wsub_get sh 101). rewrite Sh1. cbn -[Pos.ltb]. rewrite NxH, T_next. reflexivity. }
    { rewrite FKl_eq, sh_100. change (sv_subst sh (SVar 101)) with (wsub_get sh 101). rewrite Sh1.
      constructor; [|constructor; [|constructor; [|constructor]]].
      - apply holds_ult. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. cbn [eval]. rewrite T101. lia.
      - apply holds_ule. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. rewrite (Ulit rho3 4) by lia. lia.
      - apply holds_ule. cbn [eval]. rewrite T101, lit_unsigned. cbn. lia. }
    apply (reenter r0 (KdR (len + got)) tvK tvK (DG cap g) HK K sh rho3 _ 194 ent_h Idh ltac:(lia) (tvK_below 194 ltac:(lia)) Th).
    apply (IHK _ (len + got) cap g); [lia| |split; [exact Hg|exact Hcap]].
    unfold INVK, UV. cbn [rho_sub rw]. rewrite Sh0, sh_100, Sh1, Sh3. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. cbn [eval]. rewrite T101, T103.
    split; [lia|]. split; [reflexivity|]. split; [exact I3|]. split; [lia|]. split; [lia|]. split; [exact Hal | exact I7].
Qed.
End SCopyTail.

Lemma copyAS : ltac2:(tb__ "0|4|
S5S11S5S5S5S5S5S99R7A1S8SbZ2SaScS33S39Q8A1S59Vcx;A1A2A1M0R6A2A2R8A2S0S5S4dR8P64A2R7A3S0S5S4dR9P65A2R7A3S0S5S4dRaP66A2R6A3S0S5S4dRbP99A2R8A3S53Vcx;S1cRcP67A2A2S8Z4M1RcA2S1SeZ0M2RbA2S8RbZ10000A2A2S8S9ReRcA2RdA2S8S9RfRdA2G0A2S4S95S9R10ReA2M3A1S0S5G3G0A3A2S94R10A1S8S9S9RfR11A2G1A2Z7fffff800000A2S8S9Z1000Z10A2R10A2S8G2R10A2S48R14R11A2S3cS7Vok;S3fS7VJS;S9R16R14A2R15R12A3S89R17A4S3eA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fg;Fb;Fgot;Fcap;Flen;Frho;Fm;").
Proof using TXEH.
  intros m rho len cap got b g IH Hm U100 U101 U102 U153 I3 H4 Hgp Hlc HlL Hal I7 Gb Gb0 Hg Hcap.
  pose proof (CAP_facts cap I7) as (C1 & C2 & _). pose proof rs_range as RR.
  pose proof U100 as E100. pose proof U101 as E101. pose proof U102 as E102. pose proof U153 as E153. unfold UV in E100, E101, E102, E153.
  destruct nexts_A as (_ & _ & NxPA & NxA & _ & _ & _ & NxCr & NxTa & NxTb). destruct lenient_A as (_ & _ & LnPA & _).
  destruct fbX_A as (_ & _ & FbpA). destruct wfb_A as (Wb1 & Wb2 & Wd & Ws). destruct GR_nexts as (NGa & NGb & SGa & SGb).
  destruct C_E_rdA_shape as (Cpc & Cnx & C10 & C11 & C12 & Co1 & CoI). destruct Cr_E_rdA_pre as (Xo3 & Xo8 & FCr & NCr).

  apply (triple_add_facts segs ok _ rho F_E_rdA P_E_rdA PP_E_rdA _ PP_E_rdA_eq FbpA).
  { constructor; [|constructor; [|constructor; [|constructor]]].
    - apply holds_nbeq. cbn [eval]. rewrite E153, lit_unsigned. cbn. lia.
    - apply holds_ule. cbn [eval]. rewrite E153, lit_unsigned. cbn. lia.
    - apply holds_ule. rewrite (Uadd rho (SVar 100) (SVar 153) len got E100 E153) by lia. cbn [eval]. rewrite E101. lia. }
  eapply (run_trJ segs ok FUEL CUTS PP_E_rdA _ _ rho _ run_pp_E_rdA LnPA); [apply JD_okf, KdR_tcons | apply JD_stable; [|apply tvK_below]; rewrite NxPA; lia |].
  rewrite NxPA. intros Lf rho2 [<-|[]] Hag2; cbn [lf_state].
  assert (T153 : bv_unsigned (rw rho2 153) = got) by (destruct Hag2 as (Hw & _); rewrite <- Hw by lia; exact E153).
  assert (T100 : bv_unsigned (rw rho2 100) = len) by (destruct Hag2 as (Hw & _); rewrite <- Hw by lia; exact E100).
  assert (T101 : bv_unsigned (rw rho2 101) = cap) by (destruct Hag2 as (Hw & _); rewrite <- Hw by lia; exact E101).
  assert (T102 : bv_unsigned (rw rho2 102) = b) by (destruct Hag2 as (Hw & _); rewrite <- Hw by lia; exact E102).
  assert (T103 : rw rho2 103 = rw rho 103) by (destruct Hag2 as (Hw & _); rewrite <- Hw by lia; reflexivity).
  assert (Edst : bv_unsigned (eval rho2 (SAlu ALU_ADD (SVar 102) (SVar 100))) = b + len) by (apply (Uadd rho2 (SVar 102) (SVar 100) _ _ T102 T100); lia).
  assert (Elg : bv_unsigned (eval rho2 (SAlu ALU_ADD (SVar 100) (SVar 153))) = len + got) by (apply (Uadd rho2 (SVar 100) (SVar 153) _ _ T100 T153); lia).
  assert (Egr : bv_unsigned (eval rho2 (SAlu ALU_ADD (SVar 153) (SLit rs))) = got + rs) by (apply (Uadd rho2 (SVar 153) (SLit rs) _ _ T153 (Ulit rho2 rs ltac:(lia))); lia).

  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_cE_rdA rho2 C_E_rdA Cx_E_rdA w xs_cE_rdA_ok Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq with (P := SPJ segs (JS (len + got) cap g) Cr_E_rdA rho2); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- Cr_E_rdA_eq.
    apply (SPJ_reshape segs _ rho2 (reshape_obj_at Cx_E_rdA 3 O_dstE_rdA) (IRS + 3) _ O_srcE_rdA w Xo8 eq_refl eq_refl eq_refl); [exact Ws| |].
    { intros _. unfold obj_lo_of, obj_hi_of, O_srcE_rdA. cbn [ob_base ob_lo ob_hi]. rewrite (Ulit rho2 0), (Ulit rho2 rs) by lia.
      rewrite !soff_lit_small by lia. rewrite (soff_small rho2 _ _ Egr) by lia. change (eval rho2 (SVar 153)) with (rw rho2 153). rewrite (soff_small rho2 (SVar 153) got T153) by lia. lia. }
    apply (SPJ_reshape segs _ rho2 Cx_E_rdA 3 _ O_dstE_rdA w Xo3 eq_refl eq_refl eq_refl Wd); [|exact Hw].
    intros _. unfold obj_lo_of, obj_hi_of, O_dstE_rdA. cbn [ob_base ob_lo ob_hi]. rewrite Edst. change (eval rho2 (SVar 102)) with (rw rho2 102). rewrite T102.
    rewrite !soff_lit_small by lia. rewrite (soff_small rho2 (SVar 100) len T100) by lia. rewrite (soff_small rho2 _ _ Elg) by lia. rewrite (soff_small rho2 (SVar 153) got T153) by lia. lia. }

  assert (MSUM : forall rho1, triple segs ok (SP segs (fun tr md => JS (len + got) cap g rho2 tr md) PreG rho1)
                                         (LQ segs (fun tr md => JS (len + got) cap g rho2 tr md) (ss_next PreG) rho1 U.Str_memcpy__G1.Str_memcpy.Posts_memcpy)).
  { intros rho1. apply U.Str_memcpy__G1.Str_memcpy.memcpy_sum. apply HokK. intros tr md (Ai & (_ & Hk & _) & _). exact (KdR_tcons _ tr md Hk). }
  apply (pure_callD r0 (KdR (len + got)) tvK (DG cap g) Cr_E_rdA PreG s_cE_rdA R_cE_rdA U.Str_memcpy__G1.Str_memcpy.Posts_memcpy rho2 _ MSUM efr_cE_rdA chk_cE_rdA
           ltac:(rewrite NxCr; lia) ltac:(rewrite NxCr; apply tvK_below; lia) fb_cE_rdA).
  intros Lf rho3 HinL Hag3. rewrite NxCr in Hag3.
  assert (S153 : UV rho3 153 = got) by (unfold UV; destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact T153).
  assert (S100 : UV rho3 100 = len) by (unfold UV; destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact T100).
  assert (S101 : UV rho3 101 = cap) by (unfold UV; destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact T101).
  assert (S102 : UV rho3 102 = b) by (unfold UV; destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact T102).
  assert (S103 : HDR (rw rho3 103)) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; rewrite T103; exact I3).
  destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
  - rewrite TE_rdAa_eq.
    exact (copy_tailS TE_rdAa TrE_rdAa TmE_rdAa GE_rdAa HE_rdAa GRE_rdAa GKE_rdAa HKE_rdAa s_hE_rdAa s_gE_rdAa xs_tE_rdAa FKE_rdAa FGE_rdAa
             TrE_rdAa_eq TE_rdAa_objs NxTa xs_tE_rdAa_ok run_tE_rdAa HGE_rdAa_regs eq_refl HKE_rdAa_eq ent_hE_rdAa s_hE_rdAa_vals shp_hAa
             GE_rdAa_fact diff_GRE_rdAa SGa NGa eq_refl GKE_rdAa_eq ent_gE_rdAa s_gE_rdAa_vals
             (conj (proj1 (proj2 (proj2 ids_A))) (proj1 (proj2 (proj2 (proj2 ids_A)))))
             (conj (proj1 (proj2 (proj2 tvs_A))) (proj1 (proj2 (proj2 (proj2 tvs_A)))))
             (conj Wb1 Wb2) m rho3 len cap got b g IH Hm S100 S101 S102 S153 S103 H4 ltac:(lia) Hlc HlL Hal I7 Gb Hg Hcap).
  - rewrite TE_rdAb_eq.
    exact (copy_tailS TE_rdAb TrE_rdAb TmE_rdAb GE_rdAb HE_rdAb GRE_rdAb GKE_rdAb HKE_rdAb s_hE_rdAb s_gE_rdAb xs_tE_rdAb FKE_rdAb FGE_rdAb
             TrE_rdAb_eq TE_rdAb_objs NxTb xs_tE_rdAb_ok run_tE_rdAb HGE_rdAb_regs eq_refl HKE_rdAb_eq ent_hE_rdAb s_hE_rdAb_vals shp_hAb
             GE_rdAb_fact diff_GRE_rdAb SGb NGb eq_refl GKE_rdAb_eq ent_gE_rdAb s_gE_rdAb_vals
             (conj (proj1 (proj2 (proj2 (proj2 (proj2 ids_A))))) (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ids_A)))))))
             (conj (proj1 (proj2 (proj2 (proj2 (proj2 tvs_A))))) (proj2 (proj2 (proj2 (proj2 (proj2 tvs_A))))))
             (conj Wb1 Wb2) m rho3 len cap got b g IH Hm S100 S101 S102 S153 S103 H4 ltac:(lia) Hlc HlL Hal I7 Gb Hg Hcap).
Qed.

Lemma stepKS : ltac2:(tb__ "0|0|
S5S11S5S5S5S99R5A1S8SbZ2SaScS33S39Q8A1S59Vcx;A1A2A1R4A2A2R6A2S55Vcx;R5R4R6A4S8Z0R4A2S48R6R5A2S3cS7Vok;S3fS7VJS;R8R7R6A3S76R9A4S3eA4F_;F_;F_;F_;F_;Fg;Fcap;Flen;Frho;Fm;").
Proof using TXEH.
  intros m rho len cap g IH Hm HI Hg Hcap. pose proof IH as [IHK IHG].
  pose proof HI as (I1 & I2 & I3 & I4 & I5 & I6 & I7). pose proof (CAP_facts cap I7) as (C1 & C2 & C3). clear C3.
  destruct nexts_A as (NxZA & NxZB & NxPA & NxA & NxB & NxXA & NxXB & _). destruct lenient_A as (LnZA & LnZB & LnPA & LnK & _).
  destruct ids_A as (IdxA & IdxB & _). destruct tvs_A as (TxA & TxB & _). destruct fbX_A as (FbxA & FbxB & FbpA).

  apply triple_factsJ. intros HFK.
  assert (Hnz : bv_unsigned (rw rho 102) <> 0).
  { pose proof (Forall_nth_error _ _ _ _ HFK K_nz) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  clear HFK. apply (triple_Jpure segs ok (bv_unsigned (rw rho 102) + cap + 4 <= aceil_hi /\ 4096 + 16 <= bv_unsigned (rw rho 102))).
  { intros tr md HJ. destruct (JD_geom r0 _ _ _ _ _ _ (SVar 102) (SVar 101) HJ ltac:(left; reflexivity) Hnz) as (_ & G & G').
    cbn [eval] in G, G'. unfold UV in I2. rewrite I2 in G. exact (conj G G'). }
  intros [Gb Gb0].
  eapply (run_trJ segs ok FUEL CUTS K _ _ rho _ run_k LnK); [apply JD_okf, KdR_tcons | apply JD_stable; [|apply tvK_below]; rewrite (proj1 cuts_shape); lia |].
  rewrite (proj1 cuts_shape). intros Lf rho1 [<-|[<-|[]]] Hag; cbn [lf_state].
  -
    apply triple_factsJ. intros HFB.
    pose proof (Forall_nth_error _ _ _ _ HFB E_rdB_fact) as Hf. clear HFB. apply holds_bltu in Hf.
    rewrite CursorGlue.U_sub, CursorGlue.U_lit in Hf. cbn [eval] in Hf. unfold M64v in Hf.
    pose proof (INVK_agree len cap rho rho1 153 ltac:(lia) Hag HI) as (J1 & J2 & _). unfold UV in J1, J2. rewrite J1, J2 in Hf.
    rewrite (Z.mod_small 65536), Z.mod_small in Hf by lia.
    assert (HL : len = L).
    { destruct I6 as [I6|I6]; [|exact I6]. exfalso.
      unfold ALIGNED in C2, I6. assert ((cap - len) mod 65536 = 0) by (rewrite Zminus_mod, C2, I6; reflexivity).
      assert (cap - len = 65536 * ((cap - len) / 65536)) by (pose proof (Z.div_mod (cap - len) 65536 ltac:(lia)); lia). nia. }
    destruct E_rdB_shape as (Bpc & B17 & B10 & B11 & B12 & Bnx & Bo1 & BoI).
    eapply triple_seq.
    { apply triple1_triple. apply (jread_rs r0 (DG cap g) (DG_fds cap g) E_rdB rho1 len (cap - len) tvK cert_rdB B17 B10 BoI B11).
      - rewrite B12, CursorGlue.U_sub. cbn [eval]. rewrite J1, J2. unfold M64v. apply Z.mod_small. lia.
      - lia.
      - unfold L in *; lia.
      - rewrite Bnx. lia.
      - rewrite Bnx. apply tvK_below. lia. }
    rewrite P_E_rdB_eq, Bnx.
    pose proof (chunk_length len (cap - len) ltac:(lia) ltac:(lia)) as CL.
    replace (len + Z.of_nat (length (chunk len (cap - len)))) with L by lia.
    destruct shp_xB as (Sx0 & Sx1 & Sx2 & Sx3).
    apply (exit_viaS P_E_rdB PZ_E_rdB X_E_rdB XK_E_rdB s_xE_rdB tvK _ 153 cap g swf_PZ_E_rdB diff_PZ_E_rdB run_pz_E_rdB LnZB XK_E_rdB_eq ent_xE_rdB IdxB TxB
             ltac:(rewrite NxZB; lia) ltac:(rewrite NxZB; apply tvK_below; lia) FbxB).
    + rewrite rho_set_rw_at. apply len_word_zero. lia.
    + exact Hg.
    + exact Hcap.
    + intros r Hr. rewrite NxZB in Hr. unfold INVX, UV. cbn [rho_sub rw]. rewrite Sx0, Sx1, Sx3. cbn [eval].
      rewrite !Hr by lia. rewrite !rho_set_rw_other by lia. destruct Hag as (Hw & _). rewrite <- !Hw by lia.
      unfold UV in I1, I2. split; [lia|].
      split; [lia|]. split; [exact I2|]. split; [exact I3|]. unfold MAX_INPUT. split; [lia|]. split; [lia|]. exact I7.
  -
    apply triple_factsJ. intros HFA.
    pose proof (Forall_nth_error _ _ _ _ HFA E_rdA_fact) as Hf. clear HFA. apply holds_nbltu in Hf.
    rewrite CursorGlue.U_sub, CursorGlue.U_lit in Hf. cbn [eval] in Hf. unfold M64v in Hf.
    pose proof (INVK_agree len cap rho rho1 153 ltac:(lia) Hag HI) as (J1 & J2 & _). unfold UV in J1, J2. rewrite J1, J2 in Hf.
    rewrite (Z.mod_small 65536), Z.mod_small in Hf by lia.
    destruct E_rdA_shape as (Apc & A17 & A10 & A11 & A12 & Anx & Ao1 & AoI).
    assert (R102 : rw rho1 102 = rw rho 102) by (destruct Hag as (Hw & _); symmetry; apply Hw; lia).
    assert (R103 : rw rho1 103 = rw rho 103) by (destruct Hag as (Hw & _); symmetry; apply Hw; lia).
    eapply triple_seq.
    { apply triple1_triple. apply (jread_rs r0 (DG cap g) (DG_fds cap g) E_rdA rho1 len 65536 tvK cert_rdA A17 A10 AoI A11).
      - rewrite A12, CursorGlue.U_lit. reflexivity.
      - lia.
      - unfold L in *; lia.
      - rewrite Anx. lia.
      - rewrite Anx. apply tvK_below. lia. }
    rewrite P_E_rdA_eq, Anx.
    pose proof (chunk_length len 65536 ltac:(lia) ltac:(lia)) as CL.
    set (got := Z.of_nat (length (chunk len 65536))) in *.
    set (rho2 := rho_set_rw rho1 153 (len_word (chunk len 65536))).
    assert (G153 : bv_unsigned (rw rho2 153) = got).
    { subst rho2. rewrite rho_set_rw_at. unfold len_word. apply Z_to_bv_small. rewrite two64. lia. }
    assert (G100 : bv_unsigned (rw rho2 100) = len) by (subst rho2; rewrite rho_set_rw_other by lia; exact J1).
    assert (G101 : bv_unsigned (rw rho2 101) = cap) by (subst rho2; rewrite rho_set_rw_other by lia; exact J2).
    assert (G102 : rw rho2 102 = rw rho 102) by (subst rho2; rewrite rho_set_rw_other by lia; exact R102).
    assert (G103 : rw rho2 103 = rw rho 103) by (subst rho2; rewrite rho_set_rw_other by lia; exact R103).
    destruct (Z.eq_dec got 0) as [Hg0|Hgp].
    +
      replace (len + got) with L by lia.
      destruct shp_xA as (Sx0 & Sx1 & Sx2 & Sx3).
      apply (exit_viaS P_E_rdA PZ_E_rdA X_E_rdA XK_E_rdA s_xE_rdA tvK _ 153 cap g swf_PZ_E_rdA diff_PZ_E_rdA run_pz_E_rdA LnZA XK_E_rdA_eq ent_xE_rdA IdxA TxA
               ltac:(rewrite NxZA; lia) ltac:(rewrite NxZA; apply tvK_below; lia) FbxA).
      * subst rho2. rewrite rho_set_rw_at. apply len_word_zero. lia.
      * exact Hg.
      * exact Hcap.
      * intros r Hr. rewrite NxZA in Hr. unfold INVX, UV. cbn [rho_sub rw]. rewrite Sx0, Sx1, Sx3. cbn [eval].
        rewrite !Hr by lia. rewrite G103. split; [lia|].
        split; [lia|]. split; [exact G101|]. split; [exact I3|]. unfold MAX_INPUT. split; [lia|]. split; [lia|]. exact I7.
    +
      apply (copyAS m rho2 len cap got (bv_unsigned (rw rho 102)) g IH Hm); unfold UV; rewrite ?G102, ?G103; try assumption; try reflexivity; try lia.
      destruct I6 as [I6|I6]; [|lia].
      assert (Hgot : got = 65536 \/ (got < 65536 /\ len + got = L)) by lia.
      destruct Hgot as [Hg'|[Hg1 Hg2]]; [left | right; exact Hg2].
      unfold ALIGNED in *. rewrite Hg', <- Zplus_mod_idemp_l, I6. reflexivity.
Qed.

Lemma stepG_okS : ltac2:(tb__ "0|2|
S5S11S5S5S99R4A1S8S9SbZ2M0SaScS33S39Q8A1S59Vcx;A1A2A1M1R3A2A2Z1A2R5A2S0S5S4dR5P65A2R4A3S53Vcx;S1cR6P67A2A2S8R6G1A2S94R7A1SeR8SdG0Z1aA2A2S8Z0R8A2S48RaR9A2S3cS7Vok;S3fS7VJD;S50Vcx;RbA2Vr0;S58S4cRbRaA2A4S92RcA4S3eA4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fg;Fcap;Frho;Fm;").
Proof using TXEH FDX.
  intros m rho cap g [IHK IHG] Hm I1 I3 I5 I7 Hlt Hg Hcap. pose proof (CAP_facts cap I7) as (C1 & C2 & C3). pose proof (C3 Hlt) as C4. clear C3.
  pose proof (g_lt_bound cap g Hg Hcap Hlt) as [Gg Gc].
  assert (Hcap' : CAPG (2 * cap) (g + 1)) by (unfold CAPG in Hcap |- *; rewrite Z.pow_add_r, Z.pow_1_r by lia; lia).
  destruct nexts_G as (NxS & Mnx & NxM & NxCf & NxF & NxH & _). destruct lenient_G as (LnS & LnM & LnF).
  destruct tvb_G as (Tb193 & Tb233 & Tb273 & Tb153). unfold UV in I1.

  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_g rho T_gok T_gokS w xs_g_ok Hw) | intros w Hw; exact Hw |].
  eapply (run_trJ segs ok FUEL CUTS T_gokS _ _ rho _ run_goks LnS); [apply JD_okf, KdR_tcons | apply JD_stable; [rewrite NxS; lia | rewrite NxS; exact Tb193] |].
  rewrite NxS. intros Lf rho2 [<-|[]] Hag2; cbn [lf_state].
  destruct C_mc_shape as (Mpc & _ & M10 & M11 & M12).

  assert (MSUM : forall rho1, triple segs ok (SP segs (fun tr md => JD (KdR cap) r0 tvG (DM cap g) rho2 tr md) PreC rho1)
                                         (LQ segs (fun tr md => JD (KdR cap) r0 tvG (DM cap g) rho2 tr md) (ss_next PreC) rho1 U.Str_memcpy__G1.Str_memcpy_hdr.Posts_mh)).
  { intros rho1. apply U.Str_memcpy__G1.Str_memcpy_hdr.memcpy_hdr_sum. apply HokK. intros tr md (Ai & (_ & Hk & _) & _). exact (KdR_tcons _ tr md Hk). }
  apply (pure_callD r0 (KdR cap) tvG (DM cap g) C_mc PreC s_mc R_mc U.Str_memcpy__G1.Str_memcpy_hdr.Posts_mh rho2 _ MSUM efr_mc chk_mc ltac:(rewrite Mnx; lia) ltac:(rewrite Mnx; exact Tb193) fb_mc).
  intros Lf rho3 [<-|[]] Hag3; cbn [lf_state]. rewrite Mnx in Hag3. pose proof T_mc_eq as TE; unfold U.Str_memcpy__G1.Str_memcpy_hdr.P_mh in TE; rewrite TE; clear TE.

  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_m rho3 T_mc T_mcM w xs_m_ok Hw) | intros w Hw; exact Hw |].
  eapply (run_trJ segs ok FUEL CUTS T_mcM _ _ rho3 _ run_mcm LnM); [apply JD_okf, KdR_tcons | apply JD_stable; [rewrite NxM; lia | rewrite NxM; exact Tb233] |].
  rewrite NxM. intros Lf rho4 [<-|[]] Hag4; cbn [lf_state].

  destruct s_fr_vals as (F12 & F13 & F10 & F15).
  apply (dfree_call segs C_U EC_U 31 (KdR cap) r0 P0 malloc_laws_U ok C_fr s_fr R_fr rho4 tvG 1%nat (SVar 102, SVar 101) _ (DM cap g)
           (fun Ai => J_free_S segs C_U Ai (kOf g - 1) (XOf cap g - malloc_cost (2 * cap)) (KdR cap))
           (fun Ai => JLdS_free segs C_U Ai (kOf g - 1 - 1) (XOf cap g - malloc_cost (2 * cap)) (KdR cap))
           (DX (kOf g - 1 - 1) (XOf cap g - malloc_cost (2 * cap)))).
  - vm_cast_no_check (@eq_refl bool true).
  - intros Ai rho1. apply (FDX ok Ai). apply okside.
  - exact efr_fr.
  - exact chk_fr.
  - rewrite NxCf. reflexivity.
  - reflexivity.
  - rewrite NxCf. exact Tb233.
  - reflexivity.
  - intros Ai tr ms md Hsm HJ [HDd HDv]. pose proof HJ as (Hav & Hk & [HM [Hi HTPI]] & HP & (HN & HD & HZ) & HKF & HP0').
    pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
    assert (Hnz : tnz rho4 (SVar 102, SVar 101)).
    { apply tnz_of_fact. exact (holds_of_existsb rho4 _ _ HFf nz_fr). }
    split; [|split; [exact Hnz|split]].
    + intros HJF. split; [exact HJF|]. split; [exact HDd|]. split; [unfold kOf; rewrite DRV_OPS_val; lia | exact HDv].
    + rewrite F12, F13. reflexivity.
    + eapply (robjs_check_sound segs C_U [] Ai rho4 (ss_facts C_fr) tvG (Some 1%nat) (robj_inw WINS_U) R_fr _ rho4 md HM (T_ok_of_JGi _ _ _ _ _ _ _ HJ) HFf HN HD HZ rchk_fr).
      * intros o a _ Ho Hr. exact (robj_inw_caddr segs C_U WINS_U rho4 Ai _ o a WINS_U_ok Ho Hr).
      * exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Hnz|]. rewrite F12. reflexivity.
  - intros Ai r1 r' tr md (A' & l1 & l2 & HM' & Hi' & Hd' & Hv' & HbA & HbA' & Hkept & Hk).
    exists A', l1, l2. split; [exact HM'|]. split; [exact Hi'|]. split; [exact HbA|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | split; [exact Hd' | exact Hv']].
  - intros rho5 Hag5. rewrite T_fr_eq. change (remove_nth 1 tvG) with tvN.

    eapply triple_conseq with (P := SPJ segs (JD (KdR cap) r0 tvN (DG (2 * cap) (g + 1))) T_fr rho5); [| intros w Hw; exact Hw |].
    { intros w [Hsm HJ]. split; [exact Hsm|]. eapply (JGD_mono segs C_U 31 (KdR cap) r0 P0); [|exact HJ]. intros A md'. apply DG_next. }

    eapply (run_trJ segs ok FUEL CUTS T_fr _ _ rho5 _ run_fr LnF); [apply JD_okf, KdR_tcons | apply JD_stable; [rewrite NxF; lia | rewrite NxF; exact Tb273] |].
    rewrite NxF. intros Lf rho6 [<-|[]] Hag6; cbn [lf_state].
    assert (V101 : bv_unsigned (rw rho6 101) = cap).
    { destruct Hag6 as (W6 & _), Hag5 as (W5 & _), Hag4 as (W4 & _), Hag3 as (W3 & _), Hag2 as (W2 & _).
      rewrite <- W6, <- W5, <- W4, <- W3, <- W2 by (rewrite ?NxCf; lia). exact I1. }
    assert (V103 : rw rho6 103 = rw rho 103).
    { destruct Hag6 as (W6 & _), Hag5 as (W5 & _), Hag4 as (W4 & _), Hag3 as (W3 & _), Hag2 as (W2 & _).
      rewrite <- W6, <- W5, <- W4, <- W3, <- W2 by (rewrite ?NxCf; lia). reflexivity. }
    destruct s_hfr_vals as (Sh0 & Sh1 & Sh2 & Sh3).
    apply (triple_add_facts segs ok _ rho6 FK_fr H_fr HK_fr _ HK_fr_eq fb_G).
    { unfold FK_fr. change (sv_subst s_hfr (SVar 101)) with (wsub_get s_hfr 101). rewrite Sh1.
      constructor; [|constructor]. apply holds_ule. rewrite (Usll1 rho6 (SVar 101) cap V101) by lia. rewrite (Ulit rho6) by lia. lia. }
    apply (reenter r0 (KdR cap) tvN tvK (DG (2 * cap) (g + 1)) HK_fr K s_hfr rho6 _ 273 ent_hfr (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ids_A)))))) ltac:(lia) Tb273 tvs_G).
    apply (IHK _ cap (2 * cap) (g + 1)); [lia| |split; [lia|exact Hcap']].
    unfold INVK, UV. cbn [rho_sub rw]. rewrite Sh0, Sh1, Sh3. rewrite (Usll1 rho6 (SVar 101) cap V101) by lia. cbn [eval]. rewrite V101, V103.
    split; [reflexivity|]. split; [reflexivity|]. split; [apply HDR_sext; exact I3|]. split; [lia|]. split; [lia|]. split; [left; exact C2 | exact (CAP_double cap I7 Hlt)].
Qed.

Lemma stepGS : ltac2:(tb__ "0|0|
S5S11S5S5S99R4A1S8S9SbZ2SaScS33S39Q8A1S59Vcx;A1A2A1R3A2A2Z1A2R5A2S54Vcx;R4R5A3S8Z0R4A2S48R6R5A2S3cS7Vok;S3fS7VJS;R7R7R6A3S77R8A4S3eA4F_;F_;F_;F_;F_;Fg;Fcap;Frho;Fm;").
Proof using TXEH TXref FDX HX0 MBX.
  intros m rho cap g IH Hm HI Hg Hcap. pose proof IH as [IHK IHG].
  pose proof HI as (I1 & I3 & I5 & I7). pose proof (CAP_facts cap I7) as (C1 & C2 & C3). clear C3. unfold UV in I1.
  destruct lenient_A as (_ & _ & _ & _ & LnKG). destruct tvb_G as (Tb193 & Tb233 & Tb273 & Tb153).
  destruct nexts_G as (_ & _ & _ & _ & _ & _ & Cnx).
  apply triple_factsJ. intros HFK.
  assert (Hnz : bv_unsigned (rw rho 102) <> 0).
  { pose proof (Forall_nth_error _ _ _ _ HFK KG_nz) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  clear HFK. eapply (run_trJ segs ok FUEL CUTS KG _ _ rho _ run_kg LnKG); [apply JD_okf, KdR_tcons | apply JD_stable; [|apply tvK_below]; rewrite (proj1 (proj2 cuts_shape)); lia |].
  rewrite (proj1 (proj2 cuts_shape)). intros Lf rho1 [<-|[<-|[]]] Hag; cbn [lf_state].
  -
    apply triple_factsJ. intros HFX.
    destruct X_ref_shape as (_ & _ & Xf). pose proof (Forall_nth_error _ _ _ _ HFX Xf) as Hf. clear HFX. apply holds_bne in Hf.
    rewrite CursorGlue.U_srl_lit, CursorGlue.U_lit in Hf. cbn [eval] in Hf. change (26 mod 64) with 26 in Hf. change (0 mod M64v) with 0 in Hf.
    assert (R101 : rw rho1 101 = rw rho 101) by (destruct Hag as (Hw & _); symmetry; apply Hw; lia). rewrite R101, I1 in Hf.
    assert (Hcap26 : cap = 2 ^ 26).
    { destruct (Z_lt_le_dec cap (2 ^ 26)) as [Hl|Hl]; [|lia]. exfalso. apply Hf. apply Z.div_small. lia. }
    rewrite Hcap26 in I1, I5, Hcap |- *. apply TXref.
    + unfold UV. rewrite R101. exact I1.
    + exact I5.
    + destruct Hag as (Hw & _). rewrite <- Hw by lia. exact I3.
    + split; [exact Hg|]. apply pow_g_bound; [exact Hg | unfold CAPG in Hcap; lia].
  -
    apply triple_factsJ. intros HFC.
    destruct C_gm_shape as (_ & _ & C10 & Cf). pose proof (Forall_nth_error _ _ _ _ HFC Cf) as Hf. clear HFC. apply holds_nbne in Hf.
    rewrite CursorGlue.U_srl_lit, CursorGlue.U_lit in Hf. cbn [eval] in Hf. change (26 mod 64) with 26 in Hf. change (0 mod M64v) with 0 in Hf.
    assert (R101 : rw rho1 101 = rw rho 101) by (destruct Hag as (Hw & _); symmetry; apply Hw; lia). rewrite R101, I1 in Hf.
    assert (Hlt : cap < 2 ^ 26).
    { destruct (Z_lt_le_dec cap (2 ^ 26)) as [Hl|Hl]; [exact Hl|]. exfalso.
      assert (1 <= cap / 2 ^ 26) by (apply Z.div_le_lower_bound; lia). lia. }
    pose proof (g_lt_bound cap g Hg Hcap Hlt) as [Gg Gc].
    destruct s_gm_vals as (S12 & S10 & S15 & SB12 & SRES).
    apply (dmalloc_call segs C_U EC_U 31 (KdR cap) r0 P0 malloc_laws_U ok C_gm s_gm R_gm rho1 tvK _ (DG cap g)
             (fun Ai => J_big_S segs C_U Ai (kOf g) (XOf cap g) (KdR cap))
             (fun Ai => [(L_malloc_ok EC_U, JLdS_big_ok segs C_U Ai (kOf g) (XOf cap g) (KdR cap))])
             (fun Ai => JLi_null segs C_U Ai (KdR cap)) (fun Ai => JLdS_big_ok segs C_U Ai (kOf g) (XOf cap g) (KdR cap)) DTrue (DM cap g)).
    + vm_cast_no_check (@eq_refl bool true).
    + intros Ai rho2. apply (MBX ok Ai). apply okside.
    + exact efr_gm.
    + intros Ai. exact chk_gm_ok.
    + rewrite Cnx. reflexivity.
    + reflexivity.
    + rewrite Cnx. exact Tb153.
    + exact SB12.
    + exact SRES.
    +
      intros Ai tr ms md Hsm HJ [HDd HDv] HTP HTOP. pose proof HJ as (Hav & Hk & HMi & HP & (HN & HD & HZ) & HKF & HP0').
      pose proof (smatch_facts_hold segs _ _ _ Hsm) as HFf.
      assert (HRok : robjs_ok segs C_U Ai None rho1 R_gm).
      { eapply (robjs_check_sound segs C_U [] Ai rho1 (ss_facts C_gm) tvK None (robj_inw WINS_U) R_gm None rho1 md (MI1 _ _ _ _ _ _ HMi) (T_ok_of_JGi _ _ _ _ _ _ _ HJ) HFf HN HD HZ rchk_gm).
        - intros o a _ Ho Hr. exact (robj_inw_caddr segs C_U WINS_U rho1 Ai _ o a WINS_U_ok Ho Hr).
        - exact I. }
      assert (A12 : bv_unsigned (rw (rho_sub (rho_absorb rho1 R_gm ms) s_gm) 12) = 2 * cap).
      { rewrite rw_call', S12. rewrite (Usll1 rho1 (SVar 101) cap ltac:(cbn [eval]; rewrite R101; exact I1)) by lia. reflexivity. }
      split; [|split; [exact HRok|]].
      * split; [|split; [exact HDd|split; [unfold kOf; rewrite DRV_OPS_val; lia|split; [rewrite A12, MMAP_THRESHOLD_val; lia|split; [exact Hk|split; [|split; [exact HTP | exact HTOP]]]]]]].
        -- eapply MI1. eapply (MInvR_mem segs C_U _ malloc_laws_U); [exact HMi| |reflexivity].
           intros a Ha Ho. apply rm_absorb_out. eapply (R_miss segs C_U malloc_laws_U Ai None rho1 rho1 md R_gm a (MI1 _ _ _ _ _ _ HMi)); [exact HRok|exact Ha|exact Ho].
        -- split; [exact HDv|]. rewrite A12, malloc_cost_val. unfold XOf. rewrite init_cost_val in HX0 |- *. lia.
      * rewrite S12. rewrite (Usll1 rho1 (SVar 101) cap ltac:(cbn [eval]; rewrite R101; exact I1)) by lia. lia.
    + intros Ai x Hx. cbn in Hx. destruct Hx as [<-|[]]. right. reflexivity.
    + intros Ai q r' tr md (A' & HM' & Hi' & HbA' & Hkept & Hk).
      exists A'. split; [exact HM'|]. split; [exact Hi'|]. split; [exact HbA'|]. split; [exact Hkept|]. split; [exact Hk | exact I].
    + intros Ai q r' tr md Hq (A' & l1 & l2 & HM' & Hi' & Hd' & Hv' & HbA' & HbA & Hkept & Hk).
      exists A', l1, l2. split; [exact HM'|]. split; [exact Hi'|]. split; [exact HbA'|]. split; [exact HbA|]. split; [exact Hkept|]. split; [exact Hk|].
      split; [exact Hd'|]. rewrite Hq, S12 in Hv'. rewrite (Usll1 rho1 (SVar 101) cap ltac:(cbn [eval]; rewrite R101; exact I1)) in Hv' by lia. exact Hv'.
    +
      intros [Ai Hin]. exfalso. cbn in Hin. destruct Hin as [E|[]]. apply (f_equal fst) in E. cbn [fst] in E. exact (L_null_ok_differ E).
    +
      intros _ rho' Hagv. rewrite T_gok_eq, S12. change (pos_add_nat (ss_next C_gm) 10) with 163%positive. fold tvG.
      apply (stepG_okS m rho' cap g IH Hm); [|destruct Hagv as [Hw _]; rewrite <- Hw by (rewrite Cnx; lia); destruct Hag as (Hw' & _); rewrite <- Hw' by lia; exact I3|exact I5|exact I7|exact Hlt|exact Hg|exact Hcap].
      unfold UV. destruct Hagv as [Hw _]. rewrite <- Hw by (rewrite Cnx; lia). rewrite R101. exact I1.
Qed.

Lemma loop_allS : forall m, LoopIHs m.
Proof using TXEH TXref FDX HX0 MBX.
  assert (N : forall n : nat, LoopIHs (Z.of_nat n)).
  { induction n as [|n IHn].
    - split; [intros rho len cap g Hm (_ & _ & _ & _ & I5 & _); lia | intros rho cap g Hm (_ & _ & I5 & _); lia].
    - split.
      + intros rho len cap g Hm HI [Hg Hc]. apply (stepKS (Z.of_nat n) rho len cap g IHn); [lia | exact HI | exact Hg | exact Hc].
      + intros rho cap g Hm HI [Hg Hc]. apply (stepGS (Z.of_nat n) rho cap g IHn); [lia | exact HI | exact Hg | exact Hc]. }
  intros m. destruct (Z_lt_le_dec m 0) as [Hm|Hm].
  - split; [intros rho len cap g H (_ & _ & _ & _ & I5 & _); lia | intros rho cap g H (_ & _ & I5 & _); lia].
  - rewrite <- (Z2Nat.id m) by lia. apply N.
Qed.

End LoopS.

Lemma toKs : ltac2:(tb__ "0|3|
S11S11S3dS3fS7VJD;S50Vcx;Z0M0A2R3S4eS47Z10000G0A2M1A4S80R2R1A5S2S64S64S2S2eS39Q40A1A1M2G2S1S93S7S72VP0;Vwtop;S4eG1R5R2R1A9S40S7S51Vcx;G0R2R1A4S80R5R4A5A2Lmat;A2Lvm;A2F_;Fw;Frho;Fr0;").
Proof using Hargc Hent Hinp.
  intros r0 rho [tr [ms md]] [Hsm HJ]. pose proof HJ as (Ai & HJi & HD).
  pose proof (U.Drv_m__G1.Drv_m.P0_now sp brk mb draw inp Hent Hinp Hargc _ _ _ _ _ _ _ HJ) as HP0.
  destruct (deJ segs C_U 31 P0 wtop P0_top (KdR 0) r0 tv0 (DG 65536 0) Ai rho tr md HJi HD HP0) as [HSn Hk].
  exists (m_vmmaps md), (m_vm_materialized md). split; [exact HSn|]. split; [exact Hsm|]. cbn [liftK w_tr w_cfg cfg_model]. split; [exact Hk|]. split; reflexivity.
Qed.

Lemma fromKs : ltac2:(tb__ "0|1|
S11S11S64S2eS39Q40A1A1S5S16S3dS93S7S72VP0;Vwtop;S4eS47Z10000Z0A2M0R7R5R4A9S52R8R7A2S40S7S51Vcx;R5R7R6A4R4R8R3A5S1S3fS7VJD;S50Vcx;R6A2R9S4eG0A4R5R9R4A5VP0;R9A1A2F_;F_;F_;Fw;FS;Foff;Fmat;Fvm;Frho;FrhoB;").
Proof using Hargc Hent Hinp.
  intros rhoB rho vm mat off S [tr [ms md]] HS [Bw Bm] [Hsm (Hk & Hvm & Hmat)]. cbn [liftK w_tr w_cfg cfg_model] in Hk, Hvm, Hmat.
  pose proof HS as (Ai0 & md0' & _ & _ & _ & HP0B & _).
  assert (HP0 : P0 rho).
  { apply (U.Drv_m__G1.Drv_m.P0_agree sp brk mb draw inp Hent Hinp Hargc rhoB rho HP0B); [intros i Hi; apply Bw; lia | intros a _; apply Bm]. }
  split; [|exact HP0]. split; [exact Hsm|]. unfold JD, U.Drv_m__G1.Drv_m.JD, JGD.
  apply (reJ segs C_U 31 P0 wtop P0_top P0_tp (KdR off) tv0 (DG 65536 0) rho vm mat tr md); [| exact Hvm | exact Hmat | apply DG_vm | exact Hk].
  apply (snapJ_transport segs C_U P0 malloc_laws_U wtop tv0 (DG 65536 0) rhoB rho vm mat HS).
  - intros t [<-|[]]. cbn [fst snd eval]. split; [apply Bw; lia | reflexivity].
  - intros a. unfold Contract.rd_of. rewrite Bm. reflexivity.
  - intros a. unfold Contract.wok_of. rewrite Bm. reflexivity.
  - exact HP0.
Qed.

Section FirstS.

Hypothesis TLOOPK : ltac2:(tb__ "0|1|
S11S11S5S55Vcx;R1Z10000M0R2A4S3cS7Vok;S3fS7VJD;S50Vcx;R2A2R4S4fS47G0Z0A2A4S76R3A4S3eA4F_;Flen;Frho;Fr0;").
Hypothesis TLOOPG : ltac2:(tb__ "0|1|
S11S11S54Vcx;Z10000M0R1A3S3cS7Vok;S3fS7VJD;S50Vcx;G0A2R3S4fS47G0Z0A2A4S77R2A4S3eA4F_;Frho;Fr0;").
Hypothesis TXE0 : ltac2:(tb__ "0|2|
S11S11S0S5S4dR1P64A2ScS33S39Q8A1S59Vcx;A1A2A1M0A3S0S5S4dR2P65A2Z10000M1A3SeG0Z4A2S3cS7Vok;S3fS7VJD;S50Vcx;G0A2R5S4fS47G1Z0A2A4S79R4A4S3eA4F_;F_;F_;Frho;Fr0;").

Lemma exit0_viaS : ltac2:(tb__ "0|3|
S16S63S11S64S2eS39Q40A1A1S11S93S7S72VP0;Vwtop;S4eS47Z10000M0Z0A2R4R3R2A9S52R5R2A2S0S2cS6cR8S79R7A3S2dA3S0S2cS61R8P1fM1A2S2dA3S0S2cS6fR9S4eS4fA3S2dA3Sa0G1S12RbA1A2S0S2cS70S12RcA1S4eA2S2dA3S0S5S4dS62R8RcA2P64A2ScS33S39Q8A1S59Vcx;A1A2A1M2A3S0S5S4dS62R9RdA2P65A2G0A3SeG2Z4A2S3cS7Vok;S40S7S51Vcx;G2RdRcA4R10RbA4S3eA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;Fmat;Fvm;FrhoB;Fsx;FX;").
Proof using TXE0 Hargc Hent Hinp.
  intros X sx rhoB vm mat rho HS HB He Hid Htv Hn Hb H100 H101 HL.
  eapply triple_conseq; [intros w Hw; exact (proj1 (fromKs rhoB rho vm mat L X w HS HB Hw)) | intros w Hw; exact Hw |].
  apply (reenter rho (KdR L) tv0 tvK (DG 65536 0) X XE0 sx rho _ (ss_next X) He Hid Hn Hb Htv).
  apply (TXE0 rho); assumption.
Qed.

Lemma loopK_viaS : ltac2:(tb__ "0|2|
S16S63S11S64S2eS39Q40A1A1S11S5S93S7S72VP0;Vwtop;S4eS47Z10000M0Z0A2R5R4R3A9S52R6R3A2S0S2cS6cR9S76R8A3S2dA3S0S2cS61R9P1fM1A2S2dA3S0S2cS6fRaS4eS4fA3S2dA3Sa0G1S12RcA1A2S0S2cS70S12RdA1S4eA2S2dA3S55Vcx;R8G0S62R9RdA2A4S3cS7Vok;S40S7S51Vcx;R9RcRbA4RfRaA4S3eA4F_;F_;F_;F_;F_;F_;F_;F_;Flen;Frho;Fmat;Fvm;FrhoB;Fsh;FH;").
Proof using TLOOPK Hargc Hent Hinp.
  intros H sh rhoB vm mat rho len HS HB He Hid Htv Hn Hb HI.
  eapply triple_conseq; [intros w Hw; exact (proj1 (fromKs rhoB rho vm mat len H w HS HB Hw)) | intros w Hw; exact Hw |].
  apply (reenter rho (KdR len) tv0 tvK (DG 65536 0) H K sh rho _ (ss_next H) He Hid Hn Hb Htv).
  apply (TLOOPK rho _ len). exact HI.
Qed.

Lemma loopG_viaS : ltac2:(tb__ "0|2|
S16S63S11S64S2eS39Q40A1A1S11S93S7S72VP0;Vwtop;S4eS47Z10000M0Z0A2R4R3R2A9S52R5R2A2S0S2cS6cR8S77R7A3S2dA3S0S2cS61R8P1fM1A2S2dA3S0S2cS6fR9S4eS4fA3S2dA3Sa0G1S12RbA1A2S0S2cS70S12RcA1S4eA2S2dA3S54Vcx;G0S62R8RcA2A3S3cS7Vok;S40S7S51Vcx;G0RbRaA4ReR9A4S3eA4F_;F_;F_;F_;F_;F_;F_;F_;Frho;Fmat;Fvm;FrhoB;Fsg;FH;").
Proof using TLOOPG Hargc Hent Hinp.
  intros H sg rhoB vm mat rho HS HB He Hid Htv Hn Hb HI.
  eapply triple_conseq; [intros w Hw; exact (proj1 (fromKs rhoB rho vm mat 65536 H w HS HB Hw)) | intros w Hw; exact Hw |].
  apply (reenter rho (KdR 65536) tv0 tvK (DG 65536 0) H KG sg rho _ (ss_next H) He Hid Hn Hb Htv).
  apply (TLOOPG rho _). exact HI.
Qed.

Section STiny.
Variables (T Tr Tm H E1 P1 X1 : sstate) (sx : wsub) (xs : list xform).
Hypothesis T_objs : ltac2:(tb__ "0|0|
S1S0S32S1dA1S96S1dS23VT;A1U1A3S31S1dS1bS15S6aA1S15Z0A1S13S73A1S30S1fA1S1aA5A2A3S1S0S6S12VT;A1S12VTr;A1A3S0S2eS14A1S17VTr;A1S17VT;A1A3A2A2").
Hypothesis T_next : ss_next T = 112%positive.
Hypothesis Tr_eq : ltac2:(tb__ "0|1|
S0S16S9bVT;U1S1bS15Z0A1S15S6aA1M0S18S5aS13S73A1G0A3S30S1fA1S1aA5A3VTr;A3").
Hypothesis xs_ok : ltac2:(tb__ "0|0|
S0S32S16A1Sa4VTr;Vxs;A2S31S16VTm;A2A3").
Hypothesis run_t : ltac2:(tb__ "0|1|
S0S32S2eS41A1M0A1S44S7S75S74VTm;S2dA5S31G0S2fS41S42VH;S43A2S30S41A1A3A2A3").
Hypothesis run_h : ltac2:(tb__ "0|1|
S0S32S2eS41A1M0A1S44S7S75S98S5S74A2VH;S2dA5S31G0S2fS41S42VE1;S45A2S30S41A1A3A2A3").
Hypothesis E1_shape : ltac2:(tb__ "0|0|
S1S0S5S27VE1;A1S6bA3S1S0S10S19VE1;Z11A2S15Z3fA1A3S1S0S10S19VE1;ZaA2S15Z3A1A3S1S0S10S19VE1;ZbA2S15S6aA1A3S1S0S10S19VE1;ZcA2S18S5dS15Z10000A1S13S73A1A3A3S0S32S1dA1S96S1dS23VE1;A1S7fA3S31S1dS87A2A3A2A2A2A2A2").
Hypothesis cert_e1 : ltac2:(tb__ "0|0|
S0S32S5cA1S46S7S27VE1;A1A2S31S5cS5eA2A3").
Hypothesis diff_P1 : ltac2:(tb__ "0|4|
S0S32S35S2eS35S10S10A2M0A1M1S2eS14A1M2A2M3A1Sa3SaeVE1;S23VE1;A1A2VP1;A2S31G3S36G1G2S2fG0S36S10S10S13S12VE1;A1A1S15Z0A1A4S30G0A1A3S30S14A1A4A2A3").
Hypothesis swf_P1 : swf P1 = true.
Hypothesis run_p1 : ltac2:(tb__ "0|1|
S0S32S2eS41A1M0A1S44S7S75S74VP1;S2dA5S31G0S2fS41S42VX1;S43A2S30S41A1A3A2A3").
Hypothesis ent_x1 : ltac2:(tb__ "0|0|
S0S2cS6cVX1;S79Vsx;A3S2dA3").
Hypothesis sx_vals : ltac2:(tb__ "0|0|
S1S0S10S5fVsx;P64A2S13S73A1A3S1S0S10S5fVsx;P65A2S15Z10000A1A3S0S10S5fVsx;P66A2S13P29A1A3A2A2").
Hypothesis nexts : ltac2:(tb__ "0|1|
S1S0S6S12VE1;A1S12VTm;A1M0A3S1S0S6S12VH;A1G0A3S1S0S6S12VP1;A1G0A3S1S0S6G0S12VT;A1A3S1S0S2cS1eVTm;A1S34A3S1S0S2cS1eVH;A1S34A3S0S2cS1eVP1;A1S34A3A2A2A2A2A2A2").
Hypothesis X1_next : ss_next X1 = 112%positive.
Hypothesis idx : wsub_id_below sx 31 = true.
Hypothesis tvx : ltac2:(tb__ "0|0|
S0S2cS6fVsx;S4eS4fA3S2dA3").
Hypothesis wf_src : ltac2:(tb__ "0|1|
S0S2cS21S12VT;A1S1bS15Z0A1S15S6aA1M0S18S5aS13S73A1G0A3S30S1fA1S1aA5A2S2dA3").

Lemma tiny_tailS : ltac2:(tb__ "0|1|
S11S64S2eS39Q40A1A1S11S93S7S72VP0;Vwtop;S4eS47Z10000Z0A2R4R3R2A9S52R5R2A2S1S8Z1ScS33S39Q8A1S59Vcx;A1A2A1M0A2S8G0Z3A2A2S0S5S4dR4S73A2G0A3S3cS7Vok;S40S7S51Vcx;G0R7R6A4VT;R5A4S3eA4F_;F_;F_;F_;Frho;Fmat;Fvm;FrhoB;").
Proof using E1_shape TXE0 T_next T_objs Tr_eq X1_next cert_e1 diff_P1 ent_x1 idx nexts run_h run_p1 run_t swf_P1 sx_vals tvx wf_src xs_ok Hargc Hent Hinp.
  intros rhoB vm mat rho HS HB HL U71. pose proof rs_range as RR. destruct nexts_0 as (_ & _ & _ & N71 & _).
  destruct T_objs as (To1 & NxTr & FTr). destruct nexts as (NxE & NxH & NxP & NxTm & LnTm & LnH & LnP). destruct sx_vals as (Sx0 & Sx1 & Sx2).
  unfold UV in U71. rewrite N71 in *.
  assert (E71 : bv_unsigned (eval rho (SVar 71)) = L) by exact U71.
  assert (Egr : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 71) (SLit rs))) = L + rs) by (apply (Uadd rho (SVar 71) (SLit rs) _ _ E71 (Ulit rho rs ltac:(lia))); lia).

  eapply triple_conseq with (P := SP segs (KB L vm mat) Tr rho); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- Tr_eq. unfold SP.
    apply (SPJ_reshape segs _ rho T 1 _ (mkObj (SLit 0) (SLit rs) (SAlu ALU_ADD (SVar NX0) (SLit rs)) [] DUnknown) w To1 eq_refl eq_refl eq_refl wf_src); [|exact Hw].
    rewrite N71.
    intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite (Ulit rho 0), (Ulit rho rs) by lia.
    rewrite !soff_lit_small by lia. rewrite (soff_small rho _ _ Egr) by lia. rewrite (soff_small rho (SVar 71) L E71) by lia. lia. }
  eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ xs rho Tr Tm w xs_ok Hw) | intros w Hw; exact Hw |].
  eapply (run_tr ok FUEL CUTS Tm _ _ rho _ run_t LnTm); [apply KB_okf|].
  intros Lf rho1 [<-|[]] Hag1; cbn [lf_state].
  eapply (run_tr ok FUEL (tl CUTS) H _ _ rho1 _ run_h LnH); [apply KB_okf|].
  intros Lf rho2 [<-|[]] Hag2; cbn [lf_state].
  destruct E1_shape as (Epc & E17 & E10 & E11 & E12 & EoI).
  assert (T71 : bv_unsigned (rw rho2 71) = L).
  { destruct Hag2 as (W2 & _), Hag1 as (W1 & _). rewrite <- W2, <- W1 by (rewrite ?NxH, ?NxTm, ?T_next; lia). exact U71. }

  eapply triple_seq.
  { apply triple1_triple. apply (kread_rs E1 rho2 L (65536 - L) vm mat cert_e1 E17 E10 EoI E11); [|lia|lia].
    rewrite E12, CursorGlue.U_sub, CursorGlue.U_lit. cbn [eval]. rewrite T71. unfold M64v. rewrite (Z.mod_small 65536), Z.mod_small; lia. }
  pose proof (chunk_length L (65536 - L) ltac:(lia) ltac:(lia)) as CL.
  assert (Z0 : length (chunk L (65536 - L)) = 0%nat) by lia.
  replace (L + Z.of_nat (length (chunk L (65536 - L)))) with L by lia.
  set (rho3 := rho_set_rw rho2 (ss_next E1) (len_word (chunk L (65536 - L)))).
  eapply triple_conseq with (P := SP segs (KB L vm mat) P1 rho3); [intros w Hw; apply (SP_restate segs (KB L vm mat) rho3 _ P1 w _ _ swf_P1 diff_P1); [| constructor | exact Hw] | intros w Hw; exact Hw |].
  { constructor; [|constructor]. cbn [fst snd eval]. subst rho3. rewrite rho_set_rw_at, (len_word_zero _ Z0). apply bv_eq. reflexivity. }
  eapply (run_tr ok FUEL CUTS P1 _ _ rho3 _ run_p1 LnP); [apply KB_okf|].
  intros Lf rho4 [<-|[]] Hag4; cbn [lf_state].
  assert (HB4 : BR rhoB rho4).
  { apply (BR_agree rhoB rho3 rho4 _ ltac:(subst rho3; apply BR_set_rw; [|rewrite NxE, NxTm, T_next; lia]; eapply (BR_agree rhoB rho1); [eapply (BR_agree rhoB rho); [exact HB | exact Hag1 | rewrite NxTm, T_next; lia] | exact Hag2 | rewrite NxH, NxTm, T_next; lia]) Hag4).
    rewrite NxP, NxTm, T_next. lia. }
  apply (exit0_viaS X1 sx rhoB vm mat rho4 HS HB4 ent_x1 idx tvx ltac:(rewrite X1_next; lia) ltac:(rewrite X1_next; apply tvb_0; lia)); [| |lia].
  - unfold UV. cbn [rho_sub rw]. rewrite Sx0. cbn [eval]. destruct Hag4 as (W4 & _). rewrite <- W4 by (rewrite NxP, NxTm, T_next; lia).
    subst rho3. rewrite rho_set_rw_other by (rewrite NxE, NxTm, T_next; lia). exact T71.
  - unfold UV. cbn [rho_sub rw]. rewrite Sx1. apply Ulit. lia.
Qed.
End STiny.

Lemma Usubk : ltac2:(tb__ "0|1|
S11S10S5S5S0S5S3aQ40M0S24R4R3A2A2R2A3S1S8Z0R2A2S8R2R3A2A2SeR4SdZ2Z40A2A2S0S5S3aG0S24R7S18S5aR6S15SfR4A1A1A3A2A2SaR5R4A2A3F_;F_;F_;Fk;Fx;Fa;Frho;").
Proof using .
  clear. intros rho a x k Hx Hk Hx'. rewrite CursorGlue.U_add, Hx, CursorGlue.U_lit. unfold M64v.
  Z.to_euclidean_division_equations; nia.
Qed.

Section SHdrPost.
Variables (CX T Tp Tm H : sstate) (IMP : sstate) (es : list sv) (xs : list xform).
Hypothesis T_eq : ltac2:(tb__ "0|0|
S0S16S9aS17VCX;A1VIMP;A2VT;A3").
Hypothesis fbT : ltac2:(tb__ "0|0|
S0S2cS97S14S22S12VIMP;A1A1S17VCX;A1A3S2dA3").
Hypothesis Tp_eq : ltac2:(tb__ "0|0|
S0S32S16A1SabVT;U0S15Z0A1A3S31S16VTp;A2A3").
Hypothesis ES_eq : ltac2:(tb__ "0|1|
S0S32S2eS10A1M0A1SacVT;U0S15Z0A1A3S31G0Ves;A2A3").
Hypothesis xs_ok : ltac2:(tb__ "0|1|
S0S32S16A1M0G0G0Lx;Sa4VTp;Vxs;A2S16S31S16SaaR1S7fA2A2LX;S37S16A1X32x2S31S16VTm;A2A3").
Hypothesis run_t : ltac2:(tb__ "0|1|
S0S32S2eS41A1M0A1S44S7S75S74VTm;S2dA5S31G0S2fS41S42VH;S43A2S30S41A1A3A2A3").
Hypothesis nexts : ltac2:(tb__ "0|1|
S1S0S6S12VTp;A1M0Sa2S12VT;A1A1A3S1S0S6S12VTm;A1G0A3S1S0S6S12VH;A1G0A3S1S0S2cS1eVTm;A1S34A3S0S2eS14A1S17VTp;A1S17VT;A1A3A2A2A2A2").
Hypothesis T_next : (72 <= ss_next T)%positive.
Hypothesis es_hdr : ltac2:(tb__ "0|1|
S11Sa8U4S33S39Q8A1S25R1P5M0A2A2A2S0S39Q40A1SadR2Ves;A2SafS25R2G0A2A1A3F_;Frho;").

Lemma hdr_postS : ltac2:(tb__ "0|5|
S11S64S2eS39Q40A1M0A1S11S5S2eS39Q8A1M1A1M2S52R6R3A2Sa9S14S2aR4A1S17VCX;A1A3S0G2S25R5P5A2S38G1S57Vcx;Z0Z10000A3M3R3A3A3S8Z4R5A2S0S5R6ScS33G1G3A2A1A3S11S52RcR1A2S6Sa1R1S12VT;A1M4A2S0G0S1cR4R2A2S1cRcR2A2A3F_;Fi;S53Vcx;S1cR3G4A2A2S3cS7Vok;S40S7S51Vcx;RbReRdA4VH;R4A4S3eA4F_;F_;F_;Frho';S3cS7Vok;S40S7S51Vcx;R8RbRaA4VIMP;R9A4S3eA4F_;F_;F_;F_;F_;F_;Frest;Fgot;Frho;Fmat;Fvm;FrhoB;").
Proof using ES_eq T_eq T_next Tp_eq es_hdr fbT nexts run_t xs_ok.
  intros rhoB vm mat rho got rest HB HFC HL5 H4 Hgot FIN. destruct nexts as (NxTp & NxTm & NxH & LnTm & FTp).

  eapply triple_conseq with (P := SP segs (KB got vm mat) T rho); [| intros w Hw; exact Hw |].
  { intros w [Hsm Hk]. split; [|exact Hk]. rewrite <- T_eq. apply smatch_add_facts; [exact Hsm | exact HFC | exact fbT]. }

  eapply triple_conseq with (P := SP segs (KB got vm mat) Tp (pack4_rho rho T es)); [| intros w Hw; exact Hw |].
  { intros w Hw. unfold SP. apply (SPJ_pack4 segs _ rho T 0 (SLit 0) Tp es w Tp_eq ES_eq); [apply stableJ_liftK | exact Hw]. }
  assert (HX : rw (pack4_rho rho T es) (ss_next T) = hdr_val (rl rho 5)).
  { rewrite pack4_rho_nx. apply es_hdr. rewrite HL5, length_app. pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)). lia. }

  destruct (apply_xforms Tp xs) as [X|] eqn:EX; [|discriminate]. injection xs_ok as EM.
  eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ xs _ Tp X w EX Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact (SP_obj_forget segs _ _ X IRS w Hw) | intros w Hw; exact Hw |]. rewrite EM.
  eapply (run_tr ok FUEL CUTS Tm _ _ _ _ run_t LnTm); [apply KB_okf|].
  intros Lf rho6 [<-|[]] Hag6; cbn [lf_state].
  apply FIN.
  - eapply (BR_agree rhoB (pack4_rho rho T es)); [| exact Hag6 | rewrite NxTm, NxTp; lia].
    unfold pack4_rho. apply BR_set_rw; [exact HB | lia].
  - intros i Hi. destruct Hag6 as (W & _). rewrite <- W by (rewrite NxTm, NxTp; lia). unfold pack4_rho. apply rho_set_rw_other. lia.
  - destruct Hag6 as (W & _). rewrite <- W by (rewrite NxTm, NxTp; lia). rewrite HX. unfold HDR, HDRW.
    rewrite HL5. unfold hdr_val. rewrite firstn_app. pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)) as CL.
    replace (4 - length (chunk 0 65536))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
    unfold chunk. cbn [Z.to_nat skipn]. rewrite firstn_firstn. replace (Nat.min 4 (Z.to_nat 65536)) with 4%nat by lia. reflexivity.
Qed.
End SHdrPost.

Lemma es_t : ltac2:(tb__ "0|1|
S1S0S2eS10A1M0S7eS2fS10S6dZ0A1S2fS10S6dZ1A1S2fS10S6dZ2A1S2fS10S6dZ3A1S30S10A1A3A3A3A3A3S0G0S86S7eA3A2").
Proof using . split; reflexivity. Qed.
Lemma es_c : ltac2:(tb__ "0|1|
S1S0S2eS10A1M0S78S2fS10S6dZ0A1S2fS10S6dZ1A1S2fS10S6dZ2A1S2fS10S6eS30S10A1A3A3A3A3A3S1S0G0S85S78A3S1S0G0S83S78A3S0G0S84S78A3A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma fbT_0 : ltac2:(tb__ "0|5|
S1S0S2cS97S14S22S12S90A1M0A1S17S7dA1A3S2dA3S1S0S2cS97S14S22S12S8eA1M1A1S17S7cA1A3S2dA3S1S0S2cS97S14S22S12S8cA1M2A1S17S7bA1A3S2dA3S1S0S6G0P70M3A3S1S0S6S12S91A1G3A3S1S0S6G1G3A3S1S0S6S12S8fA1G3A3S1S0S6G2G3A3S1S0S6S12S8dA1G3A3S1S0S6S12S7dA1P48M4A3S1S0S6S12S7cA1G4A3S1S0S6S12S7bA1G4A3S0S6S12S81A1G4A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma lenient_0h : ltac2:(tb__ "0|0|
S1S0S2cS1eS8bA1S34A3S1S0S2cS1eS8aA1S34A3S0S2cS1eS81A1S34A3A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma wf_src0t : ltac2:(tb__ "0|1|
S1S0S2cS21P70S1bS15Z0A1S15S6aA1M0S18S5aS13S73A1G0A3S30S1fA1S1aA5A2S2dA3S0S2cS21P48S88A2S2dA3A2").
Proof using . split; reflexivity. Qed.

Lemma step0S : ltac2:(tb__ "0|0|
S11S11S3cS7Vok;S3fS7VJD;VKd0;R2S4eSa5VX0;A1A4Sa6R1A4S3eA4Frho;Fr0;").
Proof using TLOOPG TLOOPK TXE0 Hargc Hent Hinp.
  intros r0 rho. pose proof rs_range as RR.
  destruct nexts_0 as (NxT & NxK0r & NxK0 & N71 & NxR0 & NxR00 & NxX00 & NxR0t & NxC0t & NxCx0t & NxT0ta & NxT0tb & NxX1ta & NxX1tb).
  destruct lenient_0 as (LnT & LnK0 & LnR00 & LnR0t & LnP1a & LnP1b). destruct fb_0 as (Fbt & Fbs & Fbm).
  destruct fbT_0 as (FbTs & FbTm & FbTg & NTsA & NTsB & NTmA & NTmB & NTgA & NTgB & NCxs & NCxm & NCxg & NR0g). destruct lenient_0h as (LnR0s & LnR0m & LnR0g).
  destruct ids_0 as (Ix00 & Ix1a & Ix1b & IhsA & IhsB & IhmA & IhmB & IhgA & IhgB). destruct tvs_0 as (Tx00 & Tx1a & Tx1b & ThsA & ThsB & ThmA & ThmB & ThgA & ThgB).

  eapply triple_conseq with (P := SPJ segs (JD (KdR 0) r0 tv0 (DG 65536 0)) T_ok rho); [intros w [Hsm HJ]; split; [exact Hsm |] | intros w Hw; exact Hw |].
  { apply (JD_monoK r0 Kd0); [intros t m Hk; apply Kd0_KdR; exact Hk |].
    eapply (JGD_mono segs C_U 31 Kd0 r0 P0); [|exact HJ]. intros A md' HD. apply (proj2 (DG0 A md')). apply (proj1 (DX0 A md')). exact HD. }

  eapply (run_trJ segs ok FUEL [loop_read] T_ok _ _ rho _ run_tok LnT); [apply JD_okf, KdR_tcons | apply JD_stable; [rewrite NxT; lia | rewrite NxT; apply tvb_0; lia] |].
  intros Lf rho1 [<-|[]] Hag1; cbn [lf_state].
  eapply triple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs_k0 rho1 K0r K0 w xs_k0_ok Hw) | intros w Hw; exact Hw |].

  apply (triple_from ok _ (fun r w => exists vm mat, snapJ segs C_U P0 wtop tv0 (DG 65536 0) r vm mat /\ SP segs (KB 0 vm mat) K0 r w)).
  { intros w Hw. exists rho1. exact (toKs r0 rho1 w Hw). }
  clear rho rho1 Hag1 r0. intros rhoB. apply triple_ex. intros vm. apply triple_ex. intros mat. apply triple_pure. intros HS.

  eapply (run_tr ok FUEL [] K0 _ _ rhoB _ run_k0 LnK0); [apply KB_okf|].
  intros Lf rho1 [<-|[]] Hag1; cbn [lf_state].
  destruct E_rd0_shape as (_ & _ & _ & _ & _ & NxE0 & _ & EoIi & _).
  eapply triple_conseq with (P := SP segs (KB 0 vm mat) E_rd0 (rho_set_rl rho1 7 (img_bytes segs rho1 (mkObj (SLit 0) (SLit rs) (SLit (rs + 65536)) [] DImage))));
    [intros w Hw; unfold SP; apply (SPJ_img_to_list segs _ rho1 E_rd0i IRS 7 E_rd0 _ w E_rd0_eq EoIi); [intros tr md Hk; exact Hk | exact Hw] | intros w Hw; exact Hw |].
  set (rho2 := rho_set_rl rho1 7 _).
  eapply triple_seq; [apply triple1_triple; apply (kread_list rho2 vm mat)|].
  set (got := Z.of_nat (length (chunk 0 65536))).
  set (rho3 := rho_set_rw (rho_set_rl rho2 5 (chunk 0 65536 ++ skipn (length (chunk 0 65536)) (rl rho2 7))) NX0 (len_word (chunk 0 65536))).
  pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)) as CL.
  assert (HB3 : BR rhoB rho3).
  { subst rho3 rho2. apply BR_set_rw; [|rewrite N71; lia]. apply BR_set_rl. apply BR_set_rl. eapply BR_agree; [apply BR_refl | exact Hag1 | rewrite NxK0; lia]. }
  assert (G71 : bv_unsigned (rw rho3 71) = got).
  { subst rho3. rewrite N71, rho_set_rw_at. unfold len_word. apply Z_to_bv_small. rewrite two64. subst got. lia. }
  assert (L5 : rl rho3 5 = chunk 0 65536 ++ skipn (length (chunk 0 65536)) (rl rho2 7)) by (subst rho3; reflexivity).
  destruct (Z.eq_dec L 0) as [HL0|HLnz].
  {
    assert (Hg0 : got = 0) by (subst got; lia).
    eapply triple_conseq with (P := SP segs (KB got vm mat) R00 rho3); [intros w Hw; apply (SP_restate segs _ rho3 R0 R00 w _ _ swf_R00 diff_R00); [|constructor|exact Hw] | intros w Hw; exact Hw |].
    { constructor; [|constructor]. cbn [fst snd eval]. rewrite N71. apply bv_eq. rewrite G71, Hg0. reflexivity. }
    eapply (run_tr ok FUEL CUTS R00 _ _ rho3 _ run_p00 LnR00); [apply KB_okf|].
    intros Lf rho4 [<-|[]] Hag4; cbn [lf_state].
    destruct s_x00_vals as (Sx0 & Sx1 & Sx2). rewrite Hg0. rewrite <- HL0 at 1.
    apply (exit0_viaS X00 s_x00 rhoB vm mat rho4 HS ltac:(eapply BR_agree; [exact HB3 | exact Hag4 | rewrite NxR00; lia]) ent_x00 Ix00 Tx00
             ltac:(rewrite NxX00; lia) ltac:(rewrite NxX00; apply tvb_0; lia)); unfold UV; cbn [rho_sub rw]; [rewrite Sx0 | rewrite Sx1 | lia]; rewrite (Ulit rho4) by lia; lia. }
  destruct (Z_lt_le_dec L 4) as [HL4|HL4].
  {
    assert (HgL : got = L) by (subst got; lia).

    eapply triple_conseq with (P := SP segs (KB got vm mat) R0t rho3); [| intros w Hw; exact Hw |].
    { intros w [Hsm Hk]. rewrite <- R0t_eq. apply SP_obj_forget. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm| |exact Fbt].
      unfold F_0t. rewrite N71. constructor; [|constructor; [|constructor]].
      - apply holds_nbeq. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia.
      - apply holds_ult. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia. }
    eapply (run_tr ok FUEL CUTS R0t _ _ rho3 _ run_p0t LnR0t); [apply KB_okf|].
    intros Lf rho4 [<-|[]] Hag4; cbn [lf_state]. rewrite NxR0t in Hag4.
    assert (HB4 : BR rhoB rho4) by (eapply BR_agree; [exact HB3 | exact Hag4 | lia]).
    assert (T71 : bv_unsigned (rw rho4 71) = L) by (destruct Hag4 as (W & _); rewrite <- W by lia; lia).
    assert (E71 : bv_unsigned (eval rho4 (SVar 71)) = L) by exact T71.
    assert (Egr : bv_unsigned (eval rho4 (SAlu ALU_ADD (SVar 71) (SLit rs))) = L + rs) by (apply (Uadd rho4 (SVar 71) (SLit rs) _ _ E71 (Ulit rho4 rs ltac:(lia))); lia).
    destruct Cr_0t_pre as (Xo6 & FCr & NCr). destruct wf_src0t as [Ws1 Ws0].
    eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ xs_0t rho4 C_0t Cx_0t w xs_0t_ok Hw) | intros w Hw; exact Hw |].
    eapply triple_conseq with (P := SP segs (KB got vm mat) Cr_0t rho4); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- Cr_0t_eq. unfold SP.
      apply (SPJ_reshape segs _ rho4 Cx_0t (IRS + 1) _ O_src0t w Xo6 eq_refl eq_refl eq_refl ltac:(rewrite NxCx0t; exact Ws0)); [|exact Hw].
      intros _. unfold obj_lo_of, obj_hi_of, O_src0t. cbn [ob_base ob_lo ob_hi]. rewrite N71. rewrite (Ulit rho4 0), (Ulit rho4 rs) by lia.
      rewrite !soff_lit_small by lia. rewrite (soff_small rho4 _ _ Egr) by lia. rewrite (soff_small rho4 (SVar 71) L E71) by lia. lia. }
    apply (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) Cr_0t Cr_0t PreG [] s_c0t R_c0t U.Str_memcpy__G1.Str_memcpy.Posts_memcpy _ rho4 eq_refl efr_c0t chk_c0t fb_c0t).
    { intros rho5 _. apply U.Str_memcpy__G1.Str_memcpy.memcpy_sum. apply KB_okf. }
    { intros; exact I. }
    intros Lf rho5 HinL Hag5 HF5. rewrite NCr, NxC0t in Hag5.
    assert (HB5 : BR rhoB rho5) by (eapply BR_agree; [exact HB4 | exact Hag5 | lia]).
    assert (U5 : UV rho5 NX0 = L) by (unfold UV; rewrite N71; destruct Hag5 as (W & _); rewrite <- W by lia; exact T71).
    rewrite HgL. destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
    - eapply triple_conseq with (P := SP segs (KB L vm mat) T0ta rho5); [intros w [Hsm Hk]; rewrite <- T0ta_eq; split; [apply smatch_add_facts; [exact Hsm | exact HF5 | vm_cast_no_check (@eq_refl bool true)] | exact Hk] | intros w Hw; exact Hw |].
      exact (tiny_tailS T0ta Tr0ta Tm0ta H0ta E1ta P1ta X1ta s_x1ta xs_0ta T0ta_objs NxT0ta Tr0ta_eq xs_0ta_ok run_t0ta run_h0ta E1ta_shape cert_rd1ta diff_P1ta swf_P1ta run_p1ta ent_x1ta s_x1ta_vals E1ta_next NxX1ta Ix1a Tx1a ltac:(rewrite NxT0ta; exact Ws1)
               rhoB vm mat rho5 HS HB5 ltac:(lia) U5).
    - eapply triple_conseq with (P := SP segs (KB L vm mat) T0tb rho5); [intros w [Hsm Hk]; rewrite <- T0tb_eq; split; [apply smatch_add_facts; [exact Hsm | exact HF5 | vm_cast_no_check (@eq_refl bool true)] | exact Hk] | intros w Hw; exact Hw |].
      exact (tiny_tailS T0tb Tr0tb Tm0tb H0tb E1tb P1tb X1tb s_x1tb xs_0tb T0tb_objs NxT0tb Tr0tb_eq xs_0tb_ok run_t0tb run_h0tb E1tb_shape cert_rd1tb diff_P1tb swf_P1tb run_p1tb ent_x1tb s_x1tb_vals E1tb_next NxX1tb Ix1b Tx1b ltac:(rewrite NxT0tb; exact Ws1)
               rhoB vm mat rho5 HS HB5 ltac:(lia) U5). }

  assert (Hg4 : 4 <= got <= 65536) by (subst got; lia).
  destruct es_t as [EsA EsB]. destruct es_c as (EmA & EmB & EgA & EgB).
  destruct (Z_lt_le_dec got 65536) as [Hgs|Hgb].
  -
    assert (HgL : got = L) by (subst got; lia).
    assert (FIN : forall (T H : sstate) (sh : wsub) rho', wsub_get sh 100 = SVar NX0 /\ wsub_get sh 101 = SLit 65536 /\ wsub_get sh 102 = SVar 41 /\ wsub_get sh 103 = SVar (ss_next T) ->
              entails H K sh = true -> wsub_id_below sh 31 = true -> tv_sub_eqb sh tv0 tvK = true -> ss_next H = Pos.succ (ss_next T) -> (72 <= ss_next T)%positive ->
              BR rhoB rho' -> rw rho' 71%positive = rw rho3 71%positive -> HDR (rw rho' (ss_next T)) ->
              triple segs ok (SP segs (KB got vm mat) H rho') QF).
    { intros T H sh rho' (S0 & S1 & S2 & S3) He Hid Htv NH NT HB' Hw' HH.
      apply (loopK_viaS H sh rhoB vm mat rho' got HS HB' He Hid Htv ltac:(rewrite NH; lia) ltac:(rewrite NH; apply tvb_0; lia)).
      unfold INVK, UV. cbn [rho_sub rw]. rewrite S0, S1, S3, N71. cbn [eval]. rewrite Hw'. rewrite G71. rewrite lit_unsigned. cbn -[Z.lt Z.le Z.add ALIGNED CAP HDR L].
      split; [lia|]. split; [reflexivity|]. split; [exact HH|]. split; [lia|]. split; [lia|]. split; [right; lia | exact CAP_init]. }
    assert (E68 : bv_unsigned (eval rho3 (SAlu ALU_ADD (SVar 71) (SLit (-3)))) = got - 3) by (apply (Usubk rho3 (SVar 71) got 3 G71); lia).
    destruct (Z_lt_le_dec got 35) as [Hsm|Hbg].
    +
      eapply triple_conseq with (P := SP segs (KB got vm mat) R0s rho3); [| intros w Hw; exact Hw |].
      { intros w [Hsm' Hk]. rewrite <- R0s_eq. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm'| |exact Fbs].
        unfold F_0s. rewrite N71. constructor; [|constructor; [|constructor; [|constructor]]].
        - apply holds_ule. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia.
        - apply holds_bltu. rewrite E68, (Ulit rho3 32) by lia. lia.
        - apply holds_ult. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia. }
      eapply (run_tr ok FUEL CUTS R0s _ _ rho3 _ run_p0s LnR0s); [apply KB_okf|].
      intros Lf rho4 [<-|[]] Hag4; cbn [lf_state]. replace (ss_next R0s) with 72%positive in Hag4 by reflexivity.
      assert (HB4 : BR rhoB rho4) by (eapply BR_agree; [exact HB3 | exact Hag4 | lia]).
      eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ [XSplit 1 (SVar NX0)] rho4 C_0s Cx_0s w xs_0s_ok Hw) | intros w Hw; exact Hw |].
      apply (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) Cx_0s Cx_0s PreRs [] s_c0s R_c0s U.Str_memcpy_rs.Posts_rsS _ rho4 eq_refl efr_c0s chk_c0s fb_c0s).
      { intros rho5 _. apply U.Str_memcpy_rs.memcpy_rsS_sum. apply KB_okf. }
      { intros; exact I. }
      intros Lf rho5 HinL Hag5 HF5. rewrite NCxs in Hag5.
      assert (HB5 : BR rhoB rho5) by (eapply BR_agree; [exact HB4 | exact Hag5 | lia]).
      assert (R5 : forall i, (i < 72)%positive -> rw rho5 i = rw rho3 i).
      { intros i Hi. destruct Hag5 as (W5 & _). destruct Hag4 as (W4 & _). rewrite <- W5, <- W4 by lia. reflexivity. }
      assert (L55 : rl rho5 5 = chunk 0 65536 ++ skipn (length (chunk 0 65536)) (rl rho2 7)).
      { destruct Hag5 as (_ & Wl5 & _). destruct Hag4 as (_ & Wl4 & _). rewrite <- Wl5, <- Wl4. exact L5. }
      destruct HinL as [<-|[<-|[<-|[]]]]; cbn [lf_state].
      * apply (hdr_postS Cx_0s T0sA Tp0sA Tm0sA H0sA _ ES0sA xs_0sA T0sA_eq FbTs Tp0sA_eq ES0sA_eq xs_0sA_ok run_t0sA T0sA_nexts ltac:(rewrite NTsA; lia)
                 ltac:(intros r Hr; rewrite EsA; exact (pack4_hdr_t r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
        intros rho' HB' Hw' HH. apply (FIN T0sA H0sA s_h0sA rho' s_h0sA_vals ent_h0sA IhsA ThsA ltac:(destruct T0sA_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTsA; lia) HB'); [|exact HH].
        rewrite (Hw' 71%positive) by (rewrite NTsA; lia). apply R5. lia.
      * apply (hdr_postS Cx_0s T0sB Tp0sB Tm0sB H0sB _ ES0sB xs_0sB T0sB_eq ltac:(vm_cast_no_check (@eq_refl bool true)) Tp0sB_eq ES0sB_eq xs_0sB_ok run_t0sB T0sB_nexts ltac:(rewrite NTsB; lia)
                 ltac:(intros r Hr; rewrite EsB, EsA; exact (pack4_hdr_t r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
        intros rho' HB' Hw' HH. apply (FIN T0sB H0sB s_h0sB rho' s_h0sB_vals ent_h0sB IhsB ThsB ltac:(destruct T0sB_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTsB; lia) HB'); [|exact HH].
        rewrite (Hw' 71%positive) by (rewrite NTsB; lia). apply R5. lia.
      *
        eapply triple_conseq with (P := SP segs (KB got vm mat) T0sZ rho5); [intros w Hw; rewrite <- T0sZ_eq; exact Hw | intros w Hw; exact Hw |].
        unfold SP. apply triple_leafJ_absurd. intros HFZ.
        pose proof T0sZ_fz as FZ. unfold F_zs in FZ. rewrite N71 in FZ. cbn [forallb] in FZ.
        apply andb_prop in FZ as [Z1 FZ]. apply andb_prop in FZ as [Z2 FZ]. apply andb_prop in FZ as [Z4 FZ]. apply andb_prop in FZ as [Z8 FZ]. apply andb_prop in FZ as [Z16 _].
        pose proof (holds_of_existsb rho5 _ _ HFZ Z1) as H1. pose proof (holds_of_existsb rho5 _ _ HFZ Z2) as H2.
        pose proof (holds_of_existsb rho5 _ _ HFZ Z4) as H4. pose proof (holds_of_existsb rho5 _ _ HFZ Z8) as H8.
        pose proof (holds_of_existsb rho5 _ _ HFZ Z16) as H16.
        apply holds_nbne in H1. apply holds_nbne in H2. apply holds_nbne in H4. apply holds_nbne in H8. apply holds_nbgeu in H16.
        assert (T71 : bv_unsigned (eval rho5 (SVar 71)) = got) by (cbn [eval]; rewrite (R5 71%positive) by lia; exact G71).
        assert (E5 : bv_unsigned (eval rho5 (SAlu ALU_ADD (SVar 71) (SLit (-3)))) = got - 3) by (apply (Usubk rho5 (SVar 71) got 3 T71); lia).
        assert (AND : forall k, bv_unsigned (eval rho5 (SAlu ALU_AND (SAlu ALU_ADD (SVar 71) (SLit (-3))) (SLit k))) = Z.land (got - 3) (bv_unsigned (eval rho5 (SLit k)))).
        { intros k. cbn [eval]. rewrite and_val. cbn [eval] in E5. rewrite <- E5. reflexivity. }
        rewrite AND in H1, H2, H4, H8. rewrite E5 in H16. rewrite !(Ulit rho5) in H1, H2, H4, H8, H16 by lia.
        pose proof (rsZ_absurd_Z (got - 3) ltac:(lia) H1 H2 H4 H8). lia.
    +
      eapply triple_conseq with (P := SP segs (KB got vm mat) R0m rho3); [| intros w Hw; exact Hw |].
      { intros w [Hsm' Hk]. rewrite <- R0m_eq. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm'| |exact Fbm].
        unfold F_0m. rewrite N71. constructor; [|constructor; [|constructor; [|constructor]]].
        - apply holds_ule. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia.
        - apply holds_nbltu. rewrite E68, (Ulit rho3 32) by lia. lia.
        - apply holds_ult. cbn [eval]. rewrite G71, lit_unsigned. cbn. lia. }
      eapply (run_tr ok FUEL CUTS R0m _ _ rho3 _ run_p0m LnR0m); [apply KB_okf|].
      intros Lf rho4 [<-|[]] Hag4; cbn [lf_state]. replace (ss_next R0m) with 72%positive in Hag4 by reflexivity.
      assert (HB4 : BR rhoB rho4) by (eapply BR_agree; [exact HB3 | exact Hag4 | lia]).
      eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ [XSplit 1 (SVar NX0)] rho4 C_0m Cx_0m w xs_0m_ok Hw) | intros w Hw; exact Hw |].
      apply (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) Cx_0m Cx_0m PreRm [] s_c0m R_c0m U.Str_memcpy_rs.Posts_rsB _ rho4 eq_refl efr_c0m chk_c0m fb_c0m).
      { intros rho5 _. apply U.Str_memcpy_rs.memcpy_rsB_sum. apply KB_okf. }
      { intros; exact I. }
      intros Lf rho5 HinL Hag5 HF5. rewrite NCxm in Hag5.
      assert (HB5 : BR rhoB rho5) by (eapply BR_agree; [exact HB4 | exact Hag5 | lia]).
      assert (R5 : forall i, (i < 72)%positive -> rw rho5 i = rw rho3 i).
      { intros i Hi. destruct Hag5 as (W5 & _). destruct Hag4 as (W4 & _). rewrite <- W5, <- W4 by lia. reflexivity. }
      assert (L55 : rl rho5 5 = chunk 0 65536 ++ skipn (length (chunk 0 65536)) (rl rho2 7)).
      { destruct Hag5 as (_ & Wl5 & _). destruct Hag4 as (_ & Wl4 & _). rewrite <- Wl5, <- Wl4. exact L5. }
      destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
      * apply (hdr_postS Cx_0m T0mA Tp0mA Tm0mA H0mA _ ES0mA xs_0mA T0mA_eq FbTm Tp0mA_eq ES0mA_eq xs_0mA_ok run_t0mA T0mA_nexts ltac:(rewrite NTmA; lia)
                 ltac:(intros r Hr; rewrite EmA; exact (pack4_hdr_c r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
        intros rho' HB' Hw' HH. apply (FIN T0mA H0mA s_h0mA rho' s_h0mA_vals ent_h0mA IhmA ThmA ltac:(destruct T0mA_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTmA; lia) HB'); [|exact HH].
        rewrite (Hw' 71%positive) by (rewrite NTmA; lia). apply R5. lia.
      * apply (hdr_postS Cx_0m T0mB Tp0mB Tm0mB H0mB _ ES0mB xs_0mB T0mB_eq ltac:(vm_cast_no_check (@eq_refl bool true)) Tp0mB_eq ES0mB_eq xs_0mB_ok run_t0mB T0mB_nexts ltac:(rewrite NTmB; lia)
                 ltac:(intros r Hr; rewrite EmB, EmA; exact (pack4_hdr_c r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
        intros rho' HB' Hw' HH. apply (FIN T0mB H0mB s_h0mB rho' s_h0mB_vals ent_h0mB IhmB ThmB ltac:(destruct T0mB_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTmB; lia) HB'); [|exact HH].
        rewrite (Hw' 71%positive) by (rewrite NTmB; lia). apply R5. lia.
  -
    assert (Hg : got = 65536) by lia.
    assert (FIN : forall (T H : sstate) (sg : wsub) rho', wsub_get sg 101 = SLit 65536 /\ wsub_get sg 102 = SVar 41 /\ wsub_get sg 103 = SVar (ss_next T) ->
              entails H KG sg = true -> wsub_id_below sg 31 = true -> tv_sub_eqb sg tv0 tvK = true -> ss_next H = Pos.succ (ss_next T) -> (72 <= ss_next T)%positive ->
              BR rhoB rho' -> HDR (rw rho' (ss_next T)) ->
              triple segs ok (SP segs (KB got vm mat) H rho') QF).
    { intros T H sg rho' (S1 & S2 & S3) He Hid Htv NH NT HB' HH. rewrite Hg.
      apply (loopG_viaS H sg rhoB vm mat rho' HS HB' He Hid Htv ltac:(rewrite NH; lia) ltac:(rewrite NH; apply tvb_0; lia)).
      unfold INVG, UV. cbn [rho_sub rw]. rewrite S1, S3. cbn [eval]. rewrite lit_unsigned. cbn -[Z.le CAP HDR L].
      split; [reflexivity|]. split; [exact HH|]. split; [lia | exact CAP_init]. }
    eapply triple_conseq with (P := SP segs (KB got vm mat) R0g rho3); [intros w Hw; apply (SP_restate segs _ rho3 R0 R0g w _ _ swf_R0g diff_R0g); [|constructor|exact Hw] | intros w Hw; exact Hw |].
    { constructor; [|constructor]. cbn [fst snd eval]. rewrite N71. apply bv_eq. rewrite G71, Hg, lit_unsigned. reflexivity. }
    eapply (run_tr ok FUEL CUTS R0g _ _ rho3 _ run_p0g LnR0g); [apply KB_okf|].
    intros Lf rho4 [<-|[]] Hag4; cbn [lf_state]. rewrite NR0g in Hag4.
    assert (HB4 : BR rhoB rho4) by (eapply BR_agree; [exact HB3 | exact Hag4 | lia]).
    eapply triple_conseq; [intros w Hw; exact (SP_xforms segs _ [XSplit 1 (SLit 65536)] rho4 C_0g Cx_0g w xs_0g_ok Hw) | intros w Hw; exact Hw |].
    apply (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) Cx_0g Cx_0g PreRg [] s_c0g R_c0g U.Str_memcpy_rs.Posts_rsB _ rho4 eq_refl efr_c0g chk_c0g fb_c0g).
    { intros rho5 _. apply U.Str_memcpy_rs.memcpy_rsB_sum. apply KB_okf. }
    { intros; exact I. }
    intros Lf rho5 HinL Hag5 HF5. rewrite NCxg in Hag5.
    assert (HB5 : BR rhoB rho5) by (eapply BR_agree; [exact HB4 | exact Hag5 | lia]).
    assert (L55 : rl rho5 5 = chunk 0 65536 ++ skipn (length (chunk 0 65536)) (rl rho2 7)).
    { destruct Hag5 as (_ & Wl5 & _). destruct Hag4 as (_ & Wl4 & _). rewrite <- Wl5, <- Wl4. exact L5. }
    destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
    + apply (hdr_postS Cx_0g T0gA Tp0gA Tm0gA H0gA _ ES0gA xs_0gA T0gA_eq FbTg Tp0gA_eq ES0gA_eq xs_0gA_ok run_t0gA T0gA_nexts ltac:(rewrite NTgA; lia)
               ltac:(intros r Hr; rewrite EgA, EmA; exact (pack4_hdr_c r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
      intros rho' HB' Hw' HH. exact (FIN T0gA H0gA s_h0gA rho' s_h0gA_vals ent_h0gA IhgA ThgA ltac:(destruct T0gA_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTgA; lia) HB' HH).
    + apply (hdr_postS Cx_0g T0gB Tp0gB Tm0gB H0gB _ ES0gB xs_0gB T0gB_eq ltac:(vm_cast_no_check (@eq_refl bool true)) Tp0gB_eq ES0gB_eq xs_0gB_ok run_t0gB T0gB_nexts ltac:(rewrite NTgB; lia)
               ltac:(intros r Hr; rewrite EgB, EmA; exact (pack4_hdr_c r Hr)) rhoB vm mat rho5 got _ HB5 HF5 L55 ltac:(lia) eq_refl).
      intros rho' HB' Hw' HH. exact (FIN T0gB H0gB s_h0gB rho' s_h0gB_vals ent_h0gB IhgB ThgB ltac:(destruct T0gB_nexts as (A & _ & B & _); rewrite B, A; reflexivity) ltac:(rewrite NTgB; lia) HB' HH).
Qed.

End FirstS.

Theorem r_safe_loopS : ltac2:(tb__ "0|7|
S11S11S5S5S56Vcx;R2R3A3S1S8Z0M0R2A2S8R2ZaM1A2A2S48R4R3A2S3cS7Vok;S3fS7VJD;S50Vcx;ScS33S39Q8A1S59Vcx;A1A2A1M2A2M3R7S4fS47R5R4A2A4S7aR6A4S3eA4F_;F_;F_;Fg;Fcap;Frho;Fr0;S11S11S5S0S5S4dR2P65A2M4SdZ2Z1aA2M5A3S8G5G2A2S53Vcx;S1cR4P67A2A2S1S8G0R4A2S8R4G1A2A2S3cS7Vok;S3fS7VJD;S50Vcx;G5A2R7S4fS47G5R5A2A4S82R6A4S3eA4F_;F_;F_;F_;Fg;Frho;Fr0;S11S11S0S5S4dR1P64A2G2A3S0S5G4Z10000M6A3SeG2Z4A2S3cS7Vok;S3fS7VJD;G3R5S4fS47G6G0A2A4S79R4A4S3eA4F_;F_;F_;Frho;Fr0;S11S11S3cS7Vok;S3fS7VJD;VKd0;R2S4eSa5VX0;A1A4Sa6R1A4S3eA4Frho;Fr0;F_;F_;F_;").
Proof using FDX HX0 MBX Hargc Hent Hinp.
  intros TXEH TXref TXE0. apply step0S.
  - intros r0 rho len HI. exact (proj1 (loop_allS r0 (TXEH r0) (TXref r0) (2 * (L - len) + 1)) rho len 65536 0 ltac:(lia) HI (conj (Z.le_refl 0) eq_refl)).
  - intros r0 rho HI. exact (proj2 (loop_allS r0 (TXEH r0) (TXref r0) (2 * (L - 65536) + 2)) rho 65536 0 ltac:(lia) HI (conj (Z.le_refl 0) eq_refl)).
  - exact TXE0.
Qed.

End SX.
End RS.
