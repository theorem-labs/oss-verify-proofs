(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "sub"; "mul"; "of_nat"; "pow"; "lt"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_next"; "SVar"; "sprop"; "SLit"; "sstate"; "ss_facts"; "SAlu"; "reg_sv"; "DUnknown"; "mkObj"; "rw"; "sobj"; "ss_lenient"; "cell"; "SPUle"; "obj_wf"; "sprop_below"; "ss_objs"; "eval"; "rl"; "SPBranch"; "ss_pc"; "SPNot"; "SPUlt"; "holds"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "cons"; "nil"; "Some"; "option"; "length"; "false"; "prod"; "pair"; "None"; "app"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rs"; "QF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsCut"; "sym_run"; "RsEcall"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rs.RS.SX"; "DG"; "CAPG"; "DX"; "XOf"; "kOf"; "DM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r"; "UV"; "tv0"; "tvK"; "KdR"; "KB"; "BR"; "HDR"; "INVG"; "INVK"; "INVX"; "chunk"; "tvG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx"; "f_F"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "instr"; "ALU_SUB"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "sv_subst"; "wsub_id_below"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "Model"; "FdEntry"; "m_vm_materialized"; "m_vmmaps"; "with_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "rs"; "read_ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyRS"; "Eb"; "E3c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "tv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "NX0"; "CUTS"; "FUEL"; "K"; "KG"; "ES0mA"; "XE0"; "XEH"; "Cx_0g"; "Cx_0m"; "Cx_0s"; "ES0sA"; "IRS"; "K0"; "R0g"; "X_ref"; "ES0gA"; "ES0gB"; "ES0mB"; "ES0sB"; "O_rsU"; "O_src0t"; "P_E_rdA"; "R0m"; "R0s"; "T0gA"; "T0gB"; "T0mA"; "T0mB"; "T0sA"; "T0sB"; "T_gok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "snapJ"; "CAP"; "ALIGNED"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "tl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rs.RS.SX.LoopS"; "LoopIHs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "init_cost"; "malloc_cost"; "DRV_OPS"; "drvN"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m"; "DokS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states"; "T_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rs.RS"; "Dvm"; "@Corelib.Init.Peano"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue2"; "obj_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.HdrPack"; "pack4_at"; "pack4_vals"; "pack4_word"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead"; "S_after_var"; "hdr_val"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List Bool.Bool PArith.PArith micromega.Lia.
From Stdlib Require Import Strings.Ascii Strings.String.
From stdpp Require Import bitvector.bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLayout MallocIface MallocLaws Contract ContractDrv Pristine ClientLaws Glue RoomS ContractS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall SymBytes SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import
  SumConv CfgGlue CursorGlue ObjXform ObjUnbase CallGlue ListObj StrBytes InitLayout InitState InitStrs InitArg1 MuslWL MuslMemcpyHdr MuslMemcpy MuslMemcpyRS HdrPack ImgList
  DrvGlue DrvGlue2 SysExtra SysRead SysReadList DataWin TobjJV DrvJ DrvStatics DrvPristine DrvLoop DrvTail1 DrvWins.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec SpecConsts.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy_rs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy_hdr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy_rs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import MAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import XLia.
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
  intros m rho len cap got b g Loop Meas Ulen Ucap Ubuf Ugot Hdr Len4 [Gpos Gmax] Room InFile Ali CapOk Top Bot Gnn Cg.
  pose proof (CAP_facts cap CapOk) as (CapRange & _ & _). pose proof rs_range as RsR.
  unfold UV in Ulen, Ucap, Ubuf, Ugot.
  apply (triple_add_facts segs ok _ rho F_E_rdA P_E_rdA PP_E_rdA _ PP_E_rdA_eq).
  { vm_compute. reflexivity. }
  { assert (FactsA : F_E_rdA = [SPNot (SPBranch BC_EQ (SVar 153) (SLit 0)); SPUle (SVar 153) (SLit 65536);
                                SPUle (SAlu ALU_ADD (SVar 100) (SVar 153)) (SVar 101)]) by (vm_compute; reflexivity).
    rewrite FactsA. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply holds_nbeq. rewrite (Ulit rho 0) by lia. cbn [eval]. lia.
    - apply holds_ule. rewrite (Ulit rho 65536) by lia. cbn [eval]. lia.
    - apply holds_ule. rewrite (Uadd rho (SVar 100) (SVar 153) len got Ulen Ugot) by lia. cbn [eval]. lia. }
  assert (NextPP : ss_next PP_E_rdA = 154%positive) by (vm_compute; reflexivity).
  eapply (run_trJ segs ok FUEL CUTS PP_E_rdA _ _ rho _ run_pp_E_rdA).
  { vm_compute. reflexivity. }
  { apply JD_okf, KdR_tcons. }
  { apply JD_stable; rewrite NextPP; [lia | apply tvK_below; lia]. }
  intros Lf rho1 [<-|[]] Agree1. cbn [lf_state]. rewrite NextPP in Agree1. destruct Agree1 as (Agree1w & _ & _).
  assert (Same1 : forall i, (i < 154)%positive -> rw rho1 i = rw rho i) by (intros i Below; symmetry; exact (Agree1w i Below)).
  assert (W100 : bv_unsigned (eval rho1 (SVar 100)) = len) by (cbn [eval]; rewrite Same1 by lia; exact Ulen).
  assert (W102 : bv_unsigned (eval rho1 (SVar 102)) = b) by (cbn [eval]; rewrite Same1 by lia; exact Ubuf).
  assert (W153 : bv_unsigned (eval rho1 (SVar 153)) = got) by (cbn [eval]; rewrite Same1 by lia; exact Ugot).
  eapply triple_conseq; [intros w Pw; exact (SPJ_xforms segs _ xs_cE_rdA rho1 C_E_rdA Cx_E_rdA w xs_cE_rdA_ok Pw) | intros w Qw; exact Qw |].
  destruct Cr_E_rdA_pre as (Obj3 & Obj8 & _ & _).
  assert (NextCr : ss_next Cr_E_rdA = 154%positive) by (vm_compute; reflexivity).
  eapply triple_conseq with (P := SPJ segs (JS (len + got) cap g) Cr_E_rdA rho1); [|intros w Qw; exact Qw|].
  { intros w Pw. rewrite <- Cr_E_rdA_eq.
    assert (Dst : O_dstE_rdA = mkObj (SAlu ALU_ADD (SVar 102) (SVar 100)) (SLit 0) (SVar 153) [] DUnknown) by (vm_compute; reflexivity).
    assert (Src : O_srcE_rdA = mkObj (SLit rs) (SLit 0) (SVar 153) [] DUnknown) by (vm_compute; reflexivity).
    refine (SPJ_reshape segs _ rho1 _ (IRS + 3) _ O_srcE_rdA w Obj8 _ _ eq_refl _ _ _).
    { rewrite Src. reflexivity. }
    { rewrite Src. reflexivity. }
    { vm_compute. reflexivity. }
    { intros _. rewrite Src. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
      rewrite (Ulit rho1 rs), (Ulit rho1 0) by lia. rewrite !soff_lit_small by lia.
      rewrite (soff_small rho1 _ _ W153) by lia.
      rewrite (soff_small rho1 _ (got + rs) (Uadd rho1 (SVar 153) (SLit rs) got rs W153 (Ulit rho1 rs ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia))) by lia.
      lia. }
    refine (SPJ_reshape segs _ rho1 Cx_E_rdA 3 _ O_dstE_rdA w Obj3 _ _ eq_refl _ _ Pw).
    { rewrite Dst. reflexivity. }
    { rewrite Dst. reflexivity. }
    { vm_compute. reflexivity. }
    intros _. rewrite Dst. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
    rewrite (Uadd rho1 (SVar 102) (SVar 100) b len W102 W100) by lia. rewrite W102, !soff_lit_small by lia.
    rewrite (soff_small rho1 _ _ W100), (soff_small rho1 _ _ W153) by lia.
    rewrite (soff_small rho1 _ (len + got) (Uadd rho1 (SVar 100) (SVar 153) len got W100 W153 ltac:(lia) ltac:(lia) ltac:(lia))) by lia.
    lia. }
  refine (pure_callD r0 (KdR (len + got)) tvK (DG cap g) Cr_E_rdA PreG s_cE_rdA R_cE_rdA Posts_memcpy rho1 QF _ efr_cE_rdA chk_cE_rdA _ _ fb_cE_rdA _).
  - intros rho2. exact (memcpy_sum ok _ rho2 (fun tr ms md ms' Jk => JD_okf (KdR (len + got)) r0 tvK (DG cap g) (KdR_tcons (len + got)) rho1 tr ms md ms' Jk)).
  - rewrite NextCr. lia.
  - rewrite NextCr. apply tvK_below. lia.
  - intros Lf rho2 InPost Agree2. rewrite NextCr in Agree2. destruct Agree2 as (Agree2w & _ & _).
    assert (Same2 : forall i, (i < 154)%positive -> rw rho2 i = rw rho i) by (intros i Below; rewrite <- (Agree2w i Below); exact (Same1 i Below)).
    assert (V100 : UV rho2 100 = len) by (unfold UV; rewrite Same2 by lia; exact Ulen).
    assert (V101 : UV rho2 101 = cap) by (unfold UV; rewrite Same2 by lia; exact Ucap).
    assert (V102 : UV rho2 102 = b) by (unfold UV; rewrite Same2 by lia; exact Ubuf).
    assert (V153 : UV rho2 153 = got) by (unfold UV; rewrite Same2 by lia; exact Ugot).
    assert (Hdr2 : HDR (rw rho2 103)) by (rewrite Same2 by lia; exact Hdr).
    unfold Posts_memcpy, MuslMemcpy.Posts_memcpy in InPost.
    destruct InPost as [<-|[<-|[]]]; cbn [lf_state].
    + rewrite TE_rdAa_eq.
      refine (copy_tailS TE_rdAa TrE_rdAa TmE_rdAa GE_rdAa HE_rdAa GRE_rdAa GKE_rdAa HKE_rdAa s_hE_rdAa s_gE_rdAa xs_tE_rdAa FKE_rdAa FGE_rdAa
                TrE_rdAa_eq TE_rdAa_objs _ xs_tE_rdAa_ok run_tE_rdAa HGE_rdAa_regs _ HKE_rdAa_eq ent_hE_rdAa s_hE_rdAa_vals _
                GE_rdAa_fact diff_GRE_rdAa swf_GRE_rdAa _ _ GKE_rdAa_eq ent_gE_rdAa s_gE_rdAa_vals _ _ _
                m rho2 len cap got b g Loop Meas V100 V101 V102 V153 Hdr2 Len4 Gpos Room InFile Ali CapOk Top Gnn Cg).
      all: vm_compute; repeat split.
    + rewrite TE_rdAb_eq.
      refine (copy_tailS TE_rdAb TrE_rdAb TmE_rdAb GE_rdAb HE_rdAb GRE_rdAb GKE_rdAb HKE_rdAb s_hE_rdAb s_gE_rdAb xs_tE_rdAb FKE_rdAb FGE_rdAb
                TrE_rdAb_eq TE_rdAb_objs _ xs_tE_rdAb_ok run_tE_rdAb HGE_rdAb_regs _ HKE_rdAb_eq ent_hE_rdAb s_hE_rdAb_vals _
                GE_rdAb_fact diff_GRE_rdAb swf_GRE_rdAb _ _ GKE_rdAb_eq ent_gE_rdAb s_gE_rdAb_vals _ _ _
                m rho2 len cap got b g Loop Meas V100 V101 V102 V153 Hdr2 Len4 Gpos Room InFile Ali CapOk Top Gnn Cg).
      all: vm_compute; repeat split.
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
Proof using FDX TXEH.
  intros m rho cap g [LoopK _] Meas Ucap Hdr CapL CapOk Small Gnn Cg.
  pose proof (CAP_facts cap CapOk) as (CapR & CapAl & CapDbl). specialize (CapDbl Small).
  destruct (g_lt_bound cap g Gnn Cg Small) as [G9 Half].
  unfold UV in Ucap.
  eapply triple_conseq; [intros w Pw; exact (SPJ_xforms segs _ xs_g rho T_gok T_gokS w xs_g_ok Pw) | intros w Qw; exact Qw |].
  assert (NgS : ss_next T_gokS = 193%positive) by (vm_compute; reflexivity).
  eapply (run_trJ segs ok FUEL CUTS T_gokS _ _ rho _ run_goks);
    [vm_compute; reflexivity | apply JD_okf, KdR_tcons | apply JD_stable; rewrite NgS; [lia | vm_compute; reflexivity] |].
  intros Lf rho1 [<-|[]] Agree1. cbn [lf_state]. rewrite NgS in Agree1. destruct Agree1 as (Agree1w & _ & _).
  assert (Nmc : ss_next C_mc = 193%positive) by (vm_compute; reflexivity).
  refine (pure_callD r0 (KdR cap) tvG (DM cap g) C_mc PreC s_mc R_mc Posts_mh rho1 QF _ efr_mc chk_mc _ _ fb_mc _).
  { intros rho2. exact (memcpy_hdr_sum ok _ rho2 (fun tr ms md ms' Jk => JD_okf (KdR cap) r0 tvG (DM cap g) (KdR_tcons cap) rho1 tr ms md ms' Jk)). }
  { rewrite Nmc. lia. }
  { rewrite Nmc. vm_compute. reflexivity. }
  intros Lf rho2 InPost Agree2. rewrite Nmc in Agree2. destruct Agree2 as (Agree2w & _ & _).
  rewrite Posts_mh_eq in InPost. destruct InPost as [<-|[]]. cbn [lf_state]. rewrite T_mc_eq.
  eapply triple_conseq; [intros w Pw; exact (SPJ_xforms segs _ xs_m rho2 T_mc T_mcM w xs_m_ok Pw) | intros w Qw; exact Qw |].
  assert (NmM : ss_next T_mcM = 233%positive) by (vm_compute; reflexivity).
  eapply (run_trJ segs ok FUEL CUTS T_mcM _ _ rho2 _ run_mcm);
    [vm_compute; reflexivity | apply JD_okf, KdR_tcons | apply JD_stable; rewrite NmM; [lia | vm_compute; reflexivity] |].
  intros Lf rho3 [<-|[]] Agree3. cbn [lf_state]. rewrite NmM in Agree3. destruct Agree3 as (Agree3w & _ & _).
  assert (Back3 : forall i, (i < 193)%positive -> rw rho3 i = rw rho i).
  { intros i Below. rewrite <- (Agree3w i ltac:(lia)), <- (Agree2w i Below). symmetry. exact (Agree1w i Below). }
  refine (dfree_call segs C_U EC_U 31 (KdR cap) r0 P0 malloc_laws_U ok C_fr s_fr R_fr rho3 tvG 1 (SVar 102, SVar 101) QF (DM cap g)
            (fun Ai => J_free_S segs C_U Ai (kOf g - 1) (XOf cap g - malloc_cost (2 * cap)) (KdR cap))
            (fun Ai => JLdS_free segs C_U Ai (kOf g - 1 - 1) (XOf cap g - malloc_cost (2 * cap)) (KdR cap))
            (DG (2 * cap) (g + 1)) _ _ efr_fr chk_fr _ _ _ eq_refl _ _ _).
  { vm_compute. reflexivity. }
  { intros Ai rho4. exact (FDX ok Ai (kOf g - 1) (XOf cap g - malloc_cost (2 * cap)) (KdR cap) rho4 (okside cap)). }
  { vm_compute. reflexivity. }
  { vm_compute. reflexivity. }
  { vm_compute. reflexivity. }
  { intros Ai tr ms md Smatch Gi [Drv Room].
    pose proof (smatch_facts segs rho3 C_fr _ Smatch) as Facts.
    pose proof (T_ok_of_JGi (KdR cap) r0 tvG Ai rho3 tr md Gi) as Tok.
    destruct Gi as (_ & _ & (Minv & _ & _) & _ & (Tin & Td & Tz) & _ & _).
    destruct s_fr_vals as (S12 & S13 & _ & _).
    assert (Nz : bv_unsigned (eval rho3 (SVar 102)) <> 0).
    { pose proof (Forall_nth_error _ _ 5 _ Facts (ltac:(vm_compute; reflexivity) : nth_error (ss_facts C_fr) 5 = Some (SPNot (SPBranch BC_EQ (SVar 102) (SLit 0))))) as F5.
      apply holds_nbeq in F5. rewrite (Ulit rho3 0) in F5 by lia. exact F5. }
    refine (conj _ (conj Nz (conj _ _))).
    - intros Jpre. refine (conj Jpre (conj Drv (conj _ Room))). unfold kOf. rewrite DRV_OPS_val. lia.
    - rewrite S12, S13. reflexivity.
    - refine (robjs_check_sound segs C_U [] Ai rho3 (ss_facts C_fr) tvG (Some 1%nat) (robj_inw WINS_U) R_fr _ rho3 md Minv Tok Facts Tin Td Tz rchk_fr _ _).
      + intros o a _ Ext Rng. exact (robj_inw_caddr segs C_U WINS_U rho3 Ai _ o a WINS_U_ok Ext Rng).
      + exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact Nz|]. rewrite S12. reflexivity. }
  { intros Ai r0' r' tr md (A' & l1 & l2 & Minv' & [Done Top] & Drv' & Room' & Blk & Blk' & Kept & Kc).
    exists A', l1, l2. refine (conj Minv' (conj (conj Done Top) (conj Blk (conj Blk' (conj Kept (conj Kc _)))))).
    exact (DG_next cap g A' md (conj Drv' Room')). }
  intros rho4 [Agree4w _]. rewrite (ltac:(vm_compute; reflexivity) : ss_next C_fr = 233%positive) in Agree4w. rewrite T_fr_eq.
  change (triple segs ok (SPJ segs (JD (KdR cap) r0 [(SVar 163, SAlu ALU_SLL (SVar 101) (SLit 1))] (DG (2 * cap) (g + 1))) T_fr rho4) QF).
  assert (Nfr : ss_next T_fr = 273%positive) by (vm_compute; reflexivity).
  eapply (run_trJ segs ok FUEL CUTS T_fr _ _ rho4 _ run_fr);
    [vm_compute; reflexivity | apply JD_okf, KdR_tcons | apply JD_stable; rewrite Nfr; [lia | vm_compute; reflexivity] |].
  intros Lf rho5 [<-|[]] Agree5. cbn [lf_state]. rewrite Nfr in Agree5. destruct Agree5 as (Agree5w & _ & _).
  assert (Back5 : forall i, (i < 193)%positive -> rw rho5 i = rw rho i).
  { intros i Below. rewrite <- (Agree5w i ltac:(lia)), <- (Agree4w i ltac:(lia)). exact (Back3 i Below). }
  assert (R101 : bv_unsigned (eval rho5 (SVar 101)) = cap) by (cbn [eval]; rewrite Back5 by lia; exact Ucap).
  assert (R2c : bv_unsigned (eval rho5 (SAlu ALU_SLL (SVar 101) (SLit 1))) = 2 * cap) by (apply Usll1; [exact R101 | lia | lia]).
  apply (triple_add_facts segs ok _ rho5 FK_fr H_fr HK_fr _ HK_fr_eq); [vm_compute; reflexivity | |].
  { assert (FKv : FK_fr = [SPUle (SAlu ALU_SLL (SVar 101) (SLit 1)) (SLit 67108864)]) by (vm_compute; reflexivity).
    rewrite FKv. constructor; [|constructor]. apply holds_ule. rewrite R2c, (Ulit rho5 67108864) by lia. lia. }
  apply (reenter r0 (KdR cap) [(SVar 163, SAlu ALU_SLL (SVar 101) (SLit 1))] tvK (DG (2 * cap) (g + 1)) HK_fr K s_hfr rho5 QF 273 ent_hfr);
    [vm_compute; reflexivity | lia | vm_compute; reflexivity | vm_compute; reflexivity |].
  destruct s_hfr_vals as (Q100 & Q101 & _ & Q103).
  apply (LoopK (rho_sub rho5 s_hfr) cap (2 * cap) (g + 1)); [lia | | split; [lia | unfold CAPG in *; rewrite Z.pow_add_r, Z.pow_1_r by lia; lia]].
  unfold INVK, UV. cbn [rho_sub rw]. rewrite Q100, Q101, Q103.
  refine (conj R101 (conj R2c (conj _ (conj _ (conj CapL (conj (or_introl CapAl) (CAP_double cap CapOk Small))))))).
  - cbn [eval]. apply HDR_sext. rewrite Back5 by lia. exact Hdr.
  - lia.
Qed.

Lemma stepGS : ltac2:(tb__ "0|0|
S5S11S5S5S99R4A1S8S9SbZ2SaScS33S39Q8A1S59Vcx;A1A2A1R3A2A2Z1A2R5A2S54Vcx;R4R5A3S8Z0R4A2S48R6R5A2S3cS7Vok;S3fS7VJS;R7R7R6A3S77R8A4S3eA4F_;F_;F_;F_;F_;Fg;Fcap;Frho;Fm;").
Proof using HX0 MBX FDX TXEH TXref.
  intros m rho cap g Loop Meas (Ucap & Hdr & CapL & CapOk) Gnn Cg.
  pose proof (CAP_facts cap CapOk) as (CapR & CapAl & CapDbl).
  unfold UV in Ucap.
  eapply (run_trJ segs ok FUEL CUTS KG _ _ rho _ run_kg);
    [vm_compute; reflexivity | apply JD_okf, KdR_tcons | apply JD_stable; rewrite (proj1 (proj2 cuts_shape)); [lia | apply tvK_below; lia] |].
  rewrite (proj1 (proj2 cuts_shape)).
  intros Lf rho1 [<-|[<-|[]]] Agree1; cbn [lf_state]; destruct Agree1 as (Agree1w & _ & _);
    (assert (W101 : bv_unsigned (eval rho1 (SVar 101)) = cap) by (cbn [eval]; rewrite <- Agree1w by lia; exact Ucap));
    (assert (W103 : rw rho1 103 = rw rho 103) by (symmetry; apply Agree1w; lia)).
  - apply triple_factsJ. intros FX.
    destruct X_ref_shape as (_ & _ & Fx0).
    pose proof (Forall_nth_error _ _ _ _ FX Fx0) as Big. apply holds_bne in Big.
    rewrite U_srl_lit, W101, (Ulit rho1 0) in Big by lia.
    assert (Top : cap = 2 ^ 26).
    { destruct (Z_lt_le_dec cap (2 ^ 26)) as [Below|Above]; [|lia].
      exfalso. apply Big. apply Z.div_small. change (26 mod 64) with 26. lia. }
    rewrite Top in W101, CapL, Cg |- *.
    apply (TXref rho1 g); [unfold UV; cbn [eval] in W101; exact W101 | exact CapL | rewrite W103; exact Hdr |].
    split; [exact Gnn|]. apply pow_g_bound; [exact Gnn|]. unfold CAPG in Cg. lia.
  - apply triple_factsJ. intros FC.
    destruct C_gm_shape as (_ & NCgm & _ & Fc0).
    pose proof (Forall_nth_error _ _ _ _ FC Fc0) as Fit. apply holds_nbne in Fit.
    rewrite U_srl_lit, W101, (Ulit rho1 0) in Fit by lia. change (26 mod 64) with 26 in Fit.
    assert (Small : cap < 2 ^ 26).
    { destruct (Z_lt_le_dec cap (2 ^ 26)) as [Below|Above]; [exact Below|].
      exfalso. pose proof (Z.div_str_pos cap (2 ^ 26) ltac:(lia)). lia. }
    specialize (CapDbl Small).
    destruct (g_lt_bound cap g Gnn Cg Small) as [G9 Half].
    assert (Twice : bv_unsigned (eval rho1 (SAlu ALU_SLL (SVar 101) (SLit 1))) = 2 * cap) by (apply Usll1; [exact W101 | lia | lia]).
    destruct s_gm_vals as (G12 & _ & _ & _ & _).
    refine (dmalloc_call segs C_U EC_U 31 (KdR cap) r0 P0 malloc_laws_U ok C_gm s_gm R_gm rho1 tvK QF (DG cap g)
              (fun Ai => J_big_S segs C_U Ai (kOf g) (XOf cap g) (KdR cap))
              (fun Ai => [(L_malloc_ok EC_U, JLdS_big_ok segs C_U Ai (kOf g) (XOf cap g) (KdR cap))])
              (fun _ _ _ _ _ => False) (fun Ai => JLdS_big_ok segs C_U Ai (kOf g) (XOf cap g) (KdR cap))
              (DG cap g) (DM cap g) _ _ efr_gm (fun _ => chk_gm_ok) _ _ _ _ _ _ _ _ _ _ _).
    + vm_compute. reflexivity.
    + intros Ai rho2. exact (MBX ok Ai (kOf g) (XOf cap g) (KdR cap) rho2 (okside cap)).
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + intros Ai tr ms md Smatch Gi Dg TpOk TopV.
      pose proof (smatch_facts segs rho1 C_gm _ Smatch) as Facts.
      pose proof (T_ok_of_JGi (KdR cap) r0 tvK Ai rho1 tr md Gi) as Tok.
      destruct Gi as (_ & Kc & (Minv & Ini & Tpi) & _ & (Tin & Td & Tz) & _ & _).
      destruct Dg as [Drv Room].
      assert (Rok : robjs_ok segs C_U Ai None rho1 R_gm).
      { refine (robjs_check_sound segs C_U [] Ai rho1 (ss_facts C_gm) tvK None (robj_inw WINS_U) R_gm None rho1 md Minv Tok Facts Tin Td Tz rchk_gm _ I).
        intros o a _ Ext Rng. exact (robj_inw_caddr segs C_U WINS_U rho1 Ai None o a WINS_U_ok Ext Rng). }
      assert (Arg : bv_unsigned (rw (rho_sub (rho_absorb rho1 R_gm ms) s_gm) 12) = 2 * cap).
      { cbn [rho_sub rw]. rewrite G12. apply Usll1; [cbn [eval rho_absorb rw]; exact W101 | lia | lia]. }
      refine (conj _ (conj Rok _)); [|rewrite G12, Twice; lia].
      refine (conj _ (conj Drv (conj _ (conj _ (conj Kc (conj (conj Room _) (conj TpOk TopV))))))).
      * refine (proj1 (MInvR_mem segs C_U r0 malloc_laws_U Ai rho1 _ md md (conj Minv (conj Ini Tpi)) _ eq_refl)).
        intros a Ra Own. cbn [rho_sub rho_absorb rm].
        destruct (in_ranges_dec rho1 R_gm (Z_to_bv 64 a)) as [InR|Miss]; [|reflexivity].
        exfalso. exact (R_miss segs C_U malloc_laws_U Ai None rho1 rho1 md R_gm a Minv Rok Ra Own InR).
      * unfold kOf. rewrite DRV_OPS_val. lia.
      * rewrite Arg. rewrite MMAP_THRESHOLD_val. lia.
      * rewrite Arg, malloc_cost_val. unfold XOf. rewrite init_cost_val.
        assert (P21 : 2 ^ 21 = 2097152) by reflexivity. assert (P17 : 2 ^ 17 = 131072) by reflexivity.
        assert (P25 : 2 ^ 25 = 33554432) by reflexivity. assert (P28 : 2 ^ 28 = 268435456) by reflexivity.
        rewrite init_cost_val in HX0. lia.
    + intros Ai x [<-|[]]. right. reflexivity.
    + intros Ai r0' r' tr md [].
    + intros Ai r0' r' tr md R12 (A' & l1 & l2 & Minv' & [Done Top] & Drv' & Room' & Blk' & Blk & Kept & Kc').
      assert (Old12 : bv_unsigned (rw r0' 12) = 2 * cap) by (rewrite R12, G12; exact Twice).
      rewrite Old12 in Room'.
      exists A', l1, l2. refine (conj Minv' (conj (conj Done Top) (conj Blk' (conj Blk (conj Kept (conj Kc' (conj Drv' Room'))))))).
    + intros (Ai & [Same|[]]). exfalso. injection Same as Eq _. vm_compute in Eq. congruence.
    + intros _ rho2 [Agree2w _]. rewrite NCgm in Agree2w. rewrite T_gok_eq.
      change (triple segs ok (SPJ segs (JD (KdR cap) r0 tvG (DM cap g)) T_gok rho2) QF).
      apply (stepG_okS m rho2 cap g Loop Meas); [unfold UV; rewrite <- Agree2w by lia; cbn [eval] in W101; exact W101 | rewrite <- Agree2w by lia; rewrite W103; exact Hdr | exact CapL | exact CapOk | exact Small | exact Gnn | exact Cg].
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
Proof using Hent Hinp Hargc.
  intros r0 rho w [Smatch Jnow].
  pose proof (P0_now sp brk mb draw inp Hent Hinp Hargc _ _ _ _ _ _ _ Jnow) as P0rho.
  destruct Jnow as (Ai & Gi & Dg).
  destruct (deJ segs C_U 31 P0 wtop P0_top (KdR 0) r0 tv0 (DG 65536 0) Ai rho _ _ Gi Dg P0rho) as [Snap Kcur].
  exists (m_vmmaps (cfg_model (w_cfg w))), (m_vm_materialized (cfg_model (w_cfg w))).
  split; [exact Snap|]. split; [exact Smatch|]. split; [exact Kcur|]. split; reflexivity.
Qed.

Lemma fromKs : ltac2:(tb__ "0|1|
S11S11S64S2eS39Q40A1A1S5S16S3dS93S7S72VP0;Vwtop;S4eS47Z10000Z0A2M0R7R5R4A9S52R8R7A2S40S7S51Vcx;R5R7R6A4R4R8R3A5S1S3fS7VJD;S50Vcx;R6A2R9S4eG0A4R5R9R4A5VP0;R9A1A2F_;F_;F_;Fw;FS;Foff;Fmat;Fvm;Frho;FrhoB;").
Proof using Hent Hinp Hargc.
  intros rhoB rho vm mat off S w SnapB [Wlow Mem] [Smatch (Kr & Evm & Emat)].
  assert (P0rho : P0 rho).
  { destruct SnapB as (AiB & mdB & _ & _ & _ & P0B & _).
    refine (P0_agree sp brk mb draw inp Hent Hinp Hargc rhoB rho P0B _ _).
    - intros i Ilow. apply Wlow. lia.
    - intros a _. apply Mem. }
  assert (Snap : snapJ segs C_U P0 wtop tv0 (DG 65536 0) rho vm mat).
  { refine (snapJ_transport segs C_U P0 malloc_laws_U wtop tv0 (DG 65536 0) rhoB rho vm mat SnapB _ _ _ P0rho).
    - intros t [<-|[]]. cbn [fst snd eval]. rewrite Wlow by lia. split; reflexivity.
    - intros a. unfold Contract.rd_of. rewrite Mem. reflexivity.
    - intros a. unfold Contract.wok_of. rewrite Mem. reflexivity. }
  destruct (reJ segs C_U 31 P0 wtop P0_top P0_tp (KdR off) tv0 (DG 65536 0) rho vm mat _ _ Snap Evm Emat (DG_vm 65536 0) Kr) as (Ai & Gi & Dg).
  split; [|exact P0rho]. split; [exact Smatch|]. exists Ai. split; [exact Gi | exact Dg].
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
Proof using TLOOPK TLOOPG TXE0 Hargc Hent Hinp.
  intros r0 rho.
  eapply triple_conseq with (P := SPJ segs (JD (KdR 0) r0 tv0 (DG 65536 0)) T_ok rho); [|intros w Qw; exact Qw|].
  { intros w [Sm Jw]. split; [exact Sm|].
    apply (JD_monoK r0 Kd0 (KdR 0) tv0 (DG 65536 0) rho _ _ (fun t md Kt => proj1 (Kd0_KdR t md) Kt)).
    exact (JGD_mono segs C_U 31 Kd0 r0 P0 tv0 (DokS X0) (DG 65536 0) rho _ _ (fun A md Dk => proj2 (DG0 A md) (proj1 (DX0 A md) Dk)) Jw). }
  assert (Ntok : ss_next T_ok = 71%positive) by (vm_compute; reflexivity).
  eapply (run_trJ segs ok FUEL [loop_read] T_ok _ _ rho _ run_tok);
    [vm_compute; reflexivity | apply JD_okf, KdR_tcons | apply JD_stable; rewrite Ntok; [lia | apply tvb_0; lia] |].
  intros Lf rho1 [<-|[]] _. cbn [lf_state].
  eapply triple_conseq; [intros w Pw; exact (SPJ_xforms segs _ xs_k0 rho1 K0r K0 w xs_k0_ok Pw) | intros w Qw; exact Qw |].
  intros n Gd w Pw. destruct (toKs r0 rho1 w Pw) as (vm & mat & Snap & Kw). clear Pw. revert n Gd w Kw.
  change (triple segs ok (SP segs (KB 0 vm mat) K0 rho1) QF).
  assert (Nk0 : ss_next K0 = 71%positive) by (vm_compute; reflexivity).
  eapply (run_tr ok FUEL [] K0 _ _ rho1 _ run_k0); [vm_compute; reflexivity | apply KB_okf |].
  intros Lf rho2 [<-|[]] Agree2. cbn [lf_state]. rewrite Nk0 in Agree2.
  pose proof (BR_agree rho1 rho1 rho2 71 (BR_refl rho1) Agree2 ltac:(lia)) as B2.
  destruct E_rd0_shape as (_ & _ & _ & _ & _ & _ & _ & ImgObj & _).
  set (rho3 := rho_set_rl rho2 7 (img_bytes segs rho2 (mkObj (SLit 0) (SLit rs) (SLit (rs + 65536)) [] DImage))).
  eapply triple_conseq with (P := SP segs (KB 0 vm mat) E_rd0 rho3); [|intros w Qw; exact Qw|].
  { intros w Pw. exact (SPJ_img_to_list segs (liftK (KB 0 vm mat)) rho2 E_rd0i IRS 7 E_rd0 _ w E_rd0_eq ImgObj (fun tr md Kt => Kt) Pw). }
  eapply triple_seq; [apply triple1_triple; exact (kread_list rho3 vm mat) |].
  set (got := Z.of_nat (length (chunk 0 65536))).
  set (rest := skipn (length (chunk 0 65536)) (rl rho3 7)).
  set (rho4 := rho_set_rw (rho_set_rl rho3 5 (chunk 0 65536 ++ rest)) NX0 (len_word (chunk 0 65536))).
  pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)) as CL. fold got in CL.
  assert (B4 : BR rho1 rho4).
  { unfold rho4. apply BR_set_rw; [apply BR_set_rl; unfold rho3; apply BR_set_rl; exact B2 | change NX0 with 71%positive; lia]. }
  assert (V4 : bv_unsigned (eval rho4 (SVar 71)) = got).
  { cbn [eval]. unfold rho4. change 71%positive with NX0. rewrite rho_set_rw_at. unfold len_word. fold got. apply Z_to_bv_small. rewrite two64. lia. }
  assert (RL4 : rl rho4 5 = chunk 0 65536 ++ rest) by (unfold rho4; rewrite rho_set_rw_rl; reflexivity).
  assert (Carry : forall r r' k, (72 <= k)%positive -> agree_below k r r' -> BR rho1 r -> bv_unsigned (eval r (SVar 71)) = got ->
                    rl r 5 = chunk 0 65536 ++ rest -> BR rho1 r' /\ bv_unsigned (eval r' (SVar 71)) = got /\ rl r' 5 = chunk 0 65536 ++ rest).
  { intros r r' k Kk Ag Br Vr Lr. pose proof (BR_agree rho1 r r' k Br Ag ltac:(lia)) as Br'.
    destruct Ag as (Agw & Agl & _). refine (conj Br' (conj _ _)).
    - cbn [eval] in Vr |- *. rewrite <- Agw by lia. exact Vr.
    - rewrite <- Agl. exact Lr. }
  destruct (Z_lt_le_dec L 4) as [Lt4|Ge4].
  - destruct (Z.eq_dec L 0) as [L0|Lnz].
    + assert (GL : got = L) by lia.
      assert (Len0 : length (chunk 0 65536) = 0%nat) by (unfold got in GL; lia).
      eapply triple_conseq with (P := SP segs (KB got vm mat) R00 rho4); [|intros w Qw; exact Qw|].
      { intros w Pw. refine (SP_restate segs _ rho4 R0 R00 w _ [] swf_R00 diff_R00 _ (Forall_nil _) Pw).
        constructor; [|constructor]. cbn [fst snd eval]. unfold rho4. rewrite rho_set_rw_at, (len_word_zero _ Len0). reflexivity. }
      rewrite GL.
      eapply (run_tr ok FUEL CUTS R00 _ _ rho4 _ run_p00); [vm_compute; reflexivity | apply KB_okf |].
      intros Lf rho5 [<-|[]] Agree5. cbn [lf_state]. rewrite (ltac:(vm_compute; reflexivity) : ss_next R00 = 72%positive) in Agree5.
      destruct s_x00_vals as (X100 & X101 & _).
      apply (exit0_viaS X00 s_x00 rho1 vm mat rho5 Snap (BR_agree rho1 rho4 rho5 72 B4 Agree5 ltac:(lia)) ent_x00);
        [vm_compute; reflexivity | vm_compute; reflexivity
        | rewrite (ltac:(vm_compute; reflexivity) : ss_next X00 = 72%positive); lia
        | rewrite (ltac:(vm_compute; reflexivity) : ss_next X00 = 72%positive); apply tvb_0; lia
        | unfold UV; cbn [rho_sub rw]; rewrite X100; rewrite (Ulit rho5 0) by lia; lia
        | unfold UV; cbn [rho_sub rw]; rewrite X101; apply Ulit; lia
        | lia].
    + assert (GL : got = L) by lia.
      eapply triple_conseq with (P := SP segs (KB got vm mat) R0t rho4); [|intros w Qw; exact Qw|].
      { intros w Pw. rewrite <- R0t_eq. apply SP_obj_forget. unfold SP in *. apply SPJ_add_facts; [exact Pw | | vm_compute; reflexivity].
        assert (Fv : F_0t = [SPNot (SPBranch BC_EQ (SVar 71) (SLit 0)); SPUlt (SVar 71) (SLit 4)]) by (vm_compute; reflexivity). rewrite Fv.
        constructor; [|constructor; [|constructor]].
        - apply holds_nbeq. rewrite V4, (Ulit rho4 0) by lia. lia.
        - apply holds_ult. rewrite V4, (Ulit rho4 4) by lia. lia. }
      eapply (run_tr ok FUEL CUTS R0t _ _ rho4 _ run_p0t); [vm_compute; reflexivity | apply KB_okf |].
      intros Lf rho5 [<-|[]] Agree5. cbn [lf_state]. rewrite (ltac:(vm_compute; reflexivity) : ss_next R0t = 72%positive) in Agree5.
      destruct (Carry rho4 rho5 72%positive ltac:(lia) Agree5 B4 V4 RL4) as (B5 & V5 & RL5).
      eapply triple_conseq; [intros w Pw; exact (SP_xforms segs _ xs_0t rho5 C_0t Cx_0t w xs_0t_ok Pw) | intros w Qw; exact Qw |].
      eapply triple_conseq with (P := SP segs (KB got vm mat) Cr_0t rho5); [|intros w Qw; exact Qw|].
      { intros w Pw. rewrite <- Cr_0t_eq. destruct Cr_0t_pre as (PreObj & _ & _). unfold SP in *.
        assert (Src : O_src0t = mkObj (SLit rs) (SLit 0) (SVar 71) [] DUnknown) by (vm_compute; reflexivity).
        refine (SPJ_reshape segs _ rho5 Cx_0t (IRS + 1) _ O_src0t w PreObj _ _ eq_refl _ _ Pw).
        - rewrite Src. reflexivity.
        - rewrite Src. reflexivity.
        - vm_compute. reflexivity.
        - intros _. rewrite Src. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. pose proof rs_range as RsR.
          rewrite (Ulit rho5 rs), (Ulit rho5 0) by lia. rewrite !soff_lit_small by lia.
          rewrite (soff_small rho5 (SVar 71) got V5) by lia.
          rewrite (soff_small rho5 _ (got + rs) (Uadd rho5 (SVar NX0) (SLit rs) got rs V5 (Ulit rho5 rs ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia))) by lia.
          lia. }
      refine (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) Cr_0t Cr_0t PreG [] s_c0t R_c0t Posts_memcpy QF rho5 eq_refl efr_c0t chk_c0t fb_c0t (fun rho' _ => memcpy_sum ok _ rho' (KB_okf got vm mat)) (fun _ _ => I) _).
      intros Lf rho6 InPost Agree6 Facts6. rewrite (ltac:(vm_compute; reflexivity) : ss_next Cr_0t = 72%positive) in Agree6.
      destruct (Carry rho5 rho6 72%positive ltac:(lia) Agree6 B5 V5 RL5) as (B6 & V6 & RL6).
      assert (L13 : 1 <= L <= 3) by lia.
      assert (UVL : UV rho6 NX0 = L) by (unfold UV; rewrite <- GL; exact V6).
      unfold Posts_memcpy, MuslMemcpy.Posts_memcpy in InPost. destruct InPost as [<-|[<-|[]]]; cbn [lf_state].
      -- eapply triple_conseq with (P := SP segs (KB got vm mat) T0ta rho6); [|intros w Qw; exact Qw|].
         { intros w Pw. rewrite <- T0ta_eq. unfold SP in *. apply SPJ_add_facts; [exact Pw | exact Facts6 | vm_compute; reflexivity]. }
         rewrite GL.
         refine (tiny_tailS T0ta Tr0ta Tm0ta H0ta E1ta P1ta X1ta s_x1ta xs_0ta T0ta_objs _ Tr0ta_eq xs_0ta_ok run_t0ta run_h0ta E1ta_shape cert_rd1ta diff_P1ta swf_P1ta run_p1ta ent_x1ta s_x1ta_vals E1ta_next _ _ _ _ rho1 vm mat rho6 Snap B6 L13 UVL).
         all: vm_compute; repeat split.
      -- eapply triple_conseq with (P := SP segs (KB got vm mat) T0tb rho6); [|intros w Qw; exact Qw|].
         { intros w Pw. rewrite <- T0tb_eq. unfold SP in *. apply SPJ_add_facts; [exact Pw | exact Facts6 | vm_compute; reflexivity]. }
         rewrite GL.
         refine (tiny_tailS T0tb Tr0tb Tm0tb H0tb E1tb P1tb X1tb s_x1tb xs_0tb T0tb_objs _ Tr0tb_eq xs_0tb_ok run_t0tb run_h0tb E1tb_shape cert_rd1tb diff_P1tb swf_P1tb run_p1tb ent_x1tb s_x1tb_vals E1tb_next _ _ _ _ rho1 vm mat rho6 Snap B6 L13 UVL).
         all: vm_compute; repeat split.
  - destruct (Z_lt_le_dec L 65536) as [Ltg|Geg].
    + destruct (Z_lt_le_dec (L - 3) 32) as [Sm|Bg].
      * assert (GL : got = L) by lia.
        eapply triple_conseq with (P := SP segs (KB got vm mat) R0s rho4); [|intros w Qw; exact Qw|].
        { intros w Pw. rewrite <- R0s_eq. unfold SP in *. apply SPJ_add_facts; [exact Pw | | vm_compute; reflexivity].
          assert (Fv : F_0s = [SPUle (SLit 4) (SVar 71); SPBranch BC_LTU (SAlu ALU_ADD (SVar 71) (SLit (-3))) (SLit 32); SPUlt (SVar 71) (SLit 65536)]) by (vm_compute; reflexivity). rewrite Fv.
          assert (M4 : bv_unsigned (eval rho4 (SAlu ALU_ADD (SVar 71) (SLit (-3)))) = got - 3) by (exact (Usubk rho4 (SVar 71) got 3 V4 ltac:(lia) ltac:(lia))).
          constructor; [|constructor; [|constructor; [|constructor]]].
          - apply holds_ule. rewrite V4, (Ulit rho4 4) by lia. lia.
          - apply holds_bltu. rewrite M4, (Ulit rho4 32) by lia. lia.
          - apply holds_ult. rewrite V4, (Ulit rho4 65536) by lia. lia. }
        eapply (run_tr ok FUEL CUTS R0s _ _ rho4 _ run_p0s); [vm_compute; reflexivity | apply KB_okf |].
        intros Lf rho5 [<-|[]] Agree5. cbn [lf_state]. rewrite (ltac:(vm_compute; reflexivity) : ss_next R0s = 72%positive) in Agree5.
        destruct (Carry rho4 rho5 72%positive ltac:(lia) Agree5 B4 V4 RL4) as (B5 & V5 & RL5).
        refine (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) C_0s Cx_0s PreRs [XSplit 1 (SVar NX0)] s_c0s R_c0s Posts_rsS QF rho5 xs_0s_ok efr_c0s chk_c0s _ (fun rho' _ => memcpy_rsS_sum ok _ rho' (KB_okf got vm mat)) (fun _ _ => I) _); [vm_compute; reflexivity |].
        intros Lf rho6 InPost Agree6 Facts6. rewrite (ltac:(vm_compute; reflexivity) : ss_next Cx_0s = 72%positive) in Agree6.
        destruct (Carry rho5 rho6 72%positive ltac:(lia) Agree6 B5 V5 RL5) as (B6 & V6 & RL6).
        rewrite <- (xforms_facts _ _ _ xs_0s_ok) in Facts6.
        rewrite Posts_rsS_eq in InPost. destruct InPost as [<-|[<-|[<-|[]]]]; cbn [lf_state].
        -- refine (hdr_postS Cx_0s T0sA Tp0sA Tm0sA H0sA _ ES0sA xs_0sA T0sA_eq _ Tp0sA_eq ES0sA_eq xs_0sA_ok run_t0sA T0sA_nexts _ _ rho1 vm mat rho6 got rest B6 Facts6 RL6 _ eq_refl _).
          ** vm_compute. reflexivity.
          ** rewrite (ltac:(vm_compute; reflexivity) : ss_next T0sA = 112%positive). lia.
          ** intros r Len. destruct es_t as [EsA _]. rewrite EsA. apply pack4_hdr; [exact Len | apply (byte_of_Eb r 3); try unfold LS; lia].
          ** lia.
          **
          intros rho7 B7 Same7 Hdr7. rewrite GL.
          apply (loopK_viaS H0sA s_h0sA rho1 vm mat rho7 L Snap B7 ent_h0sA); [vm_compute; reflexivity | vm_compute; reflexivity | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0sA = 113%positive); lia | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0sA = 113%positive); apply tvb_0; lia |].
          destruct s_h0sA_vals as (Q100 & Q101 & _ & Q103). unfold INVK, UV. cbn [rho_sub rw]. rewrite Q100, Q101, Q103.
          refine (conj _ (conj _ (conj Hdr7 (conj _ (conj (Z.le_refl L) (conj (or_intror eq_refl) CAP_init)))))).
          ++ cbn [eval]. rewrite Same7 by (vm_compute; reflexivity). rewrite <- GL. exact V6.
          ++ apply Ulit. lia.
          ++ lia.
        -- refine (hdr_postS Cx_0s T0sB Tp0sB Tm0sB H0sB _ ES0sB xs_0sB T0sB_eq _ Tp0sB_eq ES0sB_eq xs_0sB_ok run_t0sB T0sB_nexts _ _ rho1 vm mat rho6 got rest B6 Facts6 RL6 _ eq_refl _).
          ** vm_compute. reflexivity.
          ** rewrite (ltac:(vm_compute; reflexivity) : ss_next T0sB = 112%positive). lia.
          ** intros r Len. destruct es_t as [EsA EsB]. rewrite EsB, EsA. apply pack4_hdr; [exact Len | apply (byte_of_Eb r 3); try unfold LS; lia].
          ** lia.
          **
          intros rho7 B7 Same7 Hdr7. rewrite GL.
          apply (loopK_viaS H0sB s_h0sB rho1 vm mat rho7 L Snap B7 ent_h0sB); [vm_compute; reflexivity | vm_compute; reflexivity | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0sB = 113%positive); lia | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0sB = 113%positive); apply tvb_0; lia |].
          destruct s_h0sB_vals as (Q100 & Q101 & _ & Q103). unfold INVK, UV. cbn [rho_sub rw]. rewrite Q100, Q101, Q103.
          refine (conj _ (conj _ (conj Hdr7 (conj _ (conj (Z.le_refl L) (conj (or_intror eq_refl) CAP_init)))))).
          ++ cbn [eval]. rewrite Same7 by (vm_compute; reflexivity). rewrite <- GL. exact V6.
          ++ apply Ulit. lia.
          ++ lia.
        -- rewrite T0sZ_eq. intros n Gd w [Smz _]. exfalso.
          pose proof (smatch_facts segs rho6 T0sZ _ Smz) as Fz.
          pose proof T0sZ_fz as Zall.
          assert (FzV : F_zs = [SPNot (SPBranch BC_NE (SAlu ALU_AND (SAlu ALU_ADD (SVar 71) (SLit (-3))) (SLit 1)) (SLit 0)); SPNot (SPBranch BC_NE (SAlu ALU_AND (SAlu ALU_ADD (SVar 71) (SLit (-3))) (SLit 2)) (SLit 0)); SPNot (SPBranch BC_NE (SAlu ALU_AND (SAlu ALU_ADD (SVar 71) (SLit (-3))) (SLit 4)) (SLit 0)); SPNot (SPBranch BC_NE (SAlu ALU_AND (SAlu ALU_ADD (SVar 71) (SLit (-3))) (SLit 8)) (SLit 0)); SPNot (SPBranch BC_GEU (SAlu ALU_ADD (SVar 71) (SLit (-3))) (SLit 16))]) by (vm_compute; reflexivity).
          rewrite FzV in Zall. cbn [forallb] in Zall.
          apply andb_prop in Zall as [Z1 Zall]. apply andb_prop in Zall as [Z2 Zall]. apply andb_prop in Zall as [Z3 Zall].
          apply andb_prop in Zall as [Z4 Zall]. apply andb_prop in Zall as [Z5 _].
          apply (holds_of_existsb rho6 _ _ Fz) in Z1, Z2, Z3, Z4, Z5.
          assert (Mid : bv_unsigned (eval rho6 (SAlu ALU_ADD (SVar 71) (SLit (-3)))) = got - 3) by (exact (Usubk rho6 (SVar 71) got 3 V6 ltac:(lia) ltac:(lia))).
          assert (Bit : forall k, 0 <= k < 2 ^ 64 -> holds rho6 (SPNot (SPBranch BC_NE (SAlu ALU_AND (SAlu ALU_ADD (SVar 71) (SLit (-3))) (SLit k)) (SLit 0))) -> Z.land (got - 3) k = 0).
          { intros k Kr BitFact. apply holds_nbne in BitFact. rewrite (Ulit rho6 0) in BitFact by lia.
            change (bv_unsigned (alu64 ALU_AND (eval rho6 (SAlu ALU_ADD (SVar 71) (SLit (-3)))) (eval rho6 (SLit k))) = 0) in BitFact.
            rewrite and_val, Mid, (Ulit rho6 k Kr) in BitFact. exact BitFact. }
          apply holds_nbgeu in Z5. rewrite Mid, (Ulit rho6 16) in Z5 by lia.
          pose proof (rsZ_absurd_Z (got - 3) ltac:(lia) (Bit 1 ltac:(lia) Z1) (Bit 2 ltac:(lia) Z2) (Bit 4 ltac:(lia) Z3) (Bit 8 ltac:(lia) Z4)) as Zero.
          lia.
      * assert (GL : got = L) by lia.
        eapply triple_conseq with (P := SP segs (KB got vm mat) R0m rho4); [|intros w Qw; exact Qw|].
        { intros w Pw. rewrite <- R0m_eq. unfold SP in *. apply SPJ_add_facts; [exact Pw | | vm_compute; reflexivity].
          assert (Fv : F_0m = [SPUle (SLit 4) (SVar 71); SPNot (SPBranch BC_LTU (SAlu ALU_ADD (SVar 71) (SLit (-3))) (SLit 32)); SPUlt (SVar 71) (SLit 65536)]) by (vm_compute; reflexivity). rewrite Fv.
          assert (M4 : bv_unsigned (eval rho4 (SAlu ALU_ADD (SVar 71) (SLit (-3)))) = got - 3) by (exact (Usubk rho4 (SVar 71) got 3 V4 ltac:(lia) ltac:(lia))).
          constructor; [|constructor; [|constructor; [|constructor]]].
          - apply holds_ule. rewrite V4, (Ulit rho4 4) by lia. lia.
          - apply holds_nbltu. rewrite M4, (Ulit rho4 32) by lia. lia.
          - apply holds_ult. rewrite V4, (Ulit rho4 65536) by lia. lia. }
        eapply (run_tr ok FUEL CUTS R0m _ _ rho4 _ run_p0m); [vm_compute; reflexivity | apply KB_okf |].
        intros Lf rho5 [<-|[]] Agree5. cbn [lf_state]. rewrite (ltac:(vm_compute; reflexivity) : ss_next R0m = 72%positive) in Agree5.
        destruct (Carry rho4 rho5 72%positive ltac:(lia) Agree5 B4 V4 RL4) as (B5 & V5 & RL5).
        refine (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) C_0m Cx_0m PreRm [XSplit 1 (SVar NX0)] s_c0m R_c0m Posts_rsB QF rho5 xs_0m_ok efr_c0m chk_c0m _ (fun rho' _ => memcpy_rsB_sum ok _ rho' (KB_okf got vm mat)) (fun _ _ => I) _); [vm_compute; reflexivity |].
        intros Lf rho6 InPost Agree6 Facts6. rewrite (ltac:(vm_compute; reflexivity) : ss_next Cx_0m = 72%positive) in Agree6.
        destruct (Carry rho5 rho6 72%positive ltac:(lia) Agree6 B5 V5 RL5) as (B6 & V6 & RL6).
        rewrite <- (xforms_facts _ _ _ xs_0m_ok) in Facts6.
        rewrite Posts_rsB_eq in InPost. destruct InPost as [<-|[<-|[]]]; cbn [lf_state].
        -- refine (hdr_postS Cx_0m T0mA Tp0mA Tm0mA H0mA _ ES0mA xs_0mA T0mA_eq _ Tp0mA_eq ES0mA_eq xs_0mA_ok run_t0mA T0mA_nexts _ _ rho1 vm mat rho6 got rest B6 Facts6 RL6 _ eq_refl _).
          ** vm_compute. reflexivity.
          ** rewrite (ltac:(vm_compute; reflexivity) : ss_next T0mA = 112%positive). lia.
          ** intros r Len. destruct es_c as (EmA & EmB & EgA & EgB). rewrite EmA. apply pack4_hdr; [exact Len | apply byte_of_E3c; exact Len].
          ** lia.
          **
          intros rho7 B7 Same7 Hdr7. rewrite GL.
          apply (loopK_viaS H0mA s_h0mA rho1 vm mat rho7 L Snap B7 ent_h0mA); [vm_compute; reflexivity | vm_compute; reflexivity | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0mA = 113%positive); lia | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0mA = 113%positive); apply tvb_0; lia |].
          destruct s_h0mA_vals as (Q100 & Q101 & _ & Q103). unfold INVK, UV. cbn [rho_sub rw]. rewrite Q100, Q101, Q103.
          refine (conj _ (conj _ (conj Hdr7 (conj _ (conj (Z.le_refl L) (conj (or_intror eq_refl) CAP_init)))))).
          ++ cbn [eval]. rewrite Same7 by (vm_compute; reflexivity). rewrite <- GL. exact V6.
          ++ apply Ulit. lia.
          ++ lia.
        -- refine (hdr_postS Cx_0m T0mB Tp0mB Tm0mB H0mB _ ES0mB xs_0mB T0mB_eq _ Tp0mB_eq ES0mB_eq xs_0mB_ok run_t0mB T0mB_nexts _ _ rho1 vm mat rho6 got rest B6 Facts6 RL6 _ eq_refl _).
          ** vm_compute. reflexivity.
          ** rewrite (ltac:(vm_compute; reflexivity) : ss_next T0mB = 112%positive). lia.
          ** intros r Len. destruct es_c as (EmA & EmB & EgA & EgB). rewrite EmB, EmA. apply pack4_hdr; [exact Len | apply byte_of_E3c; exact Len].
          ** lia.
          **
          intros rho7 B7 Same7 Hdr7. rewrite GL.
          apply (loopK_viaS H0mB s_h0mB rho1 vm mat rho7 L Snap B7 ent_h0mB); [vm_compute; reflexivity | vm_compute; reflexivity | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0mB = 113%positive); lia | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0mB = 113%positive); apply tvb_0; lia |].
          destruct s_h0mB_vals as (Q100 & Q101 & _ & Q103). unfold INVK, UV. cbn [rho_sub rw]. rewrite Q100, Q101, Q103.
          refine (conj _ (conj _ (conj Hdr7 (conj _ (conj (Z.le_refl L) (conj (or_intror eq_refl) CAP_init)))))).
          ++ cbn [eval]. rewrite Same7 by (vm_compute; reflexivity). rewrite <- GL. exact V6.
          ++ apply Ulit. lia.
          ++ lia.
    + assert (G64 : got = 65536) by lia.
      eapply triple_conseq with (P := SP segs (KB got vm mat) R0g rho4); [|intros w Qw; exact Qw|].
      { intros w Pw. refine (SP_restate segs _ rho4 R0 R0g w _ [] swf_R0g diff_R0g _ (Forall_nil _) Pw).
        constructor; [|constructor]. cbn [fst snd eval]. unfold rho4. rewrite rho_set_rw_at. unfold len_word. f_equal. fold got. lia. }
      eapply (run_tr ok FUEL CUTS R0g _ _ rho4 _ run_p0g); [vm_compute; reflexivity | apply KB_okf |].
      intros Lf rho5 [<-|[]] Agree5. cbn [lf_state]. rewrite (ltac:(vm_compute; reflexivity) : ss_next R0g = 72%positive) in Agree5.
      destruct (Carry rho4 rho5 72%positive ltac:(lia) Agree5 B4 V4 RL4) as (B5 & V5 & RL5).
      refine (call_path segs (fun _ => True) ok (KB got vm mat) (KB got vm mat) C_0g Cx_0g PreRg [XSplit 1 (SLit 65536)] s_c0g R_c0g Posts_rsB QF rho5 xs_0g_ok efr_c0g chk_c0g _ (fun rho' _ => memcpy_rsB_sum ok _ rho' (KB_okf got vm mat)) (fun _ _ => I) _); [vm_compute; reflexivity |].
      intros Lf rho6 InPost Agree6 Facts6. rewrite (ltac:(vm_compute; reflexivity) : ss_next Cx_0g = 72%positive) in Agree6.
      destruct (Carry rho5 rho6 72%positive ltac:(lia) Agree6 B5 V5 RL5) as (B6 & V6 & RL6).
      rewrite <- (xforms_facts _ _ _ xs_0g_ok) in Facts6.
      rewrite Posts_rsB_eq in InPost. destruct InPost as [<-|[<-|[]]]; cbn [lf_state].
      -- refine (hdr_postS Cx_0g T0gA Tp0gA Tm0gA H0gA _ ES0gA xs_0gA T0gA_eq _ Tp0gA_eq ES0gA_eq xs_0gA_ok run_t0gA T0gA_nexts _ _ rho1 vm mat rho6 got rest B6 Facts6 RL6 _ eq_refl _).
        ** vm_compute. reflexivity.
        ** rewrite (ltac:(vm_compute; reflexivity) : ss_next T0gA = 112%positive). lia.
        ** intros r Len. destruct es_c as (EmA & EmB & EgA & EgB). rewrite EgA, EmA. apply pack4_hdr; [exact Len | apply byte_of_E3c; exact Len].
        ** lia.
        **
        intros rho7 B7 Same7 Hdr7. rewrite G64.
        apply (loopG_viaS H0gA s_h0gA rho1 vm mat rho7 Snap B7 ent_h0gA); [vm_compute; reflexivity | vm_compute; reflexivity | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0gA = 113%positive); lia | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0gA = 113%positive); apply tvb_0; lia |].
        destruct s_h0gA_vals as (Q101 & _ & Q103). unfold INVG, UV. cbn [rho_sub rw]. rewrite Q101, Q103.
        refine (conj _ (conj Hdr7 (conj Geg CAP_init))).
        apply Ulit. lia.
      -- refine (hdr_postS Cx_0g T0gB Tp0gB Tm0gB H0gB _ ES0gB xs_0gB T0gB_eq _ Tp0gB_eq ES0gB_eq xs_0gB_ok run_t0gB T0gB_nexts _ _ rho1 vm mat rho6 got rest B6 Facts6 RL6 _ eq_refl _).
        ** vm_compute. reflexivity.
        ** rewrite (ltac:(vm_compute; reflexivity) : ss_next T0gB = 112%positive). lia.
        ** intros r Len. destruct es_c as (EmA & EmB & EgA & EgB). rewrite EgB, EmA. apply pack4_hdr; [exact Len | apply byte_of_E3c; exact Len].
        ** lia.
        **
        intros rho7 B7 Same7 Hdr7. rewrite G64.
        apply (loopG_viaS H0gB s_h0gB rho1 vm mat rho7 Snap B7 ent_h0gB); [vm_compute; reflexivity | vm_compute; reflexivity | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0gB = 113%positive); lia | rewrite (ltac:(vm_compute; reflexivity) : ss_next H0gB = 113%positive); apply tvb_0; lia |].
        destruct s_h0gB_vals as (Q101 & _ & Q103). unfold INVG, UV. cbn [rho_sub rw]. rewrite Q101, Q103.
        refine (conj _ (conj Hdr7 (conj Geg CAP_init))).
        apply Ulit. lia.
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
