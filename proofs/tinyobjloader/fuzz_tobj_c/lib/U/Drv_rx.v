(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "sub"; "mul"; "of_nat"; "pow"; "lt"; "opp"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_next"; "SVar"; "sprop"; "SLit"; "sstate"; "ss_facts"; "SAlu"; "reg_sv"; "DUnknown"; "mkObj"; "rw"; "sobj"; "ss_lenient"; "cell"; "SPUle"; "obj_wf"; "sprop_below"; "ss_objs"; "eval"; "rl"; "SPBranch"; "ss_pc"; "SPNot"; "SPUlt"; "holds"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "cons"; "nil"; "Some"; "option"; "length"; "false"; "prod"; "pair"; "None"; "app"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsCut"; "sym_run"; "RsEcall"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rx.RX.EX"; "DG"; "CAPG"; "DX"; "XOf"; "kOf"; "DM"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r"; "UV"; "tv0"; "tvK"; "KdR"; "KB"; "BR"; "HDR"; "INVG"; "INVK"; "INVX"; "chunk"; "tvG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx"; "f_F"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "instr"; "ALU_SUB"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "sv_subst"; "wsub_id_below"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "Model"; "FdEntry"; "m_vm_materialized"; "m_vmmaps"; "with_fds"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "rs"; "read_ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyRS"; "Eb"; "E3c"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "tv_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "NX0"; "CUTS"; "FUEL"; "K"; "KG"; "ES0mA"; "XE0"; "XEH"; "Cx_0g"; "Cx_0m"; "Cx_0s"; "ES0sA"; "IRS"; "K0"; "R0g"; "X_ref"; "ES0gA"; "ES0gB"; "ES0mB"; "ES0sB"; "O_rsU"; "O_src0t"; "P_E_rdA"; "R0m"; "R0s"; "T0gA"; "T0gB"; "T0mA"; "T0mB"; "T0sA"; "T0sB"; "T_gok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "snapJ"; "CAP"; "ALIGNED"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "tl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rx.RX.EX.LoopX"; "LoopIHx"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "init_cost"; "malloc_cost"; "DRV_OPS"; "drvN"; "vm_room"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "succ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m"; "Dok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states"; "T_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rx.RX"; "Dvm"; "@Corelib.Init.Peano"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue2"; "obj_forget"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.HdrPack"; "pack4_at"; "pack4_vals"; "pack4_word"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead"; "S_after_var"; "hdr_val"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List Bool.Bool PArith.PArith micromega.Lia.
From Stdlib Require Import Strings.Ascii Strings.String.
From stdpp Require Import bitvector.bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLayout MallocIface MallocLaws Contract ContractDrv Pristine ClientLaws Glue.
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

Section RX.
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

Let P0 := Drv_m__G1.Drv_m.P0 sp draw inp. Let P0_tp := Drv_m__G1.Drv_m.P0_tp sp draw inp.
Let P0_top := Drv_m__G1.Drv_m.P0_top sp draw inp.
Let wtop : word := wtop sp.
Let JD := Drv_m__G1.Drv_m.JD sp draw inp.
Let Kd0 := Drv_m__G1.Drv_m.Kd0 inp md0.

Local Notation KdR := (KdR cx).
Local Notation Kd0_KdR := (Kd0_KdR cx).
Local Notation KdR_vmi := (KdR_vmi cx).
Local Notation JD_stable := (JD_stable cx).
Local Notation KB := (KB cx).
Local Notation chunk := (chunk cx).
Local Notation chunk_length := (chunk_length cx).
Local Notation ejread_rs := (ejread_rs cx).
Local Notation ekread_rs := (ekread_rs cx).
Local Notation ekread_list := (ekread_list cx).
Local Notation HDRW := (HDRW cx).
Local Notation HDR := (HDR cx).
Local Notation INVK := (INVK cx).
Local Notation INVG := (INVG cx).
Local Notation INVX := (INVX cx).
Local Notation INVK_agree := (INVK_agree cx).
Local Notation INVG_agree := (INVG_agree cx).
Local Notation tvK_below := (tvK_below cx).
Local Notation tvb_0 := (tvb_0 cx).
Local Notation JD_geom := (JD_geom cx).
Local Notation JD_monoK := (JD_monoK cx).
Local Notation ereenter := (ereenter cx).
Local Notation epure_callD := (epure_callD cx).
Local Notation HDR_sext := (HDR_sext cx).
Local Notation hdr_chunk0 := (hdr_chunk0 cx).
Local Notation T_ok_of_JGi := (T_ok_of_JGi cx).

Definition Dvm (D : MA -> Model -> Prop) : Prop := ltac2:(tb__ "0|0|
S70S64S64S0S63S67R1A1S67R2A1A3S0S2eS39Q40A1A1S66R2A1S66R3A1A3VD;R5R4A2VD;R6R4A2F_;F_;F_;Fm';Fm;FA;").

Section EX.

Variable X0 : Z.
Hypothesis HX0 : ltac2:(tb__ "0|0|
S8S9S9bSdZ2Z1dA2A2VX0;A2").
Hypothesis MBX : malloc_big_ex_U true.
Hypothesis FDX : free_drv_ex_U.

Variable Q : world -> Prop.

Definition DX (k X : Z) : MA -> Model -> Prop := ltac2:(tb__ "0|0|
S70S64S1S9eS71Vk;R2A3S9fR1VX;A2A2Lmd;LA;").

Definition kOf (g : Z) : Z := DRV_OPS - 2 * g.
Definition XOf (cap g : Z) : Z := ltac2:(tb__ "0|1|
SaSaSaVX0;S9bA2SaSbZ2M0Vcap;A2SdG0Z11A2A2A2SbVg;SdG0Z15A2A2A2").
Definition DG (cap g : Z) : MA -> Model -> Prop := ltac2:(tb__ "0|0|
S48S4aVg;A1S49Vcap;Vg;A2A2").

Definition CAPG (cap g : Z) : Prop := ltac2:(tb__ "0|0|
S0S5Vcap;SbZ10000SdZ2Vg;A2A2A3").

Lemma DX_fds : ltac2:(tb__ "0|0|
S5S5S70S64S2eS35S39Q40A1S65A2A1S48R5R4R3R2A4S48R6R5R4S68R2R3A2A4F_;Ff;Fmd;FA;FX;Fk;").
Proof using . clear. intros k X A md f [Hd Hv]. split; [exact Hd | exact (vm_room_frame md (with_fds f md) X eq_refl eq_refl Hv)]. Qed.
Lemma DG_fds : ltac2:(tb__ "0|0|
S5S5S70S64S2eS35S39Q40A1S65A2A1S46R5R4R3R2A4S46R6R5R4S68R2R3A2A4F_;Ff;Fmd;FA;Fg;Fcap;").
Proof using . intros cap g. exact (DX_fds (kOf g) (XOf cap g)). Qed.
Lemma DX_vm : ltac2:(tb__ "0|0|
S5S5Sa7S48R2R1A2A1FX;Fk;").
Proof using . clear. intros k X A m m' Hv Hm [Hd Hr]. split; [exact Hd | exact (vm_room_frame m m' X Hv Hm Hr)]. Qed.
Lemma DG_vm : ltac2:(tb__ "0|0|
S5S5Sa7S46R2R1A2A1Fg;Fcap;").
Proof using . intros cap g. exact (DX_vm (kOf g) (XOf cap g)). Qed.
Lemma DX0 : ltac2:(tb__ "0|0|
S70S64S3Sa5VX0;R2R1A3S48S9dSaVX0;S9bA2R2R1A4A2Fmd;FA;").
Proof using . clear. intros A md. split; intros H; exact H. Qed.
Lemma DG0 : ltac2:(tb__ "0|0|
S70S64S3S46Z10000Z0R2R1A4S48S9dSaVX0;S9bA2R2R1A4A2Fmd;FA;").
Proof using . clear. intros A md. unfold DG, kOf, XOf. replace (DRV_OPS - 2 * 0) with DRV_OPS by lia. replace (X0 - init_cost - (2 * 65536 - 2 ^ 17) - 0 * 2 ^ 21) with (X0 - init_cost) by lia. split; intros H; exact H. Qed.
Lemma pow_g_bound : ltac2:(tb__ "0|1|
S5S8Z0R1A2S8SbZ10000SdZ2M0R2A2A2SdG0Z1aA2A2S8R3ZaA2F_;F_;Fg;").
Proof using .
  clear. intros g Hg H. destruct (Z_lt_le_dec 10 g) as [Hl|Hl]; [|exact Hl]. exfalso.
  assert (2 ^ 11 <= 2 ^ g) by (apply Z.pow_le_mono_r; lia). change (2 ^ 26) with (65536 * 2 ^ 10) in H.
  assert (2 ^ 10 < 2 ^ 11) by (apply Z.pow_lt_mono_r; lia). nia.
Qed.

Lemma g_lt_bound : ltac2:(tb__ "0|1|
S5S5S8Z0R1A2S47R3R2A2SeR4SdZ2M0Z1aA2A2S1S8R4Z9A2S8R5SdG0Z19A2A2A2F_;F_;F_;Fg;Fcap;").
Proof using .
  clear. intros cap g Hg -> Hlt. destruct (Z_lt_le_dec 9 g) as [Hl|Hl].
  - exfalso. assert (2 ^ 10 <= 2 ^ g) by (apply Z.pow_le_mono_r; lia). change (2 ^ 26) with (65536 * 2 ^ 10) in Hlt. nia.
  - split; [exact Hl|]. assert (2 ^ g <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 25) with (65536 * 2 ^ 9). nia.
Qed.
Lemma init_cost_val : init_cost = 2 ^ 25. Proof using . reflexivity. Qed.
Lemma DRV_OPS_val : DRV_OPS = 40. Proof using . reflexivity. Qed.
Lemma malloc_cost_val : ltac2:(tb__ "0|0|
S5S0S5S9cR1A1S9R1SdZ2Z15A2A2A3Fn;"). Proof using . reflexivity. Qed.
Lemma MMAP_THRESHOLD_val : MMAP_THRESHOLD = 131052. Proof using . reflexivity. Qed.

Definition DM (cap g : Z) : MA -> Model -> Prop := ltac2:(tb__ "0|0|
S48SaS4aVg;A1Z1A2SaS49Vcap;Vg;A2S9cSbZ2Vcap;A2A1A2A2").
Lemma DG_next : ltac2:(tb__ "0|2|
S5S5S70S64S48SaSaS4aR3A1Z1M0A2G0A2SaS49R4R3A2S9cSbZ2M1R4A2A1A2R2R1A4S46SbG1R5A2S9R4G0A2R3R2A4F_;Fmd;FA;Fg;Fcap;").
Proof using .
  clear. intros cap g A md [Hd Hv]. unfold DG, DX, kOf, XOf in *. rewrite malloc_cost_val in Hv.
  split; [replace (DRV_OPS - 2 * (g + 1)) with (DRV_OPS - 2 * g - 1 - 1) by lia; exact Hd|].
  eapply vm_room_mono; [|exact Hv]. pose proof (vm_room_nonneg _ _ Hv). lia.
Qed.

Section LoopX.
Variable r0 : valuation.
Let JX (off cap g : Z) : jpred := ltac2:(tb__ "0|0|
VJD;S4fVcx;Voff;A2Vr0;S4eS46Vcap;Vg;A2A4").

Hypothesis EXEH : ltac2:(tb__ "0|0|
S11S5S5S55Vcx;R2R3A3S1S8Z0R2A2S8R2ZaA2A2S47R4R3A2S3cS7S3eS7VJX;ScS33S39Q8A1S58Vcx;A1A2A1R5R4A3S79R6A4VQ;A3F_;F_;F_;Fg;Fcap;Frho;").
Hypothesis EXref : ltac2:(tb__ "0|1|
S11S5S0S5S4cR2P65A2SdZ2Z1aA2M0A3S8G0ScS33S39Q8A1S58Vcx;A1A2A1A2S52Vcx;S1cR4P67A2A2S1S8Z0R4A2S8R4ZaA2A2S3cS7S3eS7VJX;G0G0R5A3S81R6A4VQ;A3F_;F_;F_;F_;Fg;Frho;").

Definition LoopIHx (m : Z) : Prop := ltac2:(tb__ "0|3|
S1S11S5S5S5SeSbZ2M0SaScS33S39Q8A1S58Vcx;A1A2A1M1R3A2A2Vm;A2S54Vcx;R4R3R5A4S1S8Z0R3A2S47R4R3A2A2M2S3cS7S3eS7VJX;R6R5R4A3S75R7A4VQ;A3F_;F_;F_;Fg;Fcap;Flen;Frho;S11S5S5SeS9SbG0SaG1R2A2A2Z1A2Vm;A2S53Vcx;R3R4A3G2S3cS7S3eS7VJX;R5R5R4A3S76R6A4VQ;A3F_;F_;F_;Fg;Fcap;Frho;A2").

Lemma eexit_via : ltac2:(tb__ "0|e|
S16S16S16S16S62S2eS35S10S10A2M0A1M1S11S6S5S5S0S2cS2bR9A1S2dA3S0S32S35G1S2eS14A1M2A2M3A1Sa3RbRaA2S31G3S36G1G2S2fG0S36S10S10S13R4A1S15Z0M4A1A4S30G0A1A3S30S14A1M5A4A2A3S0S32S2eS40A1M6A1S43S7S74S73RbS2dA5S31G6S2fS40S41RaS42A2S30S40A1A3A2A3S0S2cS1eRcA1S34A3S0S16S99S2fS14S20S5fRaS13P65M7A1M8A2S15Z4000000A1M9A2G5A3RcA2RbA3S0S2cS6bRcS79RbA3S2dA3S0S2cS60RcP1fMaA2S2dA3S0S2cS6eRdRcS4eA3S2dA3Sa0GaS12R11A1A2S0S2cS6fS12R12A1MbReA2S2dA3S0S2cS96S14S22GbA1S2fS14S20S5fR10G8A2G9A2G5A3A3S2dA3S0S39Q40McA1MdS1cRfReA2S3bGcG4A2A3S8G4RdA2S47RfReA2S11S6Sa1R1S12R19A1A2S0GdS1cR3R2A2S1cR15R2A2A3F_;Fi;S1S8S3aGcS24R2S5eR16G7A2A2A2SdZ2Z1aA2A2S55Vcx;R12S61R2R16A2A3A2F_;Fr;S3cS7S3eS7VJD;S4fVcx;ScS33S39Q8A1S58Vcx;A1A2A1A2Vr0;R14S46R11R10A2A4R19R13A4VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fg;Fcap;Fv;Frho;FtvL;Fsx;FXK;FX;FPZ;FP;").
Proof using EXEH.
  intros P PZ X XK sx tvL rho v cap g Hwf Hd Hrun Hlen HXK He Hid Htv Hn Hb Hfb Hz Hg Hcap HI.
  apply (etriple_restate segs _ rho P PZ _ _ Hwf Hd).
  { constructor; [|constructor]. cbn [fst snd eval]. rewrite Hz. apply bv_eq. reflexivity. }
  eapply (erun_trJ segs FUEL CUTS PZ _ _ rho _ Hrun Hlen); [apply JD_stable; [lia|exact Hb] |].
  intros Lf rho1 [<-|[]] Hag. cbn [lf_state].
  destruct (HI rho1 ltac:(intros i Hi; destruct Hag as (Hw & _); symmetry; apply Hw; exact Hi)) as (H26 & HX).
  apply (etriple_add_facts segs _ rho1 _ X XK _ HXK Hfb).
  { constructor; [|constructor]. apply holds_ule. change (sv_subst sx (SVar 101)) with (wsub_get sx 101).
    rewrite CursorGlue.U_lit. unfold M64v. rewrite Z.mod_small by lia. exact H26. }
  apply (ereenter r0 (KdR L) tvL tvK (DG cap g) XK XEH sx rho1 _ (ss_next PZ) He Hid Hn Hb Htv).
  apply (EXEH _ cap g HX); [|exact Hcap]. split; [exact Hg|]. apply pow_g_bound; [exact Hg|]. unfold CAPG in Hcap. rewrite <- Hcap. destruct HX as (_ & _ & _ & _ & _ & [_ HC]). exact HC.
Qed.

Section ECopyTail.
Variables (T Tr Tm G H GR GK HK : sstate) (sh sg : wsub) (xs : list xform) (FKl FGl : list sprop).
Hypothesis Tr_eq : ltac2:(tb__ "0|4|
S0S16S9aS9aVT;U0S1bS13P66A1S13P64A1M0S18S59G0S13P99A1M1A3S30S1fA1M2S1aA5A3U1S1bS15Z0A1S15S69A1M3S18S59G1G3A3G2S1aA5A3VTr;A3").
Hypothesis T_objs : ltac2:(tb__ "0|8|
S1S0S32S1dA1M0S95S1dS23VT;A1U0M1A3S31S1dS1bS18S59S13P66A1M2S13P64A1M3A3S15Z0A1M4S13P99A1M5S30S1fA1M6S1aA5A2A3S1S0G0S95S1dS23S9aVT;G1S1bG2G3S18S59G3G5A3G6S1aA5A3A1U1A3S31S1dS1bS15S69A1G4G5G6S1aA5A2A3S1S0S6S12VT;A1M7S12VTr;A1A3S1S0S2eS14A1S17VTr;A1S17VT;A1A3S1S0S6S12VTm;A1G7A3S1S0S6S12VH;A1G7A3S1S0S6S12VG;A1G7A3S0S2cS1eVTm;A1S34A3A2A2A2A2A2A2A2").
Hypothesis T_next : ss_next T = 194%positive.
Hypothesis xs_ok : ltac2:(tb__ "0|0|
S0S32S16A1Sa4VTr;Vxs;A2S31S16VTm;A2A3").
Hypothesis run_t : ltac2:(tb__ "0|1|
S0S32S2eS40A1M0A1S43S7S74S73VTm;S2dA5S31G0S2fS40S41VG;S42A2S2fS40S41VH;S42A2S30S40A1A3A3A2A3").
Hypothesis HG_regs : ltac2:(tb__ "0|4|
S1S0S10S19VH;Z13M0A2S18S59S13P99A1S13P64A1A3M1A3S1S0S10S19VH;Z15M2A2S13P65A1M3A3S1S0S10S19VG;G0A2G1A3S1S0S10S19VG;G2A2G3A3S0S32S14A1S95S14S17VH;A1U0A3S31S14S28S26S5aG1G3A3A1A2A3A2A2A2A2").
Hypothesis FKl_eq : ltac2:(tb__ "0|2|
S0S2eS14A1VFKl;S2fS14S29S5fVsh;S13P64A1A2M0S5fVsh;S13P65A1A2M1A2S2fS14S20S15Z4A1G0A2S2fS14S20G1S15Z4000000A1A2S30S14A1A3A3A3A3").
Hypothesis HK_eq : ltac2:(tb__ "0|0|
S0S16S99VFKl;VH;A2VHK;A3").
Hypothesis ent_h : ltac2:(tb__ "0|0|
S0S2cS6bVHK;S75Vsh;A3S2dA3").
Hypothesis sh_vals : ltac2:(tb__ "0|4|
S1S0S10S5eVsh;P64M0A2S5fVsh;S13G0A1A2A3S1S0S10S5eVsh;P65M1A2S13G1A1A3S1S0S10S5eVsh;P66M2A2S13G2A1A3S0S10S5eVsh;P67M3A2S13G3A1A3A2A2A2").
Hypothesis sh_100 : ltac2:(tb__ "0|1|
S0S10S5fVsh;S13P64A1M0A2S18S59S13P99A1G0A3A3").
Hypothesis G_fact : ltac2:(tb__ "0|0|
S0S32S14A1S95S14S17VG;A1U0A3S31S14S26S5aS19VG;Z13A2S19VG;Z15A2A3A2A3").
Hypothesis diff_GR : ltac2:(tb__ "0|4|
S0S32S35S2eS35S10S10A2M0A1M1S2eS14A1M2A2M3A1Sa3VG;VGR;A2S31G3S36G1G2S2fG0S36S10S10S19VG;Z13A2S19VG;Z15A2A4S30G0A1A3S30S14A1A4A2A3").
Hypothesis swf_GR : swf GR = true.
Hypothesis GR_next : ltac2:(tb__ "0|0|
S0S6S12VGR;A1S12VT;A1A3").
Hypothesis FGl_eq : ltac2:(tb__ "0|0|
S0S2eS14A1VFGl;S2fS14S20S5fVsg;S13P65A1A2S15Z4000000A1A2S30S14A1A3A3").
Hypothesis GK_eq : ltac2:(tb__ "0|0|
S0S16S99VFGl;VGR;A2VGK;A3").
Hypothesis ent_g : ltac2:(tb__ "0|0|
S0S2cS6bVGK;S76Vsg;A3S2dA3").
Hypothesis sg_vals : ltac2:(tb__ "0|3|
S1S0S10S5eVsg;P65M0A2S13G0A1A3S1S0S10S5eVsg;P66M1A2S13G1A1A3S0S10S5eVsg;P67M2A2S13G2A1A3A2A2").
Hypothesis ids : ltac2:(tb__ "0|1|
S1S0S2cS60Vsh;P1fM0A2S2dA3S0S2cS60Vsg;G0A2S2dA3A2").
Hypothesis tvs : ltac2:(tb__ "0|0|
S1S0S2cS6eVsh;S4eS4eA3S2dA3S0S2cS6eVsg;S4eS4eA3S2dA3A2").
Hypothesis wf_back : ltac2:(tb__ "0|5|
S1S0S2cS21S12VT;A1M0S1bS13P66A1S13P64A1M1S18S59G1S13P99A1M2A3S30S1fA1M3S1aA5A2S2dA3S0S2cS21G0S1bS15Z0A1S15S69A1M4S18S59G2G4A3G3S1aA5A2S2dA3A2").

Lemma ecopy_tail : ltac2:(tb__ "0|4|
S5S11S5S5S5S5S5S98R7A1S8SbZ2SaScS33S39Q8A1S58Vcx;A1A2A1M0R6A2A2R8A2S0S5S4cR8P64A2R7A3S0S5S4cR9P65A2R7A3S0S5S4cRaP66A2R6A3S0S5S4cRbP99A2R8A3S52Vcx;S1cRcP67A2A2S8Z4M1RcA2SeZ0M2RbA2S8S9ReRcA2RdA2S8S9RfRdA2G0A2S4S94S9R10ReA2M3A1S0S5G3G0A3A2S93R10A1S8S9S9RfR11A2G1A2Z7fffff800000A2S8G2RfA2S47R13R10A2S3cS7S3eS7VJX;S9R15R13A2R14R11A3VT;R16A4VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fg;Fb;Fgot;Fcap;Flen;Frho;Fm;").
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
  eapply etriple_conseq with (P := SPJ segs (JX (len + got) cap g) Tr rho); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- Tr_eq.
    apply (SPJ_reshape segs _ rho (reshape_obj_at T 0 Obk) 1 _ Osb w To1 eq_refl eq_refl eq_refl); [| |].
    { cbn [ss_next reshape_obj_at set_objs]. exact Wb2. }
    { intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi Osb]. rewrite (Ulit rho 0), (Ulit rho rs) by lia.
      rewrite !soff_lit_small by lia. rewrite (soff_small rho _ _ Egr) by lia. rewrite (soff_small rho _ _ E153) by lia. lia. }
    apply (SPJ_reshape segs _ rho T 0 _ Obk w To0 eq_refl eq_refl eq_refl Wb1); [|exact Hw].
    intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi Obk]. rewrite Edst, E102. rewrite !soff_lit_small by lia.
    rewrite (soff_small rho _ _ E100) by lia. rewrite (soff_small rho _ _ Elg) by lia. rewrite (soff_small rho _ _ E153) by lia. lia. }
  eapply etriple_conseq; [intros w Hw; exact (SPJ_xforms segs _ xs rho Tr Tm w xs_ok Hw) | intros w Hw; exact Hw |].
  eapply (erun_trJ segs FUEL CUTS Tm _ _ rho _ run_t LnTm); [apply JD_stable; [rewrite NxTm, T_next; lia | rewrite NxTm, T_next; apply tvK_below; lia] |].
  rewrite NxTm, T_next. intros Lf rho3 [<-|[<-|[]]] Hag3; cbn [lf_state].
  -
    apply etriple_factsJ. intros HFG.
    pose proof (Forall_nth_error _ _ _ _ HFG G_fact) as Hf. clear HFG. apply holds_beq in Hf. rewrite RG19, RG21 in Hf.
    assert (T153 : bv_unsigned (rw rho3 153) = got) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U153).
    assert (T100 : bv_unsigned (rw rho3 100) = len) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U100).
    assert (T101 : bv_unsigned (rw rho3 101) = cap) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U101).
    assert (T103 : rw rho3 103 = rw rho 103) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; reflexivity).
    rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) in Hf by lia. cbn [eval] in Hf. rewrite T101 in Hf.
    apply (etriple_restate segs _ rho3 G GR _ _ swf_GR diff_GR).
    { constructor; [|constructor]. cbn [fst snd]. rewrite RG19, RG21. apply bv_eq. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. cbn [eval]. lia. }
    apply (etriple_add_facts segs _ rho3 FGl GR GK _ GK_eq).
    { rewrite FGl_eq. change (sv_subst sg (SVar 101)) with (wsub_get sg 101). rewrite Sg1. cbn -[Pos.ltb]. rewrite GR_next, T_next. reflexivity. }
    { rewrite FGl_eq. change (sv_subst sg (SVar 101)) with (wsub_get sg 101). rewrite Sg1.
      constructor; [|constructor]. apply holds_ule. cbn [eval]. rewrite T101, lit_unsigned. cbn. lia. }
    apply (ereenter r0 (KdR (len + got)) tvK tvK (DG cap g) GK KG sg rho3 _ 194 ent_g Idg ltac:(lia) (tvK_below 194 ltac:(lia)) Tg).
    replace (len + got) with cap by lia. apply (IHG _ cap g); [lia| |split; [exact Hg|exact Hcap]].
    unfold INVG, UV. cbn [rho_sub rw]. rewrite Sg1, Sg3. cbn [eval]. rewrite T101, T103.
    split; [reflexivity|]. split; [exact I3|]. split; [lia | exact I7].
  -
    apply etriple_factsJ. intros HFH.
    pose proof (Forall_nth_error _ _ _ _ HFH Hf0) as Hf. clear HFH. apply holds_nbeq in Hf.
    assert (T153 : bv_unsigned (rw rho3 153) = got) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U153).
    assert (T100 : bv_unsigned (rw rho3 100) = len) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U100).
    assert (T101 : bv_unsigned (rw rho3 101) = cap) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; exact U101).
    assert (T103 : rw rho3 103 = rw rho 103) by (destruct Hag3 as (Hw & _); rewrite <- Hw by lia; reflexivity).
    rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) in Hf by lia. cbn [eval] in Hf. rewrite T101 in Hf.
    apply (etriple_add_facts segs _ rho3 FKl H HK _ HK_eq).
    { rewrite FKl_eq, sh_100. change (sv_subst sh (SVar 101)) with (wsub_get sh 101). rewrite Sh1. cbn -[Pos.ltb]. rewrite NxH, T_next. reflexivity. }
    { rewrite FKl_eq, sh_100. change (sv_subst sh (SVar 101)) with (wsub_get sh 101). rewrite Sh1.
      constructor; [|constructor; [|constructor; [|constructor]]].
      - apply holds_ult. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. cbn [eval]. rewrite T101. lia.
      - apply holds_ule. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. rewrite (Ulit rho3 4) by lia. lia.
      - apply holds_ule. cbn [eval]. rewrite T101, lit_unsigned. cbn. lia. }
    apply (ereenter r0 (KdR (len + got)) tvK tvK (DG cap g) HK K sh rho3 _ 194 ent_h Idh ltac:(lia) (tvK_below 194 ltac:(lia)) Th).
    apply (IHK _ (len + got) cap g); [lia| |split; [exact Hg|exact Hcap]].
    unfold INVK, UV. cbn [rho_sub rw]. rewrite Sh0, sh_100, Sh1, Sh3. rewrite (Uadd rho3 (SVar 153) (SVar 100) got len T153 T100) by lia. cbn [eval]. rewrite T101, T103.
    split; [lia|]. split; [reflexivity|]. split; [exact I3|]. split; [lia|]. split; [lia|]. split; [exact Hal | exact I7].
Qed.
End ECopyTail.

Lemma ecopyA : ltac2:(tb__ "0|4|
S5S11S5S5S5S5S5S98R7A1S8SbZ2SaScS33S39Q8A1S58Vcx;A1A2A1M0R6A2A2R8A2S0S5S4cR8P64A2R7A3S0S5S4cR9P65A2R7A3S0S5S4cRaP66A2R6A3S0S5S4cRbP99A2R8A3S52Vcx;S1cRcP67A2A2S8Z4M1RcA2S1SeZ0M2RbA2S8RbZ10000A2A2S8S9ReRcA2RdA2S8S9RfRdA2G0A2S4S94S9R10ReA2M3A1S0S5G3G0A3A2S93R10A1S8S9S9RfR11A2G1A2Z7fffff800000A2S8S9Z1000Z10A2R10A2S8G2R10A2S47R14R11A2S3cS7S3eS7VJX;S9R16R14A2R15R12A3S88R17A4VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fg;Fb;Fgot;Fcap;Flen;Frho;Fm;").
Proof using EXEH.
  intros m rho len cap got b g loopIH lenBudget e100 e101 e102 e153 hdrW lenFour gotBox capRoom lRoom alignCase capOk
    topRoom bottomRoom gNonneg capPow.
  pose proof (CAP_facts cap capOk) as (capBox & _ & _).
  pose proof rs_range as rsBox.
  unfold UV in e100, e101, e102, e153.
  destruct nexts_A as (_ & _ & nxtPP & _ & _ & _ & _ & nxtCr & nxtTa & nxtTb).
  destruct lenient_A as (_ & _ & lenPP & _ & _).
  destruct fbX_A as (_ & _ & fbP).
  destruct wfb_A as (_ & _ & wfDst & wfSrc).
  apply (etriple_add_facts segs _ rho F_E_rdA P_E_rdA PP_E_rdA _ PP_E_rdA_eq fbP).
  { assert (sumAt : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 100) (SVar 153))) = len + got)
      by (apply Uadd; [exact e100 | exact e153 | lia | lia | lia]).
    unfold F_E_rdA. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    - apply holds_nbeq. rewrite (Ulit rho 0) by lia. cbn [eval]. lia.
    - apply holds_ule. rewrite (Ulit rho 65536) by lia. cbn [eval]. lia.
    - apply holds_ule. rewrite sumAt. cbn [eval]. lia. }
  eapply (erun_trJ segs FUEL CUTS PP_E_rdA _ _ rho _ run_pp_E_rdA lenPP).
  { rewrite nxtPP. apply JD_stable; [lia | apply tvK_below; lia]. }
  rewrite nxtPP. intros leafC rho1 inC agree1. destruct inC as [<-|[]]. cbn [lf_state].
  destruct agree1 as (keep1 & _ & _).
  assert (f100 : bv_unsigned (rw rho1 100) = len) by (rewrite <- keep1 by lia; exact e100).
  assert (f102 : bv_unsigned (rw rho1 102) = b) by (rewrite <- keep1 by lia; exact e102).
  assert (f153 : bv_unsigned (rw rho1 153) = got) by (rewrite <- keep1 by lia; exact e153).
  eapply etriple_conseq;
    [intros w atC; exact (SPJ_xforms segs _ xs_cE_rdA rho1 C_E_rdA Cx_E_rdA w xs_cE_rdA_ok atC) | intros w fin; exact fin |].
  destruct Cr_E_rdA_pre as (cxObj3 & cxObjRs & _ & _).
  assert (cxNext : ss_next Cx_E_rdA = 154%positive) by (vm_compute; reflexivity).
  eapply etriple_conseq with (P := SPJ segs (JX (len + got) cap g) Cr_E_rdA rho1); [| intros w fin; exact fin |].
  { intros w atCx. rewrite <- Cr_E_rdA_eq.
    refine (SPJ_reshape segs _ rho1 (reshape_obj_at Cx_E_rdA 3 O_dstE_rdA) (IRS + 3) _ O_srcE_rdA w cxObjRs
              eq_refl eq_refl eq_refl _ _ _).
    { cbn [ss_next reshape_obj_at set_objs]. rewrite cxNext. exact wfSrc. }
    { intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_srcE_rdA].
      assert (hiSrc : bv_unsigned (eval rho1 (SAlu ALU_ADD (SVar 153) (SLit rs))) = got + rs)
        by (apply Uadd; [exact f153 | apply Ulit; lia | lia | lia | lia]).
      rewrite (soff_small rho1 _ _ hiSrc) by lia. rewrite (soff_small rho1 (SVar 153) got f153) by lia.
      rewrite (Ulit rho1 rs), (Ulit rho1 0) by lia. rewrite !soff_lit_small by lia. lia. }
    refine (SPJ_reshape segs _ rho1 Cx_E_rdA 3 _ O_dstE_rdA w cxObj3 eq_refl eq_refl eq_refl _ _ atCx).
    { rewrite cxNext. exact wfDst. }
    intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_dstE_rdA].
    assert (baseDst : bv_unsigned (eval rho1 (SAlu ALU_ADD (SVar 102) (SVar 100))) = b + len)
      by (apply Uadd; [exact f102 | exact f100 | lia | lia | lia]).
    assert (hiOld : bv_unsigned (eval rho1 (SAlu ALU_ADD (SVar 100) (SVar 153))) = len + got)
      by (apply Uadd; [exact f100 | exact f153 | lia | lia | lia]).
    rewrite baseDst. rewrite (soff_small rho1 _ _ hiOld) by lia.
    rewrite (soff_small rho1 (SVar 153) got f153) by lia. rewrite (soff_small rho1 (SVar 100) len f100) by lia.
    rewrite soff_lit_small by lia. cbn [eval]. lia. }
  apply (epure_callD r0 (KdR (len + got)) tvK (DG cap g) Cr_E_rdA PreG s_cE_rdA R_cE_rdA Posts_memcpy rho1 Q).
  - intros rho2. exact (memcpy_sum_ex _ rho2).
  - exact efr_cE_rdA.
  - exact chk_cE_rdA.
  - rewrite nxtCr. lia.
  - rewrite nxtCr. apply tvK_below. lia.
  - exact fb_cE_rdA.
  - intros leafT rho2 inPost agree2. rewrite nxtCr in agree2. destruct agree2 as (keep2 & _ & _).
    assert (g100 : UV rho2 100 = len) by (unfold UV; rewrite <- keep2 by lia; exact f100).
    assert (g101 : UV rho2 101 = cap) by (unfold UV; rewrite <- keep2, <- keep1 by lia; exact e101).
    assert (g102 : UV rho2 102 = b) by (unfold UV; rewrite <- keep2 by lia; exact f102).
    assert (g153 : UV rho2 153 = got) by (unfold UV; rewrite <- keep2 by lia; exact f153).
    assert (g103 : rw rho2 103 = rw rho 103) by (rewrite <- keep2, <- keep1 by lia; reflexivity).
    destruct GR_nexts as (grA & grB & _).
    destruct ids_A as (_ & _ & idHa & idGa & idHb & idGb & _).
    destruct tvs_A as (_ & _ & tvHa & tvGa & tvHb & tvGb).
    destruct wfb_A as (wfLo & wfHi & _).
    cbn [Posts_memcpy MuslMemcpy.Posts_memcpy In] in inPost.
    destruct inPost as [<-|[<-|[]]]; cbn [lf_state].
    + rewrite TE_rdAa_eq.
      refine (ecopy_tail TE_rdAa TrE_rdAa TmE_rdAa GE_rdAa HE_rdAa GRE_rdAa GKE_rdAa HKE_rdAa s_hE_rdAa s_gE_rdAa
                xs_tE_rdAa FKE_rdAa FGE_rdAa TrE_rdAa_eq TE_rdAa_objs nxtTa xs_tE_rdAa_ok run_tE_rdAa HGE_rdAa_regs eq_refl
                HKE_rdAa_eq ent_hE_rdAa s_hE_rdAa_vals shp_hAa GE_rdAa_fact diff_GRE_rdAa swf_GRE_rdAa grA eq_refl
                GKE_rdAa_eq ent_gE_rdAa s_gE_rdAa_vals (conj idHa idGa) (conj tvHa tvGa)
                ltac:(rewrite nxtTa; exact (conj wfLo wfHi))
                m rho2 len cap got b g loopIH lenBudget g100 g101 g102 g153 _ lenFour ltac:(lia) capRoom lRoom alignCase
                capOk ltac:(lia) gNonneg capPow).
      rewrite g103. exact hdrW.
    + rewrite TE_rdAb_eq.
      refine (ecopy_tail TE_rdAb TrE_rdAb TmE_rdAb GE_rdAb HE_rdAb GRE_rdAb GKE_rdAb HKE_rdAb s_hE_rdAb s_gE_rdAb
                xs_tE_rdAb FKE_rdAb FGE_rdAb TrE_rdAb_eq TE_rdAb_objs nxtTb xs_tE_rdAb_ok run_tE_rdAb HGE_rdAb_regs eq_refl
                HKE_rdAb_eq ent_hE_rdAb s_hE_rdAb_vals shp_hAb GE_rdAb_fact diff_GRE_rdAb swf_GRE_rdAb grB eq_refl
                GKE_rdAb_eq ent_gE_rdAb s_gE_rdAb_vals (conj idHb idGb) (conj tvHb tvGb)
                ltac:(rewrite nxtTb; exact (conj wfLo wfHi))
                m rho2 len cap got b g loopIH lenBudget g100 g101 g102 g153 _ lenFour ltac:(lia) capRoom lRoom alignCase
                capOk ltac:(lia) gNonneg capPow).
      rewrite g103. exact hdrW.
Qed.

Lemma estepK : ltac2:(tb__ "0|0|
S5S11S5S5S5S98R5A1S8SbZ2SaScS33S39Q8A1S58Vcx;A1A2A1R4A2A2R6A2S54Vcx;R5R4R6A4S8Z0R4A2S47R6R5A2S3cS7S3eS7VJX;R8R7R6A3S75R9A4VQ;A3F_;F_;F_;F_;F_;Fg;Fcap;Flen;Frho;Fm;").
Proof using EXEH.
  intros m rho len cap g IH Hm HI Hg Hcap. pose proof IH as [IHK IHG].
  pose proof HI as (I1 & I2 & I3 & I4 & I5 & I6 & I7). pose proof (CAP_facts cap I7) as (C1 & C2 & C3). clear C3.
  destruct nexts_A as (NxZA & NxZB & NxPA & NxA & NxB & NxXA & NxXB & _). destruct lenient_A as (LnZA & LnZB & LnPA & LnK & _).
  destruct ids_A as (IdxA & IdxB & _). destruct tvs_A as (TxA & TxB & _). destruct fbX_A as (FbxA & FbxB & FbpA).

  apply etriple_factsJ. intros HFK.
  assert (Hnz : bv_unsigned (rw rho 102) <> 0).
  { pose proof (Forall_nth_error _ _ _ _ HFK K_nz) as Hf. apply holds_nbeq in Hf. rewrite CursorGlue.U_lit in Hf. change (0 mod M64v) with 0 in Hf. exact Hf. }
  clear HFK. apply (etriple_Jpure segs (bv_unsigned (rw rho 102) + cap + 4 <= aceil_hi /\ 4096 + 16 <= bv_unsigned (rw rho 102))).
  { intros tr md HJ. destruct (JD_geom r0 _ _ _ _ _ _ (SVar 102) (SVar 101) HJ ltac:(left; reflexivity) Hnz) as (_ & G & G').
    cbn [eval] in G, G'. unfold UV in I2. rewrite I2 in G. exact (conj G G'). }
  intros [Gb Gb0].
  eapply (erun_trJ segs FUEL CUTS K _ _ rho _ run_k LnK); [apply JD_stable; [|apply tvK_below]; rewrite (proj1 cuts_shape); lia |].
  rewrite (proj1 cuts_shape). intros Lf rho1 [<-|[<-|[]]] Hag; cbn [lf_state].
  -
    apply etriple_factsJ. intros HFB.
    pose proof (Forall_nth_error _ _ _ _ HFB E_rdB_fact) as Hf. clear HFB. apply holds_bltu in Hf.
    rewrite CursorGlue.U_sub, CursorGlue.U_lit in Hf. cbn [eval] in Hf. unfold M64v in Hf.
    pose proof (INVK_agree len cap rho rho1 153 ltac:(lia) Hag HI) as (J1 & J2 & _). unfold UV in J1, J2. rewrite J1, J2 in Hf.
    rewrite (Z.mod_small 65536), Z.mod_small in Hf by lia.
    assert (HL : len = L).
    { destruct I6 as [I6|I6]; [|exact I6]. exfalso.
      unfold ALIGNED in C2, I6. assert ((cap - len) mod 65536 = 0) by (rewrite Zminus_mod, C2, I6; reflexivity).
      assert (cap - len = 65536 * ((cap - len) / 65536)) by (pose proof (Z.div_mod (cap - len) 65536 ltac:(lia)); lia). nia. }
    destruct E_rdB_shape as (Bpc & B17 & B10 & B11 & B12 & Bnx & Bo1 & BoI).
    eapply etriple_seq.
    { apply (ejread_rs r0 (DG cap g) (DG_fds cap g) E_rdB rho1 len (cap - len) tvK cert_rdB B17 B10 BoI B11).
      - rewrite B12, CursorGlue.U_sub. cbn [eval]. rewrite J1, J2. unfold M64v. apply Z.mod_small. lia.
      - lia.
      - unfold L in *; lia.
      - rewrite Bnx. lia.
      - rewrite Bnx. apply tvK_below. lia. }
    rewrite P_E_rdB_eq, Bnx.
    pose proof (chunk_length len (cap - len) ltac:(lia) ltac:(lia)) as CL.
    replace (len + Z.of_nat (length (chunk len (cap - len)))) with L by lia.
    destruct shp_xB as (Sx0 & Sx1 & Sx2 & Sx3).
    apply (eexit_via P_E_rdB PZ_E_rdB X_E_rdB XK_E_rdB s_xE_rdB tvK _ 153 cap g swf_PZ_E_rdB diff_PZ_E_rdB run_pz_E_rdB LnZB XK_E_rdB_eq ent_xE_rdB IdxB TxB
             ltac:(rewrite NxZB; lia) ltac:(rewrite NxZB; apply tvK_below; lia) FbxB).
    + rewrite rho_set_rw_at. apply len_word_zero. lia.
    + exact Hg.
    + exact Hcap.
    + intros r Hr. rewrite NxZB in Hr. unfold INVX, UV. cbn [rho_sub rw]. rewrite Sx0, Sx1, Sx3. cbn [eval].
      rewrite !Hr by lia. rewrite !rho_set_rw_other by lia. destruct Hag as (Hw & _). rewrite <- !Hw by lia.
      unfold UV in I1, I2. split; [lia|].
      split; [lia|]. split; [exact I2|]. split; [exact I3|]. unfold MAX_INPUT. split; [lia|]. split; [lia|]. exact I7.
  -
    apply etriple_factsJ. intros HFA.
    pose proof (Forall_nth_error _ _ _ _ HFA E_rdA_fact) as Hf. clear HFA. apply holds_nbltu in Hf.
    rewrite CursorGlue.U_sub, CursorGlue.U_lit in Hf. cbn [eval] in Hf. unfold M64v in Hf.
    pose proof (INVK_agree len cap rho rho1 153 ltac:(lia) Hag HI) as (J1 & J2 & _). unfold UV in J1, J2. rewrite J1, J2 in Hf.
    rewrite (Z.mod_small 65536), Z.mod_small in Hf by lia.
    destruct E_rdA_shape as (Apc & A17 & A10 & A11 & A12 & Anx & Ao1 & AoI).
    assert (R102 : rw rho1 102 = rw rho 102) by (destruct Hag as (Hw & _); symmetry; apply Hw; lia).
    assert (R103 : rw rho1 103 = rw rho 103) by (destruct Hag as (Hw & _); symmetry; apply Hw; lia).
    eapply etriple_seq.
    { apply (ejread_rs r0 (DG cap g) (DG_fds cap g) E_rdA rho1 len 65536 tvK cert_rdA A17 A10 AoI A11).
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
      apply (eexit_via P_E_rdA PZ_E_rdA X_E_rdA XK_E_rdA s_xE_rdA tvK _ 153 cap g swf_PZ_E_rdA diff_PZ_E_rdA run_pz_E_rdA LnZA XK_E_rdA_eq ent_xE_rdA IdxA TxA
               ltac:(rewrite NxZA; lia) ltac:(rewrite NxZA; apply tvK_below; lia) FbxA).
      * subst rho2. rewrite rho_set_rw_at. apply len_word_zero. lia.
      * exact Hg.
      * exact Hcap.
      * intros r Hr. rewrite NxZA in Hr. unfold INVX, UV. cbn [rho_sub rw]. rewrite Sx0, Sx1, Sx3. cbn [eval].
        rewrite !Hr by lia. rewrite G103. split; [lia|].
        split; [lia|]. split; [exact G101|]. split; [exact I3|]. unfold MAX_INPUT. split; [lia|]. split; [lia|]. exact I7.
    +
      apply (ecopyA m rho2 len cap got (bv_unsigned (rw rho 102)) g IH Hm); unfold UV; rewrite ?G102, ?G103; try assumption; try reflexivity; try lia.
      destruct I6 as [I6|I6]; [|lia].
      assert (Hgot : got = 65536 \/ (got < 65536 /\ len + got = L)) by lia.
      destruct Hgot as [Hg'|[Hg1 Hg2]]; [left | right; exact Hg2].
      unfold ALIGNED in *. rewrite Hg', <- Zplus_mod_idemp_l, I6. reflexivity.
Qed.

Lemma estepG_ok : ltac2:(tb__ "0|2|
S5S11S5S5S98R4A1S8S9SbZ2M0SaScS33S39Q8A1S58Vcx;A1A2A1M1R3A2A2Z1A2R5A2S0S5S4cR5P65A2R4A3S52Vcx;S1cR6P67A2A2S8R6G1A2S93R7A1SeR8SdG0Z1aA2A2S8Z0R8A2S47RaR9A2S3cS7S3eS7VJD;S4fVcx;RbA2Vr0;S57S4bRbRaA2A4S91RcA4VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fg;Fcap;Frho;Fm;").
Proof using EXEH FDX.
  intros m rho cap g loopIH capBudget e101 hdrW capL capOk capSmall gNonneg capPow.
  destruct loopIH as [ihK _].
  pose proof (CAP_facts cap capOk) as (capBox & capAligned & _).
  destruct (g_lt_bound cap g gNonneg capPow capSmall) as (gNine & capHalf).
  unfold UV in e101.
  destruct nexts_G as (nGokS & nCmc & nTmcM & nCfr & nTfr & nHfr & _).
  destruct lenient_G as (lenGokS & lenTmcM & lenTfr).
  destruct tvb_G as (tvb193 & tvb233 & tvb273 & _).
  eapply etriple_conseq;
    [intros w atG; exact (SPJ_xforms segs _ xs_g rho T_gok T_gokS w xs_g_ok atG) | intros w fin; exact fin |].
  eapply (erun_trJ segs FUEL CUTS T_gokS _ _ rho _ run_goks lenGokS).
  { rewrite nGokS. apply JD_stable; [lia | exact tvb193]. }
  rewrite nGokS. intros leafM rho1 inM agree1. destruct inM as [<-|[]]. cbn [lf_state].
  destruct agree1 as (keep1 & _ & _).
  apply (epure_callD r0 (KdR cap) tvG (DM cap g) C_mc PreC s_mc R_mc Posts_mh rho1 Q).
  - intros rho2. exact (memcpy_hdr_sum_ex _ rho2).
  - exact efr_mc.
  - exact chk_mc.
  - rewrite nCmc. lia.
  - rewrite nCmc. exact tvb193.
  - exact fb_mc.
  - intros leafH rho2 inH agree2. rewrite nCmc in agree2. destruct agree2 as (keep2 & _ & _).
    rewrite Posts_mh_eq in inH. destruct inH as [<-|[]]. cbn [lf_state]. rewrite T_mc_eq.
    eapply etriple_conseq;
      [intros w atT; exact (SPJ_xforms segs _ xs_m rho2 T_mc T_mcM w xs_m_ok atT) | intros w fin; exact fin |].
    eapply (erun_trJ segs FUEL CUTS T_mcM _ _ rho2 _ run_mcm lenTmcM).
    { rewrite nTmcM. apply JD_stable; [lia | exact tvb233]. }
    rewrite nTmcM. intros leafF rho3 inF agree3. destruct inF as [<-|[]]. cbn [lf_state].
    destruct agree3 as (keep3 & _ & _).
    assert (c101 : bv_unsigned (rw rho3 101) = cap) by (rewrite <- keep3, <- keep2, <- keep1 by lia; exact e101).
    assert (c103 : rw rho3 103 = rw rho 103) by (rewrite <- keep3, <- keep2, <- keep1 by lia; reflexivity).
    apply etriple_factsJ. intros factsFr.
    assert (nzOld : bv_unsigned (eval rho3 (SVar 102)) <> 0).
    { pose proof (holds_of_existsb rho3 _ _ factsFr nz_fr) as nzHold. apply holds_nbeq in nzHold.
      rewrite (Ulit rho3 0) in nzHold by lia. exact nzHold. }
    destruct s_fr_vals as (fr12 & fr13 & _ & _).
    refine (dfree_call_ex segs C_U EC_U 31 (KdR cap) r0 P0 malloc_laws_U C_fr s_fr R_fr rho3 tvG 1 (SVar 102, SVar 101) Q
              (DM cap g)
              (fun A => J_free_drv segs C_U A (kOf g - 1) (XOf cap g - malloc_cost (2 * cap)) (KdR cap))
              (fun A => JLd_free segs C_U A (kOf g - 1 - 1) (XOf cap g - malloc_cost (2 * cap)) (KdR cap))
              (DX (kOf g - 1 - 1) (XOf cap g - malloc_cost (2 * cap)))
              eq_refl _ efr_fr chk_fr _ eq_refl _ eq_refl _ _ _).
    + intros A rho4. exact (FDX A (kOf g - 1) (XOf cap g - malloc_cost (2 * cap)) (KdR cap) rho4 (KdR_vmi cap)).
    + rewrite nCfr. reflexivity.
    + rewrite nCfr. exact tvb233.
    + intros A tr ms md _ giA dA. destruct dA as (drvA & roomA).
      pose proof (T_ok_of_JGi (KdR cap) r0 tvG A rho3 tr md giA) as topOk.
      destruct giA as (_ & _ & (minvA & _ & _) & _ & (tvinA & tvdA & tvzA) & _).
      split; [|split; [exact nzOld|split]].
      * intros preA. refine (conj preA (conj drvA (conj _ roomA))). unfold kOf. rewrite DRV_OPS_val. lia.
      * rewrite fr12, fr13. reflexivity.
      * refine (robjs_check_sound segs C_U [] A rho3 (ss_facts C_fr) tvG (Some 1%nat) (robj_inw WINS_U) R_fr _ rho3 md
                  minvA topOk factsFr tvinA tvdA tvzA rchk_fr _ _).
        -- intros o a _ inw inRange. exact (robj_inw_caddr segs C_U WINS_U rho3 A _ o a WINS_U_ok inw inRange).
        -- exists (SVar 102, SVar 101). split; [reflexivity|]. split; [exact nzOld|]. rewrite fr12. reflexivity.
    + intros A rr0 rr' tr md freed.
      destruct freed as (A' & l1 & l2 & minv' & (initA' & topA') & drv' & room' & blocksA & blocksA' & kept' & kc').
      exists A', l1, l2.
      exact (conj minv' (conj (conj initA' topA') (conj blocksA (conj blocksA' (conj kept' (conj kc' (conj drv' room'))))))).
    + intros rho4 agree4. rewrite T_fr_eq. change (remove_nth 1 tvG) with tvN.
      rewrite nCfr in agree4. destruct agree4 as (keep4 & _).
      eapply etriple_conseq with (P := SPJ segs (JD (KdR cap) r0 tvN (DG (2 * cap) (g + 1))) T_fr rho4);
        [| intros w fin; exact fin |].
      { intros w [matchT jT]. split; [exact matchT|].
        exact (JGD_mono segs C_U 31 (KdR cap) r0 P0 tvN _ _ rho4 _ _ (DG_next cap g) jT). }
      eapply (erun_trJ segs FUEL CUTS T_fr _ _ rho4 _ run_fr lenTfr).
      { rewrite nTfr. apply JD_stable; [lia | exact tvb273]. }
      rewrite nTfr. intros leafK rho5 inK agree5. destruct inK as [<-|[]]. cbn [lf_state].
      destruct agree5 as (keep5 & _ & _).
      assert (d101 : bv_unsigned (rw rho5 101) = cap) by (rewrite <- keep5, <- keep4 by lia; exact c101).
      assert (d103 : rw rho5 103 = rw rho 103) by (rewrite <- keep5, <- keep4 by lia; exact c103).
      assert (dbl : bv_unsigned (eval rho5 (SAlu ALU_SLL (SVar 101) (SLit 1))) = 2 * cap)
        by (apply Usll1; [exact d101 | lia | lia]).
      destruct s_hfr_vals as (h100 & h101 & _ & h103).
      apply (etriple_add_facts segs _ rho5 FK_fr H_fr HK_fr _ HK_fr_eq fb_G).
      { unfold FK_fr. apply Forall_cons; [|apply Forall_nil]. apply holds_ule.
        change (sv_subst s_hfr (SVar 101)) with (wsub_get s_hfr 101). rewrite h101, dbl, (Ulit rho5 67108864) by lia.
        lia. }
      destruct ids_A as (_ & _ & _ & _ & _ & _ & idHfr).
      apply (ereenter r0 (KdR cap) tvN tvK (DG (2 * cap) (g + 1)) HK_fr K s_hfr rho5 Q 273 ent_hfr idHfr ltac:(lia)
               tvb273 tvs_G).
      refine (ihK (rho_sub rho5 s_hfr) cap (2 * cap) (g + 1) ltac:(lia) _ _).
      * unfold INVK, UV. cbn [rho_sub rw]. rewrite h100, h101, h103, dbl. cbn [eval]. rewrite d101, d103.
        refine (conj eq_refl (conj eq_refl (conj (HDR_sext _ hdrW) (conj _ (conj capL (conj (or_introl capAligned)
                  (CAP_double cap capOk capSmall))))))).
        lia.
      * split; [lia|]. unfold CAPG in *. rewrite capPow, Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
Qed.

Lemma estepG : ltac2:(tb__ "0|0|
S5S11S5S5S98R4A1S8S9SbZ2SaScS33S39Q8A1S58Vcx;A1A2A1R3A2A2Z1A2R5A2S53Vcx;R4R5A3S8Z0R4A2S47R6R5A2S3cS7S3eS7VJX;R7R7R6A3S76R8A4VQ;A3F_;F_;F_;F_;F_;Fg;Fcap;Frho;Fm;").
Proof using EXEH EXref FDX HX0 MBX.
  intros m rho cap g loopIH capBudget invG gNonneg capPow.
  pose proof invG as (e101 & hdrW & capL & capOk).
  pose proof (CAP_facts cap capOk) as (capBox & _ & _).
  unfold UV in e101.
  destruct cuts_shape as (_ & nKG & _).
  destruct lenient_A as (_ & _ & _ & _ & lenKG).
  eapply (erun_trJ segs FUEL CUTS KG _ _ rho _ run_kg lenKG).
  { rewrite nKG. apply JD_stable; [lia | apply tvK_below; lia]. }
  rewrite nKG. intros leafG rho1 inG agree1. destruct agree1 as (keep1 & _ & _).
  assert (f101 : bv_unsigned (rw rho1 101) = cap) by (rewrite <- keep1 by lia; exact e101).
  assert (f103 : rw rho1 103 = rw rho 103) by (rewrite <- keep1 by lia; reflexivity).
  assert (shifted : bv_unsigned (eval rho1 (SAlu ALU_SRL (SVar 101) (SLit 26))) = cap / 2 ^ 26)
    by (rewrite U_srl_lit; cbn [eval]; rewrite f101; reflexivity).
  apply etriple_factsJ. intros factsG.
  destruct inG as [<-|[<-|[]]]; cbn [lf_state] in factsG |- *.
  - destruct X_ref_shape as (_ & _ & refFact).
    pose proof (Forall_nth_error _ _ _ _ factsG refFact) as bigCap. apply holds_bne in bigCap.
    rewrite shifted, (Ulit rho1 0) in bigCap by lia.
    assert (atTop : cap = 2 ^ 26).
    { destruct (Z.eq_dec cap (2 ^ 26)) as [same|differ]; [exact same|].
      exfalso. apply bigCap. apply Z.div_small. lia. }
    rewrite atTop in f101, capL, capPow |- *.
    refine (EXref rho1 g _ _ _ _).
    + unfold UV. exact f101.
    + exact capL.
    + rewrite f103. exact hdrW.
    + split; [exact gNonneg|]. apply pow_g_bound; [exact gNonneg|]. unfold CAPG in capPow. lia.
  - destruct C_gm_shape as (_ & nCgm & _ & gmFact).
    pose proof (Forall_nth_error _ _ _ _ factsG gmFact) as smallCap. apply holds_nbne in smallCap.
    rewrite shifted, (Ulit rho1 0) in smallCap by lia.
    assert (capSmall : cap < 2 ^ 26).
    { destruct (Z_lt_le_dec cap (2 ^ 26)) as [below|above]; [exact below|].
      exfalso. pose proof (Z.div_str_pos cap (2 ^ 26) ltac:(lia)). lia. }
    destruct (g_lt_bound cap g gNonneg capPow capSmall) as (gNine & capHalf).
    assert (dbl1 : bv_unsigned (eval rho1 (SAlu ALU_SLL (SVar 101) (SLit 1))) = 2 * cap)
      by (apply Usll1; [exact f101 | lia | lia]).
    destruct s_gm_vals as (gm12 & _ & _ & gmBelow & gmRes).
    refine (dmalloc_call_ex segs C_U EC_U 31 (KdR cap) r0 P0 malloc_laws_U C_gm s_gm R_gm rho1 tvK Q (DG cap g)
              (fun A => J_big_ex segs C_U true A (kOf g) (XOf cap g) (KdR cap))
              (fun A => [Post_big_ex segs C_U EC_U true A (kOf g) (XOf cap g) (KdR cap)])
              (fun _ _ _ _ _ => False)
              (fun A => JLd_big_ok segs C_U A (kOf g) (XOf cap g) (KdR cap))
              (DM cap g) (DM cap g)
              eq_refl _ efr_gm _ _ eq_refl _ gmBelow gmRes _ _ _ _ _ _).
    + intros A rho2. exact (MBX A (kOf g) (XOf cap g) (KdR cap) rho2 (KdR_vmi cap)).
    + intros A. exact chk_gm_ok.
    + rewrite nCgm. reflexivity.
    + rewrite nCgm. apply tvK_below. lia.
    + intros A tr ms md _ giA dA tpCallee topCallee. destruct dA as (drvA & roomA).
      pose proof (T_ok_of_JGi (KdR cap) r0 tvK A rho1 tr md giA) as topOk.
      destruct giA as (_ & kdA & (minvA & initA & tpiA) & _ & (tvinA & tvdA & tvzA) & _).
      assert (robjsOk : robjs_ok segs C_U A None rho1 R_gm).
      { refine (robjs_check_sound segs C_U [] A rho1 (ss_facts C_gm) tvK None (robj_inw WINS_U) R_gm None rho1 md
                  minvA topOk factsG tvinA tvdA tvzA rchk_gm _ I).
        intros o a _ inw inRange. exact (robj_inw_caddr segs C_U WINS_U rho1 A None o a WINS_U_ok inw inRange). }
      assert (arg12 : bv_unsigned (rw (rho_sub (rho_absorb rho1 R_gm ms) s_gm) 12) = 2 * cap).
      { cbn [rho_sub rw]. rewrite eval_absorb, gm12. exact dbl1. }
      refine (conj _ (conj robjsOk _)); [|rewrite gm12, dbl1; lia].
      refine (conj _ (conj drvA (conj _ (conj _ (conj kdA (conj _ (conj tpCallee topCallee))))))).
      * refine (proj1 (MInvR_mem segs C_U r0 malloc_laws_U A rho1 _ md md (conj minvA (conj initA tpiA)) _ eq_refl)).
        intros a aBox ownedOrStatic. apply rm_absorb_out.
        exact (R_miss segs C_U malloc_laws_U A None rho1 rho1 md R_gm a minvA robjsOk aBox ownedOrStatic).
      * unfold kOf. rewrite DRV_OPS_val. lia.
      * rewrite arg12, MMAP_THRESHOLD_val. lia.
      * intros _. split; [exact roomA|]. rewrite arg12, malloc_cost_val. unfold XOf. lia.
    + intros A post inPosts. cbn [In] in inPosts. destruct inPosts as [<-|[]]. right. reflexivity.
    + intros A rr0 rr' tr md [].
    + intros A rr0 rr' tr md r12 okPost.
      destruct okPost as (A' & l1 & l2 & minv' & (init' & top') & drv' & room' & blk' & blk & kept' & kc').
      exists A', l1, l2. rewrite r12, gm12, dbl1 in room'.
      exact (conj minv' (conj (conj init' top') (conj blk' (conj blk (conj kept' (conj kc' (conj drv' room'))))))).
    + intros (A & inNull). exfalso. cbn [In] in inNull. destruct inNull as [pairEq|[]].
      injection pairEq as pcEq. discriminate pcEq.
    + intros _ rho2 agree2. rewrite T_gok_eq. rewrite nCgm in agree2 |- *. rewrite gm12.
      destruct agree2 as (keep2 & _).
      change ((SVar (pos_add_nat 153 10), SAlu ALU_SLL (SVar 101) (SLit 1)) :: tvK) with tvG.
      refine (estepG_ok m rho2 cap g loopIH capBudget _ _ capL capOk capSmall gNonneg capPow).
      * unfold UV. rewrite <- keep2 by lia. exact f101.
      * rewrite <- keep2 by lia. rewrite f103. exact hdrW.
Qed.

Lemma eloop_all : forall m, LoopIHx m.
Proof using EXEH EXref FDX HX0 MBX.
  assert (N : forall n : nat, LoopIHx (Z.of_nat n)).
  { induction n as [|n IHn].
    - split; [intros rho len cap g Hm (_ & _ & _ & _ & I5 & _); lia | intros rho cap g Hm (_ & _ & I5 & _); lia].
    - split.
      + intros rho len cap g Hm HI [Hg Hc]. apply (estepK (Z.of_nat n) rho len cap g IHn); [lia | exact HI | exact Hg | exact Hc].
      + intros rho cap g Hm HI [Hg Hc]. apply (estepG (Z.of_nat n) rho cap g IHn); [lia | exact HI | exact Hg | exact Hc]. }
  intros m. destruct (Z_lt_le_dec m 0) as [Hm|Hm].
  - split; [intros rho len cap g H (_ & _ & _ & _ & I5 & _); lia | intros rho cap g H (_ & _ & I5 & _); lia].
  - rewrite <- (Z2Nat.id m) by lia. apply N.
Qed.

End LoopX.

Lemma toKx : ltac2:(tb__ "0|3|
S11S11S3dS3eS7VJD;S4fVcx;Z0M0A2R3S4dS46Z10000G0A2M1A4S7fR2R1A5S2S63S63S2S2eS39Q40A1A1M2G2S1S92S7S71VP0;Vwtop;S4dG1R5R2R1A9S3fS7S50Vcx;G0R2R1A4S7fR5R4A5A2Lmat;A2Lvm;A2F_;Fw;Frho;Fr0;").
Proof using Hargc Hent Hinp P0_top.
  intros r0 rho w [matchK0 jdK0].
  destruct jdK0 as (A & giA & dA).
  assert (p0R : P0 rho).
  { refine (P0_now sp brk mb draw inp Hent Hinp Hargc (KdR 0) r0 tv0 (DG 65536 0) rho (w_tr w) (cfg_model (w_cfg w)) _).
    exists A. exact (conj giA dA). }
  destruct (deJ segs C_U 31 P0 wtop P0_top (KdR 0) r0 tv0 (DG 65536 0) A rho _ _ giA dA p0R) as [snapR kdR0].
  exists (m_vmmaps (cfg_model (w_cfg w))), (m_vm_materialized (cfg_model (w_cfg w))).
  refine (conj snapR (conj matchK0 _)).
  exact (conj kdR0 (conj eq_refl eq_refl)).
Qed.

Lemma fromKx : ltac2:(tb__ "0|1|
S11S11S63S2eS39Q40A1A1S5S16S3dS92S7S71VP0;Vwtop;S4dS46Z10000Z0A2M0R7R5R4A9S51R8R7A2S3fS7S50Vcx;R5R7R6A4R4R8R3A5S1S3eS7VJD;S4fVcx;R6A2R9S4dG0A4R5R9R4A5VP0;R9A1A2F_;F_;F_;Fw;FS;Foff;Fmat;Fvm;Frho;FrhoB;").
Proof using Hargc Hent Hinp P0_top P0_tp.
  intros rhoB rho vm mat off S w snapB brB [matchS kbS].
  pose proof brB as [regsB memB].
  assert (p0B : P0 rhoB) by (destruct snapB as (A & md & _ & _ & _ & p0 & _); exact p0).
  assert (p0R : P0 rho).
  { refine (P0_agree sp brk mb draw inp Hent Hinp Hargc rhoB rho p0B _ _).
    - intros i iLow. apply regsB. lia.
    - intros a _. apply memB. }
  assert (snapR : snapJ segs C_U P0 wtop tv0 (DG 65536 0) rho vm mat).
  { refine (snapJ_transport segs C_U P0 malloc_laws_U wtop tv0 (DG 65536 0) rhoB rho vm mat snapB _ _ _ p0R).
    - intros t inTv. destruct inTv as [<-|[]]. cbn [fst snd eval].
      rewrite (regsB 41%positive) by lia. split; reflexivity.
    - intros a. unfold Contract.rd_of. rewrite memB. reflexivity.
    - intros a. unfold Contract.wok_of. rewrite memB. reflexivity. }
  destruct kbS as (kdOff & vmEq & matEq).
  destruct (reJ segs C_U 31 P0 wtop P0_top P0_tp (KdR off) tv0 (DG 65536 0) rho vm mat (w_tr w) (cfg_model (w_cfg w))
              snapR vmEq matEq (DG_vm 65536 0) kdOff) as (A & giA & dA).
  split; [|exact p0R].
  split; [exact matchS|].
  exists A. exact (conj giA dA).
Qed.

Section FirstX.

Hypothesis ELOOPK : ltac2:(tb__ "0|1|
S11S11S5S54Vcx;R1Z10000M0R2A4S3cS7S3eS7VJD;S4fVcx;R2A2R4S4eS46G0Z0A2A4S75R3A4VQ;A3F_;Flen;Frho;Fr0;").
Hypothesis ELOOPG : ltac2:(tb__ "0|1|
S11S11S53Vcx;Z10000M0R1A3S3cS7S3eS7VJD;S4fVcx;G0A2R3S4eS46G0Z0A2A4S76R2A4VQ;A3F_;Frho;Fr0;").
Hypothesis EXE0 : ltac2:(tb__ "0|2|
S11S11S0S5S4cR1P64A2ScS33S39Q8A1S58Vcx;A1A2A1M0A3S0S5S4cR2P65A2Z10000M1A3SeG0Z4A2S3cS7S3eS7VJD;S4fVcx;G0A2R5S4eS46G1Z0A2A4S78R4A4VQ;A3F_;F_;F_;Frho;Fr0;").

Lemma eexit0_via : ltac2:(tb__ "0|3|
S16S62S11S63S2eS39Q40A1A1S11S92S7S71VP0;Vwtop;S4dS46Z10000M0Z0A2R4R3R2A9S51R5R2A2S0S2cS6bR8S78R7A3S2dA3S0S2cS60R8P1fM1A2S2dA3S0S2cS6eR9S4dS4eA3S2dA3Sa0G1S12RbA1A2S0S2cS6fS12RcA1S4dA2S2dA3S0S5S4cS61R8RcA2P64A2ScS33S39Q8A1S58Vcx;A1A2A1M2A3S0S5S4cS61R9RdA2P65A2G0A3SeG2Z4A2S3cS7S3fS7S50Vcx;G2RdRcA4R10RbA4VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;Fmat;Fvm;FrhoB;Fsx;FX;").
Proof using EXE0 Hargc Hent Hinp.
  intros X sx rhoB vm mat rho HS HB He Hid Htv Hn Hb H100 H101 HL.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (fromKx rhoB rho vm mat L X w HS HB Hw)) | intros w Hw; exact Hw |].
  apply (ereenter rho (KdR L) tv0 tvK (DG 65536 0) X XE0 sx rho _ (ss_next X) He Hid Hn Hb Htv).
  apply (EXE0 rho); assumption.
Qed.

Lemma eloopK_via : ltac2:(tb__ "0|2|
S16S62S11S63S2eS39Q40A1A1S11S5S92S7S71VP0;Vwtop;S4dS46Z10000M0Z0A2R5R4R3A9S51R6R3A2S0S2cS6bR9S75R8A3S2dA3S0S2cS60R9P1fM1A2S2dA3S0S2cS6eRaS4dS4eA3S2dA3Sa0G1S12RcA1A2S0S2cS6fS12RdA1S4dA2S2dA3S54Vcx;R8G0S61R9RdA2A4S3cS7S3fS7S50Vcx;R9RcRbA4RfRaA4VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;Flen;Frho;Fmat;Fvm;FrhoB;Fsh;FH;").
Proof using ELOOPK Hargc Hent Hinp.
  intros H sh rhoB vm mat rho len HS HB He Hid Htv Hn Hb HI.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (fromKx rhoB rho vm mat len H w HS HB Hw)) | intros w Hw; exact Hw |].
  apply (ereenter rho (KdR len) tv0 tvK (DG 65536 0) H K sh rho _ (ss_next H) He Hid Hn Hb Htv).
  apply (ELOOPK rho _ len). exact HI.
Qed.

Lemma eloopG_via : ltac2:(tb__ "0|2|
S16S62S11S63S2eS39Q40A1A1S11S92S7S71VP0;Vwtop;S4dS46Z10000M0Z0A2R4R3R2A9S51R5R2A2S0S2cS6bR8S76R7A3S2dA3S0S2cS60R8P1fM1A2S2dA3S0S2cS6eR9S4dS4eA3S2dA3Sa0G1S12RbA1A2S0S2cS6fS12RcA1S4dA2S2dA3S53Vcx;G0S61R8RcA2A3S3cS7S3fS7S50Vcx;G0RbRaA4ReR9A4VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;Frho;Fmat;Fvm;FrhoB;Fsg;FH;").
Proof using ELOOPG Hargc Hent Hinp.
  intros H sg rhoB vm mat rho HS HB He Hid Htv Hn Hb HI.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (fromKx rhoB rho vm mat 65536 H w HS HB Hw)) | intros w Hw; exact Hw |].
  apply (ereenter rho (KdR 65536) tv0 tvK (DG 65536 0) H KG sg rho _ (ss_next H) He Hid Hn Hb Htv).
  apply (ELOOPG rho _). exact HI.
Qed.

Section ETiny.
Variables (T Tr Tm H E1 P1 X1 : sstate) (sx : wsub) (xs : list xform).
Hypothesis T_objs : ltac2:(tb__ "0|0|
S1S0S32S1dA1S95S1dS23VT;A1U1A3S31S1dS1bS15S69A1S15Z0A1S13S72A1S30S1fA1S1aA5A2A3S1S0S6S12VT;A1S12VTr;A1A3S0S2eS14A1S17VTr;A1S17VT;A1A3A2A2").
Hypothesis T_next : ss_next T = 112%positive.
Hypothesis Tr_eq : ltac2:(tb__ "0|1|
S0S16S9aVT;U1S1bS15Z0A1S15S69A1M0S18S59S13S72A1G0A3S30S1fA1S1aA5A3VTr;A3").
Hypothesis xs_ok : ltac2:(tb__ "0|0|
S0S32S16A1Sa4VTr;Vxs;A2S31S16VTm;A2A3").
Hypothesis run_t : ltac2:(tb__ "0|1|
S0S32S2eS40A1M0A1S43S7S74S73VTm;S2dA5S31G0S2fS40S41VH;S42A2S30S40A1A3A2A3").
Hypothesis run_h : ltac2:(tb__ "0|1|
S0S32S2eS40A1M0A1S43S7S74S97S5S73A2VH;S2dA5S31G0S2fS40S41VE1;S44A2S30S40A1A3A2A3").
Hypothesis E1_shape : ltac2:(tb__ "0|0|
S1S0S5S27VE1;A1S6aA3S1S0S10S19VE1;Z11A2S15Z3fA1A3S1S0S10S19VE1;ZaA2S15Z3A1A3S1S0S10S19VE1;ZbA2S15S69A1A3S1S0S10S19VE1;ZcA2S18S5cS15Z10000A1S13S72A1A3A3S0S32S1dA1S95S1dS23VE1;A1S7eA3S31S1dS86A2A3A2A2A2A2A2").
Hypothesis cert_e1 : ltac2:(tb__ "0|0|
S0S32S5bA1S45S7S27VE1;A1A2S31S5bS5dA2A3").
Hypothesis diff_P1 : ltac2:(tb__ "0|4|
S0S32S35S2eS35S10S10A2M0A1M1S2eS14A1M2A2M3A1Sa3SaeVE1;S23VE1;A1A2VP1;A2S31G3S36G1G2S2fG0S36S10S10S13S12VE1;A1A1S15Z0A1A4S30G0A1A3S30S14A1A4A2A3").
Hypothesis swf_P1 : swf P1 = true.
Hypothesis run_p1 : ltac2:(tb__ "0|1|
S0S32S2eS40A1M0A1S43S7S74S73VP1;S2dA5S31G0S2fS40S41VX1;S42A2S30S40A1A3A2A3").
Hypothesis ent_x1 : ltac2:(tb__ "0|0|
S0S2cS6bVX1;S78Vsx;A3S2dA3").
Hypothesis sx_vals : ltac2:(tb__ "0|0|
S1S0S10S5eVsx;P64A2S13S72A1A3S1S0S10S5eVsx;P65A2S15Z10000A1A3S0S10S5eVsx;P66A2S13P29A1A3A2A2").
Hypothesis nexts : ltac2:(tb__ "0|1|
S1S0S6S12VE1;A1S12VTm;A1M0A3S1S0S6S12VH;A1G0A3S1S0S6S12VP1;A1G0A3S1S0S6G0S12VT;A1A3S1S0S2cS1eVTm;A1S34A3S1S0S2cS1eVH;A1S34A3S0S2cS1eVP1;A1S34A3A2A2A2A2A2A2").
Hypothesis X1_next : ss_next X1 = 112%positive.
Hypothesis idx : wsub_id_below sx 31 = true.
Hypothesis tvx : ltac2:(tb__ "0|0|
S0S2cS6eVsx;S4dS4eA3S2dA3").
Hypothesis wf_src : ltac2:(tb__ "0|1|
S0S2cS21S12VT;A1S1bS15Z0A1S15S69A1M0S18S59S13S72A1G0A3S30S1fA1S1aA5A2S2dA3").

Lemma etiny_tail : ltac2:(tb__ "0|1|
S11S63S2eS39Q40A1A1S11S92S7S71VP0;Vwtop;S4dS46Z10000Z0A2R4R3R2A9S51R5R2A2S1S8Z1ScS33S39Q8A1S58Vcx;A1A2A1M0A2S8G0Z3A2A2S0S5S4cR4S72A2G0A3S3cS7S3fS7S50Vcx;G0R7R6A4VT;R5A4VQ;A3F_;F_;F_;F_;Frho;Fmat;Fvm;FrhoB;").
Proof using E1_shape EXE0 T_next T_objs Tr_eq X1_next cert_e1 diff_P1 ent_x1 idx nexts run_h run_p1 run_t swf_P1 sx_vals tvx wf_src xs_ok Hargc Hent Hinp.
  intros rhoB vm mat rho HS HB HL U71. pose proof rs_range as RR. destruct nexts_0 as (_ & _ & _ & N71 & _).
  destruct T_objs as (To1 & NxTr & FTr). destruct nexts as (NxE & NxH & NxP & NxTm & LnTm & LnH & LnP). destruct sx_vals as (Sx0 & Sx1 & Sx2).
  unfold UV in U71. rewrite N71 in *.
  assert (E71 : bv_unsigned (eval rho (SVar 71)) = L) by exact U71.
  assert (Egr : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 71) (SLit rs))) = L + rs) by (apply (Uadd rho (SVar 71) (SLit rs) _ _ E71 (Ulit rho rs ltac:(lia))); lia).

  eapply etriple_conseq with (P := SP segs (KB L vm mat) Tr rho); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- Tr_eq. unfold SP.
    apply (SPJ_reshape segs _ rho T 1 _ (mkObj (SLit 0) (SLit rs) (SAlu ALU_ADD (SVar NX0) (SLit rs)) [] DUnknown) w To1 eq_refl eq_refl eq_refl wf_src); [|exact Hw].
    rewrite N71.
    intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite (Ulit rho 0), (Ulit rho rs) by lia.
    rewrite !soff_lit_small by lia. rewrite (soff_small rho _ _ Egr) by lia. rewrite (soff_small rho (SVar 71) L E71) by lia. lia. }
  eapply etriple_conseq; [intros w Hw; exact (SP_xforms segs _ xs rho Tr Tm w xs_ok Hw) | intros w Hw; exact Hw |].
  apply (erun_tr FUEL CUTS Tm _ _ rho _ run_t LnTm).
  intros Lf rho1 [<-|[]] Hag1; cbn [lf_state].
  apply (erun_tr FUEL (tl CUTS) H _ _ rho1 _ run_h LnH).
  intros Lf rho2 [<-|[]] Hag2; cbn [lf_state].
  destruct E1_shape as (Epc & E17 & E10 & E11 & E12 & EoI).
  assert (T71 : bv_unsigned (rw rho2 71) = L).
  { destruct Hag2 as (W2 & _), Hag1 as (W1 & _). rewrite <- W2, <- W1 by (rewrite ?NxH, ?NxTm, ?T_next; lia). exact U71. }

  eapply etriple_seq.
  { apply (ekread_rs E1 rho2 L (65536 - L) vm mat cert_e1 E17 E10 EoI E11); [|lia|lia].
    rewrite E12, CursorGlue.U_sub, CursorGlue.U_lit. cbn [eval]. rewrite T71. unfold M64v. rewrite (Z.mod_small 65536), Z.mod_small; lia. }
  pose proof (chunk_length L (65536 - L) ltac:(lia) ltac:(lia)) as CL.
  assert (Z0 : length (chunk L (65536 - L)) = 0%nat) by lia.
  replace (L + Z.of_nat (length (chunk L (65536 - L)))) with L by lia.
  set (rho3 := rho_set_rw rho2 (ss_next E1) (len_word (chunk L (65536 - L)))).
  eapply etriple_conseq with (P := SP segs (KB L vm mat) P1 rho3); [intros w Hw; apply (SP_restate segs (KB L vm mat) rho3 _ P1 w _ _ swf_P1 diff_P1); [| constructor | exact Hw] | intros w Hw; exact Hw |].
  { constructor; [|constructor]. cbn [fst snd eval]. subst rho3. rewrite rho_set_rw_at, (len_word_zero _ Z0). apply bv_eq. reflexivity. }
  apply (erun_tr FUEL CUTS P1 _ _ rho3 _ run_p1 LnP).
  intros Lf rho4 [<-|[]] Hag4; cbn [lf_state].
  assert (HB4 : BR rhoB rho4).
  { apply (BR_agree rhoB rho3 rho4 _ ltac:(subst rho3; apply BR_set_rw; [|rewrite NxE, NxTm, T_next; lia]; eapply (BR_agree rhoB rho1); [eapply (BR_agree rhoB rho); [exact HB | exact Hag1 | rewrite NxTm, T_next; lia] | exact Hag2 | rewrite NxH, NxTm, T_next; lia]) Hag4).
    rewrite NxP, NxTm, T_next. lia. }
  apply (eexit0_via X1 sx rhoB vm mat rho4 HS HB4 ent_x1 idx tvx ltac:(rewrite X1_next; lia) ltac:(rewrite X1_next; apply tvb_0; lia)); [| |lia].
  - unfold UV. cbn [rho_sub rw]. rewrite Sx0. cbn [eval]. destruct Hag4 as (W4 & _). rewrite <- W4 by (rewrite NxP, NxTm, T_next; lia).
    subst rho3. rewrite rho_set_rw_other by (rewrite NxE, NxTm, T_next; lia). exact T71.
  - unfold UV. cbn [rho_sub rw]. rewrite Sx1. apply Ulit. lia.
Qed.
End ETiny.

Lemma Usubk : ltac2:(tb__ "0|1|
S11S10S5S5S0S5S3aQ40M0S24R4R3A2A2R2A3S1S8Z0R2A2S8R2R3A2A2SeR4SdZ2Z40A2A2S0S5S3aG0S24R7S18S59R6S15SfR4A1A1A3A2A2SaR5R4A2A3F_;F_;F_;Fk;Fx;Fa;Frho;").
Proof using .
  clear. intros rho a x k Hx Hk Hx'. rewrite CursorGlue.U_add, Hx, CursorGlue.U_lit. unfold M64v.
  Z.to_euclidean_division_equations; nia.
Qed.

Section EHdrPost.
Variables (CX T Tp Tm H : sstate) (IMP : sstate) (es : list sv) (xs : list xform).
Hypothesis T_eq : ltac2:(tb__ "0|0|
S0S16S99S17VCX;A1VIMP;A2VT;A3").
Hypothesis fbT : ltac2:(tb__ "0|0|
S0S2cS96S14S22S12VIMP;A1A1S17VCX;A1A3S2dA3").
Hypothesis Tp_eq : ltac2:(tb__ "0|0|
S0S32S16A1SabVT;U0S15Z0A1A3S31S16VTp;A2A3").
Hypothesis ES_eq : ltac2:(tb__ "0|1|
S0S32S2eS10A1M0A1SacVT;U0S15Z0A1A3S31G0Ves;A2A3").
Hypothesis xs_ok : ltac2:(tb__ "0|1|
S0S32S16A1M0G0G0Lx;Sa4VTp;Vxs;A2S16S31S16SaaR1S7eA2A2LX;S37S16A1X32x2S31S16VTm;A2A3").
Hypothesis run_t : ltac2:(tb__ "0|1|
S0S32S2eS40A1M0A1S43S7S74S73VTm;S2dA5S31G0S2fS40S41VH;S42A2S30S40A1A3A2A3").
Hypothesis nexts : ltac2:(tb__ "0|1|
S1S0S6S12VTp;A1M0Sa2S12VT;A1A1A3S1S0S6S12VTm;A1G0A3S1S0S6S12VH;A1G0A3S1S0S2cS1eVTm;A1S34A3S0S2eS14A1S17VTp;A1S17VT;A1A3A2A2A2A2").
Hypothesis T_next : (72 <= ss_next T)%positive.
Hypothesis es_hdr : ltac2:(tb__ "0|1|
S11Sa8U4S33S39Q8A1S25R1P5M0A2A2A2S0S39Q40A1SadR2Ves;A2SafS25R2G0A2A1A3F_;Frho;").

Lemma ehdr_post : ltac2:(tb__ "0|5|
S11S63S2eS39Q40A1M0A1S11S5S2eS39Q8A1M1A1M2S51R6R3A2Sa9S14S2aR4A1S17VCX;A1A3S0G2S25R5P5A2S38G1S56Vcx;Z0Z10000A3M3R3A3A3S8Z4R5A2S0S5R6ScS33G1G3A2A1A3S11S51RcR1A2S6Sa1R1S12VT;A1M4A2S0G0S1cR4R2A2S1cRcR2A2A3F_;Fi;S52Vcx;S1cR3G4A2A2S3cS7S3fS7S50Vcx;RbReRdA4VH;R4A4VQ;A3F_;F_;F_;Frho';S3cS7S3fS7S50Vcx;R8RbRaA4VIMP;R9A4VQ;A3F_;F_;F_;F_;F_;F_;Frest;Fgot;Frho;Fmat;Fvm;FrhoB;").
Proof using ES_eq T_eq T_next Tp_eq es_hdr fbT nexts run_t xs_ok.
  intros rhoB vm mat rho got rest HB HFC HL5 H4 Hgot FIN. destruct nexts as (NxTp & NxTm & NxH & LnTm & FTp).

  eapply etriple_conseq with (P := SP segs (KB got vm mat) T rho); [| intros w Hw; exact Hw |].
  { intros w [Hsm Hk]. split; [|exact Hk]. rewrite <- T_eq. apply smatch_add_facts; [exact Hsm | exact HFC | exact fbT]. }

  eapply etriple_conseq with (P := SP segs (KB got vm mat) Tp (pack4_rho rho T es)); [| intros w Hw; exact Hw |].
  { intros w Hw. unfold SP. apply (SPJ_pack4 segs _ rho T 0 (SLit 0) Tp es w Tp_eq ES_eq); [apply stableJ_liftK | exact Hw]. }
  assert (HX : rw (pack4_rho rho T es) (ss_next T) = hdr_val (rl rho 5)).
  { rewrite pack4_rho_nx. apply es_hdr. rewrite HL5, length_app. pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)). lia. }

  destruct (apply_xforms Tp xs) as [X|] eqn:EX; [|discriminate]. injection xs_ok as EM.
  eapply etriple_conseq; [intros w Hw; exact (SP_xforms segs _ xs _ Tp X w EX Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact (SP_obj_forget segs _ _ X IRS w Hw) | intros w Hw; exact Hw |]. rewrite EM.
  apply (erun_tr FUEL CUTS Tm _ _ _ _ run_t LnTm).
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
End EHdrPost.

Lemma es_t : ltac2:(tb__ "0|1|
S1S0S2eS10A1M0S7dS2fS10S6cZ0A1S2fS10S6cZ1A1S2fS10S6cZ2A1S2fS10S6cZ3A1S30S10A1A3A3A3A3A3S0G0S85S7dA3A2").
Proof using . split; reflexivity. Qed.
Lemma es_c : ltac2:(tb__ "0|1|
S1S0S2eS10A1M0S77S2fS10S6cZ0A1S2fS10S6cZ1A1S2fS10S6cZ2A1S2fS10S6dS30S10A1A3A3A3A3A3S1S0G0S84S77A3S1S0G0S82S77A3S0G0S83S77A3A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma fbT_0 : ltac2:(tb__ "0|5|
S1S0S2cS96S14S22S12S8fA1M0A1S17S7cA1A3S2dA3S1S0S2cS96S14S22S12S8dA1M1A1S17S7bA1A3S2dA3S1S0S2cS96S14S22S12S8bA1M2A1S17S7aA1A3S2dA3S1S0S6G0P70M3A3S1S0S6S12S90A1G3A3S1S0S6G1G3A3S1S0S6S12S8eA1G3A3S1S0S6G2G3A3S1S0S6S12S8cA1G3A3S1S0S6S12S7cA1P48M4A3S1S0S6S12S7bA1G4A3S1S0S6S12S7aA1G4A3S0S6S12S80A1G4A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma lenient_0h : ltac2:(tb__ "0|0|
S1S0S2cS1eS8aA1S34A3S1S0S2cS1eS89A1S34A3S0S2cS1eS80A1S34A3A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma wf_src0t : ltac2:(tb__ "0|1|
S1S0S2cS21P70S1bS15Z0A1S15S69A1M0S18S59S13S72A1G0A3S30S1fA1S1aA5A2S2dA3S0S2cS21P48S87A2S2dA3A2").
Proof using . split; reflexivity. Qed.

Lemma estep0 : ltac2:(tb__ "0|0|
S11S11S3cS7S3eS7VJD;VKd0;R2S4dSa5VX0;A1A4Sa6R1A4VQ;A3Frho;Fr0;").
Proof using ELOOPG ELOOPK EXE0 Hargc Hent Hinp.
  intros r0 rho.
  destruct nexts_0 as (nTok & _ & nK0 & nNX & nR0 & nR00 & nX00 & nR0t & nC0t & nCx0t & nT0ta & nT0tb & nX1ta & nX1tb).
  destruct lenient_0 as (lenTok & lenK0 & lenR00 & lenR0t & lenP1ta & lenP1tb).
  eapply (erun_trJ segs FUEL [loop_read] T_ok _ _ rho _ run_tok lenTok).
  { rewrite nTok. apply JD_stable; [lia | apply tvb_0; lia]. }
  rewrite nTok. intros leafK rho1 inK _. destruct inK as [<-|[]]. cbn [lf_state].
  eapply etriple_conseq with (P := SPJ segs (JD (KdR 0) r0 tv0 (DG 65536 0)) K0 rho1); [| intros w fin; exact fin |].
  { intros w atR. pose proof (SPJ_xforms segs _ xs_k0 rho1 K0r K0 w xs_k0_ok atR) as [matchK jK].
    split; [exact matchK|].
    refine (JD_monoK r0 Kd0 (KdR 0) tv0 (DG 65536 0) rho1 _ _ (fun t m kd => proj1 (Kd0_KdR t m) kd) _).
    refine (JGD_mono segs C_U 31 Kd0 r0 P0 tv0 (Dok X0) (DG 65536 0) rho1 _ _ _ jK).
    intros A md dok. exact (proj2 (DG0 A md) (proj1 (DX0 A md) dok)). }
  intros w preK. destruct (toKx r0 rho1 w preK) as (vm & mat & snap & atK0). clear preK. revert w atK0.
  change (etriple segs (SP segs (KB 0 vm mat) K0 rho1) Q).
  apply (erun_tr FUEL [] K0 _ _ rho1 _ run_k0 lenK0).
  rewrite nK0. intros leafE rho2 inE agree2. destruct inE as [<-|[]]. cbn [lf_state].
  pose proof (BR_agree rho1 rho1 rho2 71 (BR_refl rho1) agree2 ltac:(lia)) as br2.
  destruct E_rd0_shape as (_ & _ & _ & _ & _ & _ & _ & imgObj & _).
  eapply etriple_conseq;
    [intros w atI; exact (SPJ_img_to_list segs (liftK (KB 0 vm mat)) rho2 E_rd0i IRS 7 E_rd0 _ w E_rd0_eq imgObj
                            (fun tr md (kb : liftK (KB 0 vm mat) rho2 tr md) => (kb : KB 0 vm mat tr md)) atI)
    | intros w fin; exact fin |].
  eapply etriple_seq; [exact (ekread_list _ vm mat) |].
  match goal with |- etriple _ (SP _ _ R0 ?r) _ => remember r as rho4 eqn:rho4Def end.
  assert (br4 : BR rho1 rho4)
    by (subst rho4; apply BR_set_rw; [apply BR_set_rl, BR_set_rl; exact br2 | rewrite nNX; lia]).
  assert (gotVal : bv_unsigned (rw rho4 NX0) = Z.of_nat (length (chunk 0 65536))).
  { subst rho4. rewrite rho_set_rw_at. unfold len_word. apply Z_to_bv_small. rewrite two64.
    pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)). lia. }
  assert (rl5 : exists rest, rl rho4 5 = chunk 0 65536 ++ rest).
  { assert (rlOfRw : forall (r : valuation) (n : positive) (v : word), rl (rho_set_rw r n v) = rl r) by reflexivity.
    subst rho4. eexists. rewrite rlOfRw. apply rho_set_rl_at. }
  clear rho4Def. destruct rl5 as (rest & rl5).
  pose proof (chunk_length 0 65536 ltac:(lia) ltac:(lia)) as chunkLen.
  set (got := Z.of_nat (length (chunk 0 65536))) in *.
  pose proof rs_range as rsBox.
  assert (toLoopK : forall (St : sstate) (sh : wsub) (rho' : valuation),
            entails St K sh = true -> wsub_id_below sh 31 = true -> tv_sub_eqb sh tv0 tvK = true ->
            ss_next St = 113%positive ->
            wsub_get sh 100 = SVar NX0 -> wsub_get sh 101 = SLit 65536 -> wsub_get sh 103 = SVar 112 ->
            BR rho1 rho' -> bv_unsigned (rw rho' NX0) = got -> HDR (rw rho' 112) -> 4 <= got < 65536 -> got = L ->
            etriple segs (SP segs (KB got vm mat) St rho') Q).
  { intros St sh rho' entSt idSt tvSt nSt s100 s101 s103 brSt gotSt hdrSt gotBox gotL.
    refine (eloopK_via St sh rho1 vm mat rho' got snap brSt entSt idSt tvSt ltac:(rewrite nSt; lia)
              ltac:(rewrite nSt; apply tvb_0; lia) _).
    unfold INVK, UV. cbn [rho_sub rw]. rewrite s100, s101, s103, (Ulit rho' 65536) by lia. cbn [eval].
    rewrite gotSt.
    refine (conj eq_refl (conj eq_refl (conj hdrSt (conj gotBox (conj _ (conj (or_intror gotL) CAP_init)))))). lia. }
  assert (toLoopG : forall (St : sstate) (sg : wsub) (rho' : valuation),
            entails St KG sg = true -> wsub_id_below sg 31 = true -> tv_sub_eqb sg tv0 tvK = true ->
            ss_next St = 113%positive -> wsub_get sg 101 = SLit 65536 -> wsub_get sg 103 = SVar 112 ->
            BR rho1 rho' -> HDR (rw rho' 112) -> 65536 <= L ->
            etriple segs (SP segs (KB 65536 vm mat) St rho') Q).
  { intros St sg rho' entSt idSt tvSt nSt s101 s103 brSt hdrSt lBig.
    refine (eloopG_via St sg rho1 vm mat rho' snap brSt entSt idSt tvSt ltac:(rewrite nSt; lia)
              ltac:(rewrite nSt; apply tvb_0; lia) _).
    unfold INVG, UV. cbn [rho_sub rw]. rewrite s101, s103, (Ulit rho' 65536) by lia. cbn [eval].
    exact (conj eq_refl (conj hdrSt (conj lBig CAP_init))). }
  destruct (Z.eq_dec got 0) as [gotZero|gotPos].
  { assert (lZero : L = 0) by lia.
    eapply etriple_conseq with (P := SP segs (KB got vm mat) R00 rho4); [| intros w fin; exact fin |].
    { intros w atR. refine (SP_restate segs _ rho4 R0 R00 w _ _ swf_R00 diff_R00 _ (Forall_nil _) atR).
      apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. apply bv_eq.
      rewrite (Ulit rho4 0) by lia. cbn [eval]. rewrite gotVal. exact gotZero. }
    apply (erun_tr FUEL CUTS R00 _ _ rho4 _ run_p00 lenR00).
    rewrite nR00. intros leafX rho5 inX agree5. destruct inX as [<-|[]]. cbn [lf_state].
    pose proof (BR_agree rho1 rho4 rho5 72 br4 agree5 ltac:(lia)) as br5.
    destruct s_x00_vals as (x100 & x101 & _).
    destruct ids_0 as (id00 & _). destruct tvs_0 as (tv00 & _).
    replace got with L by lia.
    refine (eexit0_via X00 s_x00 rho1 vm mat rho5 snap br5 ent_x00 id00 tv00 _ _ _ _ _).
    - rewrite nX00. lia.
    - rewrite nX00. apply tvb_0. lia.
    - unfold UV. cbn [rho_sub rw]. rewrite x100, (Ulit rho5 0) by lia. lia.
    - unfold UV. cbn [rho_sub rw]. rewrite x101. apply Ulit. lia.
    - lia. }
  destruct (Z_lt_le_dec got 4) as [gotTiny|gotBig].
  { assert (lEq : got = L) by lia.
    destruct fb_0 as (fb0t & _ & _).
    eapply etriple_conseq with (P := SP segs (KB got vm mat) R0t rho4); [| intros w fin; exact fin |].
    { intros w atR. rewrite <- R0t_eq. apply SP_obj_forget.
      refine (SPJ_add_facts segs (liftK (KB got vm mat)) rho4 F_0t R0 w atR _ fb0t).
      unfold F_0t. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - apply holds_nbeq. rewrite (Ulit rho4 0) by lia. cbn [eval]. lia.
      - apply holds_ult. rewrite (Ulit rho4 4) by lia. cbn [eval]. lia. }
    apply (erun_tr FUEL CUTS R0t _ _ rho4 _ run_p0t lenR0t).
    rewrite nR0t. intros leafC rho5 inC agree5. destruct inC as [<-|[]]. cbn [lf_state].
    pose proof (BR_agree rho1 rho4 rho5 72 br4 agree5 ltac:(lia)) as br5.
    destruct agree5 as (keep5 & _ & _).
    assert (g5 : bv_unsigned (rw rho5 NX0) = got) by (rewrite <- keep5 by (rewrite nNX; lia); exact gotVal).
    eapply etriple_conseq;
      [intros w atC; exact (SPJ_xforms segs _ xs_0t rho5 C_0t Cx_0t w xs_0t_ok atC) | intros w fin; exact fin |].
    destruct Cr_0t_pre as (cxObj & _ & crNext).
    destruct wf_src0t as (wfT & wfSrc0).
    eapply etriple_conseq with (P := SP segs (KB got vm mat) Cr_0t rho5); [| intros w fin; exact fin |].
    { intros w atCx. rewrite <- Cr_0t_eq.
      refine (SPJ_reshape segs _ rho5 Cx_0t (IRS + 1) _ O_src0t w cxObj eq_refl eq_refl eq_refl _ _ atCx).
      { rewrite nCx0t. exact wfSrc0. }
      intros _. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_src0t].
      assert (hiSum : bv_unsigned (eval rho5 (SAlu ALU_ADD (SVar NX0) (SLit rs))) = got + rs)
        by (apply Uadd; [exact g5 | apply Ulit; lia | lia | lia | lia]).
      rewrite (soff_small rho5 _ _ hiSum) by lia. rewrite (soff_small rho5 (SVar NX0) got g5) by lia.
      rewrite (Ulit rho5 rs), (Ulit rho5 0) by lia. rewrite !soff_lit_small by lia. lia. }
    apply (call_complete_keep segs (KB got vm mat) (KB got vm mat) Cr_0t PreG s_c0t R_c0t Posts_memcpy Q rho5
             efr_c0t chk_c0t fb_c0t).
    { intros rho6. exact (memcpy_sum_ex _ rho6). }
    intros leafT rho6 inT agree6. rewrite crNext, nC0t in agree6.
    pose proof (BR_agree rho1 rho5 rho6 72 br5 agree6 ltac:(lia)) as br6.
    destruct agree6 as (keep6 & _ & _).
    assert (g6 : UV rho6 NX0 = L) by (unfold UV; rewrite <- keep6 by (rewrite nNX; lia); lia).
    destruct ids_0 as (_ & id1ta & id1tb & _). destruct tvs_0 as (_ & tv1ta & tv1tb & _).
    cbn [Posts_memcpy MuslMemcpy.Posts_memcpy In] in inT.
    rewrite lEq.
    destruct inT as [<-|[<-|[]]]; cbn [lf_state].
    - rewrite T0ta_eq.
      exact (etiny_tail T0ta Tr0ta Tm0ta H0ta E1ta P1ta X1ta s_x1ta xs_0ta T0ta_objs nT0ta Tr0ta_eq xs_0ta_ok run_t0ta
               run_h0ta E1ta_shape cert_rd1ta diff_P1ta swf_P1ta run_p1ta ent_x1ta s_x1ta_vals E1ta_next nX1ta id1ta tv1ta
               ltac:(rewrite nT0ta; exact wfT) rho1 vm mat rho6 snap br6 ltac:(lia) g6).
    - rewrite T0tb_eq.
      exact (etiny_tail T0tb Tr0tb Tm0tb H0tb E1tb P1tb X1tb s_x1tb xs_0tb T0tb_objs nT0tb Tr0tb_eq xs_0tb_ok run_t0tb
               run_h0tb E1tb_shape cert_rd1tb diff_P1tb swf_P1tb run_p1tb ent_x1tb s_x1tb_vals E1tb_next nX1tb id1tb tv1tb
               ltac:(rewrite nT0tb; exact wfT) rho1 vm mat rho6 snap br6 ltac:(lia) g6). }
  destruct (Z.eq_dec got 65536) as [gotFull|gotPart].
  { assert (lBig : 65536 <= L) by lia.
    destruct lenient_0h as (_ & _ & lenR0g).
    destruct fbT_0 as (_ & _ & _ & _ & _ & _ & _ & nT0gA & nT0gB & _ & _ & nCx0g & nR0g).
    eapply etriple_conseq with (P := SP segs (KB got vm mat) R0g rho4); [| intros w fin; exact fin |].
    { intros w atR. refine (SP_restate segs _ rho4 R0 R0g w _ _ swf_R0g diff_R0g _ (Forall_nil _) atR).
      apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. apply bv_eq.
      rewrite (Ulit rho4 65536) by lia. cbn [eval]. rewrite gotVal. exact gotFull. }
    apply (erun_tr FUEL CUTS R0g _ _ rho4 _ run_p0g lenR0g).
    rewrite nR0g. intros leafC rho5 inC agree5. destruct inC as [<-|[]]. cbn [lf_state].
    pose proof (BR_agree rho1 rho4 rho5 72 br4 agree5 ltac:(lia)) as br5.
    destruct agree5 as (_ & rlKeep5 & _).
    apply (ecall_path segs (fun _ => True) (KB got vm mat) (KB got vm mat) C_0g Cx_0g PreRg [XSplit 1 (SLit 65536)]
             s_c0g R_c0g Posts_rsB Q rho5 xs_0g_ok efr_c0g chk_c0g).
    { vm_compute. reflexivity. }
    { intros rho6 _. exact (memcpy_rsB_sum_ex _ rho6). }
    { intros ms _. exact I. }
    intros leafT rho6 inT agree6 factsC. rewrite nCx0g in agree6.
    pose proof (BR_agree rho1 rho5 rho6 72 br5 agree6 ltac:(lia)) as br6.
    destruct agree6 as (_ & rlKeep6 & _).
    assert (factsCx : Forall (holds rho6) (ss_facts Cx_0g)).
    { replace (ss_facts Cx_0g) with (ss_facts C_0g) by (vm_compute; reflexivity). exact factsC. }
    assert (rl6 : rl rho6 5 = chunk 0 65536 ++ rest) by (rewrite <- rlKeep6, <- rlKeep5; exact rl5).
    destruct ids_0 as (_ & _ & _ & _ & _ & _ & _ & idGa & idGb). destruct tvs_0 as (_ & _ & _ & _ & _ & _ & _ & tvGa & tvGb).
    destruct s_h0gA_vals as (ga101 & _ & ga103). destruct s_h0gB_vals as (gb101 & _ & gb103).
    destruct es_c as (esMA & _ & esGA & esGB).
    rewrite Posts_rsB_eq in inT. destruct inT as [<-|[<-|[]]]; cbn [lf_state].
    - refine (ehdr_post Cx_0g T0gA Tp0gA Tm0gA H0gA (import_post s_c0g (ss_next PreRg) P_rsA_c (ss_next Cx_0g) R_c0g)
                ES0gA xs_0gA T0gA_eq ltac:(vm_compute; reflexivity) Tp0gA_eq ES0gA_eq xs_0gA_ok run_t0gA T0gA_nexts
                ltac:(rewrite nT0gA; lia) _ rho1 vm mat rho6 got rest br6 factsCx rl6 ltac:(lia) eq_refl _).
      + intros r lenOk. rewrite esGA, esMA. exact (pack4_hdr_c r lenOk).
      + intros rho7 br7 _ hdr7. rewrite nT0gA in hdr7. rewrite gotFull.
        refine (toLoopG H0gA s_h0gA rho7 ent_h0gA idGa tvGa ltac:(vm_compute; reflexivity) ga101 _ br7 hdr7 lBig).
        rewrite ga103. vm_compute. reflexivity.
    - refine (ehdr_post Cx_0g T0gB Tp0gB Tm0gB H0gB (import_post s_c0g (ss_next PreRg) P_rsB_c (ss_next Cx_0g) R_c0g)
                ES0gB xs_0gB T0gB_eq ltac:(vm_compute; reflexivity) Tp0gB_eq ES0gB_eq xs_0gB_ok run_t0gB T0gB_nexts
                ltac:(rewrite nT0gB; lia) _ rho1 vm mat rho6 got rest br6 factsCx rl6 ltac:(lia) eq_refl _).
      + intros r lenOk. rewrite esGB, esMA. exact (pack4_hdr_c r lenOk).
      + intros rho7 br7 _ hdr7. rewrite nT0gB in hdr7. rewrite gotFull.
        refine (toLoopG H0gB s_h0gB rho7 ent_h0gB idGb tvGb ltac:(vm_compute; reflexivity) gb101 _ br7 hdr7 lBig).
        rewrite gb103. vm_compute. reflexivity. }
  assert (lEq : got = L) by lia.
  assert (gotBox : 4 <= got < 65536) by lia.
  destruct fbT_0 as (_ & _ & _ & nT0sA & nT0sB & nT0mA & nT0mB & _ & _ & nCx0s & nCx0m & _ & _).
  destruct lenient_0h as (lenR0s & lenR0m & _).
  destruct fb_0 as (_ & fb0s & fb0m).
  destruct ids_0 as (_ & _ & _ & idSa & idSb & idMa & idMb & _). destruct tvs_0 as (_ & _ & _ & tvSa & tvSb & tvMa & tvMb & _).
  assert (sub3 : bv_unsigned (eval rho4 (SAlu ALU_ADD (SVar NX0) (SLit (-3)))) = got - 3)
    by exact (Usubk rho4 (SVar NX0) got 3 gotVal ltac:(lia) ltac:(lia)).
  destruct (Z_lt_le_dec got 35) as [gotS|gotM].
  { eapply etriple_conseq with (P := SP segs (KB got vm mat) R0s rho4); [| intros w fin; exact fin |].
    { intros w atR. rewrite <- R0s_eq.
      refine (SPJ_add_facts segs (liftK (KB got vm mat)) rho4 F_0s R0 w atR _ fb0s).
      unfold F_0s. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      - apply holds_ule. rewrite (Ulit rho4 4) by lia. cbn [eval]. lia.
      - apply holds_bltu. rewrite sub3, (Ulit rho4 32) by lia. lia.
      - apply holds_ult. rewrite (Ulit rho4 65536) by lia. cbn [eval]. lia. }
    apply (erun_tr FUEL CUTS R0s _ _ rho4 _ run_p0s lenR0s).
    replace (ss_next R0s) with 72%positive by (vm_compute; reflexivity).
    intros leafC rho5 inC agree5. destruct inC as [<-|[]]. cbn [lf_state].
    pose proof (BR_agree rho1 rho4 rho5 72 br4 agree5 ltac:(lia)) as br5.
    destruct agree5 as (keep5 & rlKeep5 & _).
    apply (ecall_path segs (fun _ => True) (KB got vm mat) (KB got vm mat) C_0s Cx_0s PreRs [XSplit 1 (SVar NX0)]
             s_c0s R_c0s Posts_rsS Q rho5 xs_0s_ok efr_c0s chk_c0s).
    { vm_compute. reflexivity. }
    { intros rho6 _. exact (memcpy_rsS_sum_ex _ rho6). }
    { intros ms _. exact I. }
    intros leafT rho6 inT agree6 factsC. rewrite nCx0s in agree6.
    pose proof (BR_agree rho1 rho5 rho6 72 br5 agree6 ltac:(lia)) as br6.
    destruct agree6 as (keep6 & rlKeep6 & _).
    assert (factsCx : Forall (holds rho6) (ss_facts Cx_0s)).
    { replace (ss_facts Cx_0s) with (ss_facts C_0s) by (vm_compute; reflexivity). exact factsC. }
    assert (rl6 : rl rho6 5 = chunk 0 65536 ++ rest) by (rewrite <- rlKeep6, <- rlKeep5; exact rl5).
    assert (g6 : bv_unsigned (rw rho6 NX0) = got)
      by (rewrite <- keep6, <- keep5 by (rewrite nNX; lia); exact gotVal).
    destruct s_h0sA_vals as (sa100 & sa101 & _ & sa103). destruct s_h0sB_vals as (sb100 & sb101 & _ & sb103).
    destruct es_t as (esSA & esSB).
    rewrite Posts_rsS_eq in inT. destruct inT as [<-|[<-|[<-|[]]]]; cbn [lf_state].
    - refine (ehdr_post Cx_0s T0sA Tp0sA Tm0sA H0sA (import_post s_c0s (ss_next PreRs) P_rsA_t (ss_next Cx_0s) R_c0s)
                ES0sA xs_0sA T0sA_eq ltac:(vm_compute; reflexivity) Tp0sA_eq ES0sA_eq xs_0sA_ok run_t0sA T0sA_nexts
                ltac:(rewrite nT0sA; lia) _ rho1 vm mat rho6 got rest br6 factsCx rl6 ltac:(lia) eq_refl _).
      + intros r lenOk. rewrite esSA. exact (pack4_hdr_t r lenOk).
      + intros rho7 br7 keep7 hdr7. rewrite nT0sA in keep7, hdr7.
        refine (toLoopK H0sA s_h0sA rho7 ent_h0sA idSa tvSa ltac:(vm_compute; reflexivity) sa100 sa101 _ br7 _ hdr7
                  gotBox lEq).
        * rewrite sa103. vm_compute. reflexivity.
        * rewrite keep7 by (rewrite nNX; lia). exact g6.
    - refine (ehdr_post Cx_0s T0sB Tp0sB Tm0sB H0sB (import_post s_c0s (ss_next PreRs) P_rsB_t (ss_next Cx_0s) R_c0s)
                ES0sB xs_0sB T0sB_eq ltac:(vm_compute; reflexivity) Tp0sB_eq ES0sB_eq xs_0sB_ok run_t0sB T0sB_nexts
                ltac:(rewrite nT0sB; lia) _ rho1 vm mat rho6 got rest br6 factsCx rl6 ltac:(lia) eq_refl _).
      + intros r lenOk. rewrite esSB, esSA. exact (pack4_hdr_t r lenOk).
      + intros rho7 br7 keep7 hdr7. rewrite nT0sB in keep7, hdr7.
        refine (toLoopK H0sB s_h0sB rho7 ent_h0sB idSb tvSb ltac:(vm_compute; reflexivity) sb100 sb101 _ br7 _ hdr7
                  gotBox lEq).
        * rewrite sb103. vm_compute. reflexivity.
        * rewrite keep7 by (rewrite nNX; lia). exact g6.
    - rewrite T0sZ_eq. apply etriple_factsJ. intros zFacts. exfalso.
      assert (zHold : Forall (holds rho6) F_zs).
      { apply Forall_forall. intros f fIn.
        exact (holds_of_existsb rho6 (ss_facts T0sZ) f zFacts (proj1 (forallb_forall _ _) T0sZ_fz f fIn)). }
      assert (sub6 : bv_unsigned (eval rho6 (SAlu ALU_ADD (SVar NX0) (SLit (-3)))) = got - 3)
        by exact (Usubk rho6 (SVar NX0) got 3 g6 ltac:(lia) ltac:(lia)).
      assert (bitAt : forall k, 0 <= k < 2 ^ 64 ->
                bv_unsigned (eval rho6 (SAlu ALU_AND (SAlu ALU_ADD (SVar NX0) (SLit (-3))) (SLit k))) = Z.land (got - 3) k).
      { intros k kBox. change (eval rho6 (SAlu ALU_AND ?a ?b)) with (alu64 ALU_AND (eval rho6 a) (eval rho6 b)).
        rewrite and_val, sub6, (Ulit rho6 k) by exact kBox. reflexivity. }
      unfold F_zs in zHold. rewrite !Forall_cons_iff in zHold.
      destruct zHold as (bit1 & bit2 & bit4 & bit8 & small & _).
      apply holds_nbne in bit1, bit2, bit4, bit8. apply holds_nbgeu in small.
      rewrite bitAt, (Ulit rho6 0) in bit1, bit2, bit4, bit8 by lia.
      rewrite sub6, (Ulit rho6 16) in small by lia.
      destruct (Z_of_nat_complete (got - 3) ltac:(lia)) as (n & asNat).
      rewrite asNat in bit1, bit2, bit4, bit8, small.
      do 16 (destruct n as [|n]; [vm_compute in bit1, bit2, bit4, bit8; first [congruence | lia] |]).
      lia. }
  eapply etriple_conseq with (P := SP segs (KB got vm mat) R0m rho4); [| intros w fin; exact fin |].
  { intros w atR. rewrite <- R0m_eq.
    refine (SPJ_add_facts segs (liftK (KB got vm mat)) rho4 F_0m R0 w atR _ fb0m).
    unfold F_0m. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    - apply holds_ule. rewrite (Ulit rho4 4) by lia. cbn [eval]. lia.
    - apply holds_nbltu. rewrite sub3, (Ulit rho4 32) by lia. lia.
    - apply holds_ult. rewrite (Ulit rho4 65536) by lia. cbn [eval]. lia. }
  apply (erun_tr FUEL CUTS R0m _ _ rho4 _ run_p0m lenR0m).
  replace (ss_next R0m) with 72%positive by (vm_compute; reflexivity).
  intros leafC rho5 inC agree5. destruct inC as [<-|[]]. cbn [lf_state].
  pose proof (BR_agree rho1 rho4 rho5 72 br4 agree5 ltac:(lia)) as br5.
  destruct agree5 as (keep5 & rlKeep5 & _).
  apply (ecall_path segs (fun _ => True) (KB got vm mat) (KB got vm mat) C_0m Cx_0m PreRm [XSplit 1 (SVar NX0)]
           s_c0m R_c0m Posts_rsB Q rho5 xs_0m_ok efr_c0m chk_c0m).
  { vm_compute. reflexivity. }
  { intros rho6 _. exact (memcpy_rsB_sum_ex _ rho6). }
  { intros ms _. exact I. }
  intros leafT rho6 inT agree6 factsC. rewrite nCx0m in agree6.
  pose proof (BR_agree rho1 rho5 rho6 72 br5 agree6 ltac:(lia)) as br6.
  destruct agree6 as (keep6 & rlKeep6 & _).
  assert (factsCx : Forall (holds rho6) (ss_facts Cx_0m)).
  { replace (ss_facts Cx_0m) with (ss_facts C_0m) by (vm_compute; reflexivity). exact factsC. }
  assert (rl6 : rl rho6 5 = chunk 0 65536 ++ rest) by (rewrite <- rlKeep6, <- rlKeep5; exact rl5).
  assert (g6 : bv_unsigned (rw rho6 NX0) = got)
    by (rewrite <- keep6, <- keep5 by (rewrite nNX; lia); exact gotVal).
  destruct s_h0mA_vals as (ma100 & ma101 & _ & ma103). destruct s_h0mB_vals as (mb100 & mb101 & _ & mb103).
  destruct es_c as (esMA & esMB & _ & _).
  rewrite Posts_rsB_eq in inT. destruct inT as [<-|[<-|[]]]; cbn [lf_state].
  - refine (ehdr_post Cx_0m T0mA Tp0mA Tm0mA H0mA (import_post s_c0m (ss_next PreRm) P_rsA_c (ss_next Cx_0m) R_c0m)
              ES0mA xs_0mA T0mA_eq ltac:(vm_compute; reflexivity) Tp0mA_eq ES0mA_eq xs_0mA_ok run_t0mA T0mA_nexts
              ltac:(rewrite nT0mA; lia) _ rho1 vm mat rho6 got rest br6 factsCx rl6 ltac:(lia) eq_refl _).
    + intros r lenOk. rewrite esMA. exact (pack4_hdr_c r lenOk).
    + intros rho7 br7 keep7 hdr7. rewrite nT0mA in keep7, hdr7.
      refine (toLoopK H0mA s_h0mA rho7 ent_h0mA idMa tvMa ltac:(vm_compute; reflexivity) ma100 ma101 _ br7 _ hdr7
                gotBox lEq).
      * rewrite ma103. vm_compute. reflexivity.
      * rewrite keep7 by (rewrite nNX; lia). exact g6.
  - refine (ehdr_post Cx_0m T0mB Tp0mB Tm0mB H0mB (import_post s_c0m (ss_next PreRm) P_rsB_c (ss_next Cx_0m) R_c0m)
              ES0mB xs_0mB T0mB_eq ltac:(vm_compute; reflexivity) Tp0mB_eq ES0mB_eq xs_0mB_ok run_t0mB T0mB_nexts
              ltac:(rewrite nT0mB; lia) _ rho1 vm mat rho6 got rest br6 factsCx rl6 ltac:(lia) eq_refl _).
    + intros r lenOk. rewrite esMB, esMA. exact (pack4_hdr_c r lenOk).
    + intros rho7 br7 keep7 hdr7. rewrite nT0mB in keep7, hdr7.
      refine (toLoopK H0mB s_h0mB rho7 ent_h0mB idMb tvMb ltac:(vm_compute; reflexivity) mb100 mb101 _ br7 _ hdr7
                gotBox lEq).
      * rewrite mb103. vm_compute. reflexivity.
      * rewrite keep7 by (rewrite nNX; lia). exact g6.
Qed.

End FirstX.

Theorem r_exists_loop : ltac2:(tb__ "0|7|
S11S11S5S5S55Vcx;R2R3A3S1S8Z0M0R2A2S8R2ZaM1A2A2S47R4R3A2S3cS7S3eS7VJD;S4fVcx;ScS33S39Q8A1S58Vcx;A1A2A1M2A2M3R7S4eS46R5R4A2A4S79R6A4VQ;A3F_;F_;F_;Fg;Fcap;Frho;Fr0;S11S11S5S0S5S4cR2P65A2M4SdZ2Z1aA2M5A3S8G5G2A2S52Vcx;S1cR4P67A2A2S1S8G0R4A2S8R4G1A2A2S3cS7S3eS7VJD;S4fVcx;G5A2R7S4eS46G5R5A2A4S81R6A4VQ;A3F_;F_;F_;F_;Fg;Frho;Fr0;S11S11S0S5S4cR1P64A2G2A3S0S5G4Z10000M6A3SeG2Z4A2S3cS7S3eS7VJD;G3R5S4eS46G6G0A2A4S78R4A4VQ;A3F_;F_;F_;Frho;Fr0;S11S11S3cS7S3eS7VJD;VKd0;R2S4dSa5VX0;A1A4Sa6R1A4VQ;A3Frho;Fr0;F_;F_;F_;").
Proof using FDX HX0 MBX Hargc Hent Hinp.
  intros EXEH EXref EXE0. apply estep0.
  - intros r0 rho len HI. exact (proj1 (eloop_all r0 (EXEH r0) (EXref r0) (2 * (L - len) + 1)) rho len 65536 0 ltac:(lia) HI (conj (Z.le_refl 0) eq_refl)).
  - intros r0 rho HI. exact (proj2 (eloop_all r0 (EXEH r0) (EXref r0) (2 * (L - 65536) + 2)) rho 65536 0 ltac:(lia) HI (conj (Z.le_refl 0) eq_refl)).
  - exact EXE0.
Qed.

End EX.
End RX.
