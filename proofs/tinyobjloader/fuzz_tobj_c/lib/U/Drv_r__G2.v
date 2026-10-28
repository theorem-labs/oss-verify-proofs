(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "iff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rl"; "rw"; "sv"; "eval"; "ss_next"; "SAlu"; "SLit"; "SVar"; "agree_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G2.Drv_r_ref.RRef"; "KfR"; "GoodF"; "PRf"; "TRf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "msg_refused"; "die"; "ex"; "wr"; "@Corelib.Init.Datatypes"; "list"; "nil"; "nat"; "prod"; "app"; "cons"; "length"; "Some"; "bool"; "option"; "true"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "m_fds"; "FdChannel"; "fd_lookup"; "m_fs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "LQ"; "ok_frame"; "jpred"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "w_tr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r"; "tvK"; "KdR"; "fds3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.WLerr"; "Kw"; "MSG"; "Posts_wl"; "chw"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "tv_geo"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.WLerrS"; "Pre_wl2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "X_ref"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rt_states"; "E_refc"; "T_fD"; "B544"; "E_ref"; "X_refS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "is_prefix"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ"; "DTrue"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m"; "JD"; "P0"; "@Stdlib.Arith.PeanoNat.Nat"; "min"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require Stdlib.Strings.Ascii.
Require Stdlib.Strings.String.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Require LinuxProcessSemantics.LinuxProcessSem.Fs.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Specs.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rt_states.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_r_ref.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.

Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy_hdr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rt_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r.

Import ListNotations.
Import MAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Section RRef.
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
Local Notation F := (f_F cx).
Let HF : fs_lookup fs argv1 = Some F := f_HF cx.
Let Hnd : argv1 <> dot_path := f_nd cx.
Local Notation L := (Z.of_nat (length (f_F cx))).

Let P0 : ltac2:(tb__ "0|0|
S6OFr;") := ltac2:(tb__ "0|0|
S52Vsp;Vdraw;Vinp;A3").
Let JD : ltac2:(tb__ "0|1|
S18S23A1S24OF_;M0F_;S6S18S1bS9S9A2A1S43G0F_;S30FD;Ftv;Fr0;FK;") := ltac2:(tb__ "0|0|
S51Vsp;Vdraw;Vinp;A3").
Local Notation KdR := (U.Drv_r__G1.Drv_r.KdR cx).
Local Notation fds3 := (U.Drv_r__G1.Drv_r.fds3 cx).

Lemma NUsp : 0x7fff80000000 <= bv_unsigned sp <= 0x800000000000.
Proof using Hargc Hent Hinp. pose proof (U.Drv_m__G1.Drv_m.NU sp brk mb draw inp Hent Hinp Hargc) as N. lia. Qed.

Hypothesis HL : MAX_INPUT <= L.
Variable r0 : valuation.

Definition TRf (n : nat) : list event := wr 2 (firstn n msg_refused).
Definition KfR (n : nat) : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S18S23A1M0S24S2S1G0R2S13Vn;A1A3S2S1S18S1bS2aQ40A1S25A2A1S26R1A1S37Vcx;S3cZ2Z1aA2A2A3S1S4bS29R1A1Vfs;A3A2A2Lmd;Ltr;").

Lemma refused_in_spec : ltac2:(tb__ "0|1|
VSpecT;S1cS23S17Z2M0S14A2S1dS23S16Vfs;G0A2S19S23A1A3A3A1").
Proof using HF HL Hargc Hmay Hnd.
  unfold SpecT, Spec. destruct Hmay as (Hl & Hn & _).
  apply (spec_file argv fs F); [exact Hargc | exact Hl | exact Hn | exact Hnd | exact HF | apply file_traces_refused; exact HL].
Qed.
Lemma msg_refused_len : length msg_refused = 38%nat. Proof using . reflexivity. Qed.
Lemma TRf_prefix : ltac2:(tb__ "0|1|
S1aS4cS23S13R1A1S1cS23S17Z2M0S14A2S1dS23S16Vfs;G0A2S19S23A1A3A3A3Fn;").
Proof using inp.
  intros n. unfold TRf, wr.
  replace (map (WriteEv (Z_to_bv 64 2)) msg_refused ++ [ex fs 2])
    with (map (WriteEv (Z_to_bv 64 2)) (firstn n msg_refused) ++ (map (WriteEv (Z_to_bv 64 2)) (skipn n msg_refused) ++ [ex fs 2]))
    by (rewrite app_assoc, <- map_app, firstn_skipn; reflexivity).
  apply is_prefix_app.
Qed.
Lemma KfR_tcons : ltac2:(tb__ "0|0|
S1aS4eVSpecT;S10R1A1A2Fn;").
Proof using HL. intros n tr md (-> & _ & _). exists (wr 2 msg_refused ++ [ex fs 2]). split; [exact refused_in_spec | apply TRf_prefix]. Qed.
Lemma KfR_okf : ltac2:(tb__ "0|0|
S1aS2fS0Vok;S10R1A1A3Fn;"). Proof using HL. intros. apply HokK, KfR_tcons. Qed.
Lemma KfR_okp : ltac2:(tb__ "0|0|
S1aS4aS0Vok;S10R1A1A3Fn;"). Proof using HL. intros. apply HokP, KfR_tcons. Qed.
Lemma KfR0_KdR : ltac2:(tb__ "0|0|
S18S23A1S24S5S36Vcx;S3cZ2Z1aA2R2R1A4S10U0R2R1A3A2Fmd;Ftr;").
Proof using r0. intros tr md. unfold U.Drv_r__G1.Drv_r.KdR, KfR, TRf. cbn. tauto. Qed.
Lemma Kw_KfR : ltac2:(tb__ "0|0|
S1aS18S23A1S24S38S10U0A1S14S19S2aQ8A1A1R3R2R1A6S10S53R4U26A2R3R2A3F_;Fmd;Ftr;Fk;").
Proof using .
  intros k tr md (tr0 & (-> & Hf & Hs) & ->). split; [|split; [exact Hf | exact Hs]].
  unfold WLerr.TRk, WLerr.MSG, TRf, wr. cbn [app]. change WLerr.chw with (Z_to_bv 64 2).
  rewrite app_nil_r. rewrite <- msg_refused_len, <- firstn_firstn, firstn_all. reflexivity.
Qed.
Lemma KfR_fd2 : ltac2:(tb__ "0|0|
S18S23A1S24S10U0R2R1A3S1S21S25A1S28S26R2A1S3bA2S1fS25S27S3bA1A2A3F_;Fmd;Ftr;").
Proof using . intros tr md (_ & Hf & _). change WLerr.chw with (Z_to_bv 64 2). rewrite Hf. reflexivity. Qed.

Definition GoodF (rho : valuation) : Prop := rw rho 1 = sp.

Lemma tv_geo_agree : ltac2:(tb__ "0|0|
S3fS6S6S18S1bS9S9A2A1SfR4R3R2A3S1S20S50R5R2A2S22A3S40S41R5R3A3S40S41R5R4A3F_;F_;F_;Ftv;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' tv Hag Hb HG t Ht. pose proof (proj1 (forallb_forall _ _) Hb t Ht) as Hbt.
  pose proof (agree_below_vals _ _ _ Hag) as Hav.
  rewrite (tvv_agree n rho rho' t Hav Hbt).
  apply andb_prop in Hbt as [H1 H2].
  rewrite <- (eval_agree_vals n rho rho' (fst t) Hav H1), <- (eval_agree_vals n rho rho' (snd t) Hav H2). exact (HG t Ht).
Qed.

Lemma xrefS_intro : ltac2:(tb__ "0|0|
S43S24OF_;F_;S6S31S2dS0VJD;S36Vcx;S3cZ2Z1aA2A2Vr0;S35R3A4S44R2R1A5S4S6S6S2S2S11R1A1S40S41R1S35A3A2S2cS0S10U0A1S49R1R3A5A2Lrho';A2F_;Fw;Frho;FD;").
Proof using .
  intros D rho [tr [ms md]] [Hsm HJ].
  destruct HJ as (Ai & HJi & _). pose proof HJi as (Hav & Hk & [HM Hi] & _ & _ & _ & HP0).
  assert (HG0 : GoodF rho) by (unfold GoodF; destruct Hav as [Hw _]; rewrite <- (Hw 1%positive ltac:(lia)); exact (proj1 HP0)).
  pose proof (tv_geo_of_JGi segs C_U 31 (KdR (2 ^ 26)) r0 P0 tvK Ai rho tr md HJi) as HG.
  destruct (statics_view_of_MInvR segs C_U Ai rho md HM) as [g Vg].
  destruct X_ref_shape as (_ & NXn & _).
  destruct (carve_statics_fresh segs C_U statics_layout_U statics_wseg_U rho X_ref (tr, mkCfg ms md) g 153 154 Hsm
              ltac:(rewrite NXn; lia) Vg
              (robjs_missT_statics_sound C_U P0 (ss_facts X_ref) tvK (ss_objs X_ref) rho HG (smatch_facts_hold segs _ _ _ Hsm) missT_xref)
              ltac:(rewrite X_refS_eq; exact swf_X_refS)) as [Hsm' _].
  exists (rho_set_rw rho 153 (Z_to_bv 64 g)). split; [split|].
  - unfold GoodF in *. rewrite rho_set_rw_other by lia. exact HG0.
  - intros t Ht. unfold tvv. cbn in Ht. destruct Ht as [<-|[]]. cbn [fst snd eval]. rewrite !rho_set_rw_other by lia.
    exact (HG (SVar 102, SVar 101) ltac:(left; reflexivity)).
  - split; [rewrite <- X_refS_eq; exact Hsm' | apply KfR0_KdR; exact Hk].
Qed.

Lemma GoodF_B544 : ltac2:(tb__ "0|1|
S6S11R1A1S1S3eS2bQ40M0SaR2S47A2A2S3dS2bG0Vsp;A2Z230A2A3F_;Frho;").
Proof using .
  intros rho HG. pose proof NUsp. unfold B544. rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite HG. unfold M64v.
  replace ((-560) mod 18446744073709551616) with (18446744073709551616 - 560) by reflexivity.
  replace (bv_unsigned sp + (18446744073709551616 - 560)) with (bv_unsigned sp - 560 + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma GoodF_B112 : ltac2:(tb__ "0|1|
S6S11R1A1S1S3eS2bQ40M0SaR2ScS4dSeP1A1SdN80A1A3A2A2S3dS2bG0Vsp;A2Z80A2A3F_;Frho;").
Proof using .
  intros rho HG. pose proof NUsp. rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [eval]. rewrite HG. unfold M64v.
  replace ((-128) mod 18446744073709551616) with (18446744073709551616 - 128) by reflexivity.
  replace (bv_unsigned sp + (18446744073709551616 - 128)) with (bv_unsigned sp - 128 + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma refc_intro : ltac2:(tb__ "0|3|
S6S31S11R2A1S40S41R3S35A3S2cS0S10U0A1M0S48R4R3A5S4S6S6S2S1S18S2aQ8A1M1A1M2S7R1P5A2S14A3S2S1G2S7R1P6A2S19G1A1A3S2S3fS1S2aQ40A1S8R2R1A2S8R7R1A2A3Fi;S2cS0G0S45R1R5A5A2A2A2Lrho';A2F_;F_;F_;Fw;Frho;").
Proof using .
  intros rho [tr [ms md]] HG HTG [Hsm Hk]. pose proof NUsp as N.
  destruct norl_ref as [N5 N6]. destruct E_ref_facts as (Fc & Fx & Fr & Fl & Nc & Nx & Nr & Nl).
  destruct obj3_ref as (Hn3 & Hlo3 & Hhi3 & Hwr3 & Harr3 & Hb3).

  pose proof (smatch_xforms segs xs_ref rho E_ref E_refx _ xs_ref_ok Hsm) as Hx.

  pose proof (smatch_obj_to_list segs rho E_refx _ 3 5 (obj E_refx 3) (-432) (-394) BL_ref Hx Hn3 Hlo3 Hhi3 ltac:(lia) ltac:(lia) Hwr3 Harr3 cb_ref N5) as Hl.
  rewrite E_refl_eq, BL_ref_msg in Hl.
  set (rho1 := rho_set_rl rho 5 msg_refused) in Hl.
  assert (HG1 : GoodF rho1) by exact HG.

  assert (Hr : smatch segs rho1 E_refr (tr, mkCfg ms md)).
  { rewrite <- E_refr_eq. apply (smatch_reframe_listobj segs rho1 E_refl _ 3 _ 5 B544 (SLit 0) (SLit 38) Hl obj3_refl eq_refl eq_refl).
    - cbn [ob_base ob_lo]. rewrite (GoodF_B544 rho1 HG1), (GoodF_B112 rho1 HG1), !soff_lit_small by lia. lia.
    - cbn [ob_base ob_hi]. rewrite (GoodF_B544 rho1 HG1), (GoodF_B112 rho1 HG1), !soff_lit_small by lia. lia.
    - rewrite E_refr_eq. exact swf_E_refr. }

  set (rho2 := rho_set_rl rho1 6 []).
  assert (Hr2 : smatch segs rho2 E_refr (tr, mkCfg ms md)) by (apply smatch_set_rl; [exact norl_refr | exact Hr]).
  exists rho2. split; [reflexivity|]. split; [reflexivity|]. split; [intros i; reflexivity|]. split; [|exact Hk].
  rewrite <- E_refc_eq. unfold app_objs.
  apply (smatch_carve_listobj segs rho2 E_refr _ (SLit 0) (SLit 0) (SLit 0) 0 0 (DRom 6) 6 (ss_next E_refr) Hr2 eq_refl);
    rewrite ?CursorGlue.U_lit; try (change (0 mod M64v) with 0); try (rewrite ?soff_lit_small by lia; lia).
  all: try exact swf_E_refc.
  all: try reflexivity.
  all: try (apply Forall_forall; intros o _; unfold SymState.ranges_disjoint; cbn [fst snd]; lia).
  all: try (intros off Hoff D; discriminate D).
  all: intros off Hoff; lia.
Qed.

Definition PRf (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S2S1S18S2aQ8A1M0A1M1S7Vrho1;P5A2S14A3S2S1G1S7Vrho1;P6A2S19G0A1A3S2S1S3eS2bQ40M2S8Vrho1;PdA2A2Z26A3S1S3eS2bG2S8Vrho1;PfA2A2Z0A3A2A2A2").

Lemma Kw_okf : ltac2:(tb__ "0|0|
S1aS2fS0Vok;S38S10U0A1S14S19S2aQ8A1A1R1A4A3Fk;").
Proof using HL. intros k. apply HokK. intros tr md HK. exact (KfR_tcons _ tr md (Kw_KfR k tr md HK)). Qed.
Lemma Kw_okp : ltac2:(tb__ "0|0|
S1aS4aS0Vok;S38S10U0A1S14S19S2aQ8A1A1R1A4A3Fk;").
Proof using HL. intros k. apply HokP. intros tr md HK. exact (KfR_tcons _ tr md (Kw_KfR k tr md HK)). Qed.

Lemma wl2_call : ltac2:(tb__ "0|3|
S6S12R1A1S33S0Vok;S2cS0S10U0A1M0S42R2A4S2eS0S38G0S14S19S2aQ8A1M1A1M2S1eG1S39S14G2A2A2A4SbS42A1R2S3aA5A4F_;Frho1;").
Proof using HL.
  intros rho1 (H5 & H6 & H13 & H15).
  apply (WLerr.wl2_sum ok (KfR 0) rho1 msg_refused [] H5 H6 H13 H15).
  - unfold WLerr.MSG, max_write_total. cbn. lia.
  - exact Kw_okf.
  - exact Kw_okp.
  - exact KfR_fd2.
  - cbn. lia.
Qed.
Lemma wl2_ecall : ltac2:(tb__ "0|3|
S6S12R1A1S32S0S2cS0S10U0A1M0S42R2A4S2eS0S38G0S14S19S2aQ8A1M1A1M2S1eG1S39S14G2A2A2A4SbS42A1R2S3aA5A3F_;Frho1;").
Proof using .
  intros rho1 (H5 & H6 & H13 & H15).
  apply (WLerr.wl2_sum_ex (KfR 0) rho1 msg_refused [] H5 H6 H13 H15).
  - unfold WLerr.MSG, max_write_total. cbn. lia.
  - exact KfR_fd2.
  - cbn. lia.
Qed.

Lemma ref_exit : ltac2:(tb__ "0|0|
S6S33S0Vok;S2cS0S10U26A1S46R1A4S31S3L_;A4Frho;").
Proof using HL.
  intros rho. eapply (run_tr ok); [exact run_fd | reflexivity | apply KfR_okf |].
  intros Lf rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct cert_fexit as (Hi & H17 & H10).
  apply (triple_exit_eval segs ok SpecT (KfR 38) E_fex rho1 2);
    [apply KfR_okf | apply KfR_okp | exact Hokh | exact Hi | left; exact H17 | rewrite H10; cbn [eval]; rewrite U_addr by lia; reflexivity |].
  intros tr md (-> & _ & ->). unfold TRf. rewrite firstn_all2 by (rewrite msg_refused_len; lia). exact refused_in_spec.
Qed.
Lemma ref_eexit : ltac2:(tb__ "0|0|
S6S32S0S2cS0S10U26A1S46R1A4S31S1S18S23A1S34R1A1S15Vfs;S14A2A3Lw;A3Frho;").
Proof using .
  intros rho. eapply erun_tr; [exact run_fd | reflexivity |].
  intros Lf rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct cert_fexit as (Hi & H17 & H10).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    apply (etriple_exit_eval segs (KfR 38) E_fex rho1 2 Hi (or_introl H17))].
  - intros w (tr & md & (-> & _ & ->) & ->). unfold TRf, die. rewrite firstn_all2 by (rewrite msg_refused_len; lia). reflexivity.
  - rewrite H10. cbn [eval]. rewrite U_addr by lia. reflexivity.
Qed.

Lemma ref_tail_safe : ltac2:(tb__ "0|2|
S6S1S18S2aQ8A1M0A1M1S7R1P5A2S14A3S1G1S7R2P6A2S19G0A1A3S33S0Vok;S2cS0S10U0A1S45R3A4S31S3L_;A4F_;F_;Frho;").
Proof using HL.
  intros rho H5 H6. destruct E_ref_facts as (Fc & _). destruct s_f_vals as (S12 & S13 & S14 & S15).
  apply (call_path segs PRf ok (KfR 0) (WLerr.Kw (KfR 0) msg_refused [] (length (WLerr.MSG msg_refused [])))
           E_refc E_refc WLerrS.Pre_wl2 [] s_f R_f WLerr.Posts_wl _ rho eq_refl efr_f chk_f ltac:(rewrite Fc; exact fb_f)).
  - exact wl2_call.
  - intros ms _. unfold PRf. rewrite !rw_call', S13, S15.
    cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho' [<-|[]] Hag HFf. cbn [lf_state]. rewrite Fc in HFf.
    change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite T_fDi_eq.
    eapply triple_conseq with (P := SP segs (KfR 38) T_fDi rho'); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply Kw_KfR in HK. exact HK. }
    apply (post_path segs ok _ T_fDi T_fD (ss_facts E_ref) xs_fd rho' _ fb_fd xs_fd_ok HFf).
    apply ref_exit.
Qed.
Lemma ref_tail_ex : ltac2:(tb__ "0|2|
S6S1S18S2aQ8A1M0A1M1S7R1P5A2S14A3S1G1S7R2P6A2S19G0A1A3S32S0S2cS0S10U0A1S45R3A4S31S1S18S23A1S34R1A1S15Vfs;S14A2A3Lw;A3F_;F_;Frho;").
Proof using .
  intros rho H5 H6. destruct E_ref_facts as (Fc & _). destruct s_f_vals as (S12 & S13 & S14 & S15).
  apply (ecall_path segs PRf (KfR 0) (WLerr.Kw (KfR 0) msg_refused [] (length (WLerr.MSG msg_refused [])))
           E_refc E_refc WLerrS.Pre_wl2 [] s_f R_f WLerr.Posts_wl _ rho eq_refl efr_f chk_f ltac:(rewrite Fc; exact fb_f)).
  - exact wl2_ecall.
  - intros ms _. unfold PRf. rewrite !rw_call', S13, S15.
    cbn [rho_sub rho_absorb rl eval]. rewrite !U_addr by lia. auto.
  - intros Lf rho' [<-|[]] Hag HFf. cbn [lf_state]. rewrite Fc in HFf.
    change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite T_fDi_eq.
    eapply etriple_conseq with (P := SP segs (KfR 38) T_fDi rho'); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply Kw_KfR in HK. exact HK. }
    apply (epost_path segs _ T_fDi T_fD (ss_facts E_ref) xs_fd rho' _ fb_fd xs_fd_ok HFf).
    apply ref_eexit.
Qed.

Theorem ref_safe : ltac2:(tb__ "0|0|
S6S33S0Vok;S2dS0VJD;S36Vcx;S3cZ2Z1aA2A2Vr0;S35S4fA4S44R1A4S31S3L_;A4Frho;").
Proof using HL.
  intros rho.
  apply (triple_from ok _ (fun r w => (GoodF r /\ tv_geo C_U r tvK) /\ SP segs (KfR 0) X_refS r w)); [intros w Hw; exact (xrefS_intro DTrue rho w Hw)|].
  intros rho1. apply triple_pure. intros [HG1 HTG].
  eapply (run_tr ok); [exact run_xrefS | reflexivity | apply KfR_okf |].
  replace (ss_next X_refS) with 154%positive by reflexivity. intros Lf rho2 [<-|[]] Hag. cbn [lf_state].
  assert (HG2 : GoodF rho2) by (unfold GoodF in *; destruct Hag as (Hw' & _); rewrite <- (Hw' 1%positive ltac:(lia)); exact HG1).
  pose proof (tv_geo_agree 154 rho1 rho2 tvK Hag eq_refl HTG) as HTG2.
  apply (triple_from ok _ (fun r w => (rl r 5 = msg_refused /\ rl r 6 = []) /\ SP segs (KfR 0) E_refc r w)).
  { intros w Hw. destruct (refc_intro rho2 w HG2 HTG2 Hw) as (r & A & B & _ & Dd). exists r. auto. }
  intros rho3. apply triple_pure. intros [H5 H6]. exact (ref_tail_safe rho3 H5 H6).
Qed.

Theorem ref_exists : ltac2:(tb__ "0|0|
S43S24OF_;F_;S6S32S0S2dS0VJD;S36Vcx;S3cZ2Z1aA2A2Vr0;S35R2A4S44R1A4S31S1S18S23A1S34R1A1S15Vfs;S14A2A3Lw;A3Frho;FD;").
Proof using .
  intros D rho.
  apply (etriple_from _ (fun r w => (GoodF r /\ tv_geo C_U r tvK) /\ SP segs (KfR 0) X_refS r w)); [intros w Hw; exact (xrefS_intro D rho w Hw)|].
  intros rho1 w0 [[HG1 HTG] Hw0]. revert w0 Hw0. change (etriple segs (SP segs (KfR 0) X_refS rho1) (fun w => w_tr w = die fs msg_refused)).
  eapply erun_tr; [exact run_xrefS | reflexivity |].
  replace (ss_next X_refS) with 154%positive by reflexivity. intros Lf rho2 [<-|[]] Hag. cbn [lf_state].
  assert (HG2 : GoodF rho2) by (unfold GoodF in *; destruct Hag as (Hw' & _); rewrite <- (Hw' 1%positive ltac:(lia)); exact HG1).
  pose proof (tv_geo_agree 154 rho1 rho2 tvK Hag eq_refl HTG) as HTG2.
  apply (etriple_from _ (fun r w => (rl r 5 = msg_refused /\ rl r 6 = []) /\ SP segs (KfR 0) E_refc r w)).
  { intros w Hw. destruct (refc_intro rho2 w HG2 HTG2 Hw) as (r & A & B & _ & Dd). exists r. auto. }
  intros rho3 w [[H5 H6] Hw]. exact (ref_tail_ex rho3 H5 H6 w Hw).
Qed.

End RRef.
End Drv_r_ref.
