(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4 RA_vrdi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pnyh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pf3s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pis0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_p0nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpnnp AIcptdg AIcp2kv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5 AIcpzt2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5.AIcp1os OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpzt2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcp8zl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_La0bg A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VSe3i A_VSa8f A_VStbd A_VEr47 A_VSbb4 A_VS41f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_veqih.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.

Module A_ve6k0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4 RA_vrdi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pf3s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pis0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_p0nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpnnp AIcptdg AIcp2kv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5.AIcp1os OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcp8zl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_La0bg A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VSe3i A_VSa8f A_VStbd A_VEr47 A_VSbb4 A_VS41f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_veqih.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS160 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSe90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSq5u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSt8w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS8zm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_veq11 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_ve5c7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, DATA_STACK, LEN_STACK, ASSERT_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia02
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (vi : option vsb_rec) (H : henv) (lo SB N : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HFL : 0 <= vv Fflags < 16.
  Hypothesis HET : bool01 (vv Femptytag).
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis HLM : vv Flast_mark = 1.
  Hypothesis HAZ : vv Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis SZB : vb_size vr <= vb_len vr + 4096.
  Hypothesis LENB : vb_len vr + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  Hypothesis LBM : a_livebytes A0 + vb_size vr + vb_len vr + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : match vi with Some yi => vb_len yi / 4096 | None => 0 end + 8 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM + (PPOT_CAP - vsb_ppot vr) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis LF : lib_frames A0.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fvsb /\ vv Finclude_src <> vb_buf vr /\
                   vb_buf yi <> vv Fvsb /\ vb_buf yi <> vb_buf vr
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - DOINCL_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q -> vkeep vv vv' [Fstate; Finclude_src; Finclude_continue] ->
      (vv' Fstate = vv Fstate \/ vv' Fstate = vi_st VIA S_TagError) -> bool01 (vv' Finclude_continue) -> vv' Finclude_src = 0 ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      match vi with
      | None => (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0
      | Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                   (forall r, r <> vb_buf vr -> r <> vb_buf vr' -> r <> vv Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A0 r) /\
                   a_livebytes A' = a_livebytes A0 + (vb_size vr' - vb_size vr) - 40 - vb_size yi /\ a_nlive A' = a_nlive A0 - 2
      end ->
      frames_aged A0 A' 1 1 -> a_tinycred A' = a_tinycred A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40)
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HFL (conj HET (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB
      (conj SZB (conj LENB (conj LBM (conj NLV (conj SCM (conj PRM (conj LF (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO (conj SPHI
      (conj STKSH K))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Let TINV := tinv VEP vv tag q vr vi H lo SB N sp m0 md0 A0.
  Let FRAME' := FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Local Ltac pose_parts :=
    pose proof (printf_call VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as printf_call';
    pose proof (printf_c_call VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as printf_c_call';
    pose proof (tinv_xfer VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as tinv_xfer';
    pose proof (seg_end VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_end';
    pose proof (seg_loop VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_loop'.

  Local Ltac unpack_tinv TI :=
    (first [ dand26 TI as EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & VEPC & SOBJk & NEBk & LENk & SZk & RELk & LIVEk & LBk & TCk & NLk & SCk & PCk & FSk & STKSHk
                    & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Let SCR5' := SCR5 VEP.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 T fc F tp gp"] Lemma tinv_xfer2 : forall yi bs Ak mk mdk vvk e Wf (v' : mem) mq mdq sc,
    TINV yi bs Ak mk mdk vvk e ->
    munch Wf (aview Ak mk) v' -> wmono rsegs (aview Ak mk) v' -> mem_inv rsegs v' ->
    (forall a, ~ outside Wf a -> bv_unsigned sp - DOINCL_STACK <= a < bv_unsigned sp) ->
    stk rsegs v' lo (bv_unsigned sp + -144) ->
    rw_cells rsegs v' (bv_unsigned sp + -144) (FRAME' sc) -> cells_size sc = 40%nat ->
    ainv Ak mq mdq -> aview Ak mq = v' -> amd_frame mdk mdq ->
    TINV yi bs Ak mq mdq vvk e.
  Proof.
    touch_all. intros until sc. intros TI MU WM MI' WIN ST' FR' SC40 AINVq EV MDF'.
    unpack_tinv TI. prelims.
    pose proof VOBJ as (VLV & VEPC0 & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_2; dand7 dR_2 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]). unfold kHighMemBeg in VEPlo. all_app_facts.
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    unfold TINV, tinv. rewrite EV. cbv delta [FRAME' FRAME] in FR'.
    assert (LVk : a_live Ak VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    (first [ pose proof ((live_geomP LPA Ak mk mdk _ _ AINVk LVk)) as dR_4; dand5 dR_4 as _ _ _ VEPkhi _ | pose proof (live_geomP LPA Ak mk mdk _ _ AINVk LVk) as (_ & _ & _ & VEPkhi & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA Ak mk mdk S vvk false AINVk SOBJk)) as dR_5; dand8 dR_5 as _ _ Skhi _ _ _ Bkhi _ | pose proof (vsb_obj_geom LPA Ak mk mdk S vvk false AINVk SOBJk) as (_ & _ & Skhi & _ & _ & _ & Bkhi & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA Ak mk mdk (vv Finclude_src) yi true AINVk IOBJk)) as dR_6; dand8 dR_6 as _ _ SIkhi _ _ _ BIkhi _ | pose proof (vsb_obj_geom LPA Ak mk mdk (vv Finclude_src) yi true AINVk IOBJk) as (_ & _ & SIkhi & _ & _ & _ & BIkhi & _) ]).
    assert (OUT : forall a, a < bv_unsigned sp - (144 + (128 + 16 + (192 + 16 + (80 + 8192)))) -> outside Wf a).
    { intros a Ha. destruct (Classical_Prop.classic (outside Wf a)) as [X|X]; [exact X|]. exfalso. pose proof (WIN a X) as Y. ufs. keeplia Ha Y. }
    split; [exact EVI|]. split; [exact AINVq|]. split; [exact MI'|]. split; [exact (amd_frame_trans _ _ _ MDFk MDF')|]. split; [exact ST'|].
    split. { eapply (henv_ok_munch LPA); [exact HENVk| exact MU| exact WM| exact HG|].
             intros a Ha. apply OUT. pose proof (proj1 (proj1 (proj2 HENVk))) as EB. cbn [vi_bss_vsc vi_bss_cp VIA] in Ha.
             unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha.
             pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF. rewrite SHMAX_val in SHF.
             change ((8192 + 7) / 8) with 1024 in SHF. change (8192 / 8) with 1024 in Ha.
             keeplia Ha GCE GHI SHF ACV CEIL LO. }
    split. { eapply (rw_cells_munch LPA); [exact VEPC| exact MU| exact WM|]. rewrite (vep_cells_size vv tag q TAG8 PADS). change (Z.of_nat 312) with 312.
             intros a Ha. apply OUT. keeplia Ha VEPkhi ACV CEIL LO. }
    split. { eapply vsb_obj_munch; [exact SOBJk| exact MU| exact WM|]. intros a Ha. apply OUT. keeplia Ha Skhi Bkhi ACV CEIL LO. }
    split; [exact NEBk|]. split; [exact LENk|]. split; [exact SZk|]. split; [exact RELk|]. split; [exact LIVEk|].
    split; [exact LBk|]. split; [exact TCk|]. split; [exact NLk|]. split; [exact SCk|]. split; [exact PCk|]. split; [exact FSk|].
    split. { (first [ pose proof (STKSHk) as dR_7; dand6 dR_7 as SSB SSN _ _ SSC SST | pose proof STKSHk as (SSB & SSN & _ & _ & SSC & SST) ]). unfold kHighMemBeg in SST. all_app_facts.
             eapply stack_shadow_again; [exact STKSHk| | reflexivity].
             eapply (bytes_at_munch LPA); [exact SSB| exact MU|]. rewrite ?zeros_length, ?repeat_length, Z2Nat.id by exact SSN.
             intros a Ha. apply OUT. keeplia Ha SST ACV CEIL LO. }
    split. { ufs. eapply cframe_after; [exact CFk| exact MU| intros a Ha NO; left; pose proof (WIN a NO) as Y; ufs; keeplia Y|].
             eapply (window_mapped LPA _ lo (bv_unsigned sp + -144) (bv_unsigned sp));
               [exact ST' | exact FR' | rewrite cells_size_app, SC40; cbn [cells_size csize Nat.add]; clear; lia | exact CEIL | keeplia LO | clear; lia]. }
    split. { eapply vsb_obj_munch; [exact IOBJk| exact MU| exact WM|]. intros a Ha. apply OUT. keeplia Ha SIkhi BIkhi ACV CEIL LO. }
    split. { destruct U8k as [UB UW]. split; [| eapply wr_at_transport; [exact UW| exact WM]].
             eapply (bytes_at_munch LPA); [exact UB| exact MU|]. rewrite LBS. intros a Ha. apply OUT. keeplia Ha BIkhi ACV CEIL LO. }
    split; [exact LBS|]. split; [exact NISBk| exact NIBBk].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 SCR5' S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00"] Lemma seg_mid : forall (yi : vsb_rec) (bs : list byte)
      (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs4 xs6 xt3 xt4 xt5 xt6 : word) (j : list byte)
      (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e i0 : Z),
    TINV yi bs Ak mk mdk vvk e ->
    rw_cells rsegs (aview Ak mk) (bv_unsigned sp + -144) (FRAME' [CB 40 j]) ->
    0 <= e -> 0 <= i0 <= vb_len yi -> e + (vb_len yi - i0) + 1 <= vb_len yi + 8 ->
    nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880))
                                    a0 a1 a2 a3 a4 a5 a6 a7
                                    xs2 (Z_to_bv 64 (VEP + 8)) xs4 (Z_to_bv 64 (vb_len yi)) xs6
                                    (Z_to_bv 64 (vb_buf yi + i0)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 280)) (Z_to_bv 64 (VEP + 288))
                                    (Z_to_bv 64 ((VEP + 288) / 8 + 2147450880)) xt3 xt4 xt5 xt6)
                               F (Z_to_bv 64 0x8f110) fc None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all. intros until i0. intros TI FR E0 IR BUD NUL. pose_parts.
    pose proof TI as TI0. unpack_tinv TI0. prelims.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_8; dand7 dR_8 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]). unfold kHighMemBeg in VEPlo. all_app_facts.
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    pose proof (as_minv LPA Ak _ _ AINVk) as [_ MHk].
    assert (LVk : a_live Ak VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk. pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk.
    (first [ pose proof ((vsb_obj_geom LPA Ak mk mdk (vv Finclude_src) yi true AINVk IOBJk)) as dR_10; dand11 dR_10 as SI16 SIklo SIkhi _ BI16 BIklo BIkhi _ _ _ _ | pose proof (vsb_obj_geom LPA Ak mk mdk (vv Finclude_src) yi true AINVk IOBJk) as (SI16 & SIklo & SIkhi & _ & BI16 & BIklo & BIkhi & _ & _ & _ & _) ]).
    unfold kHighMemBeg in SIklo, BIklo. all_app_facts.
    pose proof (proj1 (proj2 IOBJk)) as VINVI. (first [ pose proof (VINVI) as dR_11; dand8 dR_11 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    pose proof (mod8_of_mod16 (vv Finclude_src) SI16) as SI8.
    pose proof (conj (sh_boundL (Clg:=Clg) (vv Finclude_src) 40 ltac:(keeplia SIklo) ltac:(clear; lia) ltac:(exact SIkhi)) (sh_top_le' (vv Finclude_src) 40 ltac:(keeplia SIklo) ltac:(clear; lia) ltac:(exact SIkhi))) as SHSIB. rewrite SHMAX_val in SHSIB. change ((40 + 7) / 8) with 5 in SHSIB.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINVk LVk) as SHV. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    pose proof (as_live_shadow LPA _ _ _ (vv Finclude_src) 40 AINVk LSIk) as SHSI. fold_cl_segs. fold_aview.
    pose proof (cenv_intro Ak mk mdk AINVk) as CEk. fold_aview.
    pose proof IOBJk as IO. vsb_open IO. clear VBUF VLS VLB VNE. fold_cl_segs. hide VSBC. hide SHSI.
    unfold vep_cells in VEPC. cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - (144 + (128 + 16 + (192 + 16 + (80 + 8192)))), bv_unsigned sp + -144); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40)] (aview Ak mk)) as MU.
    pose proof (wmono_refl rsegs (aview Ak mk)) as WM.
    assert (CFPm : client_fp LPA Ak (aview Ak mk) [(bv_unsigned sp - (144 + (128 + 16 + (192 + 16 + (80 + 8192)))), bv_unsigned sp + -144); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40)]).
    { cbn. split; [| split; [| exact I]].
      - left. split; [keeplia CEIL LO|]. split; [keeplia SPR|]. eapply (stk_mapped (L:=LPA)); [exact STk | exact CEIL | keeplia LO | clear; lia].
      - left. split; [keeplia CEIL LO|]. split; [keeplia SPR|].
        pose proof (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA)) as MPF. cbn [cells_size csize Nat.add length] in MPF.
        eapply (mapped_sub _ _ _ _ _ MPF); clear; lia. }
    ago AINVk. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    vrechk SHV EzsV (VEP + 280) 8 0.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    unhide VSBC. unhide SHSI.
    eapply (rw_cells_munch LPA) in VSBC; [| exact MU| exact WM| rewrite vsb_cells_size; change (Z.of_nat 40) with 40; intros a__ Ha__; cbn [outside]; keeplia Ha__ SIkhi ACV CEIL LO].
    eapply (bytes_at_munch LPA) in SHSI; [| exact MU| rewrite shpat_length by (clear; lia); change ((40 + 7) / 8) with 5; intros a__ Ha__; cbn [outside]; keeplia Ha__ SHSIB ACV CEIL LO].
    lazymatch goal with CE : cenv ?v, ST : stk _ ?v _ _, MI : mem_inv _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename ST into STv; rename MI into MIv; rename CE into CEv
      | |- evt _ _ (MS _ _ _ _ _ ?v _) =>
          lazymatch goal with ST : stk _ v _ _, MI : mem_inv _ v |- _ => rename ST into STv; rename MI into MIv end;
          assert (CEv : cenv v) by (eapply cenv_munch; [exact CEk| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV SPR])
    end.
    rename SHSI into SHSIv.
    icall (VSB_data_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (vv Finclude_src) yi lo)
      by (try rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); ufs; unfold kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV
                | (eexists _, _; split; [exact SHSIv| try (generalize alloc_ceiling_val); clear - SI8 SIkhi SIklo ACV; try pose proof alloc_ceiling_val as ACV__; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | exact CEv
                | exact SI8
                | exact STv
                | assumption
                | keeplia SIklo | keeplia SIkhi | keeplia LO | exact CEIL ]).
    (* [comment removed for export] *)
    do 18 zstep.
    rewrite (shr3_div8 (VEP + 8)).
    lazymatch goal with ST : stk _ ?v _ _, MI : mem_inv _ ?v, FRv : rw_cells _ ?v (bv_unsigned sp + -144) _ |- evt _ _ (MS _ _ _ _ _ ?v _) =>
      rename ST into STw; rename MI into MIw; rename FRv into FRw end.
    astopk AINVk MU WM CFPm.
    pose proof (tinv_xfer2 yi bs Ak mk mdk vvk e _ _ mq mdq SCR5' TI MU WM MIw ltac:(intros a__ X; cbn [outside] in X; ufs; keeplia X) STw ltac:(cbv delta [FRAME' FRAME SCR5' SCR5]; cbn [app]; exact FRw) eq_refl AINVq EVq (amd_frame_sbm _ _ SBq MHk)) as TIq.
    rewrite <- EVq in FRw.
    eapply (seg_loop' (Z.to_nat (vb_len yi - i0)) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mq mdq vvk e i0);
      [ exact TIq | cbv delta [FRAME SCR5]; cbn [app]; exact FRw | exact E0 | exact IR | exact BUD | keeplia IR | exact NUL ].
  Qed.

  (* [comment removed for export] *)
  Local Ltac lit_chk1 SRC X U :=
    zstep; zstep; shadow_addr_at SRC X 1;
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end;
    lazymatch goal with |- evt ?segs ?Q _ =>
      eapply (evt_cut segs _ Q);
      [ zstep;
        let K := fresh "KS" in
        zstep; if_cases K; zify_cond K;
        [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ]
        | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ] ]
      | let ms := fresh "ms" in let x := fresh "junk" in
        intros ms [x ->]; simp_regs ]
    end;
    shadow_cleanup.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 SCR5' S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00"] Lemma seg_pfx : forall (yi : vsb_rec) (bs : list byte)
      (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs4 xt3 xt4 xt5 xt6 : word) (incl : Z) (j : list byte)
      (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec),
    TINV yi bs Ak mk mdk vvk 0 ->
    rw_cells rsegs (aview Ak mk) (bv_unsigned sp + -144) (FRAME' [CB 40 j]) ->
    0 <= incl < 256 ->
    nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880))
                                    a0 a1 a2 a3 a4 a5 a6 a7
                                    xs2 (Z_to_bv 64 (VEP + 8)) xs4 (Z_to_bv 64 (vb_len yi)) (Z_to_bv 64 incl)
                                    (Z_to_bv 64 (vb_buf yi)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 280)) (Z_to_bv 64 (VEP + 288))
                                    (Z_to_bv 64 ((VEP + 288) / 8 + 2147450880)) xt3 xt4 xt5 xt6)
                               F (Z_to_bv 64 0x8ef18) fc None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all. intros until vvk. intros TI FR INCL NUL. pose_parts.
    pose proof TI as TI0. unpack_tinv TI0. prelims.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_12; dand7 dR_12 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]). unfold kHighMemBeg in VEPlo. all_app_facts.
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    pose proof (as_minv LPA Ak _ _ AINVk) as [_ MHk].
    assert (LVk : a_live Ak VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk. pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk.
    (first [ pose proof ((vsb_obj_geom LPA Ak mk mdk (vv Finclude_src) yi true AINVk IOBJk)) as dR_14; dand11 dR_14 as SI16 SIklo SIkhi _ BI16 BIklo BIkhi _ _ _ _ | pose proof (vsb_obj_geom LPA Ak mk mdk (vv Finclude_src) yi true AINVk IOBJk) as (SI16 & SIklo & SIkhi & _ & BI16 & BIklo & BIkhi & _ & _ & _ & _) ]).
    unfold kHighMemBeg in SIklo, BIklo. all_app_facts.
    pose proof (proj1 (proj2 IOBJk)) as VINVI. (first [ pose proof (VINVI) as dR_15; dand8 dR_15 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINVk LVk) as SHV. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    pose proof (as_live_shadow LPA _ _ _ (vb_buf yi) (vb_size yi) AINVk LBIk) as SHBI. fold_cl_segs. fold_aview.
    (* [comment removed for export] *)
    destruct (nth_error bs 0) as [b0|] eqn:Hb0; [| apply nth_error_None in Hb0; exfalso; keeplia Hb0 LBS VszI].
    pose proof (byte_range b0) as RB0.
    pose proof (u8arr_read rsegs (aview Ak mk) (vb_buf yi) bs 0 b0 (Z_to_bv 64 (vb_buf yi)) U8k Hb0 ltac:(clear; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    unfold vep_cells in VEPC. pose proof (proj2 (proj2 (proj2 (proj2 VBASE)))) as EURL. rewrite EURL in VEPC. cbn [vi_url VIA] in VEPC.
    cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview Ak mk)) as MU. pose proof (wmono_refl rsegs (aview Ak mk)) as WM.
    ago AINVk. fold_cl_segs.
    shadow_chk SHBI 1 11.
    vchk SHV EzsV 8 0.
    zstep. clear RD. zstep. zstep. zstep. zstep. zstep.
    astopk AINVk MU WM I.
    pose proof (tinv_xfer' yi bs Ak mk mdk vvk 0 [] _ mq mdq [CB 40 j] TI MU WM MIk ltac:(intros a__ X; exfalso; exact (X I)) STk FR eq_refl AINVq EVq (amd_frame_sbm _ _ SBq MHk)) as TIq.
    rewrite <- EVq in FR.
    eapply (printf_c_call' yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 incl) 0x8ef50 Ak mq mdq vvk 0 [CB 40 j]);
      [ exact TIq | cbv delta [FRAME]; cbn [app]; exact FR | reflexivity | clear; lia | keeplia VlenI | clear; lia | reflexivity | ].
    clear TIq FR. clear dependent mq. try clear SBq. try (clear dependent mdq). clear MU WM SHV SHBI.
    clear EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk MHk LVk LSIk LBIk SIklo SIkhi BIklo BIkhi.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A1 m1 md1 vv1 TI1 FR1.
    (* [comment removed for export] *)
    pose proof TI1 as TI0. unpack_tinv TI0. pose proof (as_minv LPA A1 _ _ AINVk) as [_ MH1].
    assert (LV1 : a_live A1 VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINVk LV1) as SHV. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV. rewrite <- EzsV in SHV.
    unfold vep_cells in VEPC. rewrite EURL in VEPC. cbn [vi_url VIA] in VEPC. cbv delta [FRAME' FRAME] in FR1. cbn [app] in FR1.
    pose proof (munch_refl [] (aview A1 m1)) as MU. pose proof (wmono_refl rsegs (aview A1 m1)) as WM.
    ago AINVk. fold_cl_segs.
    vrechk SHV EzsV (VEP + 8) 8 0.
    zstep. zstep. zstep. zstep. zstep.
    astopk AINVk MU WM I.
    pose proof (tinv_xfer' yi bs A1 m1 md1 vv1 (0 + 1) [] _ mq mdq [CB 40 j] TI1 MU WM MIk ltac:(intros a__ X; exfalso; exact (X I)) STk FR1 eq_refl AINVq EVq (amd_frame_sbm _ _ SBq MH1)) as TIq.
    rewrite <- EVq in FR1.
    eapply (printf_c_call' yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) 0x8ef6c A1 mq mdq vv1 (0 + 1) [CB 40 j]);
      [ exact TIq | cbv delta [FRAME]; cbn [app]; exact FR1 | reflexivity | clear; lia | keeplia VlenI | clear; lia | reflexivity | ].
    clear TIq FR1. clear dependent mq. try clear SBq. try (clear dependent mdq). clear MU WM SHV.
    clear EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk MH1 LV1 TI1.
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' r2 A2 m2 md2 vv2 TI2 FR2.
    (* [comment removed for export] *)
    pose proof TI2 as TI0. unpack_tinv TI0. pose proof (as_minv LPA A2 _ _ AINVk) as [_ MH2].
    assert (LV2 : a_live A2 VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINVk LV2) as SHV. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV. rewrite <- EzsV in SHV.
    pose proof (cenv_intro A2 m2 md2 AINVk) as CE2. fold_aview.
    pose proof (global_shadow_pat (aview A2 m2) 0x217e0 2 32 (proj1 CE2) ltac:(gdesc_in)) as SHU.
    unfold vep_cells in VEPC. rewrite EURL in VEPC. cbn [vi_url VIA] in VEPC. cbv delta [FRAME' FRAME] in FR2. cbn [app] in FR2.
    pose proof (munch_refl [] (aview A2 m2)) as MU. pose proof (wmono_refl rsegs (aview A2 m2)) as WM.
    ago AINVk. fold_cl_segs.
    zstep. zstep. if_cases KS; zify_cond KS.
    - (* [comment removed for export] *)
      astopk AINVk MU WM I.
      pose proof (tinv_xfer' yi bs A2 m2 md2 vv2 (0 + 1 + 1) [] _ mq mdq [CB 40 j] TI2 MU WM MIk ltac:(intros a__ X; exfalso; exact (X I)) STk FR2 eq_refl AINVq EVq (amd_frame_sbm _ _ SBq MH2)) as TIq.
      rewrite <- EVq in FR2.
      replace (Z_to_bv 64 (vb_buf yi)) with (Z_to_bv 64 (vb_buf yi + 0)) by (f_equal; clear; lia).
      eapply (seg_mid yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A2 mq mdq vv2 (0 + 1 + 1) 0);
        [ exact TIq | cbv delta [FRAME' FRAME]; cbn [app]; exact FR2 | clear; lia | keeplia VlenI | keeplia VlenI | exact NUL ].
    - (* [comment removed for export] *)
      zstep. vchk SHV EzsV 8 0. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      lit_chk1 SHU 137184 17.
      zstep. zstep. if_cases U1; zify_cond U1; [| exfalso; apply U1; reflexivity].
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      lit_chk1 SHU 137185 17.
      zstep. zstep. if_cases U2; zify_cond U2; [exfalso; clear - U2; lia|].
      zstep. if_cases U3; zify_cond U3; [| exfalso; apply U3; reflexivity].
      (* [comment removed for export] *)
      zstep. if_cases U4; zify_cond U4; [| exfalso; clear - U4; lia].
      vrechk SHV EzsV (VEP + 8) 8 0.
      zstep. zstep. zstep. zstep. zstep.
      astopk AINVk MU WM I.
      pose proof (tinv_xfer' yi bs A2 m2 md2 vv2 (0 + 1 + 1) [] _ mq mdq [CB 40 j] TI2 MU WM MIk ltac:(intros a__ X; exfalso; exact (X I)) STk FR2 eq_refl AINVq EVq (amd_frame_sbm _ _ SBq MH2)) as TIq.
      rewrite <- EVq in FR2.
      eapply (printf_call' FMT_PFX 6 2 PRE_PFX OUT_PFX eq_refl HOUT_PFX HOUT1_PFX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pf3s.pc1_pfx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_p0nl.pc2_pfx FMTB_PFX SLOTS_S pcm_fmt_pfx FBY_PFX yi bs
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A_fmtpfx 137184 [] 1 0x8f004 A2 mq mdq vv2 (0 + 1 + 1) [CB 40 j]);
        [ exact TIq | cbv delta [FRAME]; cbn [app]; exact FR2 | reflexivity | apply fmt_pfx_at | unfold IMG_LO, A_fmtpfx; clear; lia | unfold RO_TOP, A_fmtpfx; clear; lia | apply fmt_pfx_range
        | exists (Z_to_bv 64 0); split; [reflexivity|]; split; [reflexivity|];
          assert (SZ0 : sint32 (Z_to_bv 64 0) = 0) by (vm_compute; reflexivity);
          unfold str_arg_ok, memchr_ok; rewrite SZ0; unfold INT_MAX; clear; cbv; intuition congruence
        | exists (Z_to_bv 64 137184); split; [reflexivity| rewrite unsigned_lit by (clear; lia); clear; lia]
        | apply bytes_at_nil; clear; lia | left; split; [reflexivity| right; clear; lia]
        | vm_compute; reflexivity | clear; lia | keeplia VlenI | clear; lia | reflexivity | ].
      clear TIq FR2. clear dependent mq. try clear SBq. try (clear dependent mdq). clear MU WM SHV SHU CE2.
      clear EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk MH2 LV2 TI2.
      intros t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x r3 A3 m3 md3 vv3 TI3 FR3.
      (* [comment removed for export] *)
      pose proof TI3 as TI0. unpack_tinv TI0. pose proof (as_minv LPA A3 _ _ AINVk) as [_ MH3].
      pose proof (munch_refl [] (aview A3 m3)) as MU. pose proof (wmono_refl rsegs (aview A3 m3)) as WM.
      cbv delta [FRAME' FRAME] in FR3. cbn [app] in FR3.
      ago AINVk. fold_cl_segs. zstep.
      astopk AINVk MU WM I.
      pose proof (tinv_xfer' yi bs A3 m3 md3 vv3 (0 + 1 + 1 + 1) [] _ mq mdq [CB 40 j] TI3 MU WM MIk ltac:(intros a__ X; exfalso; exact (X I)) STk FR3 eq_refl AINVq EVq (amd_frame_sbm _ _ SBq MH3)) as TIq.
      rewrite <- EVq in FR3.
      replace (Z_to_bv 64 (vb_buf yi)) with (Z_to_bv 64 (vb_buf yi + 0)) by (f_equal; clear; lia).
      eapply (seg_mid yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A3 mq mdq vv3 (0 + 1 + 1 + 1) 0);
        [ exact TIq | cbv delta [FRAME' FRAME]; cbn [app]; exact FR3 | clear; lia | keeplia VlenI | keeplia VlenI | exact NUL ].
  Qed.
End S.
End A_ve6k0.


Module A_vep3z.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4 RA_vrdi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pf3s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pis0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_p0nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpnnp AIcptdg AIcp2kv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5 AIcpzt2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5.AIcp1os OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpzt2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcp8zl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_La0bg A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VSe3i A_VSa8f A_VStbd A_VEr47 A_VSbb4 A_VS41f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_veqih.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS160 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSe90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSq5u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSt8w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS8zm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_veq11 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_ve5c7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_ve6k0.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strchr_icpt_post, DATA_STACK, LEN_STACK, ASSERT_STACK, STRCHR_ICPT_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].



(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kit5.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma strchr_icpt_cells_of_consts : forall v, consts_hold LPA v -> strchr_icpt_cells v.
  Proof.
    intros v CH. eapply (strchr_icpt_cells_of_bytes v pa_common_flags_bytes);
      [ .. | exact (map_cells_of_consts v CH)];
      first [ reflexivity | (apply (consts_lookup v _ _ CH); vm_compute; reflexivity) ].
  Qed.
End Kit5.

Lemma u8arr_suffix : forall m B bs (i : Z),
  u8arr rsegs m B bs -> 0 <= i -> (Z.to_nat i <= length bs)%nat -> bytes_at rsegs m (B + i) (skipn (Z.to_nat i) bs).
Proof.
  intros m B bs i [BA _] Hi Hn.
  rewrite <- (firstn_skipn (Z.to_nat i) bs) in BA. apply bytes_at_app in BA. destruct BA as [_ BA].
  rewrite firstn_length_le in BA by lia. replace (B + Z.of_nat (Z.to_nat i)) with (B + i) in BA by lia. exact BA.
Qed.

Lemma nonul_firstn : forall (str : list byte) k, ~ In (Z_to_bv 8 0) str -> find_byte 0 (firstn k str) = None.
Proof.
  intros str k NZ. apply find_byte_notin. intros b IN E. apply NZ.
  replace (Z_to_bv 8 0) with b; [| apply bv_eq; rewrite E; reflexivity].
  rewrite <- (firstn_skipn k str). apply in_app_iff. left. exact IN.
Qed.

(* [comment removed for export] *)
Lemma host_arg_ok2 : forall (str : list byte) (jx : nat) (HS : Z),
  ~ In (Z_to_bv 8 0) str -> (jx < length str)%nat -> 0 < HS -> Z.of_nat (length str) + 2 < 2^31 - 16 ->
  str_arg_ok (Z_to_bv 64 (Z.of_nat jx)) HS (str ++ [Z_to_bv 8 0])
  /\ Z.of_nat (length (out_s (Z_to_bv 64 (Z.of_nat jx)) (str ++ [Z_to_bv 8 0]))) = Z.of_nat jx.
Proof.
  intros str jx HS NZ JL H0 JB.
  assert (SJ : sint32 (Z_to_bv 64 (Z.of_nat jx)) = Z.of_nat jx).
  { unfold sint32. rewrite unsigned_lit by lia. apply swrap32_id. lia. }
  assert (FJ : firstn jx (str ++ [Z_to_bv 8 0]) = firstn jx str).
  { rewrite firstn_app. replace (jx - length str)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r. }
  assert (FB : find_byte 0 (firstn (Z.to_nat (Z.of_nat jx)) (str ++ [Z_to_bv 8 0])) = None).
  { rewrite Nat2Z.id, FJ. apply nonul_firstn. exact NZ. }
  assert (LH : length (str ++ [Z_to_bv 8 0]) = S (length str)) by (rewrite length_app; cbn [length]; lia).
  split.
  - unfold str_arg_ok. rewrite SJ. unfold INT_MAX. split; [lia|]. split; [exact H0|]. split.
    + unfold memchr_ok. rewrite FB. rewrite LH. lia.
    + rewrite LH. lia.
  - unfold out_s, strnlen_res. rewrite SJ, FB. rewrite Nat2Z.id, FJ. rewrite firstn_length_le by lia. reflexivity.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (vi : option vsb_rec) (H : henv) (lo SB N : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HFL : 0 <= vv Fflags < 16.
  Hypothesis HET : bool01 (vv Femptytag).
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis HLM : vv Flast_mark = 1.
  Hypothesis HAZ : vv Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis SZB : vb_size vr <= vb_len vr + 4096.
  Hypothesis LENB : vb_len vr + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  Hypothesis LBM : a_livebytes A0 + vb_size vr + vb_len vr + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : match vi with Some yi => vb_len yi / 4096 | None => 0 end + 8 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM + (PPOT_CAP - vsb_ppot vr) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis LF : lib_frames A0.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fvsb /\ vv Finclude_src <> vb_buf vr /\
                   vb_buf yi <> vv Fvsb /\ vb_buf yi <> vb_buf vr
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - DOINCL_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q -> vkeep vv vv' [Fstate; Finclude_src; Finclude_continue] ->
      (vv' Fstate = vv Fstate \/ vv' Fstate = vi_st VIA S_TagError) -> bool01 (vv' Finclude_continue) -> vv' Finclude_src = 0 ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      match vi with
      | None => (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0
      | Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                   (forall r, r <> vb_buf vr -> r <> vb_buf vr' -> r <> vv Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A0 r) /\
                   a_livebytes A' = a_livebytes A0 + (vb_size vr' - vb_size vr) - 40 - vb_size yi /\ a_nlive A' = a_nlive A0 - 2
      end ->
      frames_aged A0 A' 1 1 -> a_tinycred A' = a_tinycred A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40)
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HFL (conj HET (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB
      (conj SZB (conj LENB (conj LBM (conj NLV (conj SCM (conj PRM (conj LF (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO (conj SPHI
      (conj STKSH K))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Let TINV := tinv VEP vv tag q vr vi H lo SB N sp m0 md0 A0.
  Let FRAME' := FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Local Ltac pose_parts :=
    pose proof (printf_call VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as printf_call';
    pose proof (printf_c_call VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as printf_c_call';
    pose proof (tinv_xfer VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as tinv_xfer';
    pose proof (seg_end VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_end';
    pose proof (seg_loop VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_loop';
    pose proof (seg_mid VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_mid';
    pose proof (CFP VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as CFP';
    pose proof (W_cover VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as W_cover'.

  Local Ltac unpack_tinv TI :=
    (first [ dand26 TI as EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & VEPC & SOBJk & NEBk & LENk & SZk & RELk & LIVEk & LBk & TCk & NLk & SCk & PCk & FSk & STKSHk
                    & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Let SCR5' := SCR5 VEP.
  (* [comment removed for export] *)
  Let W : list (Z * Z) := [(bv_unsigned sp - DOINCL_STACK, bv_unsigned sp); (h_ff H + 1336, h_ff H + 1352); (VEP, VEP + 312)].

  (* [comment removed for export] *)
  Local Ltac henv_here mx MU WM CNT HENVx DJ GCE GHI SHF VEPlo :=
    try unhide DJ;
    lazymatch goal with HGx : henv_geom LPA H |- _ =>
    let ACV := fresh "ACV" in pose proof alloc_ceiling_num as ACV;
    let HFRM := fresh "HFRM" in let GLOB := fresh "GLOB" in let HOBJ := fresh "HOBJ" in let HSH := fresh "HSH" in
    let BSSV := fresh "BSSV" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT'" in
    pose proof HENV as (HFRM & GLOB & HOBJ & HSH);
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as BSSV BSS CP _ | pose proof GLOB as (BSSV & BSS & CP & _) ]); fold_cl_segs; cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS; unfold h_vsc, h_cp in BSSV, BSS, CP;
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in BSS; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in CP; [| exact MU| exact WM| cbn; keeplia DJ GHI GCE VEPlo ACV CEIL LO];
    destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
    assert (HENVx : henv_ok LPA VIA H A0 mx);
    [ split; [exact HFRM|]; split;
      [ eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp;
        [exact BSSV| exact BSS| exact CP| replace (h_ff H + 32 + 1304) with (h_ff H + 1336) by lia; exact C]
      | split; [ eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|];
                 intros a__ Ha__; unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_vsc in *; cbn [outside]; keeplia Ha__ DJ GHI GCE ACV CEIL LO
               | eapply (hshadow_munch LPA); [exact HSH| exact MU| exact HGx|];
                 intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ SHF GCE VEPlo ACV CEIL LO ] ]
    | clear BSSV BSS CP C c HFRM GLOB HOBJ HSH ACV ]
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 T fc F tp gp"] Lemma tinv_init : forall (yi : vsb_rec) (bs : list byte) (v : mem) (mq : mem) (mdq : Model) (sc : list cell) (cnt : list byte),
    vi = Some yi ->
    munch W (aview A0 m0) v -> wmono rsegs (aview A0 m0) v -> mem_inv rsegs v ->
    stk rsegs v lo (bv_unsigned sp + -144) ->
    rw_cells rsegs v (bv_unsigned sp + -144) (FRAME' sc) -> cells_size sc = 40%nat ->
    rw_cells rsegs v VEP (vep_cells vv tag q) ->
    rw_cells rsegs v (h_ff H + 1336) [CB 16 cnt] ->
    u8arr rsegs (aview A0 m0) (vb_buf yi) bs -> Z.of_nat (length bs) = vb_size yi ->
    ainv A0 mq mdq -> aview A0 mq = v -> amd_frame md0 mdq ->
    TINV yi bs A0 mq mdq vr 0.
  Proof.
    touch_all. intros until cnt. intros EVI MU WM MI ST FR SC40 VEPC CNT U8 LBS AINVq EV MDF. pose_parts.
    prelims. cbv delta [W] in MU. cbv delta [FRAME' FRAME] in FR.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_3; dand7 dR_3 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ)) as dR_5; dand11 dR_5 as S16 Slo Shi _ B16 Blo Bhi _ DSB _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ) as (S16 & Slo & Shi & _ & B16 & Blo & Bhi & _ & DSB & _ & _) ]).
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS. pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_6; dand11 dR_6 as SI16 SIlo SIhi _ BI16 BIlo BIhi _ _ _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (SI16 & SIlo & SIhi & _ & BI16 & BIlo & BIhi & _ & _ & _ & _) ]).
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI. pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI.
    unfold kHighMemBeg in VEPlo, Slo, Blo, SIlo, BIlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 S 40 AINV00 VLV LS NES) as DVS.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 (vb_buf vr) (vb_size vr) AINV00 VLV LB NEB) as DVB.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LSI (not_eq_sym NIS)) as DVSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LBI (not_eq_sym NIB)) as DVBI.
    pose proof (proj1 HENV) as [ageh HFRh].
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LB) as DJfB.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LSI) as DJfSI.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LBI) as DJfBI.
    change (fsize HCLASS) with 8192 in DJfV, DJfS, DJfB, DJfSI, DJfBI.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    henv_here v MU WM CNT HENVv DJfV GCE GHI SHF VEPlo.
    unfold TINV, tinv. rewrite EV.
    split; [exact EVI|]. split; [exact AINVq|]. split; [exact MI|]. split; [exact MDF|]. split; [exact ST|].
    split; [exact HENVv|]. split; [exact VEPC|].
    split. { eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM|]. intros a Ha. cbn. keeplia Ha Shi Bhi DJfS DJfB DVS DVB ACV CEIL LO. }
    split; [exact NEB|]. split; [clear; lia|]. split; [clear; lia|]. split; [left; reflexivity|]. split; [intros; reflexivity|].
    split; [clear; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|]. split; [clear; lia|] (* [comment removed for export] *). split; [intros ff; reflexivity|].
    split. { pose proof STKSH as (SSB & SSN & _ & _ & SSC & SST). unfold kHighMemBeg in SST. all_app_facts.
             eapply stack_shadow_again; [exact STKSH| | reflexivity].
             eapply (bytes_at_munch LPA); [exact SSB| exact MU|]. rewrite ?zeros_length, ?repeat_length, Z2Nat.id by exact SSN.
             intros a Ha. cbn. keeplia Ha SST SSC ACV CEIL LO GCE VEPlo. }
    split. { ufs. eapply (cframe_noalloc LPA); [exact MU| | | intros a X; right; left; exact X].
             - intros a Ha NO. apply (W_cover' (vsb_blocks (vv Finclude_src) yi)); [exact Ha| ufs; exact NO].
             - eapply (window_mapped LPA _ lo (bv_unsigned sp + -144) (bv_unsigned sp));
                 [exact ST | exact FR | rewrite cells_size_app, SC40; cbn [cells_size csize Nat.add]; clear; lia | exact CEIL | keeplia LO | clear; lia]. }
    split. { eapply vsb_obj_munch; [exact IOBJ| exact MU| exact WM|]. intros a Ha. cbn. keeplia Ha SIhi BIhi DJfSI DJfBI DVSI DVBI ACV CEIL LO. }
    split. { destruct U8 as [UB UW]. split; [| eapply wr_at_transport; [exact UW| exact WM]].
             eapply (bytes_at_munch LPA); [exact UB| exact MU|]. rewrite LBS. intros a Ha. cbn. keeplia Ha BIhi DJfBI DVBI ACV CEIL LO. }
    split; [exact LBS|]. split; [exact NISB| exact NIBB].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vr"] Lemma seg_err : forall (yi : vsb_rec) (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (m1 : mem) (j40 cnt : list byte),
    vi = Some yi ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -144) (FRAME' [CB 40 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1 a0 a1 a2 a3 a4 a5 a6 a7
                 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 280)) xs10 xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x8f430) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    (* [comment removed for export] *)
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_8; dand7 dR_8 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ)) as dR_9; dand11 dR_9 as S16 Slo Shi _ B16 Blo Bhi _ DSB _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ) as (S16 & Slo & Shi & _ & B16 & Blo & Bhi & _ & DSB & _ & _) ]).
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS. pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_10; dand11 dR_10 as SI16 SIlo SIhi _ BI16 BIlo BIhi _ DSBI _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (SI16 & SIlo & SIhi & _ & BI16 & BIlo & BIhi & _ & DSBI & _ & _) ]).
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI. pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI.
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_11; dand3 dR_11 as VszI VlenI _ | pose proof VINVI as (VszI & VlenI & _) ]).
    unfold kHighMemBeg in VEPlo, Slo, Blo, SIlo, BIlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 S 40 AINV00 VLV LS NES) as DVS.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 (vb_buf vr) (vb_size vr) AINV00 VLV LB NEB) as DVB.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI VLV NIS) as DVSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI VLV NIB) as DVBI.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI LS NISS) as DSSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI LS NIBS) as DBSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI LB NISB) as DSBI'.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI LB NIBB) as DBBI.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LB) as DJfB.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LSI) as DJfSI.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LBI) as DJfBI.
    change (fsize HCLASS) with 8192 in DJfV, DJfS, DJfB, DJfSI, DJfBI.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (conj (sh_boundL (Clg:=Clg) S 40 ltac:(keeplia Slo) ltac:(clear; lia) ltac:(exact Shi)) (sh_top_le' S 40 ltac:(keeplia Slo) ltac:(clear; lia) ltac:(exact Shi))) as SHSB. rewrite SHMAX_val in SHSB.
    pose proof (conj (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(keeplia Blo) ltac:(try (generalize alloc_ceiling_val); clear - SOBJ; try pose proof alloc_ceiling_val as ACV__; pose proof (proj1 (proj1 (proj2 SOBJ))); lia) ltac:(exact Bhi))
                     (sh_top_le' (vb_buf vr) (vb_size vr) ltac:(keeplia Blo) ltac:(try (generalize alloc_ceiling_val); clear - SOBJ; try pose proof alloc_ceiling_val as ACV__; pose proof (proj1 (proj1 (proj2 SOBJ))); lia) ltac:(exact Bhi))) as SHBB. rewrite SHMAX_val in SHBB.
    pose proof (conj (sh_boundL (Clg:=Clg) (vv Finclude_src) 40 ltac:(keeplia SIlo) ltac:(clear; lia) ltac:(exact SIhi)) (sh_top_le' (vv Finclude_src) 40 ltac:(keeplia SIlo) ltac:(clear; lia) ltac:(exact SIhi))) as SHSI. rewrite SHMAX_val in SHSI.
    pose proof (conj (sh_boundL (Clg:=Clg) (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi)) (sh_top_le' (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi))) as SHBI. rewrite SHMAX_val in SHBI.
    (* [comment removed for export] *)
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    (* [comment removed for export] *)
    pose proof (got_vsc_cell m1 (proj1 CE1)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    pose proof HENV as (_ & GLOB & HOBJ & HSH).
    (first [ pose proof (HSH) as dR_12; dand10 dR_12 as SHvs _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHvs & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHvs, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHwR. rewrite SHMAX_val in SHwR.
    eapply (bytes_at_munch LPA) in SHvs; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHVR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHc; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHcR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHw; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHwR GCE VEPlo LO CEIL ACV].
    (first [ pose proof ((shadowed_bss_vsc _ (proj1 CE1))) as dR_13; dand8 dR_13 as PG NG SHG GAL G0 GLE GGE GCE' | destruct (shadowed_bss_vsc _ (proj1 CE1)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE') ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (GLOB) as dR_14; dand4 dR_14 as BSSV _ _ _ | pose proof GLOB as (BSSV & _ & _ & _) ]). fold_cl_segs. cbn [vi_bss_vsc VIA] in BSSV. unfold h_vsc in BSSV.
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO].
    (first [ pose proof (HOBJ) as dR_15; dand3 dR_15 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    eapply (rw_cells_munch LPA) in VC; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    eapply (rw_cells_munch LPA) in WK; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    (* [comment removed for export] *)
    assert (IOBJ1 : vsb_obj LPA A0 m1 (vv Finclude_src) yi true).
    { eapply vsb_obj_munch; [exact IOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SIhi BIhi DJfSI DJfBI DVSI DVBI ACV CEIL LO]. }
    hide DVS. hide DVB. hide DVSI. hide DVBI. hide DSSI. hide DBSI. hide DSBI'. hide DBBI. hide DJfV. hide DJfS. hide DJfB. hide DJfSI. hide DJfBI.
    hide DSB. hide DSBI. hide_neqs.
    unfold vep_cells in VEPC. rewrite EVC in VEPC. unfold h_vc in VEPC. rewrite HAZ in VEPC. cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    (* [comment removed for export] *)
    fold_cl_segs. unhide DJfV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    shadow_addr_at SHG 6191680 8.
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end.
    zstep. zstep; if_cases K0; zify_cond K0;
      [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
      | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk0 SHvs 8. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep. shadow_chk0 SHc 8. zstep. zstep. shadow_chk0 SHw 8.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    zstep. carve_frame 48%nat ST.
    try replace (bv_unsigned sp + -144 + -48) with (bv_unsigned sp + -192) in * by lia.
    do 8 zstep.
    try replace (bv_unsigned sp + -192 + 48) with (bv_unsigned sp + -144) by lia.
    lazymatch goal with FRv : rw_cells _ ?mx (bv_unsigned sp + -192) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      release_frame FRv ST (bv_unsigned sp + -144) end.
    lazymatch goal with X : rw_cells rsegs ?mx (h_ff H + 1336) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (rw_cells_forget _ _ _ _ X) as [cnt' CNT']; cbn [cells_size csize Nat.add] in CNT'; clear X end.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep.
    zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
    hide DJfV.
    (* [comment removed for export] *)
    zstep. zstep. do 13 zstep. zstep.
    try replace (bv_unsigned sp + -144 + 144) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    astop AINV00 MU WM CFP'.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, VEPCq : rw_cells _ ?ma VEP _, CNTq : rw_cells _ ?ma (h_ff H + 1336) _, STq : stk _ ?ma lo _, FRq : rw_cells _ ?ma (bv_unsigned sp + -144) _
      |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa;
      henv_here ma MU WM CNTq HENVa DJfV GCE GHI SHF VEPlo;
      release_frame FRq STq (bv_unsigned sp); rename STq into STw;
      (* [comment removed for export] *)
      (first [ pose proof ((rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (vv Finclude_src))) VEPCq eq_refl)) as dR_18; dand3 dR_18 as VA VM VBk | pose proof (rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (vv Finclude_src))) VEPCq eq_refl) as (VA & VM & VBk) ]); clear VEPCq;
      cbn [firstn skipn cells_size csize Nat.add length] in VA, VM, VBk;
      change (Z.of_nat 280) with 280 in VM; change (Z.of_nat 280) with 280 in VBk; change (Z.of_nat 8) with 8 in VBk;
      replace (VEP + 280 + 8) with (VEP + 288) in VBk by lia
    end.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
      assert (IOBJa : vsb_obj LPA A0 (aview A0 mq) (vv Finclude_src) yi true)
        by (unhide DJfSI; unhide DJfBI; unhide DVSI; unhide DVBI;
            eapply vsb_obj_munch; [exact IOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SIhi BIhi DJfSI DJfBI DVSI DVBI ACV CEIL LO]);
      assert (SOBJa : vsb_obj LPA A0 (aview A0 mq) S vr false)
        by (unhide DJfS; unhide DJfB; unhide DVS; unhide DVB;
            eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi DJfS DJfB DVS DVB ACV CEIL LO]) end.
    clear IOBJ1.
    unhide NIS. unhide NIB.
    eapply (VSB_destroy_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _ A0 (VEP + 280) (vv Finclude_src) yi true lo);
      [ exact AINVa | assumption | reflexivity | exact VM
      | eapply cobj_block; [exact VLV| cbn; intros [X|[X|X]]; [exact (NIS X)| exact (NIB X)| exact X] | lia | lia]
      | rewrite Z.add_mod, V8 by lia; reflexivity
      | keeplia VEPhi
      | exact IOBJa | exact TP | exact SP16 | exact STw | exact CEIL | ufs; keeplia LO | ].
    hide NIS. hide NIB.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 mf mdf. cbv zeta.
    intros AINV1 MI1 MDF1 FRS1 LB1 TC1 NL1 SC1 PC1 ST1 PSC DEADI DEADBI LIVEq CF1. ufs.
    unhide_neqs.
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NIS) (not_eq_sym NIB)); exact VLV).
    assert (LS1 : a_live A1 S = Some 40) by (rewrite (LIVEq S (not_eq_sym NISS) (not_eq_sym NIBS)); exact LS).
    assert (LBF1 : a_live A1 (vb_buf vr) = Some (vb_size vr)) by (rewrite (LIVEq (vb_buf vr) (not_eq_sym NISB) (not_eq_sym NIBB)); exact LB).
    (* [comment removed for export] *)
    assert (HENV1 : henv_ok LPA VIA H A1 (aview A1 mf)).
    { eapply (henv_ok_acall_gen H A0 A1); [exact AINVa| exact CF1| exact HENVa| keeplia CEIL LO| intros ff k age HFf; exists age; rewrite (FRS1 ff); exact HFf|].
      intros a [X|[X|X]].
      - exists (vv Finclude_src), 40. split; [exact LSI|]. unfold newblk, blk in X. keeplia X.
      - exists (vb_buf yi), (vb_size yi). split; [exact LBI|]. unfold newblk, blk in X. keeplia X.
      - exists VEP, 312. split; [exact VLV|]. left. keeplia X. }
    (* [comment removed for export] *)
    unhide DVSI. unhide DVBI. unhide DSSI. unhide DBSI. unhide DSBI'. unhide DBBI.
    lazymatch type of CF1 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 VEP) in VA;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 VEP 280 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; rewrite ?TAG8; cbn [Nat.add]; split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DVSI DVBI SHSI SHBI VEPlo] ];
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 (VEP + 288)) in VBk;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 (VEP + 288) 24 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length];
           split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DVSI DVBI SHSI SHBI VEPlo] ];
      assert (SOBJ1 : vsb_obj LPA A1 mb S vr false);
      [ eapply (vsb_obj_ccall A0 A1); [exact AINVa| exact CF1| exact SOBJa| keeplia CEIL LO| exact LS1| exact LBF1|];
        intros a Ha X; unfold newblk, blk in X; keeplia Ha X DSSI DBSI DSBI' DBBI DVS DVB SHSI SHBI Slo Blo VEPlo
      | ]
    end.
    hide DVSI. hide DVBI. hide DSSI. hide DBSI. hide DSBI'. hide DBBI.
    assert (VEPC1 : rw_cells rsegs (aview A1 mf) VEP (vep_cells (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Finclude_src 0) tag q)).
    { rewrite <- vep_cells_include_src. unfold vep_cells. cbn [firstn skipn fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA].
      rewrite EVC, HAZ. unfold h_vc.
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs (aview A1 mf) VEP pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; rewrite ?TAG8; cbn [Nat.add]; change (Z.of_nat 280) with 280; change (Z.of_nat 8) with 8; lia]. }
    clear VA VBk PSC.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 mf mdf (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Finclude_src 0) vr);
      [ exact AINV1 | exact MI1
      | eapply amd_frame_sbm_l; [exact SBM| exact MH| exact MDF1]
      | exact ST1 | exact HENV1
      | split; [exact LVEP1|]; split; [exact VEPC1|]; split; [exact TAG8| exact PADS]
      | vkeep_tac (vkeep_refl vv [Fstate; Finclude_src; Finclude_continue])
      | right; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; reflexivity
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact HIC
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; reflexivity
      | exact SOBJ1
      | rewrite EVI; keeplia VlenI | clear; lia | left; reflexivity
      | rewrite EVI; split; [exact DEADI|]; split; [exact DEADBI|]; split;
        [ intros r R1 R2 R3 R4; exact (LIVEq r R3 R4) | split; [rewrite LB1; clear; lia| exact NL1] ]
      | split; [intros ff k age HFf; exists 0%nat; rewrite Nat.add_0_r, (FRS1 ff); split; [exact HFf| clear; lia]
              | intros ff HFf; rewrite (FRS1 ff); exact HFf]
      | exact TC1 | rewrite SC1; clear; lia | rewrite PC1; clear; lia (* [comment removed for export] *)
      | ].
    (* [comment removed for export] *)
    unhide DVS.
    lazymatch type of CF1 with cframe _ _ _ _ _ _ _ ?ma ?mb =>
      eapply (cframe_extend LPA _ _ (bv_unsigned sp) _ (bv_unsigned sp) _ _ _ _ _ (aview A0 m0) ma mb mb W []);
        [ cbv delta [W]; ufs; exact MU | cbv delta [W]; ufs; rewrite EVI; apply W_cover' | exact CF1 | ufs; clear; lia | clear; lia
        | rewrite EVI; intros a [X|[X|X]]; [right; right; right; left; left; exact X | right; right; right; left; right; exact X | left; split; [keeplia VEPlo| keeplia X]]
        | intros a X; right; right; left; exact X
        | apply munch_refl
        | intros a _ X; exfalso; apply X; exact I
        | eapply (stk_mapped (L:=LPA)); [exact ST1 | exact CEIL | keeplia LO | clear; lia] ]
    end.
  Qed.
End S.
End A_vep3z.


Module A_ve8qw.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4 RA_vrdi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pnyh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pf3s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pis0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_p0nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpnnp AIcptdg AIcp2kv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5 AIcpzt2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5.AIcp1os OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpzt2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcp8zl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_La0bg A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VSe3i A_VSa8f A_VStbd A_VEr47 A_VSbb4 A_VS41f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_veqih.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS160 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSe90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSq5u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSt8w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS8zm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_veq11 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_ve5c7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_ve6k0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_vep3z.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strchr_icpt_post, DATA_STACK, LEN_STACK, ASSERT_STACK, STRCHR_ICPT_STACK in H.
(* [comment removed for export] *)
Ltac simpl_sizes ::=
  rewrite ?app_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length];
  try (rewrite vep_cells_size by assumption); try (rewrite vsb_cells_size).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].



Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (vi : option vsb_rec) (H : henv) (lo SB N : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HFL : 0 <= vv Fflags < 16.
  Hypothesis HET : bool01 (vv Femptytag).
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis HLM : vv Flast_mark = 1.
  Hypothesis HAZ : vv Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis SZB : vb_size vr <= vb_len vr + 4096.
  Hypothesis LENB : vb_len vr + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  Hypothesis LBM : a_livebytes A0 + vb_size vr + vb_len vr + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : match vi with Some yi => vb_len yi / 4096 | None => 0 end + 8 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM + (PPOT_CAP - vsb_ppot vr) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis LF : lib_frames A0.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fvsb /\ vv Finclude_src <> vb_buf vr /\
                   vb_buf yi <> vv Fvsb /\ vb_buf yi <> vb_buf vr
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - DOINCL_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q -> vkeep vv vv' [Fstate; Finclude_src; Finclude_continue] ->
      (vv' Fstate = vv Fstate \/ vv' Fstate = vi_st VIA S_TagError) -> bool01 (vv' Finclude_continue) -> vv' Finclude_src = 0 ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      match vi with
      | None => (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0
      | Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                   (forall r, r <> vb_buf vr -> r <> vb_buf vr' -> r <> vv Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A0 r) /\
                   a_livebytes A' = a_livebytes A0 + (vb_size vr' - vb_size vr) - 40 - vb_size yi /\ a_nlive A' = a_nlive A0 - 2
      end ->
      frames_aged A0 A' 1 1 -> a_tinycred A' = a_tinycred A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40)
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HFL (conj HET (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB
      (conj SZB (conj LENB (conj LBM (conj NLV (conj SCM (conj PRM (conj LF (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO (conj SPHI
      (conj STKSH K))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Let TINV := tinv VEP vv tag q vr vi H lo SB N sp m0 md0 A0.
  Let FRAME' := FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Local Ltac pose_parts :=
    pose proof (printf_call VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as printf_call';
    pose proof (printf_c_call VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as printf_c_call';
    pose proof (tinv_xfer VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as tinv_xfer';
    pose proof (seg_end VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_end';
    pose proof (seg_loop VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_loop';
    pose proof (seg_mid VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_mid';
    pose proof (CFP VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as CFP';
    pose proof (W_cover VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as W_cover';
    pose proof (seg_err VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_err';
    pose proof (tinv_init VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as tinv_init'.

  Local Ltac unpack_tinv TI :=
    (first [ dand26 TI as EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & VEPC & SOBJk & NEBk & LENk & SZk & RELk & LIVEk & LBk & TCk & NLk & SCk & PCk & FSk & STKSHk
                    & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Let SCR5' := SCR5 VEP.
  (* [comment removed for export] *)
  Let W : list (Z * Z) := [(bv_unsigned sp - DOINCL_STACK, bv_unsigned sp); (h_ff H + 1336, h_ff H + 1352); (VEP, VEP + 312)].

  (* [comment removed for export] *)
  Local Ltac henv_here mx MU WM CNT HENVx DJ GCE GHI SHF VEPlo :=
    try unhide DJ;
    lazymatch goal with HGx : henv_geom LPA H |- _ =>
    let ACV := fresh "ACV" in pose proof alloc_ceiling_num as ACV;
    let HFRM := fresh "HFRM" in let GLOB := fresh "GLOB" in let HOBJ := fresh "HOBJ" in let HSH := fresh "HSH" in
    let BSSV := fresh "BSSV" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT'" in
    pose proof HENV as (HFRM & GLOB & HOBJ & HSH);
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as BSSV BSS CP _ | pose proof GLOB as (BSSV & BSS & CP & _) ]); fold_cl_segs; cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS; unfold h_vsc, h_cp in BSSV, BSS, CP;
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in BSS; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in CP; [| exact MU| exact WM| cbn; keeplia DJ GHI GCE VEPlo ACV CEIL LO];
    destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
    assert (HENVx : henv_ok LPA VIA H A0 mx);
    [ split; [exact HFRM|]; split;
      [ eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp;
        [exact BSSV| exact BSS| exact CP| replace (h_ff H + 32 + 1304) with (h_ff H + 1336) by lia; exact C]
      | split; [ eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|];
                 intros a__ Ha__; unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_vsc in *; cbn [outside]; keeplia Ha__ DJ GHI GCE ACV CEIL LO
               | eapply (hshadow_munch LPA); [exact HSH| exact MU| exact HGx|];
                 intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ SHF GCE VEPlo ACV CEIL LO ] ]
    | clear BSSV BSS CP C c HFRM GLOB HOBJ HSH ACV ]
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vr"] Lemma seg_http : forall (yi : vsb_rec) (bs : list byte) (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs4 xt3 xt4 xt5 xt6 : word)
      (incl : Z) (m1 : mem) (j40 cnt : list byte),
    vi = Some yi ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -144) (FRAME' [CB 40 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    u8arr rsegs (aview A0 m0) (vb_buf yi) bs -> Z.of_nat (length bs) = vb_size yi -> nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    0 <= incl < 256 -> 8 <= vb_len yi ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880))
                 a0 a1 a2 a3 a4 a5 a6 a7
                 xs2 (Z_to_bv 64 (VEP + 8)) xs4 (Z_to_bv 64 (vb_len yi)) (Z_to_bv 64 incl)
                 (Z_to_bv 64 (vb_buf yi)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 280)) (Z_to_bv 64 (VEP + 288))
                 (Z_to_bv 64 ((VEP + 288) / 8 + 2147450880)) xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x8f0b0) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM U8 LBS NUL INCL L8. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    pose proof LENB as LENB'. rewrite EVI in LENB'. pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_4; dand7 dR_4 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI. pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_5; dand11 dR_5 as SI16 SIlo SIhi _ BI16 BIlo BIhi _ DSBI _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (SI16 & SIlo & SIhi & _ & BI16 & BIlo & BIhi & _ & DSBI & _ & _) ]).
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_6; dand8 dR_6 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    unfold kHighMemBeg in VEPlo, SIlo, BIlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LSI (not_eq_sym NIS)) as DVSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LBI (not_eq_sym NIB)) as DVBI.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LBI) as DJfBI.
    change (fsize HCLASS) with 8192 in DJfV, DJfBI.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (conj (sh_boundL (Clg:=Clg) (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi)) (sh_top_le' (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi))) as SHBIB. rewrite SHMAX_val in SHBIB.
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    assert (U81 : u8arr rsegs m1 (vb_buf yi) bs).
    { destruct U8 as [UB UW]. split; [| eapply wr_at_transport; [exact UW| exact WM]].
      eapply (bytes_at_munch LPA); [exact UB| exact MU|]. rewrite LBS. intros a Ha. cbn. keeplia Ha BIhi DJfBI DVBI GCE VEPlo ACV CEIL LO. }
    (* [comment removed for export] *)
    assert (NUL7 : nth_error (skipn 7 bs) (Z.to_nat (vb_len yi) - 7) = Some (Z_to_bv 8 0)).
    { rewrite nth_error_skipn. replace (7 + (Z.to_nat (vb_len yi) - 7))%nat with (Z.to_nat (vb_len yi)) by (clear - L8; lia). exact NUL. }
    (first [ pose proof ((cstr_split (skipn 7 bs) _ NUL7)) as dR_7; dex1 dR_7 as z; dand4 dR_7 as ZLE SPLIT NONUL LZ | pose proof ((cstr_split (skipn 7 bs) _ NUL7)) as dR_7; dand5 dR_7 as z ZLE SPLIT NONUL LZ | destruct (cstr_split (skipn 7 bs) _ NUL7) as (z & ZLE & SPLIT & NONUL & LZ) ]).
    assert (LREST : length (skipn 7 bs) = (length bs - 7)%nat) by (rewrite skipn_length; reflexivity).
    assert (LSL : Z.of_nat (length (skipn (Datatypes.S z) (skipn 7 bs))) = vb_size yi - 8 - Z.of_nat z).
    { rewrite skipn_length, LREST. clear - LBS ZLE VlenI L8. lia. }
    assert (STR : bytes_at rsegs m1 (vb_buf yi + 7) (firstn z (skipn 7 bs) ++ Z_to_bv 8 0 :: skipn (Datatypes.S z) (skipn 7 bs))).
    { rewrite <- SPLIT. apply (u8arr_suffix m1 (vb_buf yi) bs 7 U81); [clear; lia| clear - LBS VlenI L8; lia]. }
    hide DJfV. hide DJfBI. hide DVSI. hide DVBI. hide DSBI. hide_neqs.
    cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    icall (strchr_icpt_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (firstn z (skipn 7 bs)) (skipn (Datatypes.S z) (skipn 7 bs)) lo)
      by (cbv zeta; rewrite ?(unsigned_lit (vb_buf yi + 7)) by (keeplia BIlo BIhi VszI ACV); rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by (keeplia SPR LO CEIL ACV); rewrite ?unsigned_lit by (clear; lia);
          unfold STRCHR_ICPT_STACK;
          first [ exact STR
                | exact NONUL
                | exact MI
                | exact (strchr_icpt_cells_of_consts _ (proj1 CE1))
                | exact ST
                | exact CEIL
                | (rewrite LZ, LSL; unhide VbmI; clear - VbmI ZLE VlenI L8 LBS BI16; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia)
                | (left; rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add, Nat2Z.inj_succ, LZ, LSL; keeplia BIhi CEIL LO ZLE VlenI)
                | (change (47 mod 256) with 47; clear; lia)
                | keeplia BIlo
                | (rewrite LZ; keeplia ZLE VlenI LENB' Vlen0)
                | (rewrite LZ; eapply (range_ok_high_munch _ (aview A0 m0) m1);
                    [ eapply (live_range_ok A0 m0 md0 (vb_buf yi) (vb_size yi)); [exact AINV00| exact LBI| clear; lia| keeplia ZLE VlenI L8 LBS LREST| keeplia ZLE]
                    | exact MU | keeplia BIlo | keeplia ZLE | keeplia BIhi ZLE VlenI L8 LBS LREST
                    | repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; keeplia LO CEIL ACV GCE VEPlo ])
                | keeplia LO ]).
    clear CE1 STR. change (47 mod 256) with 47. unfold strchr_res.
    lazymatch goal with M : munch _ (aview A0 m0) ?v1, ST1 : stk _ ?v1 _ _, MI1 : mem_inv _ ?v1 |- evt _ _ (MS _ _ _ _ _ ?v1 _) =>
      rename v1 into m2; rename ST1 into ST2; rename MI1 into MI2 end.
    destruct (find_byte 47 (firstn z (skipn 7 bs))) as [jx|] eqn:FJ.
    - (* [comment removed for export] *)
      (first [ pose proof ((find_byte_Some _ _ _ FJ)) as dR_8; dand3 dR_8 as JLT _ _ | destruct (find_byte_Some _ _ _ FJ) as (JLT & _ & _) ]). rewrite LZ in JLT.
      (* [comment removed for export] *)
      zstep. if_cases KQ; zify_cond KQ.
      { exfalso. rewrite ?unsigned_lit in KQ by (keeplia BIlo BIhi VszI ACV JLT ZLE VlenI). keeplia KQ BIlo. }
      clear KQ. zstep.
      (* [comment removed for export] *)
      lazymatch goal with V : rw_cells _ ?mx VEP (vep_cells vv tag q) |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof V as VEPCu; unfold vep_cells in VEPCu end.
      vchk SHV EzsV 8 0. zstep. zstep. zstep. zstep. zstep. clear VEPCu.
      astopk AINV00 MU WM CFP'.
      lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, VEq : rw_cells _ ?mx VEP (vep_cells vv tag q), CNTq : rw_cells _ ?mx (h_ff H + 1336) _ |- _ =>
        pose proof (tinv_init' yi bs _ mq mdq [CB 40 j40] _ EVI MU WM MIq STq ltac:(cbv delta [FRAME' FRAME]; cbn [app]; exact FRq) eq_refl VEq CNTq U8 LBS AINVq EVq (amd_frame_sbm _ _ SBq MH)) as TIq;
        rewrite <- EVq in FRq;
        eapply (printf_c_call' yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 incl) 0x8f0ec A0 mq mdq vr 0 [CB 40 j40]);
        [ exact TIq | cbv delta [FRAME]; cbn [app]; exact FRq | reflexivity | clear; lia | keeplia VlenI | clear; lia | reflexivity | ]
      end.
      clear dependent mq. try clear SBq. try (clear dependent mdq). clear dependent m2. clear dependent m1. clear EVI LBS U8.
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A1 mk1 mdk1 vv1 TI1 FR1.
      (* [comment removed for export] *)
      pose proof TI1 as TI0. unpack_tinv TI0. pose proof (as_minv LPA A1 _ _ AINVk) as [_ MH1].
      assert (LV1 : a_live A1 VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
      pose proof (as_live_shadow LPA _ _ _ VEP 312 AINVk LV1) as SHV1. fold_cl_segs. fold_aview.
      change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV1. rewrite <- EzsV in SHV1.
      unfold vep_cells in VEPC. rewrite EVC in VEPC. unfold h_vc in VEPC. cbv delta [FRAME' FRAME] in FR1. cbn [app] in FR1.
      pose proof (munch_refl [] (aview A1 mk1)) as MU1. pose proof (wmono_refl rsegs (aview A1 mk1)) as WM1.
      hide_neqs.
      ago AINVk. fold_cl_segs.
      vrechk SHV1 EzsV (VEP + 8) 8 0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      replace (vb_buf yi + 7 + Z.of_nat jx - (vb_buf yi + 7)) with (Z.of_nat jx) by (clear; lia).
      rewrite (swrap32_id (Z.of_nat jx)) by (keeplia JLT ZLE VlenI LENB' Vlen0).
      astopk AINVk MU1 WM1 I.
      pose proof (tinv_xfer' yi bs A1 mk1 mdk1 vv1 (0 + 1) [] _ mq mdq [CB 40 j40] TI1 MU1 WM1 MIk ltac:(intros a__ X; exfalso; exact (X I)) STk FR1 eq_refl AINVq EVq (amd_frame_sbm _ _ SBq MH1)) as TIq.
      rewrite <- EVq in FR1.
      destruct (host_arg_ok2 (firstn z (skipn 7 bs)) jx (vb_buf yi + 7) NONUL ltac:(rewrite LZ; exact JLT) ltac:(keeplia BIlo) ltac:(rewrite LZ; keeplia ZLE VlenI LENB' Vlen0)) as [HARG HOUTL].
      assert (HSB : bytes_at rsegs (aview A1 mq) (vb_buf yi + 7) (firstn z (skipn 7 bs) ++ [Z_to_bv 8 0])).
      { pose proof (u8arr_suffix _ (vb_buf yi) bs 7 U8k ltac:(clear; lia) ltac:(keeplia LBS VlenI L8)) as STR'.
        change (Z.to_nat 7) with 7%nat in STR'. rewrite SPLIT in STR'.
        replace (firstn z (skipn 7 bs) ++ Z_to_bv 8 0 :: skipn (Datatypes.S z) (skipn 7 bs))
           with ((firstn z (skipn 7 bs) ++ [Z_to_bv 8 0]) ++ skipn (Datatypes.S z) (skipn 7 bs)) in STR' by (rewrite <- app_assoc; reflexivity).
        apply bytes_at_app in STR'. rewrite EVq. exact (proj1 STR'). }
      eapply (printf_call' FMT_HOST 13 3 PRE_HOST OUT_HOST eq_refl HOUT_HOST HOUT1_HOST OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pis0.pc1_host OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_p0nl.pc2_host FMTB_HOST SLOTS_S pcm_fmt_host FBY_HOST yi bs
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A_fmthost (vb_buf yi + 7) (firstn z (skipn 7 bs) ++ [Z_to_bv 8 0]) (7 + Z.of_nat jx) 0x8f110 A1 mq mdq vv1 (0 + 1) [CB 40 j40]);
        [ exact TIq | cbv delta [FRAME]; cbn [app]; exact FR1 | reflexivity | apply fmt_host_at | unfold IMG_LO, A_fmthost; clear; lia | unfold RO_TOP, A_fmthost; clear; lia | apply fmt_host_range
        | eexists _, _; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact HARG]
        | exists (Z_to_bv 64 (vb_buf yi + 7)); split; [reflexivity| rewrite unsigned_lit by (keeplia BIlo BIhi VszI ACV); keeplia BIlo]
        | exact HSB
        | right; rewrite length_app, LZ; cbn [length]; split; [clear; lia|]; split; [keeplia ZLE VlenI LBS L8| apply in_app_iff; right; left; reflexivity]
        | unfold OUT_HOST; cbn [nth_error]; rewrite !length_app, !Nat2Z.inj_add, HOUTL; unfold TXT_HOST, out_c; cbn [length]; clear; lia
        | clear; lia | keeplia JLT ZLE VlenI | clear; lia | reflexivity | ].
      clear TIq FR1 HSB. clear dependent mq. try clear SBq. try (clear dependent mdq). clear MU1 WM1 SHV1.
      clear EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk MH1 LV1 TI1.
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' r2 A2 mk2 mdk2 vv2 TI2 FR2.
      (* [comment removed for export] *)
      replace (vb_buf yi + 7 + Z.of_nat jx) with (vb_buf yi + (7 + Z.of_nat jx)) by (clear; lia).
      eapply (seg_mid' yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A2 mk2 mdk2 vv2 (0 + 1 + (7 + Z.of_nat jx)) (7 + Z.of_nat jx));
        [ exact TI2 | exact FR2 | clear; lia | keeplia JLT ZLE VlenI | keeplia JLT ZLE VlenI | exact NUL ].
    - (* [comment removed for export] *)
      zstep. if_cases KQ; zify_cond KQ; [| exfalso; apply KQ; reflexivity].
      eapply (seg_err' yi); [exact EVI | exact MI2 | exact ST2 | cbv delta [FRAME' FRAME]; cbn [app]; exact FR | | | exact MU | exact WM].
      + lazymatch goal with V : rw_cells _ m2 VEP (vep_cells vv tag q) |- _ => exact V end.
      + lazymatch goal with C : rw_cells _ m2 (h_ff H + 1336) _ |- _ => exact C end.
  Qed.
End S.
End A_ve8qw.


Module A_ver79.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4 RA_vrdi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pnyh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pf3s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pis0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_p0nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpnnp AIcptdg AIcp2kv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5 AIcpzt2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5.AIcp1os OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpzt2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcp8zl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_La0bg A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VSe3i A_VSa8f A_VStbd A_VEr47 A_VSbb4 A_VS41f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_veqih.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS160 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSe90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSq5u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSt8w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS8zm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_veq11 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_ve5c7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_ve6k0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_vep3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_ve8qw.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strchr_icpt_post, vep_error_post, DATA_STACK, LEN_STACK, ASSERT_STACK, STRCHR_ICPT_STACK, VEPERR_STACK in H.
(* [comment removed for export] *)
Ltac simpl_sizes ::=
  rewrite ?app_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length];
  try (rewrite vep_cells_size by assumption); try (rewrite vsb_cells_size).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].



Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (vi : option vsb_rec) (H : henv) (lo SB N : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HFL : 0 <= vv Fflags < 16.
  Hypothesis HET : bool01 (vv Femptytag).
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis HLM : vv Flast_mark = 1.
  Hypothesis HAZ : vv Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis SZB : vb_size vr <= vb_len vr + 4096.
  Hypothesis LENB : vb_len vr + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  Hypothesis LBM : a_livebytes A0 + vb_size vr + vb_len vr + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : match vi with Some yi => vb_len yi / 4096 | None => 0 end + 8 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM + (PPOT_CAP - vsb_ppot vr) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis LF : lib_frames A0.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fvsb /\ vv Finclude_src <> vb_buf vr /\
                   vb_buf yi <> vv Fvsb /\ vb_buf yi <> vb_buf vr
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - DOINCL_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q -> vkeep vv vv' [Fstate; Finclude_src; Finclude_continue] ->
      (vv' Fstate = vv Fstate \/ vv' Fstate = vi_st VIA S_TagError) -> bool01 (vv' Finclude_continue) -> vv' Finclude_src = 0 ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      match vi with
      | None => (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0
      | Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                   (forall r, r <> vb_buf vr -> r <> vb_buf vr' -> r <> vv Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A0 r) /\
                   a_livebytes A' = a_livebytes A0 + (vb_size vr' - vb_size vr) - 40 - vb_size yi /\ a_nlive A' = a_nlive A0 - 2
      end ->
      frames_aged A0 A' 1 1 -> a_tinycred A' = a_tinycred A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40)
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HFL (conj HET (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB
      (conj SZB (conj LENB (conj LBM (conj NLV (conj SCM (conj PRM (conj LF (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO (conj SPHI
      (conj STKSH K))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Let TINV := tinv VEP vv tag q vr vi H lo SB N sp m0 md0 A0.
  Let FRAME' := FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Local Ltac pose_parts :=
    pose proof (printf_call VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as printf_call';
    pose proof (printf_c_call VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as printf_c_call';
    pose proof (tinv_xfer VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as tinv_xfer';
    pose proof (seg_end VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_end';
    pose proof (seg_loop VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_loop';
    pose proof (seg_mid VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_mid';
    pose proof (CFP VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as CFP';
    pose proof (W_cover VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as W_cover';
    pose proof (seg_err VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_err';
    pose proof (tinv_init VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as tinv_init'.

  Local Ltac unpack_tinv TI :=
    (first [ dand26 TI as EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & VEPC & SOBJk & NEBk & LENk & SZk & RELk & LIVEk & LBk & TCk & NLk & SCk & PCk & FSk & STKSHk
                    & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Let SCR5' := SCR5 VEP.
  (* [comment removed for export] *)
  Let W : list (Z * Z) := [(bv_unsigned sp - DOINCL_STACK, bv_unsigned sp); (h_ff H + 1336, h_ff H + 1352); (VEP, VEP + 312)].

  (* [comment removed for export] *)
  Local Ltac henv_here mx MU WM CNT HENVx DJ GCE GHI SHF VEPlo :=
    try unhide DJ;
    lazymatch goal with HGx : henv_geom LPA H |- _ =>
    let ACV := fresh "ACV" in pose proof alloc_ceiling_num as ACV;
    let HFRM := fresh "HFRM" in let GLOB := fresh "GLOB" in let HOBJ := fresh "HOBJ" in let HSH := fresh "HSH" in
    let BSSV := fresh "BSSV" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT'" in
    pose proof HENV as (HFRM & GLOB & HOBJ & HSH);
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as BSSV BSS CP _ | pose proof GLOB as (BSSV & BSS & CP & _) ]); fold_cl_segs; cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS; unfold h_vsc, h_cp in BSSV, BSS, CP;
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in BSS; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in CP; [| exact MU| exact WM| cbn; keeplia DJ GHI GCE VEPlo ACV CEIL LO];
    destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
    assert (HENVx : henv_ok LPA VIA H A0 mx);
    [ split; [exact HFRM|]; split;
      [ eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp;
        [exact BSSV| exact BSS| exact CP| replace (h_ff H + 32 + 1304) with (h_ff H + 1336) by lia; exact C]
      | split; [ eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|];
                 intros a__ Ha__; unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_vsc in *; cbn [outside]; keeplia Ha__ DJ GHI GCE ACV CEIL LO
               | eapply (hshadow_munch LPA); [exact HSH| exact MU| exact HGx|];
                 intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ SHF GCE VEPlo ACV CEIL LO ] ]
    | clear BSSV BSS CP C c HFRM GLOB HOBJ HSH ACV ]
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vr"] Lemma seg_tail : forall (yi : vsb_rec) (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (m1 : mem) (j40 : list byte),
    vi = Some yi ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -144) (FRAME' [CB 40 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells (fupd vv Fstate (vi_st VIA S_TagError)) tag q) ->
    henv_ok LPA VIA H A0 m1 ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1 a0 a1 a2 a3 a4 a5 a6 a7
                 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 280)) xs10 xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x8f734) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until j40. intros EVI MI ST FR VEPC HENV1 MU WM. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_4; dand7 dR_4 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ)) as dR_5; dand11 dR_5 as S16 Slo Shi _ B16 Blo Bhi _ DSB _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ) as (S16 & Slo & Shi & _ & B16 & Blo & Bhi & _ & DSB & _ & _) ]).
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS. pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_6; dand11 dR_6 as SI16 SIlo SIhi _ BI16 BIlo BIhi _ DSBI _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (SI16 & SIlo & SIhi & _ & BI16 & BIlo & BIhi & _ & DSBI & _ & _) ]).
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI. pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI.
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_7; dand3 dR_7 as VszI VlenI _ | pose proof VINVI as (VszI & VlenI & _) ]).
    unfold kHighMemBeg in VEPlo, Slo, Blo, SIlo, BIlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 S 40 AINV00 VLV LS NES) as DVS.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 (vb_buf vr) (vb_size vr) AINV00 VLV LB NEB) as DVB.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI VLV NIS) as DVSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI VLV NIB) as DVBI.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI LS NISS) as DSSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI LS NIBS) as DBSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LSI LB NISB) as DSBI'.
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LBI LB NIBB) as DBBI.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LB) as DJfB.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LSI) as DJfSI.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LBI) as DJfBI.
    change (fsize HCLASS) with 8192 in DJfV, DJfS, DJfB, DJfSI, DJfBI.
    pose proof (conj (sh_boundL (Clg:=Clg) S 40 ltac:(keeplia Slo) ltac:(clear; lia) ltac:(exact Shi)) (sh_top_le' S 40 ltac:(keeplia Slo) ltac:(clear; lia) ltac:(exact Shi))) as SHSB. rewrite SHMAX_val in SHSB.
    pose proof (conj (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(keeplia Blo) ltac:(try (generalize alloc_ceiling_val); clear - SOBJ; try pose proof alloc_ceiling_val as ACV__; pose proof (proj1 (proj1 (proj2 SOBJ))); lia) ltac:(exact Bhi))
                     (sh_top_le' (vb_buf vr) (vb_size vr) ltac:(keeplia Blo) ltac:(try (generalize alloc_ceiling_val); clear - SOBJ; try pose proof alloc_ceiling_val as ACV__; pose proof (proj1 (proj1 (proj2 SOBJ))); lia) ltac:(exact Bhi))) as SHBB. rewrite SHMAX_val in SHBB.
    pose proof (conj (sh_boundL (Clg:=Clg) (vv Finclude_src) 40 ltac:(keeplia SIlo) ltac:(clear; lia) ltac:(exact SIhi)) (sh_top_le' (vv Finclude_src) 40 ltac:(keeplia SIlo) ltac:(clear; lia) ltac:(exact SIhi))) as SHSI. rewrite SHMAX_val in SHSI.
    pose proof (conj (sh_boundL (Clg:=Clg) (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi)) (sh_top_le' (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi))) as SHBI. rewrite SHMAX_val in SHBI.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    hide DVS. hide DVB. hide DVSI. hide DVBI. hide DSSI. hide DBSI. hide DSBI'. hide DBBI. hide DJfV. hide DJfS. hide DJfB. hide DJfSI. hide DJfBI.
    hide DSB. hide DSBI. hide_neqs.
    unfold vep_cells in VEPC. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA] in VEPC. cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    (* [comment removed for export] *)
    zstep. zstep. do 13 zstep. zstep.
    try replace (bv_unsigned sp + -144 + 144) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    astop AINV00 MU WM CFP'.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, VEPCq : rw_cells _ ?ma VEP _, HEq : henv_ok LPA VIA H A0 ?ma, STq : stk _ ?ma lo _, FRq : rw_cells _ ?ma (bv_unsigned sp + -144) _
      |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename HEq into HENVa;
      release_frame FRq STq (bv_unsigned sp); rename STq into STw;
      (* [comment removed for export] *)
      (first [ pose proof ((rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (vv Finclude_src))) VEPCq eq_refl)) as dR_8; dand3 dR_8 as VA VM VBk | pose proof (rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (vv Finclude_src))) VEPCq eq_refl) as (VA & VM & VBk) ]); clear VEPCq;
      cbn [firstn skipn cells_size csize Nat.add length] in VA, VM, VBk;
      change (Z.of_nat 280) with 280 in VM; change (Z.of_nat 280) with 280 in VBk; change (Z.of_nat 8) with 8 in VBk;
      replace (VEP + 280 + 8) with (VEP + 288) in VBk by lia
    end.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
      assert (IOBJa : vsb_obj LPA A0 (aview A0 mq) (vv Finclude_src) yi true)
        by (unhide DJfSI; unhide DJfBI; unhide DVSI; unhide DVBI;
            eapply vsb_obj_munch; [exact IOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ SIhi BIhi DJfSI DJfBI DVSI DVBI ACV CEIL LO]);
      assert (SOBJa : vsb_obj LPA A0 (aview A0 mq) S vr false)
        by (unhide DJfS; unhide DJfB; unhide DVS; unhide DVB;
            eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi DJfS DJfB DVS DVB ACV CEIL LO]) end.
    unhide NIS. unhide NIB.
    eapply (VSB_destroy_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _ A0 (VEP + 280) (vv Finclude_src) yi true lo);
      [ exact AINVa | assumption | reflexivity | exact VM
      | eapply cobj_block; [exact VLV| cbn; intros [X|[X|X]]; [exact (NIS X)| exact (NIB X)| exact X] | lia | lia]
      | rewrite Z.add_mod, V8 by lia; reflexivity
      | keeplia VEPhi
      | exact IOBJa | exact TP | exact SP16 | exact STw | exact CEIL | ufs; keeplia LO | ].
    hide NIS. hide NIB.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 mf mdf. cbv zeta.
    intros AINV1 MI1 MDF1 FRS1 LB1 TC1 NL1 SC1 PC1 ST1 PSC DEADI DEADBI LIVEq CF1. ufs.
    unhide_neqs.
    assert (LVEP1 : a_live A1 VEP = Some 312) by (rewrite (LIVEq VEP (not_eq_sym NIS) (not_eq_sym NIB)); exact VLV).
    assert (LS1 : a_live A1 S = Some 40) by (rewrite (LIVEq S (not_eq_sym NISS) (not_eq_sym NIBS)); exact LS).
    assert (LBF1 : a_live A1 (vb_buf vr) = Some (vb_size vr)) by (rewrite (LIVEq (vb_buf vr) (not_eq_sym NISB) (not_eq_sym NIBB)); exact LB).
    (* [comment removed for export] *)
    assert (HENVf : henv_ok LPA VIA H A1 (aview A1 mf)).
    { eapply (henv_ok_acall_gen H A0 A1); [exact AINVa| exact CF1| exact HENVa| keeplia CEIL LO| intros ff k age HFf; exists age; rewrite (FRS1 ff); exact HFf|].
      intros a [X|[X|X]].
      - exists (vv Finclude_src), 40. split; [exact LSI|]. unfold newblk, blk in X. keeplia X.
      - exists (vb_buf yi), (vb_size yi). split; [exact LBI|]. unfold newblk, blk in X. keeplia X.
      - exists VEP, 312. split; [exact VLV|]. left. keeplia X. }
    (* [comment removed for export] *)
    unhide DVSI. unhide DVBI. unhide DSSI. unhide DBSI. unhide DSBI'. unhide DBBI. unhide DVS. unhide DVB.
    lazymatch type of CF1 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 VEP) in VA;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 VEP 280 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length]; rewrite ?TAG8; cbn [Nat.add]; split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DVSI DVBI SHSI SHBI VEPlo] ];
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 (VEP + 288)) in VBk;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A0 _ _ VEP 312 (VEP + 288) 24 AINVa VLV ltac:(keeplia VEPlo) ltac:(keeplia VEPlo) ltac:(keeplia VEPlo))
         | cbn [cells_size csize Nat.add length];
           split; [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DVSI DVBI SHSI SHBI VEPlo] ];
      assert (SOBJ1 : vsb_obj LPA A1 mb S vr false);
      [ eapply (vsb_obj_ccall A0 A1); [exact AINVa| exact CF1| exact SOBJa| keeplia CEIL LO| exact LS1| exact LBF1|];
        intros a Ha X; unfold newblk, blk in X; keeplia Ha X DSSI DBSI DSBI' DBBI DVS DVB SHSI SHBI Slo Blo VEPlo
      | ]
    end.
    hide DVSI. hide DVBI. hide DSSI. hide DBSI. hide DSBI'. hide DBBI. hide DVS. hide DVB.
    assert (VEPC1 : rw_cells rsegs (aview A1 mf) VEP (vep_cells (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Finclude_src 0) tag q)).
    { rewrite <- vep_cells_include_src. unfold vep_cells. cbn [firstn skipn fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA].
      lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs (aview A1 mf) VEP pre); [exact VA| exact PSC|] end.
      eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; rewrite ?TAG8; cbn [Nat.add]; change (Z.of_nat 280) with 280; change (Z.of_nat 8) with 8; lia]. }
    clear VA VBk PSC.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 mf mdf (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Finclude_src 0) vr);
      [ exact AINV1 | exact MI1
      | eapply amd_frame_sbm_l; [exact SBM| exact MH| exact MDF1]
      | exact ST1 | exact HENVf
      | split; [exact LVEP1|]; split; [exact VEPC1|]; split; [exact TAG8| exact PADS]
      | vkeep_tac (vkeep_refl vv [Fstate; Finclude_src; Finclude_continue])
      | right; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; reflexivity
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact HIC
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; reflexivity
      | exact SOBJ1
      | rewrite EVI; keeplia VlenI | clear; lia | left; reflexivity
      | rewrite EVI; split; [exact DEADI|]; split; [exact DEADBI|]; split;
        [ intros r R1 R2 R3 R4; exact (LIVEq r R3 R4) | split; [rewrite LB1; clear; lia| exact NL1] ]
      | split; [intros ff k age HFf; exists 0%nat; rewrite Nat.add_0_r, (FRS1 ff); split; [exact HFf| clear; lia]
              | intros ff HFf; rewrite (FRS1 ff); exact HFf]
      | exact TC1 | rewrite SC1; clear; lia | rewrite PC1; clear; lia (* [comment removed for export] *)
      | ].
    (* [comment removed for export] *)
    lazymatch type of CF1 with cframe _ _ _ _ _ _ _ ?ma ?mb =>
      eapply (cframe_extend LPA _ _ (bv_unsigned sp) _ (bv_unsigned sp) _ _ _ _ _ (aview A0 m0) ma mb mb _ []);
        [ exact MU | ufs; rewrite EVI; apply W_cover' | exact CF1 | ufs; clear; lia | clear; lia
        | rewrite EVI; intros a [X|[X|X]]; [right; right; right; left; left; exact X | right; right; right; left; right; exact X | left; split; [keeplia VEPlo| keeplia X]]
        | intros a X; right; right; left; exact X
        | apply munch_refl
        | intros a _ X; exfalso; apply X; exact I
        | eapply (stk_mapped (L:=LPA)); [exact ST1 | exact CEIL | keeplia LO | clear; lia] ]
    end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vr"] Lemma seg_https_A : forall (yi : vsb_rec) (bs : list byte) (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs4 xt3 xt4 xt5 xt6 : word)
      (incl : Z) (m1 : mem) (j40 cnt : list byte),
    vi = Some yi ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -144) (FRAME' [CB 40 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    u8arr rsegs (aview A0 m0) (vb_buf yi) bs -> Z.of_nat (length bs) = vb_size yi -> nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    0 <= incl < 256 -> 9 <= vb_len yi ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880))
                 a0 a1 a2 a3 a4 a5 a6 a7
                 xs2 (Z_to_bv 64 (VEP + 8)) xs4 (Z_to_bv 64 (vb_len yi)) (Z_to_bv 64 incl)
                 (Z_to_bv 64 (vb_buf yi)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 280)) (Z_to_bv 64 (VEP + 288))
                 (Z_to_bv 64 ((VEP + 288) / 8 + 2147450880)) xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x8f600) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM U8 LBS NUL INCL L9. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    pose proof LENB as LENB'. rewrite EVI in LENB'. pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_10; dand7 dR_10 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI. pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_11; dand11 dR_11 as SI16 SIlo SIhi _ BI16 BIlo BIhi _ DSBI _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (SI16 & SIlo & SIhi & _ & BI16 & BIlo & BIhi & _ & DSBI & _ & _) ]).
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_12; dand8 dR_12 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    unfold kHighMemBeg in VEPlo, SIlo, BIlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LSI (not_eq_sym NIS)) as DVSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LBI (not_eq_sym NIB)) as DVBI.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LBI) as DJfBI.
    change (fsize HCLASS) with 8192 in DJfV, DJfBI.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (conj (sh_boundL (Clg:=Clg) (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi)) (sh_top_le' (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi))) as SHBIB. rewrite SHMAX_val in SHBIB.
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    (* [comment removed for export] *)
    pose proof (got_vsc_cell m1 (proj1 CE1)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    pose proof HENV as (_ & GLOB & HOBJ & HSH).
    (first [ pose proof (HSH) as dR_13; dand10 dR_13 as SHvs _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHvs & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHvs, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHwR. rewrite SHMAX_val in SHwR.
    eapply (bytes_at_munch LPA) in SHvs; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHVR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHc; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHcR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHw; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHwR GCE VEPlo LO CEIL ACV].
    (first [ pose proof ((shadowed_bss_vsc _ (proj1 CE1))) as dR_14; dand8 dR_14 as PG NG SHG GAL G0 GLE GGE GCE' | destruct (shadowed_bss_vsc _ (proj1 CE1)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE') ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (GLOB) as dR_15; dand4 dR_15 as BSSV _ _ _ | pose proof GLOB as (BSSV & _ & _ & _) ]). fold_cl_segs. cbn [vi_bss_vsc VIA] in BSSV. unfold h_vsc in BSSV.
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO].
    (first [ pose proof (HOBJ) as dR_16; dand3 dR_16 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    eapply (rw_cells_munch LPA) in VC; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    eapply (rw_cells_munch LPA) in WK; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    assert (U81 : u8arr rsegs m1 (vb_buf yi) bs).
    { destruct U8 as [UB UW]. split; [| eapply wr_at_transport; [exact UW| exact WM]].
      eapply (bytes_at_munch LPA); [exact UB| exact MU|]. rewrite LBS. intros a Ha. cbn. keeplia Ha BIhi DJfBI DVBI GCE VEPlo ACV CEIL LO. }
    hide DVSI. hide DVBI. hide DSBI. hide_neqs.
    pose proof VEPC as VEPCf. unfold vep_cells in VEPC. rewrite EVC in VEPC. unfold h_vc in VEPC. rewrite HAZ in VEPC. cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    hide VEPCf. fold_cl_segs.
    unhide DJfV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    zstep. carve_frame 48%nat ST.
    try replace (bv_unsigned sp + -144 + -48) with (bv_unsigned sp + -192) in * by lia.
    do 8 zstep.
    try replace (bv_unsigned sp + -192 + 48) with (bv_unsigned sp + -144) by lia.
    lazymatch goal with FRv : rw_cells _ ?mx (bv_unsigned sp + -192) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      release_frame FRv ST (bv_unsigned sp + -144) end.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep. try clear U81. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep.
    zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
    hide DJfV.
    lazymatch goal with VEPCq : rw_cells _ ?mx VEP _, CNTq : rw_cells _ ?mx (h_ff H + 1336) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _
      |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      henv_here mx MU WM CNTq HENVx DJfV GCE GHI SHF VEPlo;
      eapply (seg_tail yi); [exact EVI | exact MIq | exact STq | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq
        | unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA]; rewrite EVC, HAZ; unfold h_vc; exact VEPCq
        | exact HENVx | exact MU | exact WM ]
    end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vr"] Lemma seg_https_B : forall (yi : vsb_rec) (bs : list byte) (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs4 xt3 xt4 xt5 xt6 : word)
      (incl : Z) (m1 : mem) (j40 cnt : list byte),
    vi = Some yi ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -144) (FRAME' [CB 40 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    u8arr rsegs (aview A0 m0) (vb_buf yi) bs -> Z.of_nat (length bs) = vb_size yi -> nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    0 <= incl < 256 -> 9 <= vb_len yi ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880))
                 a0 a1 a2 a3 a4 a5 a6 a7
                 xs2 (Z_to_bv 64 (VEP + 8)) xs4 (Z_to_bv 64 (vb_len yi)) (Z_to_bv 64 incl)
                 (Z_to_bv 64 (vb_buf yi)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 280)) (Z_to_bv 64 (VEP + 288))
                 (Z_to_bv 64 ((VEP + 288) / 8 + 2147450880)) xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x8f678) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM U8 LBS NUL INCL L9. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    pose proof LENB as LENB'. rewrite EVI in LENB'. pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_20; dand7 dR_20 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI. pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_21; dand11 dR_21 as SI16 SIlo SIhi _ BI16 BIlo BIhi _ DSBI _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (SI16 & SIlo & SIhi & _ & BI16 & BIlo & BIhi & _ & DSBI & _ & _) ]).
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_22; dand8 dR_22 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    unfold kHighMemBeg in VEPlo, SIlo, BIlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LSI (not_eq_sym NIS)) as DVSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LBI (not_eq_sym NIB)) as DVBI.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LBI) as DJfBI.
    change (fsize HCLASS) with 8192 in DJfV, DJfBI.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (conj (sh_boundL (Clg:=Clg) (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi)) (sh_top_le' (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi))) as SHBIB. rewrite SHMAX_val in SHBIB.
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (EVSC : h_vsc H = h_ff H + 32) by reflexivity.
    (* [comment removed for export] *)
    assert (NUL8 : nth_error (skipn 8 bs) (Z.to_nat (vb_len yi) - 8) = Some (Z_to_bv 8 0)).
    { rewrite nth_error_skipn. replace (8 + (Z.to_nat (vb_len yi) - 8))%nat with (Z.to_nat (vb_len yi)) by (clear - L9; lia). exact NUL. }
    (first [ pose proof ((cstr_split (skipn 8 bs) _ NUL8)) as dR_23; dex1 dR_23 as z; dand4 dR_23 as ZLE SPLIT NONUL LZ | pose proof ((cstr_split (skipn 8 bs) _ NUL8)) as dR_23; dand5 dR_23 as z ZLE SPLIT NONUL LZ | destruct (cstr_split (skipn 8 bs) _ NUL8) as (z & ZLE & SPLIT & NONUL & LZ) ]).
    assert (LREST : length (skipn 8 bs) = (length bs - 8)%nat) by (rewrite skipn_length; reflexivity).
    assert (LSL : Z.of_nat (length (skipn (Datatypes.S z) (skipn 8 bs))) = vb_size yi - 9 - Z.of_nat z).
    { rewrite skipn_length, LREST. clear - LBS ZLE VlenI L9. lia. }
    hide DVSI. hide DVBI. hide DSBI. hide DJfBI. hide_neqs.
    cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    zstep. carve_frame 48%nat ST.
    try replace (bv_unsigned sp + -144 + -48) with (bv_unsigned sp + -192) in * by lia.
    do 8 zstep.
    try replace (bv_unsigned sp + -192 + 48) with (bv_unsigned sp + -144) by lia.
    lazymatch goal with FRv : rw_cells _ ?mx (bv_unsigned sp + -192) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      release_frame FRv ST (bv_unsigned sp + -144) end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1b end.
    assert (CE1 : cenv m1b)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    assert (U81 : u8arr rsegs m1b (vb_buf yi) bs).
    { destruct U8 as [UB UW]. split; [| eapply wr_at_transport; [exact UW| exact WM]].
      eapply (bytes_at_munch LPA); [exact UB| exact MU|]. rewrite LBS. intros a Ha. cbn. unhide DJfBI. unhide DVBI. keeplia Ha BIhi DJfBI DVBI GCE VEPlo ACV CEIL LO. }
    assert (STR : bytes_at rsegs m1b (vb_buf yi + 8) (firstn z (skipn 8 bs) ++ Z_to_bv 8 0 :: skipn (Datatypes.S z) (skipn 8 bs))).
    { rewrite <- SPLIT. apply (u8arr_suffix m1b (vb_buf yi) bs 8 U81); [clear; lia| clear - LBS VlenI L9; lia]. }
    clear U81.
    icall (strchr_icpt_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1b (firstn z (skipn 8 bs)) (skipn (Datatypes.S z) (skipn 8 bs)) lo)
      by (cbv zeta; rewrite ?(unsigned_lit (vb_buf yi + 8)) by (keeplia BIlo BIhi VszI ACV); rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by (keeplia SPR LO CEIL ACV); rewrite ?unsigned_lit by (clear; lia);
          unfold STRCHR_ICPT_STACK;
          first [ exact STR
                | exact NONUL
                | exact MI
                | exact (strchr_icpt_cells_of_consts _ (proj1 CE1))
                | exact ST
                | exact CEIL
                | (rewrite LZ, LSL; unhide VbmI; clear - VbmI ZLE VlenI L9 LBS BI16; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia)
                | (left; rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add, Nat2Z.inj_succ, LZ, LSL; keeplia BIhi CEIL LO ZLE VlenI)
                | (change (47 mod 256) with 47; clear; lia)
                | keeplia BIlo
                | (rewrite LZ; keeplia ZLE VlenI LENB' Vlen0)
                | (rewrite LZ; eapply (range_ok_high_munch _ (aview A0 m0) m1b);
                    [ eapply (live_range_ok A0 m0 md0 (vb_buf yi) (vb_size yi)); [exact AINV00| exact LBI| clear; lia| keeplia ZLE VlenI L9 LBS LREST| keeplia ZLE]
                    | exact MU | keeplia BIlo | keeplia ZLE | keeplia BIhi ZLE VlenI L9 LBS LREST
                    | repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; keeplia LO CEIL ACV GCE VEPlo ])
                | keeplia LO ]).
    clear CE1 STR. change (47 mod 256) with 47. unfold strchr_res.
    lazymatch goal with M : munch _ (aview A0 m0) ?v1, ST1 : stk _ ?v1 _ _, MI1 : mem_inv _ ?v1 |- evt _ _ (MS _ _ _ _ _ ?v1 _) =>
      rename v1 into m2; rename ST1 into ST2; rename MI1 into MI2 end.
    try clear dependent m1b.
    destruct (find_byte 47 (firstn z (skipn 8 bs))) as [jx|] eqn:FJ.
    2:{ (* [comment removed for export] *)
      zstep. if_cases KQ; zify_cond KQ; [| exfalso; apply KQ; reflexivity]. clear KQ.
      zstep. zstep. zstep. zstep.
      assert (CE2 : cenv m2)
        by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
      assert (SHVD : shadowed LPA m2 VEP 312).
      { exists VEP, 312. split; [pose proof SHV as T__; rewrite EzsV in T__; exact T__|].
        split; [exact V8|]. keeplia VEPlo VEPhi. }
      try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CNT); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_POST); lazymatch goal with VEPCq : rw_cells _ m2 VEP _, CNTq : rw_cells _ m2 (h_ff H + 1336) _ |- _ =>
        henv_here m2 MU WM CNTq HENVx DJfV GCE GHI SHF VEPlo;
        (first [ dand4 HENVx as HFRM2 GLOB2 HOBJ2 HSH2 | destruct HENVx as (HFRM2 & GLOB2 & HOBJ2 & HSH2) ]);
        unhide DJfV;
        icall (vep_error_ok VEP vv tag q H lo)
          by (rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by (keeplia SPR LO CEIL ACV); rewrite ?unsigned_lit by (clear; lia);
              first [ reflexivity | exact VEPCq | exact TAG8 | exact PADS | exact EVC | exact GLOB2 | exact HOBJ2 | exact HSH2 | exact HG
                    | exact CE2 | exact SHVD | (unfold kHighMemBeg; keeplia VEPlo) | exact V8 | exact VEPhi
                    | (unfold HFSIZE; keeplia DJfV) | exact ST2 | exact CEIL | exact MI2
                    | (unfold VEPERR_STACK; keeplia LO) ]);
        clear GLOB2 HOBJ2 HSH2 CE2 SHVD
      end.
      lazymatch goal with X : glob_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into GLOB3 end.
      lazymatch goal with X : hobj_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HOBJ3 end.
      lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into ST3 end.
      lazymatch goal with X : mem_inv _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into MI3 end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV3 : henv_ok LPA VIA H A0 v)
          by (split; [exact (proj1 HENV)| split; [exact GLOB3| split; [exact HOBJ3|]]];
              eapply (hshadow_munch LPA); [exact (proj2 (proj2 (proj2 HENV)))| exact MU| exact HG|];
              intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ SHF GCE VEPlo ACV CEIL LO);
        pose proof (munch_refl [(VEP, VEP + 312)] v) as MU3; pose proof (wmono_refl rsegs v) as WM3;
        rename v into m3
      end.
      clear GLOB3 HOBJ3.
      lazymatch goal with V : rw_cells _ m3 VEP _ |- _ => unfold vep_cells in V; rewrite EVC in V; unfold h_vc in V; rewrite HAZ in V end.
      (* [comment removed for export] *)
      zstep. vchk SHV EzsV 8 0. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. vchk SHV EzsV 8 0. zstep.
      zstep. if_cases KZ; zify_cond KZ; [exfalso; apply KZ; reflexivity|]. clear KZ.
      lazymatch goal with VEPCq : rw_cells _ ?mx VEP _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _
        |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (HENV4 : henv_ok LPA VIA H A0 mx)
          by (eapply henv_ok_munch; [exact HENV3| exact MU3| exact WM3| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; rewrite EVSC in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; keeplia Ha__ SHF VEPlo VEPhi ACV GCE GHI DJfV CEIL LO);
        eapply (seg_tail yi); [exact EVI | exact MIq | exact STq | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq
          | unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VIA stA]; rewrite EVC, HAZ; unfold h_vc; exact VEPCq
          | exact HENV4 | exact MU | exact WM ]
      end. }
    (* [comment removed for export] *)
    (first [ pose proof ((find_byte_Some _ _ _ FJ)) as dR_25; dand3 dR_25 as JLT _ _ | destruct (find_byte_Some _ _ _ FJ) as (JLT & _ & _) ]). rewrite LZ in JLT.
    (* [comment removed for export] *)
    zstep. if_cases KQ; zify_cond KQ.
    { exfalso. rewrite ?unsigned_lit in KQ by (keeplia BIlo BIhi VszI ACV JLT ZLE VlenI). keeplia KQ BIlo. }
    clear KQ. zstep.
    (* [comment removed for export] *)
    lazymatch goal with V : rw_cells _ ?mx VEP (vep_cells vv tag q) |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof V as VEPCu; unfold vep_cells in VEPCu end.
    vchk SHV EzsV 8 0. zstep. zstep. zstep. zstep. zstep. clear VEPCu.
    astopk AINV00 MU WM CFP'.
    lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, VEq : rw_cells _ ?mx VEP (vep_cells vv tag q), CNTq : rw_cells _ ?mx (h_ff H + 1336) _ |- _ =>
      pose proof (tinv_init' yi bs _ mq mdq [CB 40 j40] _ EVI MU WM MIq STq ltac:(cbv delta [FRAME' FRAME]; cbn [app]; exact FRq) eq_refl VEq CNTq U8 LBS AINVq EVq (amd_frame_sbm _ _ SBq MH)) as TIq;
      rewrite <- EVq in FRq;
      eapply (printf_c_call' yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 incl) 0x8f6cc A0 mq mdq vr 0 [CB 40 j40]);
      [ exact TIq | cbv delta [FRAME]; cbn [app]; exact FRq | reflexivity | clear; lia | keeplia VlenI | clear; lia | reflexivity | ]
    end.
    clear dependent mq. try clear SBq. try (clear dependent mdq). clear dependent m2. try (clear dependent m1). clear EVI LBS U8.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A1 mk1 mdk1 vv1 TI1 FR1.
    (* [comment removed for export] *)
    pose proof TI1 as TI0. unpack_tinv TI0. pose proof (as_minv LPA A1 _ _ AINVk) as [_ MH1].
    assert (LV1 : a_live A1 VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINVk LV1) as SHV1. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV1. rewrite <- EzsV in SHV1.
    unfold vep_cells in VEPC. rewrite EVC in VEPC. unfold h_vc in VEPC. cbv delta [FRAME' FRAME] in FR1. cbn [app] in FR1.
    pose proof (munch_refl [] (aview A1 mk1)) as MU1. pose proof (wmono_refl rsegs (aview A1 mk1)) as WM1.
    hide_neqs.
    ago AINVk. fold_cl_segs.
    vrechk SHV1 EzsV (VEP + 8) 8 0.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (vb_buf yi + 8 + Z.of_nat jx - (vb_buf yi + 8)) with (Z.of_nat jx) by (clear; lia).
    rewrite (swrap32_id (Z.of_nat jx)) by (keeplia JLT ZLE VlenI LENB' Vlen0).
    astopk AINVk MU1 WM1 I.
    pose proof (tinv_xfer' yi bs A1 mk1 mdk1 vv1 (0 + 1) [] _ mq mdq [CB 40 j40] TI1 MU1 WM1 MIk ltac:(intros a__ X; exfalso; exact (X I)) STk FR1 eq_refl AINVq EVq (amd_frame_sbm _ _ SBq MH1)) as TIq.
    rewrite <- EVq in FR1.
    destruct (host_arg_ok2 (firstn z (skipn 8 bs)) jx (vb_buf yi + 8) NONUL ltac:(rewrite LZ; exact JLT) ltac:(keeplia BIlo) ltac:(rewrite LZ; keeplia ZLE VlenI LENB' Vlen0)) as [HARG HOUTL].
    assert (HSB : bytes_at rsegs (aview A1 mq) (vb_buf yi + 8) (firstn z (skipn 8 bs) ++ [Z_to_bv 8 0])).
    { pose proof (u8arr_suffix _ (vb_buf yi) bs 8 U8k ltac:(clear; lia) ltac:(keeplia LBS VlenI L9)) as STR'.
      change (Z.to_nat 8) with 8%nat in STR'. rewrite SPLIT in STR'.
      replace (firstn z (skipn 8 bs) ++ Z_to_bv 8 0 :: skipn (Datatypes.S z) (skipn 8 bs))
         with ((firstn z (skipn 8 bs) ++ [Z_to_bv 8 0]) ++ skipn (Datatypes.S z) (skipn 8 bs)) in STR' by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in STR'. rewrite EVq. exact (proj1 STR'). }
    eapply (printf_call' FMT_HOST 13 3 PRE_HOST OUT_HOST eq_refl HOUT_HOST HOUT1_HOST OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pis0.pc1_host OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_p0nl.pc2_host FMTB_HOST SLOTS_S pcm_fmt_host FBY_HOST yi bs
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A_fmthost (vb_buf yi + 8) (firstn z (skipn 8 bs) ++ [Z_to_bv 8 0]) (7 + Z.of_nat jx) 0x8f110 A1 mq mdq vv1 (0 + 1) [CB 40 j40]);
      [ exact TIq | cbv delta [FRAME]; cbn [app]; exact FR1 | reflexivity | apply fmt_host_at | unfold IMG_LO, A_fmthost; clear; lia | unfold RO_TOP, A_fmthost; clear; lia | apply fmt_host_range
      | eexists _, _; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact HARG]
      | exists (Z_to_bv 64 (vb_buf yi + 8)); split; [reflexivity| rewrite unsigned_lit by (keeplia BIlo BIhi VszI ACV); keeplia BIlo]
      | exact HSB
      | right; rewrite length_app, LZ; cbn [length]; split; [clear; lia|]; split; [keeplia ZLE VlenI LBS L9| apply in_app_iff; right; left; reflexivity]
      | unfold OUT_HOST; cbn [nth_error]; rewrite !length_app, !Nat2Z.inj_add, HOUTL; unfold TXT_HOST, out_c; cbn [length]; clear; lia
      | clear; lia | keeplia JLT ZLE VlenI | clear; lia | reflexivity | ].
    clear TIq FR1 HSB. clear dependent mq. try clear SBq. try (clear dependent mdq). clear MU1 WM1 SHV1.
    clear EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk MH1 LV1 TI1.
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' r2 A2 mk2 mdk2 vv2 TI2 FR2.
    (* [comment removed for export] *)
    replace (vb_buf yi + 8 + Z.of_nat jx) with (vb_buf yi + (8 + Z.of_nat jx)) by (clear; lia).
    eapply (seg_mid' yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A2 mk2 mdk2 vv2 (0 + 1 + (7 + Z.of_nat jx)) (8 + Z.of_nat jx));
      [ exact TI2 | exact FR2 | clear; lia | keeplia JLT ZLE VlenI | keeplia JLT ZLE VlenI | exact NUL ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vr"] Lemma seg_https : forall (yi : vsb_rec) (bs : list byte) (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs4 xt3 xt4 xt5 xt6 : word)
      (incl : Z) (m1 : mem) (j40 cnt : list byte),
    vi = Some yi ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -144) (FRAME' [CB 40 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    u8arr rsegs (aview A0 m0) (vb_buf yi) bs -> Z.of_nat (length bs) = vb_size yi -> nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    0 <= incl < 256 -> 9 <= vb_len yi ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880))
                 a0 a1 a2 a3 a4 a5 a6 a7
                 xs2 (Z_to_bv 64 (VEP + 8)) xs4 (Z_to_bv 64 (vb_len yi)) (Z_to_bv 64 incl)
                 (Z_to_bv 64 (vb_buf yi)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 280)) (Z_to_bv 64 (VEP + 288))
                 (Z_to_bv 64 ((VEP + 288) / 8 + 2147450880)) xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x8f544) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM U8 LBS NUL INCL L9. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    pose proof LENB as LENB'. rewrite EVI in LENB'. pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_27; dand7 dR_27 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI. pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_28; dand11 dR_28 as SI16 SIlo SIhi _ BI16 BIlo BIhi _ DSBI _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (SI16 & SIlo & SIhi & _ & BI16 & BIlo & BIhi & _ & DSBI & _ & _) ]).
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_29; dand8 dR_29 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    unfold kHighMemBeg in VEPlo, SIlo, BIlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LSI (not_eq_sym NIS)) as DVSI.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LBI (not_eq_sym NIB)) as DVBI.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LBI) as DJfBI.
    change (fsize HCLASS) with 8192 in DJfV, DJfBI.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (conj (sh_boundL (Clg:=Clg) (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi)) (sh_top_le' (vb_buf yi) (vb_size yi) ltac:(keeplia BIlo) ltac:(keeplia VszI) ltac:(exact BIhi))) as SHBIB. rewrite SHMAX_val in SHBIB.
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    (* [comment removed for export] *)
    pose proof (got_vsc_cell m1 (proj1 CE1)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    pose proof HENV as (_ & GLOB & HOBJ & HSH).
    (first [ pose proof (HSH) as dR_30; dand10 dR_30 as SHvs _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHvs & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHvs, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHwR. rewrite SHMAX_val in SHwR.
    eapply (bytes_at_munch LPA) in SHvs; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHVR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHc; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHcR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHw; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHwR GCE VEPlo LO CEIL ACV].
    (first [ pose proof ((shadowed_bss_vsc _ (proj1 CE1))) as dR_31; dand8 dR_31 as PG NG SHG GAL G0 GLE GGE GCE' | destruct (shadowed_bss_vsc _ (proj1 CE1)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE') ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (GLOB) as dR_32; dand4 dR_32 as BSSV _ _ _ | pose proof GLOB as (BSSV & _ & _ & _) ]). fold_cl_segs. cbn [vi_bss_vsc VIA] in BSSV. unfold h_vsc in BSSV.
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO].
    (first [ pose proof (HOBJ) as dR_33; dand3 dR_33 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    eapply (rw_cells_munch LPA) in VC; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    eapply (rw_cells_munch LPA) in WK; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    hide DVSI. hide DVBI. hide DSBI. hide_neqs.
    pose proof VEPC as VEPCu. unfold vep_cells in VEPCu. rewrite EVC in VEPCu. unfold h_vc in VEPCu. rewrite HAZ in VEPCu. cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    fold_cl_segs.
    (* [comment removed for export] *)
    pose proof (rw_cells_read_sub rsegs _ _ _ 4 1 VEPCu ltac:(clear; lia) ltac:(cbn; clear; lia)) as RDF.
    change (Z.to_nat 4) with 4%nat in RDF.
    match type of RDF with _ = Some ?r => let r' := eval cbn in r in change r with r' in RDF end.
    rewrite (unsigned_lit (vv Fflags)) in RDF by (keeplia HFL).
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 1 0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    shadow_addr_at SHG 6191680 8.
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end.
    zstep. zstep; if_cases K0; zify_cond K0;
      [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
      | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk0 SHvs 8. zstep. zstep. clear RDF. zstep. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep. shadow_chk0 SHc 8. zstep. zstep. shadow_chk0 SHw 8.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    clear VEPCu.
    lazymatch goal with X : rw_cells rsegs ?mx (h_ff H + 1336) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (rw_cells_forget _ _ _ _ X) as [cnt' CNT']; cbn [cells_size csize Nat.add length firstn] in CNT'; clear X end.
    zstep; if_cases KB; zify_cond KB.
    - lazymatch goal with STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _, VEPCq : rw_cells _ ?mx VEP (vep_cells vv tag q)
        |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (seg_https_B yi bs); [exact EVI | exact MIq | exact STq | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPCq | exact CNT'
          | exact MU | exact WM | exact U8 | exact LBS | exact NUL | exact INCL | exact L9] end.
    - lazymatch goal with STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _, VEPCq : rw_cells _ ?mx VEP (vep_cells vv tag q)
        |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (seg_https_A yi bs); [exact EVI | exact MIq | exact STq | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPCq | exact CNT'
          | exact MU | exact WM | exact U8 | exact LBS | exact NUL | exact INCL | exact L9] end.
  Qed.
End S.
End A_ver79.


Module A_ve2so.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4 RA_vrdi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pnyh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pf3s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_pis0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.RA_p0nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpnnp AIcptdg AIcp2kv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpoo5 AIcpzt2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5.AIcp1os OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpzt2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcp8zl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_La0bg A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_VSe3i A_VSa8f A_VStbd A_VEr47 A_VSbb4 A_VS41f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_veqih.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vemjo.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS160 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSe90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSq5u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSt8w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS8zm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_veq11 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_ve5c7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_ve6k0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_vep3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_ve8qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_ver79.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strchr_icpt_post, vep_error_post, DATA_STACK, LEN_STACK, ASSERT_STACK, STRCHR_ICPT_STACK, VEPERR_STACK in H.
(* [comment removed for export] *)
Ltac simpl_sizes ::=
  rewrite ?app_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length];
  try (rewrite vep_cells_size by assumption); try (rewrite vsb_cells_size).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].




(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kit8.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma lit_http_range : forall v, cenv v -> range_ok v A_http 7.
  Proof. intros v CE. eapply (global_range_ok v A_http 8 32); [exact CE| gdesc_in| unfold A_http; lia| unfold A_http; lia| lia| unfold pa_static, A_http; cbn; lia| unfold pa_static, A_http; cbn; lia]. Qed.
  Lemma lit_https_range : forall v, cenv v -> range_ok v A_https 8.
  Proof. intros v CE. eapply (global_range_ok v A_https 9 32); [exact CE| gdesc_in| unfold A_https; lia| unfold A_https; lia| lia| unfold pa_static, A_https; cbn; lia| unfold pa_static, A_https; cbn; lia]. Qed.
End Kit8.

Lemma u8arr_prefix : forall m B bs (n : nat),
  u8arr rsegs m B bs -> (n <= length bs)%nat -> bytes_at rsegs m B (firstn n bs).
Proof.
  intros m B bs n U Hn. pose proof (u8arr_sub m B bs 0 n U ltac:(lia) ltac:(cbn; lia)) as X.
  rewrite Z.add_0_r in X. exact X.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (vi : option vsb_rec) (H : henv) (lo SB N : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HFL : 0 <= vv Fflags < 16.
  Hypothesis HET : bool01 (vv Femptytag).
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis HLM : vv Flast_mark = 1.
  Hypothesis HAZ : vv Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis SZB : vb_size vr <= vb_len vr + 4096.
  Hypothesis LENB : vb_len vr + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  Hypothesis LBM : a_livebytes A0 + vb_size vr + vb_len vr + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : match vi with Some yi => vb_len yi / 4096 | None => 0 end + 8 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM + (PPOT_CAP - vsb_ppot vr) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis LF : lib_frames A0.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fvsb /\ vv Finclude_src <> vb_buf vr /\
                   vb_buf yi <> vv Fvsb /\ vb_buf yi <> vb_buf vr
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - DOINCL_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q -> vkeep vv vv' [Fstate; Finclude_src; Finclude_continue] ->
      (vv' Fstate = vv Fstate \/ vv' Fstate = vi_st VIA S_TagError) -> bool01 (vv' Finclude_continue) -> vv' Finclude_src = 0 ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      match vi with
      | None => (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0
      | Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                   (forall r, r <> vb_buf vr -> r <> vb_buf vr' -> r <> vv Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A0 r) /\
                   a_livebytes A' = a_livebytes A0 + (vb_size vr' - vb_size vr) - 40 - vb_size yi /\ a_nlive A' = a_nlive A0 - 2
      end ->
      frames_aged A0 A' 1 1 -> a_tinycred A' = a_tinycred A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40)
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HFL (conj HET (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB
      (conj SZB (conj LENB (conj LBM (conj NLV (conj SCM (conj PRM (conj LF (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO (conj SPHI
      (conj STKSH K))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Let TINV := tinv VEP vv tag q vr vi H lo SB N sp m0 md0 A0.
  Let FRAME' := FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Local Ltac pose_parts :=
    pose proof (CFP VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as CFP';
    pose proof (W_cover VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as W_cover';
    pose proof (tinv_init VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as tinv_init';
    pose proof (seg_pfx VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_pfx';
    pose proof (seg_http VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_http';
    pose proof (seg_https VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_https'.

  Local Ltac unpack_tinv TI :=
    (first [ dand26 TI as EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & VEPC & SOBJk & NEBk & LENk & SZk & RELk & LIVEk & LBk & TCk & NLk & SCk & PCk & FSk & STKSHk
                    & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Let SCR5' := SCR5 VEP.
  (* [comment removed for export] *)
  Let W : list (Z * Z) := [(bv_unsigned sp - DOINCL_STACK, bv_unsigned sp); (h_ff H + 1336, h_ff H + 1352); (VEP, VEP + 312)].

  (* [comment removed for export] *)
  Local Ltac henv_here mx MU WM CNT HENVx DJ GCE GHI SHF VEPlo :=
    try unhide DJ;
    lazymatch goal with HGx : henv_geom LPA H |- _ =>
    let ACV := fresh "ACV" in pose proof alloc_ceiling_num as ACV;
    let HFRM := fresh "HFRM" in let GLOB := fresh "GLOB" in let HOBJ := fresh "HOBJ" in let HSH := fresh "HSH" in
    let BSSV := fresh "BSSV" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT'" in
    pose proof HENV as (HFRM & GLOB & HOBJ & HSH);
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as BSSV BSS CP _ | pose proof GLOB as (BSSV & BSS & CP & _) ]); fold_cl_segs; cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS; unfold h_vsc, h_cp in BSSV, BSS, CP;
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in BSS; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in CP; [| exact MU| exact WM| cbn; keeplia DJ GHI GCE VEPlo ACV CEIL LO];
    destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
    assert (HENVx : henv_ok LPA VIA H A0 mx);
    [ split; [exact HFRM|]; split;
      [ eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp;
        [exact BSSV| exact BSS| exact CP| replace (h_ff H + 32 + 1304) with (h_ff H + 1336) by lia; exact C]
      | split; [ eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|];
                 intros a__ Ha__; unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_vsc in *; cbn [outside]; keeplia Ha__ DJ GHI GCE ACV CEIL LO
               | eapply (hshadow_munch LPA); [exact HSH| exact MU| exact HGx|];
                 intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ SHF GCE VEPlo ACV CEIL LO ] ]
    | clear BSSV BSS CP C c HFRM GLOB HOBJ HSH ACV ]
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vr"] Lemma seg_disp : forall (yi : vsb_rec) (bs : list byte) (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 : word)
      (incl : Z) (m1 : mem) (j40 cnt : list byte),
    vi = Some yi ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -144) (FRAME' [CB 40 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    u8arr rsegs (aview A0 m0) (vb_buf yi) bs -> Z.of_nat (length bs) = vb_size yi -> nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    0 <= incl < 256 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880))
                 a0 a1 a2 a3 a4 a5 a6 a7
                 xs2 xs3 xs4 (Z_to_bv 64 (vb_len yi)) (Z_to_bv 64 incl)
                 (Z_to_bv 64 (vb_buf yi)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 280)) (Z_to_bv 64 (VEP + 288))
                 (Z_to_bv 64 ((VEP + 288) / 8 + 2147450880)) xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x8eed4) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM U8 LBS NUL INCL. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    pose proof LENB as LENB'. rewrite EVI in LENB'. pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_4; dand7 dR_4 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI. pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_5; dand11 dR_5 as SI16 SIlo SIhi _ BI16 BIlo BIhi _ DSBI _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (SI16 & SIlo & SIhi & _ & BI16 & BIlo & BIhi & _ & DSBI & _ & _) ]).
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_6; dand8 dR_6 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    unfold kHighMemBeg in VEPlo, SIlo, BIlo. all_app_facts.
    pose proof (proj1 HENV) as [ageh HFRh].
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LBI) as DJfBI.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LBI (not_eq_sym NIB)) as DVBI.
    change (fsize HCLASS) with 8192 in DJfBI.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (L7 : (7 <= length bs)%nat) by (clear - LBS VlenI VszI; lia).
    (* [comment removed for export] *)
    assert (MIDX : forall (v : mem) (yra ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 : word) (c : list byte),
      munch W (aview A0 m0) v -> wmono rsegs (aview A0 m0) v -> mem_inv rsegs v -> stk rsegs v lo (bv_unsigned sp + -144) ->
      rw_cells rsegs v (bv_unsigned sp + -144) (FRAME' [CB 40 j40]) -> rw_cells rsegs v VEP (vep_cells vv tag q) -> rw_cells rsegs v (h_ff H + 1336) [CB 16 c] ->
      evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
          (MS (mkR yra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp yt0 yt1 yt2 (Z_to_bv 64 VEP) (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880))
                   ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   xs2 (Z_to_bv 64 (VEP + 8)) xs4 (Z_to_bv 64 (vb_len yi)) (Z_to_bv 64 incl)
                   (Z_to_bv 64 (vb_buf yi)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 280)) (Z_to_bv 64 (VEP + 288))
                   (Z_to_bv 64 ((VEP + 288) / 8 + 2147450880)) yt3 yt4 yt5 yt6)
              F (Z_to_bv 64 0x8ef18) fc None v (seg_rom rsegs))).
    { intros v yra ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 c MUv WMv MIv STv FRv VEv CNTv. cbv delta [W] in MUv.
      astopk AINV00 MUv WMv CFP'.
      pose proof (tinv_init' yi bs _ mq mdq [CB 40 j40] _ EVI MUv WMv MIv STv FRv eq_refl VEv CNTv U8 LBS AINVq EVq (amd_frame_sbm _ _ SBq MH)) as TIq.
      rewrite <- EVq in FRv.
      eapply (seg_pfx' yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ incl j40 A0 mq mdq vr);
        [ exact TIq | exact FRv | exact INCL | exact NUL ]. }
    hide DJfBI. hide DVBI. hide DSBI. hide_neqs.
    cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep; if_cases KL8; zify_cond KL8; rewrite ?zb_signed, ?(unsigned_lit (vb_len yi)) in KL8 by (keeplia VlenI LENB' Vlen0);
      rewrite ?(proj2 (Z.ltb_lt (vb_len yi) _)) in KL8 by (keeplia VlenI LENB' Vlen0).
    { eapply MIDX; [exact MU| exact WM| exact MI| exact ST| cbv delta [FRAME' FRAME]; cbn [app]; exact FR| exact VEPC| exact CNT]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    assert (U81 : u8arr rsegs m1 (vb_buf yi) bs).
    { destruct U8 as [UB UW]. split; [| eapply wr_at_transport; [exact UW| exact WM]].
      eapply (bytes_at_munch LPA); [exact UB| exact MU|]. rewrite LBS. intros a Ha. cbn. unhide DJfBI. unhide DVBI. keeplia Ha BIhi DJfBI DVBI GCE VEPlo ACV CEIL LO. }
    assert (RNG1 : forall w, 1 <= w -> w <= vb_len yi -> range_ok m1 (vb_buf yi) w).
    { intros w W1 Wl. eapply (range_ok_high_munch _ (aview A0 m0) m1);
        [ eapply (live_range_ok A0 m0 md0 (vb_buf yi) (vb_size yi)); [exact AINV00| exact LBI| clear; lia| keeplia Wl VlenI| exact W1]
        | exact MU | keeplia BIlo | exact W1 | keeplia BIhi Wl VlenI
        | repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; keeplia LO CEIL ACV GCE VEPlo ]. }
    destruct (memcmp_model_total (firstn 7 bs) LIT_http 7) as [vq Mq]; [ rewrite firstn_length_le; [clear; lia| exact L7] | cbn; clear; lia | ].
    icall (bcmp_icpt_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (firstn 7 bs) LIT_http vq lo)
      by (cbv delta [A_http];
          rewrite ?(unsigned_lit (vb_buf yi)) by (keeplia BIlo BIhi VszI ACV);
          rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by (keeplia SPR LO CEIL ACV);
          rewrite ?unsigned_lit by (clear; lia);
          lazymatch goal with
          | |- bytes_at _ _ (vb_buf yi) _ => apply (u8arr_prefix _ _ _ _ U81 L7)
          | |- bytes_at _ _ _ _ => apply lit_http_at; exact MI
          | |- memcmp_model _ _ _ = _ => exact Mq
          | |- mem_inv _ _ => exact MI
          | |- mic_cells _ => apply mic_cells_of_consts; exact (proj1 CE1)
          | |- stk _ _ _ _ => exact ST
          | |- alloc_ceiling <= _ => exact CEIL
          | |- _ = 0 \/ _ => right; split; [apply RNG1; [clear; lia| keeplia KL8] | apply lit_http_range; exact CE1]
          | |- vb_buf yi + Z.of_nat (length _) <= _ \/ _ => left; rewrite firstn_length_le by (exact L7); keeplia BIhi CEIL VlenI VszI LBS
          | |- _ + Z.of_nat (length _) <= _ \/ _ => left; cbv delta [LIT_http]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; keeplia LO CEIL ACV
          | |- _ < 2 ^ 32 => clear; lia
          | |- _ + 4560 <= _ => keeplia LO
          end).
    clear CE1 RNG1 U81.
    lazymatch goal with M : munch _ (aview A0 m0) ?v1, ST1 : stk _ ?v1 _ _, MI1 : mem_inv _ ?v1 |- evt _ _ (MS _ _ _ _ _ ?v1 _) =>
      rename v1 into m2; rename ST1 into ST2; rename MI1 into MI2 end.
    try (clear dependent m1).
    (* [comment removed for export] *)
    zstep; if_cases KQ1; zify_cond KQ1.
    { lazymatch goal with FRq : rw_cells _ m2 (bv_unsigned sp + -144) _, VEPCq : rw_cells _ m2 VEP (vep_cells vv tag q), CNTq : rw_cells _ m2 (h_ff H + 1336) _ |- _ =>
        eapply (seg_http' yi bs); [exact EVI | exact MI2 | exact ST2 | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPCq | exact CNTq
          | exact MU | exact WM | exact U8 | exact LBS | exact NUL | exact INCL | keeplia KL8] end. }
    clear KQ1 Mq.
    (* [comment removed for export] *)
    zstep. zstep; if_cases KE8; zify_cond KE8; rewrite ?(unsigned_lit (vb_len yi)) in KE8 by (keeplia VlenI LENB' Vlen0).
    { lazymatch goal with FRq : rw_cells _ m2 (bv_unsigned sp + -144) _, VEPCq : rw_cells _ m2 VEP (vep_cells vv tag q), CNTq : rw_cells _ m2 (h_ff H + 1336) _ |- _ =>
        eapply MIDX; [exact MU| exact WM| exact MI2| exact ST2| cbv delta [FRAME' FRAME]; cbn [app]; exact FRq| exact VEPCq| exact CNTq] end. }
    assert (L8 : (8 <= length bs)%nat) by (clear - LBS VlenI VszI KL8 KE8; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    assert (CE2 : cenv m2)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    assert (U82 : u8arr rsegs m2 (vb_buf yi) bs).
    { destruct U8 as [UB UW]. split; [| eapply wr_at_transport; [exact UW| exact WM]].
      eapply (bytes_at_munch LPA); [exact UB| exact MU|]. rewrite LBS. intros a Ha. cbn. unhide DJfBI. unhide DVBI. keeplia Ha BIhi DJfBI DVBI GCE VEPlo ACV CEIL LO. }
    assert (RNG2 : forall w, 1 <= w -> w <= vb_len yi -> range_ok m2 (vb_buf yi) w).
    { intros w W1 Wl. eapply (range_ok_high_munch _ (aview A0 m0) m2);
        [ eapply (live_range_ok A0 m0 md0 (vb_buf yi) (vb_size yi)); [exact AINV00| exact LBI| clear; lia| keeplia Wl VlenI| exact W1]
        | exact MU | keeplia BIlo | exact W1 | keeplia BIhi Wl VlenI
        | repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; keeplia LO CEIL ACV GCE VEPlo ]. }
    destruct (memcmp_model_total (firstn 8 bs) LIT_https 8) as [vq2 Mq2]; [ rewrite firstn_length_le; [clear; lia| exact L8] | cbn; clear; lia | ].
    try clear PC0. icall (bcmp_icpt_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (firstn 8 bs) LIT_https vq2 lo)
      by (cbv delta [A_https];
          rewrite ?(unsigned_lit (vb_buf yi)) by (keeplia BIlo BIhi VszI ACV);
          rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by (keeplia SPR LO CEIL ACV);
          rewrite ?unsigned_lit by (clear; lia);
          lazymatch goal with
          | |- bytes_at _ _ (vb_buf yi) _ => apply (u8arr_prefix _ _ _ _ U82 L8)
          | |- bytes_at _ _ _ _ => apply lit_https_at; exact MI2
          | |- memcmp_model _ _ _ = _ => exact Mq2
          | |- mem_inv _ _ => exact MI2
          | |- mic_cells _ => apply mic_cells_of_consts; exact (proj1 CE2)
          | |- stk _ _ _ _ => exact ST2
          | |- alloc_ceiling <= _ => exact CEIL
          | |- _ = 0 \/ _ => right; split; [apply RNG2; [clear; lia| keeplia KL8 KE8] | apply lit_https_range; exact CE2]
          | |- vb_buf yi + Z.of_nat (length _) <= _ \/ _ => left; rewrite firstn_length_le by (exact L8); keeplia BIhi CEIL VlenI VszI LBS
          | |- _ + Z.of_nat (length _) <= _ \/ _ => left; cbv delta [LIT_https]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; keeplia LO CEIL ACV
          | |- _ < 2 ^ 32 => clear; lia
          | |- _ + 4560 <= _ => keeplia LO
          end).
    clear CE2 RNG2 U82.
    lazymatch goal with M : munch _ (aview A0 m0) ?v1, ST1 : stk _ ?v1 _ _, MI1 : mem_inv _ ?v1 |- evt _ _ (MS _ _ _ _ _ ?v1 _) =>
      rename v1 into m3; rename ST1 into ST3; rename MI1 into MI3 end.
    try (clear dependent m2).
    (* [comment removed for export] *)
    zstep; if_cases KQ2; zify_cond KQ2.
    { lazymatch goal with FRq : rw_cells _ m3 (bv_unsigned sp + -144) _, VEPCq : rw_cells _ m3 VEP (vep_cells vv tag q), CNTq : rw_cells _ m3 (h_ff H + 1336) _ |- _ =>
        eapply (seg_https' yi bs); [exact EVI | exact MI3 | exact ST3 | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPCq | exact CNTq
          | exact MU | exact WM | exact U8 | exact LBS | exact NUL | exact INCL | keeplia KL8 KE8] end. }
    lazymatch goal with FRq : rw_cells _ m3 (bv_unsigned sp + -144) _, VEPCq : rw_cells _ m3 VEP (vep_cells vv tag q), CNTq : rw_cells _ m3 (h_ff H + 1336) _ |- _ =>
      eapply MIDX; [exact MU| exact WM| exact MI3| exact ST3| cbv delta [FRAME' FRAME]; cbn [app]; exact FRq| exact VEPCq| exact CNTq] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vr"] Lemma seg_main3 : forall (yi : vsb_rec) (bs : list byte) (xra xt0 xt1 xt2 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (m1 : mem) (j40 cnt : list byte),
    vi = Some yi ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -144) (FRAME' [CB 40 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    u8arr rsegs (aview A0 m0) (vb_buf yi) bs -> Z.of_nat (length bs) = vb_size yi -> nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) (Z_to_bv 64 ((VEP + 280) / 8 + 2147450880))
                 (Z_to_bv 64 (vv Finclude_src)) a1 a2 a3 a4 a5 a6 a7
                 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 280)) xs10 xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x8ec6c) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM U8 LBS NUL. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    pose proof LENB as LENB'. rewrite EVI in LENB'. pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_8; dand7 dR_8 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI. pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_9; dand11 dR_9 as SI16 SIlo SIhi _ BI16 BIlo BIhi _ DSBI _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (SI16 & SIlo & SIhi & _ & BI16 & BIlo & BIhi & _ & DSBI & _ & _) ]).
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_10; dand8 dR_10 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    pose proof (mod8_of_mod16 (vv Finclude_src) SI16) as SI8.
    unfold kHighMemBeg in VEPlo, SIlo, BIlo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LSI (not_eq_sym NIS)) as DVSI.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LSI) as DJfSI.
    change (fsize HCLASS) with 8192 in DJfV, DJfSI.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (conj (sh_boundL (Clg:=Clg) (vv Finclude_src) 40 ltac:(keeplia SIlo) ltac:(clear; lia) ltac:(exact SIhi)) (sh_top_le' (vv Finclude_src) 40 ltac:(keeplia SIlo) ltac:(clear; lia) ltac:(exact SIhi))) as SHSIB. rewrite SHMAX_val in SHSIB. change ((40 + 7) / 8) with 5 in SHSIB.
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (as_live_shadow LPA _ _ _ (vv Finclude_src) 40 AINV00 LSI) as SHSI0. fold_cl_segs. fold_aview.
    assert (SHSI : bytes_at rsegs m1 (sh (vv Finclude_src)) (shpat 40)).
    { eapply (bytes_at_munch LPA); [exact SHSI0| exact MU|]. rewrite shpat_length by (clear; lia). change ((40 + 7) / 8) with 5. intros a__ Ha__. cbn [outside]. keeplia Ha__ SHSIB GCE VEPlo ACV CEIL LO. }
    hide SHSI0.
    pose proof IOBJ as IO. vsb_open IO. clear VBUF VLS VLB VNE. fold_cl_segs. fold_aview. rename VSBC into VSBC0.
    assert (VSBC : rw_cells rsegs m1 (vv Finclude_src) (vsb_cells yi)).
    { eapply (rw_cells_munch LPA); [exact VSBC0| exact MU| exact WM|]. rewrite vsb_cells_size. change (Z.of_nat 40) with 40. intros a__ Ha__. cbn [outside]. keeplia Ha__ SIhi DJfSI DVSI GCE VEPlo ACV CEIL LO. }
    clear VSBC0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    hide DVSI. hide DJfSI. hide DSBI. hide_neqs.
    pose proof VEPC as VEPCu. unfold vep_cells in VEPCu.
    cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    (* [comment removed for export] *)
    zstep.
    icall (VSB_data_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (vv Finclude_src) yi lo)
      by (try rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); ufs; unfold kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV
                | (eexists _, _; split; [exact SHSI| try (generalize alloc_ceiling_val); clear - SI8 SIhi SIlo ACV; try pose proof alloc_ceiling_val as ACV__; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | exact CE1
                | exact SI8
                | exact ST
                | exact MI
                | keeplia SIlo | keeplia SIhi | keeplia LO | exact CEIL ]).
    clear CE1.
    lazymatch goal with ST1 : stk _ ?v1 _ _, MI1 : mem_inv _ ?v1 |- evt _ _ (MS _ _ _ _ _ ?v1 _) =>
      rename v1 into m2; rename ST1 into ST2; rename MI1 into MI2 end.
    try (clear dependent m1).
    assert (CE2 : cenv m2)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    (* [comment removed for export] *)
    try clear SHSI. unhide SHSI0.
    assert (SHSI : bytes_at rsegs m2 (sh (vv Finclude_src)) (shpat 40)).
    { eapply (bytes_at_munch LPA); [exact SHSI0| exact MU|]. rewrite shpat_length by (clear; lia). change ((40 + 7) / 8) with 5. intros a__ Ha__. cbn [outside]. keeplia Ha__ SHSIB GCE VEPlo ACV CEIL LO. }
    clear SHSI0.
    (* [comment removed for export] *)
    vrechk SHV EzsV (VEP + 280) 8 0.
    zstep. zstep. zstep.
    icall (VSB_len_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (vv Finclude_src) yi true lo)
      by (try rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); ufs; unfold kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV
                | (eexists _, _; split; [exact SHSI| try (generalize alloc_ceiling_val); clear - SI8 SIhi SIlo ACV; try pose proof alloc_ceiling_val as ACV__; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | exact CE2
                | exact SI8
                | exact ST2
                | exact MI2
                | keeplia SIlo | keeplia SIhi | keeplia LO | exact CEIL ]).
    clear CE2.
    lazymatch goal with ST1 : stk _ ?v1 _ _, MI1 : mem_inv _ ?v1 |- evt _ _ (MS _ _ _ _ _ ?v1 _) =>
      rename v1 into m3; rename ST1 into ST3; rename MI1 into MI3 end.
    try (clear dependent m2).
    unfold vsb_result. rewrite IERR. cbn [Z.eqb].
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 4 1. try rewrite (shr3_div8 (VEP + 288)).
    (* [comment removed for export] *)
    zstep. pose proof HIC as IC; destruct IC as [IC|IC]; rewrite IC, ?sx32_small by (clear; lia).
    - zstep; if_cases KB; zify_cond KB; [| exfalso; apply KB; reflexivity]. clear KB.
      zstep. clear VEPCu VSBC. try clear SHSI.
      lazymatch goal with FRq : rw_cells _ m3 (bv_unsigned sp + -144) _, VEPCq : rw_cells _ m3 VEP (vep_cells vv tag q), CNTq : rw_cells _ m3 (h_ff H + 1336) _ |- _ =>
        eapply (seg_disp yi bs); [exact EVI | exact MI3 | exact ST3 | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPCq | exact CNTq
          | exact MU | exact WM | exact U8 | exact LBS | exact NUL | clear; lia] end.
    - zstep; if_cases KB; zify_cond KB; [exfalso; clear - KB; lia|]. clear KB.
      zstep. zstep. clear VEPCu VSBC. try clear SHSI.
      lazymatch goal with FRq : rw_cells _ m3 (bv_unsigned sp + -144) _, VEPCq : rw_cells _ m3 VEP (vep_cells vv tag q), CNTq : rw_cells _ m3 (h_ff H + 1336) _ |- _ =>
        eapply (seg_disp yi bs); [exact EVI | exact MI3 | exact ST3 | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPCq | exact CNTq
          | exact MU | exact WM | exact U8 | exact LBS | exact NUL | clear; lia] end.
  Qed.
End S.
End A_ve2so.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS160 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSe90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSq5u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VSt8w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_VS8zm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veqih OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_veq11 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo.A_ve5c7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vemjo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_ve6k0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_vep3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_ve8qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_ver79 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_veoi5.A_ve2so.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, strchr_icpt_post, vep_error_post, DATA_STACK, LEN_STACK, ASSERT_STACK, STRCHR_ICPT_STACK, VEPERR_STACK in H.
(* [comment removed for export] *)
Ltac simpl_sizes ::=
  rewrite ?app_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length];
  try (rewrite vep_cells_size by assumption); try (rewrite vsb_cells_size).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].




(* [comment removed for export] *)
Lemma stack_shadow_sp_hi {Clg : Ceiling} : forall v SB N lo hi, stack_shadow LPA v SB N lo hi -> hi <= 2^47.
Proof.
  (intros v SB N lo hi; (first [ intro dR_22; dand6 dR_22 as _ _ _ SH _ NK | intros (_ & _ & _ & SH & _ & NK) ])). unfold sh, kShadowOffset, kHighMemBeg in *.
  Z.div_mod_to_equations. lia.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (vi : option vsb_rec) (H : henv) (lo SB N : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HFL : 0 <= vv Fflags < 16.
  Hypothesis HET : bool01 (vv Femptytag).
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis HLM : vv Flast_mark = 1.
  Hypothesis HAZ : vv Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis SZB : vb_size vr <= vb_len vr + 4096.
  Hypothesis LENB : vb_len vr + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  Hypothesis LBM : a_livebytes A0 + vb_size vr + vb_len vr + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : match vi with Some yi => vb_len yi / 4096 | None => 0 end + 8 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM + (PPOT_CAP - vsb_ppot vr) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis LF : lib_frames A0.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fvsb /\ vv Finclude_src <> vb_buf vr /\
                   vb_buf yi <> vv Fvsb /\ vb_buf yi <> vb_buf vr
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - DOINCL_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q -> vkeep vv vv' [Fstate; Finclude_src; Finclude_continue] ->
      (vv' Fstate = vv Fstate \/ vv' Fstate = vi_st VIA S_TagError) -> bool01 (vv' Finclude_continue) -> vv' Finclude_src = 0 ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      match vi with
      | None => (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0
      | Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                   (forall r, r <> vb_buf vr -> r <> vb_buf vr' -> r <> vv Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A0 r) /\
                   a_livebytes A' = a_livebytes A0 + (vb_size vr' - vb_size vr) - 40 - vb_size yi /\ a_nlive A' = a_nlive A0 - 2
      end ->
      frames_aged A0 A' 1 1 -> a_tinycred A' = a_tinycred A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40)
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HFL (conj HET (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB
      (conj SZB (conj LENB (conj LBM (conj NLV (conj SCM (conj PRM (conj LF (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO (conj SPHI
      (conj STKSH K))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Let TINV := tinv VEP vv tag q vr vi H lo SB N sp m0 md0 A0.
  Let FRAME' := FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Local Ltac pose_parts :=
    pose proof (CFP VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as CFP';
    pose proof (W_cover VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as W_cover';
    pose proof (seg_main3 VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as seg_main3'.

  Local Ltac unpack_tinv TI :=
    (first [ dand26 TI as EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & VEPC & SOBJk & NEBk & LENk & SZk & RELk & LIVEk & LBk & TCk & NLk & SCk & PCk & FSk & STKSHk
                    & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Let SCR5' := SCR5 VEP.
  (* [comment removed for export] *)
  Let W : list (Z * Z) := [(bv_unsigned sp - DOINCL_STACK, bv_unsigned sp); (h_ff H + 1336, h_ff H + 1352); (VEP, VEP + 312)].

  (* [comment removed for export] *)
  Local Ltac henv_here mx MU WM CNT HENVx DJ GCE GHI SHF VEPlo :=
    try unhide DJ;
    lazymatch goal with HGx : henv_geom LPA H |- _ =>
    let ACV := fresh "ACV" in pose proof alloc_ceiling_num as ACV;
    let HFRM := fresh "HFRM" in let GLOB := fresh "GLOB" in let HOBJ := fresh "HOBJ" in let HSH := fresh "HSH" in
    let BSSV := fresh "BSSV" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT'" in
    pose proof HENV as (HFRM & GLOB & HOBJ & HSH);
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as BSSV BSS CP _ | pose proof GLOB as (BSSV & BSS & CP & _) ]); fold_cl_segs; cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS; unfold h_vsc, h_cp in BSSV, BSS, CP;
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in BSS; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO];
    eapply (rw_cells_munch LPA) in CP; [| exact MU| exact WM| cbn; keeplia DJ GHI GCE VEPlo ACV CEIL LO];
    destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
    assert (HENVx : henv_ok LPA VIA H A0 mx);
    [ split; [exact HFRM|]; split;
      [ eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp;
        [exact BSSV| exact BSS| exact CP| replace (h_ff H + 32 + 1304) with (h_ff H + 1336) by lia; exact C]
      | split; [ eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|];
                 intros a__ Ha__; unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_vsc in *; cbn [outside]; keeplia Ha__ DJ GHI GCE ACV CEIL LO
               | eapply (hshadow_munch LPA); [exact HSH| exact MU| exact HGx|];
                 intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ SHF GCE VEPlo ACV CEIL LO ] ]
    | clear BSSV BSS CP C c HFRM GLOB HOBJ HSH ACV ]
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vr"] Lemma seg_nosrc : forall (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (m1 : mem) (j40 cnt : list byte),
    vi = None ->
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -144) (FRAME' [CB 40 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1 a0 a1 a2 a3 a4 a5 a6 a7
                 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 2147450880) xs9 xs10 xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x8ede4) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros EVI MI ST FR VEPC CNT MU WM. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof HVI as ISRC0. rewrite EVI in ISRC0.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_3; dand7 dR_3 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ)) as dR_4; dand11 dR_4 as S16 Slo Shi _ B16 Blo Bhi _ DSB _ _ | pose proof (vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ) as (S16 & Slo & Shi & _ & B16 & Blo & Bhi & _ & DSB & _ & _) ]).
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS. pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB.
    unfold kHighMemBeg in VEPlo, Slo, Blo. all_app_facts.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 S 40 AINV00 VLV LS NES) as DVS.
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 (vb_buf vr) (vb_size vr) AINV00 VLV LB NEB) as DVB.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh _ _ AINV00 HFRh LB) as DJfB.
    change (fsize HCLASS) with 8192 in DJfV, DJfS, DJfB.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    assert (CE1 : cenv m1)
      by (eapply cenv_munch; [exact CE0| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; keeplia LO CEIL ACV GCE VEPlo]).
    (* [comment removed for export] *)
    pose proof (got_vsc_cell m1 (proj1 CE1)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    pose proof HENV as (_ & GLOB & HOBJ & HSH).
    (first [ pose proof (HSH) as dR_5; dand10 dR_5 as SHvs _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHvs & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHvs, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHwR. rewrite SHMAX_val in SHwR.
    eapply (bytes_at_munch LPA) in SHvs; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHVR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHc; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHcR GCE VEPlo LO CEIL ACV].
    eapply (bytes_at_munch LPA) in SHw; [| exact MU| intros a__ Ha__; cbn; keeplia Ha__ SHwR GCE VEPlo LO CEIL ACV].
    (first [ pose proof ((shadowed_bss_vsc _ (proj1 CE1))) as dR_6; dand8 dR_6 as PG NG SHG GAL G0 GLE GGE GCE' | destruct (shadowed_bss_vsc _ (proj1 CE1)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE') ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (GLOB) as dR_7; dand4 dR_7 as BSSV _ _ _ | pose proof GLOB as (BSSV & _ & _ & _) ]). fold_cl_segs. cbn [vi_bss_vsc VIA] in BSSV. unfold h_vsc in BSSV.
    eapply (rw_cells_munch LPA) in BSSV; [| exact MU| exact WM| cbn; keeplia GCE VEPlo ACV CEIL LO].
    (first [ pose proof (HOBJ) as dR_8; dand3 dR_8 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    eapply (rw_cells_munch LPA) in VC; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    eapply (rw_cells_munch LPA) in WK; [| exact MU| exact WM| cbn; keeplia DJfV GHI GCE VEPlo ACV CEIL LO].
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    hide DVS. hide DVB. hide DJfS. hide DJfB. hide DSB. hide_neqs.
    pose proof VEPC as VEPCu. unfold vep_cells in VEPCu. rewrite EVC in VEPCu. unfold h_vc in VEPCu. cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    fold_cl_segs.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    shadow_addr_at SHG 6191680 8.
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end.
    zstep. zstep; if_cases K0; zify_cond K0;
      [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
      | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk0 SHvs 8. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep. shadow_chk0 SHc 8. zstep. zstep. shadow_chk0 SHw 8.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    clear VEPCu.
    (* [comment removed for export] *)
    do 13 zstep. zstep.
    try replace (bv_unsigned sp + -144 + 144) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _, STq : stk _ ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      release_frame FRq STq (bv_unsigned sp); rename STq into STw end.
    carve_frame 48%nat STw.
    do 7 zstep.
    try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    lazymatch goal with FRv : rw_cells _ ?mx (bv_unsigned sp + -48) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      release_frame FRv STw (bv_unsigned sp) end.
    zstep.
    (* [comment removed for export] *)
    astop AINV00 MU WM CFP'.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, VEPCq : rw_cells _ ?ma VEP _, CNTq : rw_cells _ ?ma (h_ff H + 1336) _, STq : stk _ ?ma lo _
      |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename VEPCq into VEPC1; rename STq into STv;
      henv_here ma MU WM CNTq HENVa DJfV GCE GHI SHF VEPlo;
      assert (SOBJa : vsb_obj LPA A0 ma S vr false)
        by (unhide DJfS; unhide DJfB; unhide DVS; unhide DVB;
            eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi DJfS DJfB DVS DVB ACV CEIL LO])
    end.
    unhide_neqs.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A0 _ _ vv vr);
      [ exact AINVa | assumption
      | apply amd_frame_sbm; [exact SBM| exact MH]
      | exact STv | exact HENVa
      | split; [exact VLV|]; split; [exact VEPC1| split; [exact TAG8| exact PADS]]
      | exact (vkeep_refl vv [Fstate; Finclude_src; Finclude_continue])
      | left; reflexivity
      | exact HIC
      | exact ISRC0
      | exact SOBJa
      | rewrite EVI; clear; cbn; lia
      | clear; lia
      | left; reflexivity
      | rewrite EVI; split; [intros r; reflexivity|]; split; reflexivity
      | apply frames_same_aged; intros ff; reflexivity
      | reflexivity
      | clear; lia
      | clear; lia (* [comment removed for export] *)
      | ].
    (* [comment removed for export] *)
    eapply (cframe_noalloc LPA); [exact MU| ufs; apply W_cover'| eapply (stk_mapped (L:=LPA)); [exact STv | exact CEIL | keeplia LO | clear; lia]
      | intros a__ X; right; left; exact X].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB vi vr"] Lemma seg_head2 : forall (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (m1 : mem) (j40 cnt : list byte),
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -144) (FRAME' [CB 40 j40]) ->
    rw_cells rsegs m1 VEP (vep_cells vv tag q) ->
    rw_cells rsegs m1 (h_ff H + 1336) [CB 16 cnt] ->
    munch W (aview A0 m0) m1 -> wmono rsegs (aview A0 m0) m1 ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A0) (alhull A0) (aeager A0) m0 md0 T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1 a0 a1 a2 a3 a4 a5 a6 a7
                 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 2147450880) xs9 xs10 xs11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x8ec14) fc None m1 (seg_rom rsegs)).
  Proof.
    touch_all. intros until cnt. intros MI ST FR VEPC CNT MU WM. pose_parts.
    prelims. cbv delta [W] in MU.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_11; dand7 dR_11 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    unfold kHighMemBeg in VEPlo. all_app_facts.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV0. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    assert (SHV : bytes_at rsegs m1 (sh VEP) zsV).
    { eapply (bytes_at_munch LPA); [exact SHV0| exact MU|]. rewrite LZV. intros a Ha. cbn. keeplia Ha SHVB GCE VEPlo LO CEIL ACV. }
    clear SHV0.
    hide_neqs.
    pose proof VEPC as VEPCu. unfold vep_cells in VEPCu. rewrite HLM in VEPCu.
    cbv delta [FRAME' FRAME] in FR. cbn [app] in FR.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. try rewrite (shr3_div8 (VEP + 280)). zstep.
    assert (EV : (exists yi, vi = Some yi) \/ vi = None) by (clear; destruct vi; [left; eexists; reflexivity | right; reflexivity]).
    destruct EV as [[yi EVI]|EVI].
    - (* [comment removed for export] *)
      pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand3 HVI' as INZ IOBJ _ | destruct HVI' as (INZ & IOBJ & _) ]).
      (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ)) as dR_13; dand4 dR_13 as _ SIlo SIhi _ | pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) yi true AINV00 IOBJ) as (_ & SIlo & SIhi & _) ]). unfold kHighMemBeg in SIlo. all_app_facts.
      pose proof IOBJ as IO. vsb_open IO. clear VSBC VINV VLS VLB VNE. (first [ dex1 VBUF as bs; dand3 VBUF as U8 LBS NULi | dand4 VBUF as bs U8 LBS NULi | destruct VBUF as (bs & U8 & LBS & NULi) ]). pose proof (NULi eq_refl) as NUL. clear NULi.
      zstep. if_cases KT; zify_cond KT; [exfalso; apply INZ; clear - KT SIlo SIhi ACV; try pose proof alloc_ceiling_val as ACV__; mlia|]. clear KT.
      (* [comment removed for export] *)
      zstep. vchk SHV EzsV 8 0. zstep.
      zstep; if_cases KW; zify_cond KW.
      { clear VEPCu KW.
        lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, CNTq : rw_cells _ ?mx (h_ff H + 1336) _
          |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (seg_main3' yi bs); [exact EVI | exact MIq | exact STq | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPC | exact CNTq
            | exact MU | exact WM | exact U8 | exact LBS | exact NUL] end. }
      (* [comment removed for export] *)
      zstep. vchk SHV EzsV 4 0. zstep. rewrite ?sx32_small by (clear; lia). zstep.
      zstep; if_cases KT; zify_cond KT; [exfalso; apply KT; reflexivity|]. clear KT KW VEPCu.
      lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, CNTq : rw_cells _ ?mx (h_ff H + 1336) _
        |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (seg_main3' yi bs); [exact EVI | exact MIq | exact STq | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPC | exact CNTq
          | exact MU | exact WM | exact U8 | exact LBS | exact NUL] end.
    - (* [comment removed for export] *)
      pose proof HVI as ISRC0. rewrite EVI in ISRC0. rewrite ISRC0.
      zstep. if_cases KT; zify_cond KT; [| exfalso; apply KT; reflexivity]. clear KT VEPCu.
      lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, CNTq : rw_cells _ ?mx (h_ff H + 1336) _
        |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply seg_nosrc; [exact EVI | exact MIq | exact STq | cbv delta [FRAME' FRAME]; cbn [app]; exact FRq | exact VEPC | exact CNTq | exact MU | exact WM] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 W FRAME' S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 N SB H vi vr q tag vv"] Lemma main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv rsegs (aview A0 m0) -> a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 1 ->
    stk rsegs (aview A0 m0) lo (bv_unsigned sp) ->
    srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 vep_do_include_entry) fc None m0 (seg_rom rsegs)) md0) T.
  Proof.
    touch_all. intros until t6. intros MI -> -> ST. unfold vep_do_include_entry. pose_parts.
    prelims.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    (* [comment removed for export] *)
    pose proof VOBJ as (VLV & VEPC & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_15; dand7 dR_15 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]).
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    pose proof (proj1 HENV) as [ageh HFRh]. pose proof (proj1 VBASE) as EVC.
    pose proof (as_frame_blk_disjoint LPA A0 m0 md0 (h_ff H) HCLASS ageh VEP 312 AINV00 HFRh VLV) as DJfV.
    change (fsize HCLASS) with 8192 in DJfV.
    unfold kHighMemBeg in VEPlo. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF. rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(keeplia VEPlo) ltac:(clear; lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV00 VLV) as SHV. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV.
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    (* [comment removed for export] *)
    pose proof HENV as (_ & GLOB & HOBJ & HSH). (first [ pose proof (GLOB) as dR_16; dand4 dR_16 as BSSV _ _ [cnt CNT] | pose proof GLOB as (BSSV & _ & _ & [cnt CNT]) ]). fold_cl_segs. unfold h_vsc in CNT.
    replace (h_ff H + 32 + 1304) with (h_ff H + 1336) in CNT by lia.
    cbn [vi_bss_vsc VIA] in BSSV. unfold h_vsc in BSSV.
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    pose proof (map_cells_of_consts _ (proj1 CE0)) as MC. fold_aview. open_map_cells MC.
    pose proof (got_vsc_cell _ (proj1 CE0)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    (first [ pose proof (HSH) as dR_17; dand10 dR_17 as SHvs _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHvs & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHvs, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHwR. rewrite SHMAX_val in SHwR.
    (first [ pose proof ((shadowed_bss_vsc _ (proj1 CE0))) as dR_18; dand8 dR_18 as PG NG SHG GAL G0 GLE GGE GCE' | destruct (shadowed_bss_vsc _ (proj1 CE0)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE') ]). fold_cl_segs. fold_aview.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (HOBJ) as dR_19; dand3 dR_19 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. fold_aview. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    hide_neqs.
    pose proof (munch_refl W (aview A0 m0)) as MU. cbv delta [W] in MU. pose proof (wmono_refl rsegs (aview A0 m0)) as WM.
    pose proof VEPC as VEPCu. unfold vep_cells in VEPCu. rewrite EVC in VEPCu. unfold h_vc in VEPCu.
    ago AINV00. fold_cl_segs.
    carve_frame 144%nat ST.
    (* [comment removed for export] *)
    do 14 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT; [| exfalso; apply KT; reflexivity]. clear KT.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 4 0.
    zstep. pose proof HET as ET; destruct ET as [ET|ET]; rewrite ET, ?sx32_small by (clear; lia).
    2:{ (* [comment removed for export] *)
      zstep; if_cases KT; zify_cond KT; [| exfalso; clear - KT; lia]. clear KT VEPCu.
      lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx, CNTq : rw_cells _ ?mx (h_ff H + 1336) _,
                          VEq : rw_cells _ ?mx VEP (vep_cells vv tag q) |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply seg_head2; [exact MIq | exact STq | exact FRq | exact VEq | exact CNTq | exact MU | exact WM] end. }
    (* [comment removed for export] *)
    zstep; if_cases KT; zify_cond KT; [exfalso; apply KT; reflexivity|]. clear KT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    shadow_addr_at SHG 6191680 8.
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end.
    zstep. zstep; if_cases K0; zify_cond K0;
      [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
      | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk0 SHvs 8. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep. shadow_chk0 SHc 8. zstep. zstep. shadow_chk0 SHw 8.
    (* [comment removed for export] *)
    zstep. vchk SHV EzsV 8 0. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with STq : stk _ ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename STq into ST1 end.
    zstep. carve_frame 48%nat ST1.
    try replace (bv_unsigned sp + -144 + -48) with (bv_unsigned sp + -192) in * by lia.
    do 8 zstep.
    try replace (bv_unsigned sp + -192 + 48) with (bv_unsigned sp + -144) by lia.
    lazymatch goal with FRv : rw_cells _ ?mx (bv_unsigned sp + -192) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      release_frame FRv ST1 (bv_unsigned sp + -144) end.
    clear VEPCu.
    lazymatch goal with X : rw_cells rsegs ?mx (h_ff H + 1336) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (rw_cells_forget _ _ _ _ X) as [cnt' CNT']; cbn [cells_size csize Nat.add] in CNT'; clear X end.
    lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -144) _, STq : stk _ ?mx lo _, MIq : mem_inv _ ?mx,
                        VEq : rw_cells _ ?mx VEP (vep_cells vv tag q) |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      eapply seg_head2; [exact MIq | exact STq | exact FRq | exact VEq | exact CNT' | exact MU | exact WM] end.
  Qed.
End S.

(* [comment removed for export] *)
Section T.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  #[using="AI16"] Theorem vep_do_include_tag_ok : vep_do_include_tag_stmt.
  Proof.
    unfold vep_do_include_tag_stmt. intros until T. cbv zeta.
    intros AINV MI A0e A1e VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 ST CEIL LO STKSH K.
    eapply (main VEP vv tag q vr vi H lo SB N); try eassumption.
    - eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL| pose proof (zr_word sp) as SPR; unfold inr64 in SPR; lia| unfold_stacks; lia].
    - exact (stack_shadow_sp_hi _ _ _ _ _ STKSH).
  Qed.
End T.
