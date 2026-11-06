(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_020.   (* [comment removed for export] *)
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "ss_regs"; "sobj"; "ss_facts"; "ss_pc"; "sv_eqb"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "bool"; "nil"; "None"; "Some"; "negb"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "BAD"; "vDp"; "vF"; "Pre_00"; "cps_pro"; "leafL_at"; "ms_carve"; "s_msx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs.LOAddr"; "memset_pc"; "DW"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "vARn"; "vBo"; "E_mb"; "E_mc"; "E_s00"; "Pre_mc48"; "T_ma_ok0"; "VST"; "blkAR"; "fnodup"; "vALo"; "xnodup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve_darr"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "tv_factsA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueC ObjEmptyA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_vec_reserve_darr Lib_build_line_index.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_load_obj_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr VRAddr RA.ReallocAddr VRDAddr LOAddr.
Definition bli_entry : Z := BLIAddr.bli_entry.

Definition pAR : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_ma)) 10.
Definition vARn : sv := SVar pAR.
Definition blkAR : sv * sv := ltac2:(tb__ "0|0|
SaS0S0S24S1Z40A1A4").
Definition T_ma_null : axst := Eval vm_compute in T_afterA Pre_ma E_ma s_ma R_ma (L_malloc_null AE_A W2 UStopLe).
Definition T_ma_ok0 : axst := Eval vm_compute in T_afterA Pre_ma E_ma s_ma R_ma (L_malloc_ok AE_A W2 UStopLe).
Definition T_ma_ok : axst := ltac2:(tb__ "0|0|
S33S36S2cA1S2aA2").

Definition E_mc0 : axst := Eval vm_compute in leafL_at cps_pro T_ma_ok memcpy_pc 0.
Definition E_mc1 : axst := Eval vm_compute in optL (apply_axforms E_mc0 [AXSplit (idxB E_mc0 vARn 0) (SLit 48)]).
Definition E_mc2 : axst := Eval vm_compute in optS E_mc1 (zero_cells_at (ax_S E_mc1) (idxB E_mc1 vF 496) [c8 496 (SLit 0); c8 504 (SLit 0)]).
Definition E_mc3 : axst := Eval vm_compute in optL (apply_axforms E_mc2 [AXSplit (idxB E_mc2 vF 0) (SLit 464)]).
Definition E_mc4 : axst := Eval vm_compute in optL (apply_axforms E_mc3 [AXSelect (sel2last E_mc3 (idxB E_mc3 vF 464) (idxB E_mc3 vF 496))]).
Definition E_mc5 : axst := Eval vm_compute in optL (apply_axforms E_mc4 [AXMerge (length (ss_objs (ax_S E_mc4)) - 2)%nat]).
Definition E_mc : axst := Eval vm_compute in optL (apply_axforms E_mc5 [AXUnbase (ilast E_mc5) 464]).
Definition vALo : sv := SAlu ALU_ADD vF (SLit 464).
Definition vBo : sv := SAlu ALU_ADD vF (SLit 544).
Definition Pre_mc48 : axst := Pre_memcpy48 AE_A al48_cells.
Definition L_mc48 : axst := L_memcpy48 AE_A al48_cells.
Definition s_mc : wsub := ltac2:(tb__ "0|1|
SbScS7S0A2M0SaS7S0P35S24A4SbG0SaS7S0P36S1Z40A1A4SbG0SaS7S0P37S2eA4SbG0SaS7S0P38S1Z30A1A4SbG0SaS7S0S31S1aA4S30PaS13S27A1S13S29A1A3A3A3A3A3A3").
Definition R_mc : list sobj := Eval vm_compute in optR (entails_frA E_mc Pre_mc48 s_mc).
Definition T_mc : axst := Eval vm_compute in T_afterA Pre_mc48 E_mc s_mc R_mc L_mc48.

Definition E_s00_0 : axst := Eval vm_compute in leafL_at cps_pro T_mc ss00_pc 0.
Definition E_s00_1 : axst := Eval vm_compute in shadow_reopen_stateA E_s00_0 (ax_X E_s00_0) g5 68 231.
Definition E_s00 : axst := Eval vm_compute in optL (apply_axforms E_s00_1 (xf_shcall E_s00_1 68)).
Definition s_s00 : wsub := ltac2:(tb__ "0|0|
SbScS7S0A2SaS7S0S31S1aA4S30PaS13S28A1S13S1cA1A3A3").
Definition R_s00 : list sobj := Eval vm_compute in optR (entails_frA E_s00 Pre_00 s_s00).
Definition T_s00_0 : axst := Eval vm_compute in T_afterA Pre_00 E_s00 s_s00 R_s00 L_00.
Definition T_s00_1 : axst := Eval vm_compute in optL (apply_axforms T_s00_0 (xf_shback T_s00_0)).
Definition T_s00 : axst := Eval vm_compute in shadow_release_stateA T_s00_1 (objs_butlast T_s00_1) 110 [(544, 1304)].

Definition E_mb0 : axst := Eval vm_compute in leafL_at cps_pro T_s00 memset_pc 0.
Definition E_mb : axst := Eval vm_compute in ms_carve E_mb0 vF 640 1208.
Definition s_mb : wsub := ltac2:(tb__ "0|0|
S20S26S25S1Z518A1A3").
Definition R_mb : list sobj := Eval vm_compute in R_of E_mb Pre_ms s_mb.
Definition T_mb0 : axst := Eval vm_compute in ms_T0 E_mb s_mb.
Definition T_mb : axst := Eval vm_compute in optL (apply_axforms T_mb0 [AXRebase 1]).

Fixpoint xnodup (l : list (sv * sv)) : list (sv * sv) :=
  match l with
  | [] => []
  | x :: r => if existsb (fun y => sv_eqb (fst y) (fst x) && sv_eqb (snd y) (snd x)) r then xnodup r else x :: xnodup r
  end.
Definition ax_xnodup (A : axst) : axst := ltac2:(tb__ "0|0|
S34VA;S2fS15VA;A1A1A2").

Fixpoint fnodup (l : list sprop) : list sprop :=
  match l with [] => [] | x :: r => if existsb (sprop_eqb x) r then fnodup r else x :: fnodup r end.
Definition ax_fnodup (A : axst) : axst := ltac2:(tb__ "0|0|
S35VA;S2dS4S13VA;A1A1A1A2").
Definition ax_tidy (A : axst) : axst := ax_fnodup (ax_xnodup A).

Definition xcover (b : sv) : sv * sv := ltac2:(tb__ "0|1|
SdScS0S0A2L_;S6Vb;S1bA2SaS0S0S25S1Z518A1A4SaS0S0S32S37S23S22A2M0A1S1G0A1A4Xdx2").

Definition ms_auto_E (T : axst) : option (axst * sv * Z) := ltac2:(tb__ "0|10|
S1eS1dVT;S21U0A4S14SdS12ScScS14S0A2M0S8A2M1A1M2L_;S11S38S5S13R1A1M3A1S21A2A1SfG1A1M4S0G2Lx;M5S18S0UaS2G3A1S1Z0A1M6A4S8G4Lz;S7G4Li;M7S16S0S0S16G2Lop;R3S0G2Lb0;R1S8G5S18S0UcS2S13R5A1A1G6A4S8S8G2Lz;R1G4S7S7G2Lp;R1S7G4Lp0;S7S7G2Lp0;R1S7G4Lp1;S7S7G2Lp1;R1S7G4Lp2;S7S7G2Lp2;R1S7S7G2Lp3;R1S7G4Lp4;M8G8S10G1SaG0S8SaS14S0S1fRbR9R7Z18A4R9A4R7A4A2X7x3Lp3;S7G4Lp3;G4X7x3Lp2;G4X7x3Lp1;G4X7x3Lp0;G4X7x3Lp;S7G4Lp;X8x3Lz;G7S16S0S0G4Lb1;La;M9Lop0;MaGaS17G9Lop0;MbGbSdS9S0G4La;Lw;Lsgn;McS7S0S8G4Lk;Li;Ll;MdX0x8Loff;G7GaGaGbGbGcGdX0x8G4G4G4G4G4G4G4G4G4X16xaLb0;Lb;Lop;S16S0S0G4Lb;La;MeLop;S17GeLop;MfGfGcGdX0x8Xdx2TE0;").
Record vstep := VST { vs_E : axst; vs_b : sv; vs_off : Z; vs_s : wsub; vs_R : list sobj; vs_T : axst }.
Fixpoint vchain (n : nat) (T : axst) : list vstep :=
  match n with
  | O => []
  | S n' =>
      match ms_auto_E T with
      | Some (E, b, off) =>
          let s := s_msx E (fst (xcover b)) (snd (xcover b)) in
          let R := R_of E Pre_ms s in
          let T1 := ax_tidy (ms_back24 (T_afterA Pre_ms E s R L_ms) b off) in
          VST E b off s R T1 :: vchain n' T1
      | None => []
      end
  end.
Definition VCH : list vstep := Eval vm_compute in vchain 34 T_mb.
Definition vsBAD : vstep := ltac2:(tb__ "0|0|
S2bS19S1bZ0SeScS7S0A2A1SeS3A1S19A6").
Definition vsn (j : nat) : vstep := nth j VCH vsBAD.

Definition T_vend : axst := vs_T (vsn 33).

Goal length VCH = 34%nat
  /\ forallb (fun v => match entails_frA (vs_E v) Pre_ms (vs_s v) with Some R => call_checkPA (vs_E v) Pre_ms (vs_s v) R [L_ms] | None => false end) VCH = true
  /\ map vs_off VCH = [664; 696; 728; 760; 792; 824; 864; 896; 928; 960; 992; 1040; 1072; 1104; 1136; 1168; 1200; 1232; 1264; 1296; 1328; 1360; 1392;
                        1480; 1512; 1544; 1576; 1608; 1640; 1672; 1704; 1736; 1768; -216].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

