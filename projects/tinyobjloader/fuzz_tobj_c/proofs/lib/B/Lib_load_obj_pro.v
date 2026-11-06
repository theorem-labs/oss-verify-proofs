(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "ss_regs"; "SAlu"; "SVar"; "ss_facts"; "ss_objs"; "ss_pc"; "sv_eqb"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "bool"; "nil"; "nat"; "None"; "S"; "Some"; "app"; "length"; "negb"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vDp"; "vF"; "BAD"; "Pre_ms"; "cps_pro"; "idxB"; "ilast"; "leafL_at"; "ms_carve"; "sel_last"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXRebase"; "AXSelect"; "AXUnbase"; "@Corelib.Lists.ListDef"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs.LOAddr"; "FR"; "memset_pc"; "DW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "vARn"; "E_f8a"; "E_ma"; "E_mc"; "E_mz"; "E_s00"; "E_sm0"; "Pre_00"; "Pre_f8"; "Pre_ma"; "Pre_mc48"; "Pre_sm"; "T_ma_ok0"; "VST"; "blkAR"; "fnodup"; "vALo"; "vBo"; "xnodup"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "opp"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "tv_factsA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjZeroFillB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr VRAddr RA.ReallocAddr LOAddr.

Definition E_sm0 : axst := Eval vm_compute in leafL_at cps_pro Pre_lo sm5_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 5.
Definition L_sm : axst := L_stack_malloc AE_A 5.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
SeSfSaS0A2SdSaS0S29S1dA4S28PaS1aS3cA1S1aS41A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition fr_lo : list (sv * Z * sv) := ltac2:(tb__ "0|2|
SeSfSfS0SbA2M0S0A2M1SdG0S0SdS0SbS1eZ5A4S27A4S11G1A1A3").
Definition T_sm1 : axst := Eval vm_compute in optL (apply_axforms T_sm [AXSelect (sel_last T_sm 3)]).
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 (objs_butlast T_sm1) X_lo 110 2048.
Definition C_pro : axst := Eval vm_compute in ax_setX C_pro0 ((vF, SLit 0) :: ax_X C_pro0).

Definition Pre_f8 : axst := Pre_set_shadow AE_A 248.
Definition L_f8 : axst := L_set_shadow 248.
Definition Pre_00 : axst := Pre_set_shadow AE_A 0.
Definition L_00 : axst := L_set_shadow 0.
Definition E_f8a0 : axst := Eval vm_compute in leafL_at cps_pro C_pro ssf8_pc 0.

Definition E_f8a1 : axst := Eval vm_compute in shadow_release_stateA E_f8a0 (objs_butlast E_f8a0) 110 [].
Definition E_f8a2 : axst := Eval vm_compute in shadow_reopen_stateA E_f8a1 X_lo g5 56 219.
Definition xf_shcall (A : axst) (k : Z) : list axform := ltac2:(tb__ "0|0|
SeS2dS30S23VA;A1S49S4dVk;A2A2S11S2dA1A3").
Definition E_f8a : axst := Eval vm_compute in optL (apply_axforms E_f8a2 (xf_shcall E_f8a2 56)).
Definition s_f8a : wsub := ltac2:(tb__ "0|0|
SeSfSaS0A2SdSaS0S29S1dA4S28PaS1aS37A1S1aS3eA1A3A3").
Definition R_f8a : list sobj := Eval vm_compute in optR (entails_frA E_f8a Pre_f8 s_f8a).
Definition T_f8a0 : axst := Eval vm_compute in T_afterA Pre_f8 E_f8a s_f8a R_f8a L_f8.

Definition xf_shback (A : axst) : list axform := ltac2:(tb__ "0|1|
SeS2dS2eU1M0A1SeS2dS2fS26VA;G0A2A1S11S2dA1A3A3").
Definition T_f8a1 : axst := Eval vm_compute in optL (apply_axforms T_f8a0 (xf_shback T_f8a0)).
Definition T_f8a2 : axst := Eval vm_compute in shadow_release_stateA T_f8a1 (objs_butlast T_f8a1) 110 [].
Definition C_pro2 : axst := Eval vm_compute in shadow_reopen_stateA T_f8a2 (ax_X T_f8a2) g5 219 240.

Definition pc_oz : Z := 0x8d008.
Definition cps_oz : list Z := pc_oz :: cps_pro.
Definition E_oz0 : axst := Eval vm_compute in leafL_at cps_oz C_pro2 pc_oz 0.

Definition iOUT (A : axst) : nat := idxB A vOUT 0.
Definition E_oz1 : axst := Eval vm_compute in optS E_oz0 (zero_fill_at (ax_S E_oz0) (iOUT E_oz0)).

Definition E_oz2 : axst := Eval vm_compute in shadow_release_stateA E_oz1 (objs_butlast E_oz1) 110 [].
Definition C_pro3 : axst := Eval vm_compute in shadow_reopen_stateA E_oz2 (ax_X E_oz2) g5 20 52.

Definition E_mz0 : axst := Eval vm_compute in leafL_at cps_pro C_pro3 memset_pc 0.

Definition E_mz1 : axst := Eval vm_compute in shadow_release_stateA E_mz0 (objs_butlast E_mz0) 110 [(368, 48)].

Definition E_mz2 : axst := Eval vm_compute in optL (apply_axforms E_mz1 [AXSplit (idxF E_mz1) (SLit 400); AXSplit (S (idxF E_mz1)) (SLit 416)]).
Definition E_mz : axst := Eval vm_compute in ax_setS E_mz2 (reshape_obj_at (ax_S E_mz2) (S (idxF E_mz1)) (fslot 400 16 [] DUnknown)).
Definition s_mz : wsub := ltac2:(tb__ "0|1|
SeSfSaS0A2M0SdSaS0P35S4S2cS1eS1Z170A1A3A4SeG0SdSaS0P36S1Z30A1A4SeG0SdSaS0S29S1dA4S28PaS1aS3aA1S1aS20A1A3A3A3A3").
Definition R_mz : list sobj := Eval vm_compute in optR (entails_frA E_mz Pre_ms s_mz).
Definition T_mz0 : axst := Eval vm_compute in T_afterA Pre_ms E_mz s_mz R_mz L_ms.

Definition T_mz1 : axst := Eval vm_compute in ax_setS T_mz0 (reshape_obj_at (ax_S T_mz0) 1 (fpiece 400 416 [] DZero)).

Definition E_ma0 : axst := Eval vm_compute in leafL_at cps_pro T_mz1 malloc_pc 0.
Definition W2 : list ulink := Wcan 2.
Definition Pre_ma : axst := Pre_malloc AE_A W2 UStopLe.
Definition idxFlo (A : axst) : nat := ltac2:(tb__ "0|0|
S22VA;S5PaA1S4bS33A1A3").
Definition E_ma : axst := Eval vm_compute in optL (apply_axforms E_ma0 [AXSplit (idxFlo E_ma0) (SLit (-16))]).
Definition s_ma : wsub := ltac2:(tb__ "0|0|
SeSfSaS0A2SdSaS0S29S1dA4S28PaS1aS38A1S1aS3fA1A3A3").
Definition R_ma : list sobj := Eval vm_compute in optR (entails_frA E_ma Pre_ma s_ma).

Definition pAR : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_ma)) 10.
Definition vARn : sv := SVar pAR.
Definition blkAR : sv * sv := ltac2:(tb__ "0|0|
SdS0S0S36S1Z40A1A4").
Definition T_ma_null : axst := Eval vm_compute in T_afterA Pre_ma E_ma s_ma R_ma (L_malloc_null AE_A W2 UStopLe).
Definition T_ma_ok0 : axst := Eval vm_compute in T_afterA Pre_ma E_ma s_ma R_ma (L_malloc_ok AE_A W2 UStopLe).
Definition T_ma_ok : axst := ltac2:(tb__ "0|0|
S4fS52S44A1S42A2").

Definition E_mc0 : axst := Eval vm_compute in leafL_at cps_pro T_ma_ok memcpy_pc 0.
Definition E_mc1 : axst := Eval vm_compute in optL (apply_axforms E_mc0 [AXSplit (idxB E_mc0 vARn 0) (SLit 48)]).
Definition E_mc2 : axst := Eval vm_compute in optS E_mc1 (zero_cells_at (ax_S E_mc1) (idxB E_mc1 vF 400) [c8 400 (SLit 0); c8 408 (SLit 0)]).
Definition E_mc3 : axst := Eval vm_compute in optL (apply_axforms E_mc2 [AXSplit (idxB E_mc2 vF 0) (SLit 368)]).
Definition E_mc4 : axst := Eval vm_compute in optL (apply_axforms E_mc3 [AXSelect (sel2last E_mc3 (idxB E_mc3 vF 368) (idxB E_mc3 vF 400))]).
Definition E_mc5 : axst := Eval vm_compute in optL (apply_axforms E_mc4 [AXMerge (length (ss_objs (ax_S E_mc4)) - 2)%nat]).
Definition E_mc : axst := Eval vm_compute in optL (apply_axforms E_mc5 [AXUnbase (ilast E_mc5) 368]).
Definition vALo : sv := SAlu ALU_ADD vF (SLit 368).
Definition vBo : sv := SAlu ALU_ADD vF (SLit 448).
Definition Pre_mc48 : axst := Pre_memcpy48 AE_A al48_cells.
Definition L_mc48 : axst := L_memcpy48 AE_A al48_cells.
Definition s_mc : wsub := ltac2:(tb__ "0|1|
SeSfSaS0A2M0SdSaS0P35S36A4SeG0SdSaS0P36S1Z40A1A4SeG0SdSaS0P37S46A4SeG0SdSaS0P38S1Z30A1A4SeG0SdSaS0S29S1dA4S28PaS1aS39A1S1aS40A1A3A3A3A3A3A3").
Definition R_mc : list sobj := Eval vm_compute in optR (entails_frA E_mc Pre_mc48 s_mc).
Definition T_mc : axst := Eval vm_compute in T_afterA Pre_mc48 E_mc s_mc R_mc L_mc48.

Definition E_s00_0 : axst := Eval vm_compute in leafL_at cps_pro T_mc ss00_pc 0.
Definition E_s00_1 : axst := Eval vm_compute in shadow_reopen_stateA E_s00_0 (ax_X E_s00_0) g5 56 219.
Definition E_s00 : axst := Eval vm_compute in optL (apply_axforms E_s00_1 (xf_shcall E_s00_1 56)).
Definition s_s00 : wsub := ltac2:(tb__ "0|0|
SeSfSaS0A2SdSaS0S29S1dA4S28PaS1aS3bA1S1aS3dA1A3A3").
Definition R_s00 : list sobj := Eval vm_compute in optR (entails_frA E_s00 Pre_00 s_s00).
Definition T_s00_0 : axst := Eval vm_compute in T_afterA Pre_00 E_s00 s_s00 R_s00 L_00.
Definition T_s00_1 : axst := Eval vm_compute in optL (apply_axforms T_s00_0 (xf_shback T_s00_0)).
Definition T_s00 : axst := Eval vm_compute in shadow_release_stateA T_s00_1 (objs_butlast T_s00_1) 110 [(448, 1304)].

Definition pc_bz : Z := 0x8d3b0.
Definition cps_bz : list Z := pc_bz :: cps_pro.
Definition iFb (A : axst) : nat := idxC A vF 448.
Definition sel_first (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
SeS12Vi;S16S12S32U0Vi;A2S32S14Vi;A1M0S4cS17S2S7S1aVA;A1A1A2G0A2A2A3A3").
Definition E_bz_p0 : axst := Eval vm_compute in optL (apply_axforms T_s00 [AXSplit (iFb T_s00) (SLit 448); AXSplit (S (iFb T_s00)) (SLit 1752)]).
Definition E_bz_pre : axst := Eval vm_compute in optL (apply_axforms E_bz_p0 [AXSelect (sel_first E_bz_p0 (idxB E_bz_p0 vF 448))]).
Definition E_bz0 : axst := Eval vm_compute in leafL_at cps_bz E_bz_pre pc_bz 0.
Definition E_bz1 : axst := Eval vm_compute in optL (apply_axforms E_bz0 [AXSplit 0 (SLit 544)]).
Definition T_mb : axst := Eval vm_compute in optS E_bz1 (zero_fill_at (ax_S E_bz1) 1).

Fixpoint xnodup (l : list (sv * sv)) : list (sv * sv) :=
  match l with
  | [] => []
  | x :: r => if existsb (fun y => sv_eqb (fst y) (fst x) && sv_eqb (snd y) (snd x)) r then xnodup r else x :: xnodup r
  end.
Definition ax_xnodup (A : axst) : axst := ltac2:(tb__ "0|0|
S50VA;S48S1cVA;A1A1A2").

Fixpoint fnodup (l : list sprop) : list sprop :=
  match l with [] => [] | x :: r => if existsb (sprop_eqb x) r then fnodup r else x :: fnodup r end.
Definition ax_fnodup (A : axst) : axst := ltac2:(tb__ "0|0|
S51VA;S45S6S1aVA;A1A1A1A2").
Definition ax_tidy (A : axst) : axst := ax_fnodup (ax_xnodup A).

Definition xcover (b : sv) : sv * sv := ltac2:(tb__ "0|1|
S10SfS0S0A2L_;S9Vb;S1eA2SdS0S0S47S1Z518A1A4SdS0S0S4eS49S33S35A2M0A1S1G0A1A4X10x2").

Definition ms_auto_E (T : axst) : option (axst * sv * Z) := ltac2:(tb__ "0|10|
S24S21VT;S34U0A4S1bS10S19SfSfS1bS0A2M0SbA2M1A1M2L_;S18S4aS8S1aR1A1M3A1S34A2A1S13G1A1M4S0G2Lx;M5S31S0UaS3G3A1S1Z0A1M6A4SbG4Lz;SaG4Li;M7S2aS0S0S2aG2Lop;R3S0G2Lb0;R1SbG5S31S0UcS3S1aR5A1A1G6A4SbSbG2Lz;R1G4SaSaG2Lp;R1SaG4Lp0;SaSaG2Lp0;R1SaG4Lp1;SaSaG2Lp1;R1SaG4Lp2;SaSaG2Lp2;R1SaSaG2Lp3;R1SaG4Lp4;M8G8S15G1SdG0SbSdS1bS0S25RbR9R7Z18A4R9A4R7A4A2Xax3Lp3;SaG4Lp3;G4Xax3Lp2;G4Xax3Lp1;G4Xax3Lp0;G4Xax3Lp;SaG4Lp;Xbx3Lz;G7S2aS0S0G4Lb1;La;M9Lop0;MaGaS2bG9Lop0;MbGbS10ScS0G4La;Lw;Lsgn;McSaS0SbG4Lk;Li;Ll;MdX0x8Loff;G7GaGaGbGbGcGdX0x8G4G4G4G4G4G4G4G4G4X2axaLb0;Lb;Lop;S2aS0S0G4Lb;La;MeLop;S2bGeLop;MfGfGcGdX0x8X10x2TE0;").
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
Definition VCH : list vstep := Eval vm_compute in vchain 1 T_mb.
Definition vsBAD : vstep := ltac2:(tb__ "0|0|
S43S1fS1eZ0S11SfSaS0A2A1S11S2A1S1fA6").
Definition vsn (j : nat) : vstep := nth j VCH vsBAD.

Definition T_vend : axst := vs_T (vsn 0).
Goal length VCH = 1%nat /\ ss_pc (ax_S (vs_E (vsn 0))) = memset_pc /\ vs_off (vsn 0) = -328.
Proof. vm_compute. repeat split; reflexivity. Qed.
