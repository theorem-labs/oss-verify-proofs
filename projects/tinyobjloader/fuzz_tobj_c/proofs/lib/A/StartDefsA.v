(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "cell"; "ss_objs"; "mkObj"; "ob_base"; "ob_cells"; "ob_hi"; "ob_lo"; "DUnknown"; "SLit"; "c_off"; "c_width"; "ob_dflt"; "@Corelib.Init.Datatypes"; "app"; "false"; "S"; "cons"; "bool"; "nil"; "prod"; "orb"; "pair"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "snorm"; "@Stdlib.ZArith.BinInt.Z"; "add"; "leb"; "mul"; "of_nat"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_base"; "mkAX"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "obj_to_unknown"; "@Stdlib.Lists.List"; "forallb"; "@stdpp.bitvector.definitions"; "Z_to_bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundL SymObj.
Import ListNotations.
Open Scope Z_scope.

Definition move_obj_last (St : sstate) (i : nat) : sstate := ltac2:(tb__ "0|1|
S1aVSt;SeS0S17S0Vi;S3VSt;A1M0A3SeS0S18S0S10Vi;A1G0A3S17S0U1S18S0Vi;G0A3A3A3A3A2").

Definition obj_to_unknown (o : sobj) : sobj := ltac2:(tb__ "0|0|
S4S5Vo;A1S8Vo;A1S7Vo;A1S6Vo;A1S9A5").
Definition unknown_obj_at (St : sstate) (i : nat) : sstate := ltac2:(tb__ "0|1|
S1aVSt;SeS0S17S0Vi;S3VSt;A1M0A3SeS0S19S0S0S29S17S0U1S18S0Vi;G0A3A3A4S18S0S10Vi;A1G0A3A3A3A2").

Definition pageZ (q : Z) (k : nat) : bv 64 := ltac2:(tb__ "0|0|
S2bQ40S1cVq;S1eZ1000S1fVk;A1A2A2A2").
Fixpoint pages_rev (q : Z) (n : nat) : list (bv 64) :=
  match n with O => [] | S k => pageZ q k :: pages_rev q k end.

Fixpoint split_chain (St : sstate) (l : list (nat * sv)) : option sstate :=
  match l with
  | [] => Some St
  | (i, mid) :: r => match split_obj_at St i mid with Some St' => split_chain St' r | None => None end
  end.

Definition replace_obj_at (St : sstate) (i : nat) (o' : sobj) : sstate := ltac2:(tb__ "0|1|
S1aVSt;SeS0S17S0Vi;S3VSt;A1M0A3S11S0Vo';S18S0S10Vi;A1G0A3A3A3A2").

Definition add_cell_front (o : sobj) (c : cell) : sobj := ltac2:(tb__ "0|0|
S4S5Vo;A1S8Vo;A1S7Vo;A1S11S2Vc;S6Vo;A1A3SdVo;A1A5").
Definition cells_clear_lit (cells : list cell) (off k : Z) : bool := ltac2:(tb__ "0|4|
S2aS2S2S1S12Lx;SbR1A1S20S15S1dS1cS1bR1A1M0ScR2A1A2Voff;A2S1dS1cVoff;Vk;A2G0A2A2Lco;S21SfLi;S26S1S1SfLb;La;M1Lop;M2G2S27G1Lop;M3G3S12S22S1SfLa;Lw;Lsgn;S21S1S20SfLk0;Li;Ll;X1x8Lc;Vcells;A3").

Definition X0 : list (sv * sv) := ltac2:(tb__ "0|2|
S11S14S1S1A2M0S16S1S1SaZ0A1M1G1A4S13G0A1A3").
Definition withX0 (A : axst) : axst := ltac2:(tb__ "0|0|
S25S23VA;A1S28S24VA;A1A3").
Definition noX (A : axst) : axst := ltac2:(tb__ "0|0|
S25S23VA;A1S13S14S1S1A2A1S24VA;A1A3").
