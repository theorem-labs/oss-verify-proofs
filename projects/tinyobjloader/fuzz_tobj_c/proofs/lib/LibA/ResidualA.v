(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "prod"; "bool"; "list"; "nat"; "pair"; "option"; "negb"; "fst"; "snd"; "andb"; "true"; "app"; "false"; "length"; "option_map"; "None"; "Some"; "nil"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_pc"; "sv_eqb"; "ss_facts"; "freg_sv"; "reg_sv"; "sobj"; "sprop"; "ss_objs"; "sstate"; "SLit"; "SPTrue"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "ax_S"; "ax_X"; "la_state"; "sym_runA"; "ax_base"; "axwf"; "la_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "wsub"; "wsub_id_below"; "obj_subst"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "sv_equiv"; "fdig"; "mk_dig"; "@stdpp.list_basics.list"; "list_filter"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "existsb_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.R"; "leaf_matchesA"; "show_leafA'"; "cfg_residualA"; "entailsA_dbg"; "entails_diagA"; "leaf_matches1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "fact_entailed_d"; "objs_entailed"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section R.
Variable segs : list Segment.

Definition entailsA_dbg (L T : axst) (s : wsub) : bool := ltac2:(tb__ "0|1|
S9S9S45S23VL;A1S23VT;A1Vs;A3S3aS0S13S13A2M0G0S39G0G0S9S15S2aVs;S7S13S13R2A3A2S7S13S13R1A3A2S15S2aVs;S8S13S13R2A3A2S8S13S13R1A3A2A2Lr';S24VL;A1A3Lr;S24VT;A1A3A2S15S2aVs;S27VT;A1A2S27VL;A1A2A2").
Definition leaf_matches1A (g : positive) (L X : axst) : bool := ltac2:(tb__ "0|3|
S1S1L_;M0S3bS14S23VL;A1M1A1S14S23VX;A1M2A1A2S3dVg;G1G2A3S2bG0S2cR1Vg;A2S42VL;VX;R1A3ScX1x2Ts;ScX1x2").
Definition leaf_matchesA (g : positive) (L : axst) (targets : list axst) : bool := ltac2:(tb__ "0|0|
S3eS22S44Vg;VL;A2Vtargets;A3").

Definition cfg_residualA (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list axst)
  : list (Z * option (list leafA)) := ltac2:(tb__ "0|3|
S2eS22S0S20S5S2S21A1M0A1M1A2S22S4S20G1S14S23R1A1A1G1G1Lx;S26Vsegs;Vfuel;Vcutpcs;R1SaA5G0S10G0S32S21G0S38S21A1S21S31S6S3fVg;S25R1A1SbS22Vcuts;Vexits;A3A3A1M2A1LL;S21S33G2A1Lx;R1A6A2Lleaves;SfG0A1X5x2A4LT;Vcuts;A4").
Definition show_leafA' (L : leafA) : Z * stop_reason := ltac2:(tb__ "0|0|
S4S20S34S14S23S25VL;A1A1A1S29VL;A1A4").
Definition cfg_residualA_show (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list axst) : ltac2:(tb__ "0|0|
S2S0S20S5S2S0S20S34A2A1A1A2A1") := ltac2:(tb__ "0|6|
S2eS0S20S5S2S21A1M0A1M1A2M2S0S20S5S2S0S20S34A2M3A1M4A1M5A2G2S4S20G5S7S20G1R1A3SeG0G4S2eS21G3S40A3S8S20G1R1A3A4A4Lp;S41Vfuel;Vcutpcs;Vg;Vcuts;Vexits;A5A4").

Definition cfg_leavesA_show (fuel : nat) (cutpcs : list Z) (cuts : list axst) : ltac2:(tb__ "0|0|
S2S0S20S5S2S0S20S34A2A1A1A2A1") := ltac2:(tb__ "0|3|
S2eS22S0S20S5S2S0S20S34A2M0A1M1A1M2A2S22S4S20G2S14S23R1A1A1SeS2S21A1G1S2eS21G0S40A3S26Vsegs;Vfuel;Vcutpcs;R1SaA5A4A4LT;Vcuts;A4").

Definition entails_diagA (g : positive) (L T : axst) : ltac2:(tb__ "0|1|
S0S0S0S0S0S0S1S2S3A1M0A2G0A2S1A2G0A2G0A2S0S1S1A2A2") := ltac2:(tb__ "0|16|
S23VL;A1S1cS23VT;A1S1cS3dVg;R2R1A3S2bS2cR1Vg;A2S1S32S3S2S3A1M0S38S3A1M1S3S31S6S12S3bS3cR1A1M2Z0M3A2S35S18R5G2A2S2aR3S18R4G2A2A2A2A2A1M4A1Lr;S3S33G4A1Lx;S30U0M5U20A2M6A6G0S32S3G0G1S3S31S6S35S17R6G2A2S2aR4S17R5G2A2A2A2A1M7A1Lr;S3S33G7A1Lx;G6A6G0S47S16R6A1S1bR6A1S2eS19S19S2dR4A1S1bR5A1A4A3S1S37S16R7A1M8A1S36S32S3G0G1S3S31S6S46R2S16R9A1R7S2fS1aR1S16R8A1S1eA4A4A1M9A1Li;S3S33G9A1Lx;S30G5SdS1aG8A2A2A6G0S32S3G0G1S3S2fS0S13S13A2MaR1S24VT;A1MbS4S13S13S1dG3A1McGcA4MdA4GaS31S6S39GaGaS9S15S2aRaS7S13S13R2A3A2S7S13S13R1A3MeA2S15S2aRaS8S13S13R2A3A2S8S13S13R1A3MfA2A2Lr';S24VL;A1M10A3A1A1Tr;Li;S3S33S6S39GaGaS9S15S2aR9S7S13S13S2fGaR2GbGdA4M11A3A2GeA2S15S2aR9S8S13S13G11A3A2GfA2A2Lr';G10A3A1A1Lx;S30G5SdGaGbA2A2A6G0S4S0S0S0S0S0S1G0A2M12G0A2M13S1A2M14G0A2M15G0A2S0S1S1A2S4G15G0S4G14G0S4G13S1S4G12G0S4S1G0R7R6A4R5A4R4A4R2A4R1A4S4S1S1S1fR9A1S28VT;A1A4A4Txs;Tff;Td;Tob;Tfr;Txr;Tokid;Ts;TST;TSL;").

Definition cfg_diagA (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list axst) (T : axst) : ltac2:(tb__ "0|1|
S2S0S20S2S0S0S0S0S0S0S1S2S3A1M0A2G0A2S1A2G0A2G0A2S0S1S1A2A2A1A2A1") := ltac2:(tb__ "0|a|
S5S2S21A1M0A1S2S0S20S2S0S0S0S0S0S0S1S2S3A1M1A2G1A2S1A2G1A2G1A2S0S1S1A2A2M2A1M3A2M4A1Lx;S26Vsegs;Vfuel;Vcutpcs;VT;SaA5G0S2eS21G4S21S4S20G3S14S23S25R1A1M5A1A1S2eS22G2S22S43Vg;S25R2A1M6R1A3LX;S32S22S2S22A1S38S22A1S22S31S3bS14S23R1A1A1S14S23G6A1A1A2M7A1LX;S22S33G7A1Lx;SbS22Vcuts;Vexits;A3M8A6A4A4LL;S32S21G0S38S21A1S21S31S6S3fVg;G5G8A3A1M9A1LL;S21S33G9A1Lx;R1A6A4Lleaves;S11G4A1X5x2").
End R.
