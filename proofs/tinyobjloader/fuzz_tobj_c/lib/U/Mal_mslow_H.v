(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "add"; "sub"; "le"; "div"; "of_nat"; "pow"; "lt"; "modulo"; "leb"; "eqb"; "ltb"; "opp"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SLit"; "SVar"; "cell"; "soff"; "SMd"; "rw"; "sv"; "c_val"; "smatch"; "sobj"; "c_off"; "c_width"; "eval"; "ob_base"; "ob_cells"; "@Corelib.Init.Datatypes"; "bool"; "pair"; "cons"; "list"; "nat"; "option"; "Some"; "prod"; "true"; "app"; "nil"; "None"; "length"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "toS"; "zsupported"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_I1"; "kd"; "zl1"; "zr1"; "off"; "stv"; "zz"; "zSt"; "sz"; "zE"; "zG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LMem"; "MCell"; "VZ"; "le_byte"; "frame_ptr"; "loc_addr"; "mc_w"; "U0"; "hdr_byte3"; "hdr_off16"; "mc_loc"; "mc_val"; "sval_num"; "yields"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "VM1"; "vkind"; "E_sll"; "E_strideT"; "E_stride"; "E_strideM"; "VL"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "M_MUL"; "ALU_OR"; "ALU_SLL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "padd"; "sptr"; "am_maplen"; "astate"; "slot_start"; "NEST_FUEL"; "alloc_slot"; "nth_slot"; "ss_hdr"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "wz"; "C_U"; "byteview_of"; "malloc_stack"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_D"; "rsv"; "vo"; "vr"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocSlowPost"; "ms_frame"; "f_newcells"; "ms_ptr"; "as_ok_facts"; "ms_hdr"; "ms_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow_H.ReabH"; "AND155"; "AND157"; "@Stdlib.Lists.List"; "In"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sv_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost"; "malloc_class"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "slot_end"; "reserved_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.Mal_mslow_G"; "m'"; "slot_cells"; "oMeta"; "oSlot"; "@Corelib.Lists.ListDef"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs.RS"; "LF"; "R0"; "Sok"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundR SymFrame SymSummary SymCall SymEntail Glue3 ExampleMemcpy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfSurgery MallocWfGeom MallocWfRepr MallocWfMain
  MallocWfSlot MallocLayout MallocFooter MallocFooterLemmas MallocIface MallocLaws Contract Glue ReprGlue ZEval ZBits
  FreeQuickModel Zones ImageUpd FpLaws MallocFastPost WalkLink MallocIfaceI NestTier MallocSlowPost TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G1.Mal_mslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_I1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G2.Mal_mslow_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G3.Mal_mslow_G.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RS.

Section ReabH.

Variables (s0 s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta) (idx : Z) (ktr : list (kreq * Z)).
Variable rho : valuation.
Variables (b3 b16 : Z).
Hypothesis HW0 : WF s0.
Hypothesis HCS : slow_case s0 n.
Hypothesis HF : ltac2:(tb__ "0|0|
S75Vs;S80Vs0;Vn;A2Vn;Vg;Vam;Vidx;A6").
Hypothesis HUB : ub_same s0 s.
Hypothesis HYA : ltac2:(tb__ "0|0|
S4aS29S0S5cA2S5fS5eS80Vs0;Vn;A2Vn;Vs0;A4Vktr;S23S0S5cVidx;Vs;A4A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S1S0S64Q40S18Vrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.
Hypothesis Hhdr : ltac2:(tb__ "0|1|
S0S0S1S27S29S0S0A2M0A1S61S60Vam;Vidx;A2A1S28G0S23S0S0R2R1A4A2A3S2S1S0Vb3;R3A3S1S0Vb16;R2A3A2F_;Fh16;Fh3;").
Local Abbreviation stv := (@U.Mal_mslow__G2.Mal_mslow_I1.stv am).
Local Abbreviation sz := (@U.Mal_mslow__G2.Mal_mslow_I1.sz am).
Local Abbreviation zG := (@U.Mal_mslow__G2.Mal_mslow_I1.zG L g).
Local Abbreviation zSt := (@U.Mal_mslow__G2.Mal_mslow_I1.zSt L am idx).
Local Abbreviation zE := (@U.Mal_mslow__G2.Mal_mslow_I1.zE L am idx).
Local Notation "§1§ h__" := (h__ s n am b3 b16) (at level 10, h__ global).
Local Abbreviation off := (§1§ U.Mal_mslow__G2.Mal_mslow_I1.off).
Local Abbreviation zz := (@U.Mal_mslow__G2.Mal_mslow_I1.zz s b3 b16).
Local Abbreviation kd := (@U.Mal_mslow__G2.Mal_mslow_I1.kd am).
Local Abbreviation Hmaplen := (@U.Mal_mslow__G2.Mal_mslow_I1.Hmaplen s0 s n g am idx HF).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S8aS69S2cS5aA1S28S29S5aS0A2S23S5aS0Vg;Vidx;A4A2S44S89Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Abbreviation Hoff := (@U.Mal_mslow__G2.Mal_mslow_I1.Hoff s0 s n g am idx b3 b16 HCS HF Hb3 Hb16).
Local Abbreviation off_model := (@U.Mal_mslow__G2.Mal_mslow_I1.off_model s n am idx b3 b16 Hb3 Hb16 Hhdr).
Local Notation "§2§ h__" := (h__ s L n g am idx rho b3 b16) (at level 10, h__ global).
Local Abbreviation rho1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.rho1).
Local Abbreviation zr1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.zr1).
Local Abbreviation zl1 := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.zl1).
Local Abbreviation Hmaplen_small := (@U.Mal_mslow__G2.Mal_mslow_I1.Hmaplen_small s0 s L n g am idx b3 b16 HF Hb3 Hb16 rd0 wok0 vm HMI).
Local Abbreviation R_all := (@U.Mal_mslow__G2.Mal_mslow_I1.R_all s0 s L n g am idx b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI).
Local Abbreviation ze_var := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_var).
Local Abbreviation ze_lit := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_lit).
Local Abbreviation ze_alu := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_alu).
Local Abbreviation ze_aluw := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_aluw).
Local Abbreviation ze_mul := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_mul).
Local Abbreviation ze_ext := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_ext).
Local Abbreviation ze_lbytes := (§2§ U.Mal_mslow__G2.Mal_mslow_I1.ze_lbytes).
Local Notation "§3§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze12 := (§3§ U.Mal_mslow__G2.Mal_mslow_I1.ze12).
Local Notation "§4§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze157 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze157).
Local Abbreviation ze158 := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze158).
Local Abbreviation ze_strideT := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze_strideT).
Local Abbreviation ze_stride := (§4§ U.Mal_mslow__G2.Mal_mslow_I1.ze_stride).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S2S8Z1000S64Q40S18Vrho;PaA2A2M0A2S1S0SdG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S2S8S30Z40S64Q40S18Vrho;PfA2A2A2M0S11S6bA1A2S8S11SbZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S8S6cVL;A1S6S64Q40M0S18Vrho;PaA2A2S30Z40S64G0S18Vrho;PfA2A2A2A2A2").
Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S1S62Q40A1S27S62Q8A1A1F_;Vrd0;S65S4bVm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S1S62Q40A1S22F_;Vwok0;S66S4bVm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S0S2S8Z0R1A2ScR1Z60A2A2S1S27S62Q8A1M0A1Vm0;S63Q40S6Z108ecR2A2A2A1S2dG0A1A3F_;Fkk;").
Hypothesis Hm3 : ltac2:(tb__ "0|2|
S1S27S62Q8M0A1M1A1S65S4bVm0;S63Q40S7S38VL;Vam;Vidx;A3Z3A2A2A3S28G1S63G0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S26S70R1U2M0A2S1S27S62Q8M1A1M2A1S65S4bVm0;S63Q40S6S7S38VL;Vam;Vidx;A3Z2A2SaR2A1A2A2A3S28G2S63G1S40Vb16;G0R2A3A2A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S6aS65S4bVm0;A2S66S4bVm0;A2A2").
Local Abbreviation soff_of_ev := (@U.Mal_mslow__G2.Mal_mslow_I1.soff_of_ev s L n g am idx rho b3 b16 Hb3 Hb16 m0).
Local Abbreviation Zones := (@U.Mal_mslow__G2.Mal_mslow_I1.Zones s0 s L n g am idx rho b3 b16 HCS HF HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hsp_high).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S8bS4bVKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S25S78A1S79OF_;F_;").
Hypothesis HK : implK Kc K.
Variable mW : word -> option byte.
Let rhoW : valuation := rho1 mW.
Local Abbreviation Zv12 := (§3§ U.Mal_mslow__G2.Mal_mslow_D.Zv12).
Local Abbreviation Zv142 := (§4§ U.Mal_mslow__G2.Mal_mslow_D.Zv142).
Local Abbreviation Zv143 := (§4§ U.Mal_mslow__G2.Mal_mslow_D.Zv143).
Local Abbreviation Zv150 := (§4§ U.Mal_mslow__G2.Mal_mslow_D.Zv150).
Local Abbreviation Zv151 := (§4§ U.Mal_mslow__G2.Mal_mslow_D.Zv151).
Local Abbreviation Zv152 := (§4§ U.Mal_mslow__G2.Mal_mslow_D.Zv152).
Local Abbreviation Zv153 := (§4§ U.Mal_mslow__G2.Mal_mslow_D.Zv153).
Local Abbreviation Zv154 := (§4§ U.Mal_mslow__G2.Mal_mslow_D.Zv154).
Local Abbreviation Zv155 := (§4§ U.Mal_mslow__G2.Mal_mslow_D.Zv155).
Local Abbreviation Zv156 := (§4§ U.Mal_mslow__G2.Mal_mslow_D.Zv156).
Local Abbreviation Zv157 := (§4§ U.Mal_mslow__G2.Mal_mslow_D.Zv157).
Local Abbreviation Zv158 := (§4§ U.Mal_mslow__G2.Mal_mslow_D.Zv158).
Local Abbreviation ZE_S := (§4§ U.Mal_mslow__G2.Mal_mslow_D.ZE_S).
Local Abbreviation ZE_strideT := (§4§ U.Mal_mslow__G2.Mal_mslow_D.ZE_strideT).
Local Notation "§5§ h__" := (h__ s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp) (at level 10, h__ global).
Local Abbreviation ZE_and155 := (§5§ U.Mal_mslow__G2.Mal_mslow_D.ZE_and155).
Local Abbreviation ZE_strideM := (§4§ U.Mal_mslow__G2.Mal_mslow_D.ZE_strideM).
Local Abbreviation ZE_sll := (§5§ U.Mal_mslow__G2.Mal_mslow_D.ZE_sll).
Local Notation "§6§ h__" := (h__ rho b3 b16 Hb3 Hb16) (at level 10, h__ global).
Local Abbreviation land_255 := (§6§ U.Mal_mslow__G2.Mal_mslow_D.land_255).
Local Abbreviation land_31' := (§6§ U.Mal_mslow__G2.Mal_mslow_D.land_31').
Local Abbreviation rsv := (§1§ U.Mal_mslow__G2.Mal_mslow_D.rsv).
Local Abbreviation vo := (§1§ U.Mal_mslow__G2.Mal_mslow_D.vo).
Local Abbreviation vr := (§1§ U.Mal_mslow__G2.Mal_mslow_D.vr).
Local Abbreviation ze_sll := (§5§ U.Mal_mslow__G2.Mal_mslow_D.ze_sll).
Local Notation "§7§ h__" := (h__ s0 s n g am idx rho b3 b16 HF Hb3 Hb16 Hsp) (at level 10, h__ global).
Local Abbreviation kd_cases := (§7§ U.Mal_mslow__G2.Mal_mslow_D.kd_cases).
Local Abbreviation vo_cases := (@U.Mal_mslow__G2.Mal_mslow_D.vo_cases s0 s n g am idx rho b3 b16 HCS HF Hb3 Hb16).
Local Abbreviation vr_cases := (§5§ U.Mal_mslow__G2.Mal_mslow_D.vr_cases).
Local Abbreviation stv_VM1 := (§7§ U.Mal_mslow__G2.Mal_mslow_D.stv_VM1).
Local Abbreviation stv_T := (§7§ U.Mal_mslow__G2.Mal_mslow_D.stv_T).
Variables (tr : list event) (md : Model) (ms' : machine_state) (rhoF : valuation).
Hypothesis EmW : mW = rm rho.
Hypothesis Em0 : m0 = rm rho.
Hypothesis Evm : vm = m_vmmaps md.
Hypothesis Hsm : ltac2:(tb__ "0|0|
S1bS4bVrho;S8eS23S25S78A1S7aVtr;S7bVms;Vmd;A2A4A4").
Hypothesis Hsm0 : ltac2:(tb__ "0|0|
S1bS4bVrhoW;S8dS32Vam;A1A1S23S25S78A1S7aVtr;S7bVms;Vmd;A2A4A4").
Hypothesis HagF : agrees rhoW rhoF.
Hypothesis HsmF : ltac2:(tb__ "0|0|
S1bS4bVrhoF;S8cS32Vam;A1S6eVs;Vn;Vam;Vb3;Vb16;A5S6fVs;Vn;Vam;Vb3;Vb16;A5A3S23S25S78A1S7aVtr;S7bVms';Vmd;A2A4A4").
Local Abbreviation oMeta := (@U.Mal_mslow__G3.Mal_mslow_G.oMeta).
Local Abbreviation oSlot := (§1§ U.Mal_mslow__G3.Mal_mslow_G.oSlot).
Local Abbreviation NL := (§1§ U.Mal_mslow__G3.Mal_mslow_G.NL).
Local Notation "§8§ h__" := (h__ s n am rho b3 b16 ms' rhoF) (at level 10, h__ global).
Local Abbreviation m' := (§8§ U.Mal_mslow__G3.Mal_mslow_G.m').
Local Notation "§9§ h__" := (h__ s L n g am idx rho b3 b16 mW rhoF HagF) (at level 10, h__ global).
Local Abbreviation evF := (§9§ U.Mal_mslow__G3.Mal_mslow_G.evF).
Local Abbreviation rhoW_m0 := (@U.Mal_mslow__G3.Mal_mslow_G.rhoW_m0 s L n g am idx rho b3 b16 m0 mW EmW Em0).
Local Abbreviation HromF := (@U.Mal_mslow__G3.Mal_mslow_G.HromF s n am b3 b16 tr md ms' rhoF HsmF).
Local Abbreviation m'_in := (§8§ U.Mal_mslow__G3.Mal_mslow_G.m'_in).
Local Notation "§10§ h__" := (h__ s n am rho b3 b16 Hb3 Hb16 Hsp Hdepth tr md ms' rhoF HsmF) (at level 10, h__ global).
Local Abbreviation HoSlotF := (§10§ U.Mal_mslow__G3.Mal_mslow_G.HoSlotF).
Local Abbreviation HoMetaF := (§10§ U.Mal_mslow__G3.Mal_mslow_G.HoMetaF).
Local Abbreviation soffFW := (§9§ U.Mal_mslow__G3.Mal_mslow_G.soffFW).
Local Abbreviation baseF_p0 := (@U.Mal_mslow__G3.Mal_mslow_G.baseF_p0 s0 s L n g am idx rho b3 b16 HCS HF Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp mW rhoF HagF).
Local Abbreviation soffF_lit := (@U.Mal_mslow__G3.Mal_mslow_G.soffF_lit rho b3 b16 Hb3 Hb16 rhoF).

Ltac zlits :=
  repeat match goal with
  | |- context [ (?x mod ?y) ] =>
      lazymatch x with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      lazymatch y with Zpos _ => idtac | Z.pow (Zpos _) (Zpos _) => idtac end;
      let vv := eval vm_compute in (x mod y) in change (x mod y) with vv
  end.
Ltac mlia := Z.to_euclidean_division_equations; lia.

Ltac zpeel side :=
  repeat (first
    [ rewrite ZE_strideT | rewrite ZE_strideM by side | rewrite ZE_and155 by side | rewrite ZE_sll | rewrite ZE_S
    | rewrite ze_alu | rewrite ze_aluw | rewrite ze_mul | rewrite ze_ext | rewrite ze_lbytes | rewrite ze_var | rewrite ze_lit ]).
Ltac flat_mods := repeat (first [rewrite Zplus_mod_idemp_l | rewrite Zplus_mod_idemp_r | rewrite Zminus_mod_idemp_l | rewrite Zminus_mod_idemp_r
                               | rewrite Zmult_mod_idemp_l | rewrite Zmult_mod_idemp_r | rewrite Zmod_mod]).

Ltac small_mods := repeat match goal with |- context [?a mod 2 ^ 64] =>
        lazymatch a with context [_ mod _] => fail | _ => idtac end;
        rewrite (Z.mod_small a (2 ^ 64)) by lia end.
Ltac zev2 side :=
  cbn [E_pn E_p E_p0 E_stride E_strideT E_strideM E_S E_sll E_X E_X0 E_X1 E_lowbit v];
  zpeel side; cbn [zalu Z.of_N];
  rewrite ?Zv12, ?Zv142, ?Zv143, ?Zv150, ?Zv151, ?Zv152, ?Zv153, ?Zv154, ?Zv155, ?Zv156, ?Zv157, ?Zv158;
  flat_mods; zlits;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by (clear; lia);
  rewrite ?land_255, ?land_31'.

Lemma loc_padd : ltac2:(tb__ "0|0|
S5aS0S1S0S42VL;S3dS59R2R1A2A1A2S6S67VL;R2A2R1A2A3Fd;Fp;").
Proof using Hb16 Hb3 rho. intros [r o] d. unfold addr_of, loc_addr, padd. lia. Qed.
Lemma A_g : ltac2:(tb__ "0|0|
S1S0S67VL;Vg;A2S3bVL;Vg;A2A3"). Proof using . reflexivity. Qed.
Lemma A_st : ltac2:(tb__ "0|0|
S1S0S67VL;S5dVam;Vidx;A2A2S38VL;Vam;Vidx;A3A3"). Proof using . reflexivity. Qed.
Lemma A_e : ltac2:(tb__ "0|0|
S1S0S67VL;S81Vam;Vidx;A2A2S3aVL;Vam;Vidx;A3A3"). Proof using . reflexivity. Qed.
Lemma A_p : ltac2:(tb__ "0|0|
S1S0S67VL;S74Vs;Vn;Vam;Vidx;S37Vs;Vb3;Vb16;A3A5A2S6S38VL;Vam;Vidx;A3S5Z10S35Vs;Vn;Vam;Vb3;Vb16;A5A2A2A3").
Proof using Hb16 Hb3 Hhdr rho. unfold ms_ptr. rewrite <- (loc_padd (slot_start am idx)). unfold addr_of. rewrite <- off_model. unfold UNIT. reflexivity. Qed.
Lemma A_fp : ltac2:(tb__ "0|0|
S1S0S67VL;S41Vam;Vidx;S72Vs;Vn;Vam;Vidx;S37Vs;Vb3;Vb16;A3A5A3A2S6S38VL;Vam;Vidx;A3S5Z10S35Vs;Vn;Vam;Vb3;Vb16;A5A2A2A3").
Proof using Hb16 Hb3 Hhdr rho. unfold frame_ptr, ms_frame. cbn [fr_off]. rewrite <- (loc_padd (slot_start am idx)). unfold addr_of. rewrite <- off_model. unfold UNIT. reflexivity. Qed.
Lemma rsv_eq1 : ltac2:(tb__ "0|0|
S1S0S77Vs;Vn;Vam;Vidx;S37Vs;Vb3;Vb16;A3A5S6dVs;Vn;Vam;Vb3;Vb16;A5A3").
Proof using Hb16 Hb3 Hhdr rho. unfold ms_reserved, U.Mal_mslow__G2.Mal_mslow_D.rsv. rewrite <- off_model. change (ms_stride am) with stv. unfold IB, UNIT. lia. Qed.
Lemma rsv_eq2 : ltac2:(tb__ "0|0|
S1S0S82Vam;S72Vs;Vn;Vam;Vidx;S37Vs;Vb3;Vb16;A3A5A2S6dVs;Vn;Vam;Vb3;Vb16;A5A3").
Proof using Hb16 Hb3 Hhdr rho. unfold reserved_of, ms_frame, U.Mal_mslow__G2.Mal_mslow_D.rsv. cbn [fr_off fr_n]. rewrite <- off_model. change (stride_of am) with stv. unfold IB, UNIT. lia. Qed.
Lemma hdr3_eq : ltac2:(tb__ "0|2|
S1S0S45Vam;Vidx;S72Vs;Vn;Vam;Vidx;S37Vs;Vb3;Vb16;A3A5A3S6Vidx;S5Z20S22S0L_;SeZ5M0S6dVs;Vn;Vam;Vb3;Vb16;A5M1A2G0G1X22x2A2A2A3").
Proof using Hb16 Hb3 Hhdr rho.
  unfold hdr_byte3, rsv_code, ms_frame. cbn [fr_kind fr_off fr_n]. rewrite <- off_model.
  change (stride_of am) with stv. unfold U.Mal_mslow__G2.Mal_mslow_D.rsv, IB, UNIT.
  replace (stv - 4 - 16 * off - n) with (stv - 16 * off - n - 4) by lia. reflexivity.
Qed.
Lemma hoff16_eq : ltac2:(tb__ "0|0|
S1S0S46Vam;Vidx;S72Vs;Vn;Vam;Vidx;S37Vs;Vb3;Vb16;A3A5A3S6S9S5S36Vam;A1Vidx;A2Z10A2S35Vs;Vn;Vam;Vb3;Vb16;A5A2A3").
Proof using Hb16 Hb3 Hhdr. unfold hdr_off16, ms_frame. cbn [fr_off]. rewrite <- off_model. reflexivity. Qed.
Lemma ms_hdr_eq : ltac2:(tb__ "0|4|
S1S29S0S0A2M0S76Vs;Vn;Vam;Vidx;S37Vs;Vb3;Vb16;A3A5S22G0L_;SfS35Vs;Vn;Vam;Vb3;Vb16;A5M1Z0A2S23S0S0S6Vidx;S5S22S0L_;SeZ5M2S6dVs;Vn;Vam;Vb3;Vb16;A5M3A2G2G3X22x2Z20A2A2S9S5S36Vam;A1Vidx;A2Z10A2A4S23S0S0Ze0G1A4X22x2A3").
Proof using Hb16 Hb3 Hhdr rho. unfold ms_hdr, ms_rsv. rewrite rsv_eq1, <- off_model. change (ms_stride am) with stv. unfold UNIT. reflexivity. Qed.

Lemma newcells_eq : ltac2:(tb__ "0|17|
S1S25S3cA1M0S73Vs;Vn;Vam;Vidx;S37Vs;Vb3;Vb16;A3M1A5S2bS3cS29S0S0A2M2G0Lp;S22G2L_;SfS35Vs;Vn;Vam;Vb3;Vb16;A5M3Z0M4A2M5S23S0S0S6Vidx;S5S22S0L_;SeZ5M6S6dVs;Vn;Vam;Vb3;Vb16;A5M7A2M8G6G7X22x2M9Z20MaA2A2S9S5S36Vam;A1Vidx;A2Z10A2MbA4S23S0S0Ze0G3A4X22x2S0S0S24S3cS3eS3dS59S5dVam;Vidx;A2McN3MdA2A1U1MeS3fR2A1A3S24S3cS3eS3dS59GcN2MfA2A1U2M10S3fR1A1A3S2cS3cA1M11A3A3Lh16;Lh3;X29x1S2bS3cS22G0L_;M12G5G11S24S3cS3eS3dS59S74Vs;Vn;Vam;Vidx;G1A5M13N4M14A2A1GeS3fG4A1M15A3S24S3cS3eS3dS59G13GdA2A1GeS3fS6Vidx;S5GaG9A2A2A1A3S24S3cS3eS3dS59G13GfA2A1G10S3fS6GbG3A2A1A3G11A3A3A3X22x2S2bS3cG12S10G4G7A2S24S3cS3eS3dS59S41Vam;Vidx;S72Vs;Vn;Vam;Vidx;G1A5A3Vn;A2A1GeG15A3G11A3G11X22x2S2bS3cG12G8S24S3cS3eS3dS59S81Vam;Vidx;A2M16G14A2A1U4S3fG7A1A3G11A3G11X22x2G12S10G6G7A2S24S3cS3eS3dS59G16N5A2A1GeG15A3G11A3G11X22x2A3A3A3A3A3").
Proof using Hb16 Hb3 Hhdr rho.
  unfold MallocSlowPost.f_newcells, MallocSlowPost.f_hdrcells, MallocSlowPost.f_frcells, MallocSlowPost.f_footcells, MallocSlowPost.f_off, MallocSlowPost.f_fr.
  rewrite ms_hdr_eq, hdr3_eq, hoff16_eq. unfold frame_footer_cells. cbn [fr_kind ms_frame fr_n]. rewrite rsv_eq2.
  rewrite <- off_model. reflexivity.
Qed.

Lemma le_byte_congr : ltac2:(tb__ "0|1|
S0S0S26S26S1S0SdR4SbZ2S5Z8SaR2A1A2A2M0A2SdR3G0A2A3S1S0S40R5R3R2A3S40R4R3R2A3A3F_;Fk;Fw;Fy;Fx;").
Proof using . intros x y w k E. unfold le_byte. rewrite E. reflexivity. Qed.

Lemma In_nth_eq : ltac2:(tb__ "0|0|
S25S15A1S26S15S15S1S15S88S15R3R4R2A4R1A3S70R4S2eS15R5A2A2S7eS15R3R6A3F_;F_;Fc;Fd;Fi;Fl;").
Proof using . intros l i d c <- Hi. apply nth_In. exact Hi. Qed.

Lemma soffF_ev : ltac2:(tb__ "0|0|
S19S0S1S22S7fS83R2A2S2aA3S1S22S31R3A1S2aA3S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9R4A3R3A3S2S8Z0R4A2ScR4SbZ2Z3fA2A2A2S1S0S16VrhoF;R6A2R5A3F_;F_;F_;F_;Fz;Fe;").
Proof using Em0 EmW HagF Hb16 Hb3. intros e z Hv Hs Hz Hr. rewrite (soffFW e Hv). rewrite rhoW_m0. exact (soff_of_ev e z Hs Hz Hr). Qed.

Lemma V3_cell : ltac2:(tb__ "0|5|
S1cS15S0S0S26S4S1S1cR5S87Vs;Vn;Vam;Vb3;Vb16;A5A3S1S1cR5S86A3A2S7eS15R5S21R6A1A3S1S0S1eR6A1SaR3A1A3S2S70U0R4A2S71R4U8A2A2S1S0S6S64Q40S1fVrhoF;S20R9A1A2A2S16VrhoF;S1dR8A1A2A2R7A3S1S22S7fS83S1aR9A1A2S2aA3S1S22S31S1aRaA1A1S2aA3S1S0SdS2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S1aRbA1A3SbZ2S5Z8SaR8A1A2A2M0A2SdR9G0A2A3S26S70R1RaA2S2S1S22S66S4bS84Vs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8M1S68S6RdSaR2A1A2A1M2A3S2aA3S1S27S62Q8M3A1M4A1S65S4bG1G2A3S28G4S63G3S40RcRbR2A3A2A2A3A2F_;Fj;F_;F_;F_;F_;F_;F_;F_;F_;Fw;FV;FA;Fc;Fo;").
Proof using HagF Hb16 Hb3 Hdepth HsmF Hsp.
  intros o c A V w Ho Hc Hw Hw8 HA Vv Zs HV j Hj.
  assert (HOo : obj_holds segsU rhoF ms' o) by (destruct Ho as [-> | ->]; [apply HoSlotF|apply HoMetaF]).
  pose proof HOo as (Hb & _ & Hcs & _). pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as (C1 & C2 & _).
  unfold obj_lo_of, obj_hi_of in Hb, C1, C2.
  assert (Rx : fst (obj_range rhoF o) <= A + Z.of_nat j < snd (obj_range rhoF o)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. lia. }
  assert (IN : in_ranges rhoF NL (wz (A + Z.of_nat j))).
  { exists o. split; [destruct Ho as [-> | ->]; unfold NL; cbn; tauto|]. unfold wz. rewrite u64 by lia. exact Rx. }
  pose proof (m'_in _ IN) as E.
  destruct (dunk_byte rhoF ms' o (A + Z.of_nat j) HOo ltac:(destruct Ho as [-> | ->]; reflexivity) Rx) as [_ W].
  split; [exact (wok_of_at m' ms' _ E W)|].
  rewrite (rd_of_at m' ms' _ HromF E).
  pose proof (cell_bytes_sym rhoF ms' o c j HOo Hc ltac:(rewrite Hw; lia)) as R. rewrite HA in R. unfold wz. rewrite R. f_equal.
  rewrite (evF (c_val c) Vv Zs), Hw, Nat2Z.id. rewrite nth_enc_bytes by lia. f_equal. apply le_byte_congr. exact HV.
Qed.

Ltac model_addr :=
  rewrite ?loc_padd, ?A_g, ?A_st, ?A_e, ?A_p, ?A_fp.

Definition arith_facts (P : Prop) : Prop := P.
Ltac lean := match goal with AR : arith_facts _ |- _ => generalize AR; clear; intros AR; unfold arith_facts in AR; decompose [and] AR; clear AR end.
Ltac side := lean; lia.

Definition AND155 : sv := SAlu ALU_AND (SVar 155) (SLit 18446744073709547520).
Definition AND157 : sv := SAlu ALU_AND (SVar 157) (SLit 31).

Local Ltac zfin := cbn [zalu Z.of_N]; zlits; pose proof R_all as R; pose proof Hoff as HO.

Lemma a_sll : ltac2:(tb__ "0|1|
S0S8Z1S35Vs;Vn;Vam;Vb3;Vb16;A5M0A2S2ScN10R2A2S8R2Z0A2A2S1S0S16VrhoF;S12S53S4eS13R3A1A3A2S6S5Z10G0A2R3A2A3F_;F_;Fk;").
Proof using Em0 EmW HCS HF HMI HagF Hb16 Hb3 Hhdr Hsp.
  intros k Ho Hk. apply soffF_ev; [reflexivity|reflexivity| |pose proof Hoff; lia].
  rewrite ze_alu, ze_sll, ze_lit. zfin. mlia.
Qed.
Lemma a_12 : ltac2:(tb__ "0|0|
S1S0S16VrhoF;S14PcA1A2Vn;A3").
Proof using Em0 EmW HCS HF HMI HP12 HagF Hb16 Hb3 Hhdr Hsp. apply soffF_ev; [reflexivity|reflexivity| exact ze12 |pose proof R_all; lia]. Qed.
Lemma a_12sll : ltac2:(tb__ "0|0|
S1S0S16VrhoF;S12S53S14PcA1S4eA3A2S6Vn;S5Z10S35Vs;Vn;Vam;Vb3;Vb16;A5A2A2A3").
Proof using Em0 EmW HCS HF HMI HP12 HagF Hb16 Hb3 Hhdr Hsp.
  apply soffF_ev; [reflexivity|reflexivity| |pose proof R_all; pose proof Hoff; lia].
  rewrite ze_alu, ze_sll. change (SVar 12) with (v 12). rewrite ze12. zfin. mlia.
Qed.
Lemma a_T : ltac2:(tb__ "0|0|
S0S3S1S4dS32Vam;A1S4cA3A1S2S8N10R2A2S8R2Z0A2A2S1S0S16VrhoF;S12S53S4fS13R3A1A3A2S6S5Z10S39Vam;A1A2R3A2A3F_;F_;Fk;").
Proof using Em0 EmW HCS HF HMI HagF Hb16 Hb3 Hhdr Hsp.
  intros k Hk Hr. apply soffF_ev; [reflexivity|reflexivity| |pose proof R_all; lia].
  rewrite ze_alu, ze_strideT, ze_lit. zfin. mlia.
Qed.
Lemma a_M : ltac2:(tb__ "0|0|
S0S1S4dS32Vam;A1S4cA3S2S8N20R2A2S8R2Z0A2A2S1S0S16VrhoF;S12S53S7cS13R3A1A3A2S6S5S5bVam;A1Z1000A2R3A2A3F_;F_;Fk;").
Proof using Em0 EmW HCS HF HMI HagF Hb16 Hb3 Hhdr Hsp.
  intros k Hk Hr. pose proof kd_cases as KC. rewrite Hk in KC. destruct KC as [[? _]|[[? _]|[_ [_ KF]]]]; try discriminate.
  apply soffF_ev; [reflexivity|reflexivity| |pose proof R_all; pose proof Hmaplen_small; lia].
  unfold AND155. rewrite ze_alu, ZE_and155, ze_lit by lia. zfin. pose proof Hmaplen_small. mlia.
Qed.

Lemma v_and157 : ltac2:(tb__ "0|0|
S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S7dA3Vidx;A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr. unfold AND157. rewrite ze_alu, ze_var, ze_lit. zfin. rewrite Zv157. rewrite land_31'. mlia. Qed.
Lemma v_or160 : ltac2:(tb__ "0|1|
S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S12S57S13Za0M0A1S7dA3A3S6G0Vidx;A2A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp. rewrite ze_alu, v_and157, ze_lit. zfin. rewrite (Z.mod_small idx) by lia. apply lor_low5; mlia. Qed.
Lemma v_orX : ltac2:(tb__ "0|2|
S19S0S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9M0S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9M1R2A3R1A3S2S8Z0R2A2ScR2SbZ2Z14A2A2A2S1S0S2fG0G1S12S57S12S58R4S13Z5A1A3S7dA3A3S6S5R3Z20A2Vidx;A2A3F_;F_;Fx;Fe;").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  intros e x He Hx. rewrite ze_alu, (ze_alu ALU_SLL), He, v_and157, ze_lit. zfin.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. rewrite !Z.mod_small by lia. apply lor_low5; mlia.
Qed.
Lemma v_xT0 : ltac2:(tb__ "0|0|
S3S1S4dS32Vam;A1S4cA3A1S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S12S53S12S55S4fS14PcA1A3S13N4A1A3A3S7S7S5Z10S39Vam;A1A2Vn;A2Z4A2A3F_;").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr Hsp. intros Hk. rewrite !ze_alu, ze_strideT, ze_lit. change (SVar 12) with (v 12). rewrite ze12. zfin. pose proof (stv_T Hk). mlia. Qed.
Lemma v_xT1 : ltac2:(tb__ "0|1|
S3S1S4dS32Vam;A1S4cA3A1S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S12S53S12S55S12S55S4fS4eA3S14PcA1A3S13N4A1A3A3S7S7S7S5Z10M0S39Vam;A1A2S5G0S35Vs;Vn;Vam;Vb3;Vb16;A5A2A2Vn;A2Z4A2A3F_;").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr Hsp. intros Hk. rewrite !ze_alu, ze_strideT, ze_sll, ze_lit. change (SVar 12) with (v 12). rewrite ze12. zfin. pose proof (stv_T Hk). mlia. Qed.
Lemma v_xM0 : ltac2:(tb__ "0|0|
S1S4dS32Vam;A1S4cA3S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S12S53S12S55S7cS14PcA1A3S13N14A1A3A3S7S7S5S5bVam;A1Z1000A2Vn;A2Z14A2A3F_;").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr Hsp.
  intros Hk. pose proof kd_cases as KC. rewrite Hk in KC. destruct KC as [[? _]|[[? _]|[_ [_ KF]]]]; try discriminate.
  unfold AND155. rewrite ze_alu, (ze_alu ALU_SUB), ZE_and155, ze_lit by lia. change (SVar 12) with (v 12). rewrite ze12. zfin. pose proof (stv_VM1 Hk). pose proof Hmaplen_small. mlia.
Qed.
Lemma v_xM1 : ltac2:(tb__ "0|0|
S1S4dS32Vam;A1S4cA3S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S12S53S12S55S12S55S7cS4eA3S14PcA1A3S13N14A1A3A3S7S7S7S5S5bVam;A1Z1000A2S5Z10S35Vs;Vn;Vam;Vb3;Vb16;A5A2A2Vn;A2Z14A2A3F_;").
Proof using HCS HF HMI HP12 Hb16 Hb3 Hhdr Hsp.
  intros Hk. pose proof kd_cases as KC. rewrite Hk in KC. destruct KC as [[? _]|[[? _]|[_ [_ KF]]]]; try discriminate.
  unfold AND155. rewrite ze_alu, (ze_alu ALU_SUB), (ze_alu ALU_SUB), ZE_and155, ze_sll, ze_lit by lia. change (SVar 12) with (v 12). rewrite ze12. zfin. pose proof (stv_VM1 Hk). pose proof Hmaplen_small. mlia.
Qed.
Lemma v_h16 : ltac2:(tb__ "0|0|
S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S12S54S17S56S50S32Vam;A1A1S14P9dA1A3S13Z4A1A3A3S9S5S36Vam;A1Vidx;A2Z10A2A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr. rewrite ze_alu, ze_mul, ze_stride, ze_lit. change (SVar 157) with (v 157). rewrite ze157. zfin. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. mlia. Qed.
Lemma v_f16 : ltac2:(tb__ "0|0|
S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S12S54S12S53S4eS17S56S50S32Vam;A1A1S14P9dA1A3A3S13Z4A1A3A3S6S35Vs;Vn;Vam;Vb3;Vb16;A5S9S5S36Vam;A1Vidx;A2Z10A2A2A3").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp. rewrite !ze_alu, ze_mul, ze_sll, ze_stride, ze_lit. change (SVar 157) with (v 157). rewrite ze157. zfin. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. mlia. Qed.
Lemma v_158 : ltac2:(tb__ "0|0|
S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S14P9eA1A3S35Vs;Vn;Vam;Vb3;Vb16;A5A3"). Proof using HCS HF HMI Hb16 Hb3 Hhdr. exact ze158. Qed.
Lemma v_litv : ltac2:(tb__ "0|0|
S0S2S8Z0R1A2ScR1SbZ2Z40A2A2A2S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S13R2A1A3R2A3F_;Fz;"). Proof using . intros z Hz. rewrite ze_lit. apply Z.mod_small. exact Hz. Qed.

Lemma E_stride_T : ltac2:(tb__ "0|1|
S3S1S4dS32Vam;A1M0S4cA3A1S1S19S50G0A1S4fA3F_;").
Proof using HF Hb16 Hb3 Hsp. intros Hk. destruct kd_cases as [[-> _]|[[-> _]|[E _]]]; [reflexivity|reflexivity|exfalso; exact (Hk E)]. Qed.
Lemma E_stride_M : ltac2:(tb__ "0|1|
S1S4dS32Vam;A1M0S4cA3S1S19S50G0A1S51A3F_;").
Proof using . intros ->. reflexivity. Qed.
Lemma v_h16T : ltac2:(tb__ "0|0|
S3S1S4dS32Vam;A1S4cA3A1S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S12S54S17S56S4fS14P9dA1A3S13Z4A1A3A3S9S5S36Vam;A1Vidx;A2Z10A2A3F_;").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp. intros Hk. rewrite <- (E_stride_T Hk). apply v_h16. Qed.
Lemma v_h16M : ltac2:(tb__ "0|0|
S1S4dS32Vam;A1S4cA3S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S12S54S17S56S51S14P9dA1A3S13Z4A1A3A3S9S5S36Vam;A1Vidx;A2Z10A2A3F_;").
Proof using HCS HF HMI Hb16 Hb3 Hhdr. intros Hk. rewrite <- (E_stride_M Hk). apply v_h16. Qed.
Lemma v_f16T : ltac2:(tb__ "0|0|
S3S1S4dS32Vam;A1S4cA3A1S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S12S54S12S53S4eS17S56S4fS14P9dA1A3A3S13Z4A1A3A3S6S35Vs;Vn;Vam;Vb3;Vb16;A5S9S5S36Vam;A1Vidx;A2Z10A2A2A3F_;").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp. intros Hk. rewrite <- (E_stride_T Hk). apply v_f16. Qed.
Lemma v_f16M : ltac2:(tb__ "0|0|
S1S4dS32Vam;A1S4cA3S1S0S2fS34Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S33Vs;VL;Vn;Vg;Vam;Vidx;Vrho;Vb3;Vb16;A9S12S54S12S53S4eS17S56S51S14P9dA1A3A3S13Z4A1A3A3S6S35Vs;Vn;Vam;Vb3;Vb16;A5S9S5S36Vam;A1Vidx;A2Z10A2A2A3F_;").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp. intros Hk. rewrite <- (E_stride_M Hk). apply v_f16. Qed.

Ltac rwu lem tac :=
  let T := fresh "RW" in
  pose proof lem as T; cbv beta iota delta [AND157 AND155 E_sll E_strideT E_strideM E_S E_stride v] in T;
  rewrite T by tac; clear T.
Ltac triv := first [assumption | clear; lia].
Ltac addr_soff :=
  first [ rewrite soffF_lit by (clear; lia)
        | rwu a_12 triv
        | rwu a_12sll triv
        | rwu a_sll side
        | rwu a_T triv
        | rwu a_M triv ].
Ltac val_rw :=
  first [ rewrite v_litv by (clear; lia)
        | rwu v_158 triv
        | rwu v_and157 triv
        | rwu v_or160 triv
        | match goal with K : kd <> VM1 |- _ => first [ rwu (v_orX _ _ (v_xT0 K)) side | rwu (v_orX _ _ (v_xT1 K)) side | rwu (v_xT0 K) triv | rwu (v_xT1 K) triv ] end
        | match goal with K : kd = VM1 |- _ => first [ rwu (v_orX _ _ (v_xM0 K)) side | rwu (v_orX _ _ (v_xM1 K)) side | rwu (v_xM0 K) triv | rwu (v_xM1 K) triv ] end
        | match goal with K : kd <> VM1 |- _ => first [ rwu (v_f16T K) triv | rwu (v_h16T K) triv ] end
        | match goal with K : kd = VM1 |- _ => first [ rwu (v_f16M K) triv | rwu (v_h16M K) triv ] end ].

Ltac v3slot i :=
  cbn [mc_w mc_loc mc_val sval_num]; model_addr;
  lazymatch goal with
  | SCE : slot_cells kd vo vr = slot_cells ?Kd _ _, Ko : vo = ?O, Kr : vr = ?R |- forall j, (j < ?w)%nat -> _ /\ _ = Some (Z_to_bv 8 (le_byte ?V _ _)) =>
    let cc := eval vm_compute in (nth i (slot_cells Kd O R) (mkCell (SLit 0) 1 (SLit 0))) in
    apply (V3_cell oSlot cc _ V w);
    [ left; reflexivity
    | unfold U.Mal_mslow__G3.Mal_mslow_G.oSlot; cbn [ob_cells]; rewrite SCE, Ko, Kr; apply (nth_error_In _ i); vm_compute; reflexivity
    | reflexivity
    | clear; cbn; lia
    | unfold U.Mal_mslow__G3.Mal_mslow_G.oSlot; cbn [ob_base c_off]; rewrite baseF_p0; addr_soff; lean; lia
    | reflexivity | reflexivity
    | cbn [c_val]; let m := eval vm_compute in (2 ^ (8 * Z.of_nat w)) in change (2 ^ (8 * Z.of_nat w)) with m;
      val_rw; lean; mlia ]
  end.

Lemma rsv_def : ltac2:(tb__ "0|0|
S1S0S6dVs;Vn;Vam;Vb3;Vb16;A5S7S7S7S36Vam;A1S5Z10S35Vs;Vn;Vam;Vb3;Vb16;A5A2A2Vn;A2Z4A2A3"). Proof using . reflexivity. Qed.

Lemma slot_cells_T : ltac2:(tb__ "0|3|
S3S1S4dS32Vam;A1M0S4cA3A1S1S25S15A1S85G0S6eVs;Vn;Vam;Vb3;Vb16;A5M1S6fVs;Vn;Vam;Vb3;Vb16;A5M2A3S85S52G1G2A3A3F_;").
Proof using HCS HF HMI Hb16 Hb3 Hhdr Hsp.
  intros Hk. destruct kd_cases as [[-> _]|[[-> _]|[E _]]]; [reflexivity| |exfalso; exact (Hk E)].
  destruct vo_cases as [[-> _]|[-> _]]; destruct vr_cases as [[-> _]|[[-> _]|[[-> _]|[-> _]]]]; reflexivity.
Qed.

Ltac decide_cond b :=
  first [ replace b with true by (symmetry; lean; first [apply (proj2 (Z.eqb_eq _ _)) | apply (proj2 (Z.ltb_lt _ _)) | apply (proj2 (Z.leb_le _ _))]; lia)
        | replace b with false by (symmetry; lean; first [apply (proj2 (Z.eqb_neq _ _)) | apply (proj2 (Z.ltb_ge _ _)) | apply (proj2 (Z.leb_gt _ _))]; lia) ].

Theorem V3 : ltac2:(tb__ "0|4|
S3cS7eS3cR1S73Vs;Vn;Vam;Vidx;S37Vs;Vb3;Vb16;A3A5A3S26S70R1S43R3A1A2S2S1S22S66S4bS84Vs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8M0S68S6S42VL;S47R4A1A2SaR2A1A2A1M1A3S2aA3S1S27S62Q8M2A1M3A1S65S4bG0G1A3S28G3S63G2S40S49VL;S48R4A1A2S43R4A1R2A3A2A2A3A2F_;Fj;F_;Fc;").
Proof using Em0 EmW HCS HF HMI HP12 HagF Hb16 Hb3 Hdepth Hhdr HsmF Hsp.
  intros c Hc. rewrite newcells_eq in Hc. revert Hc.
  pose proof R_all as R. pose proof Hoff as HO. assert (PI : True) by exact I. pose proof rsv_def as RD.
  pose proof stv_VM1 as SM. pose proof stv_T as ST. pose proof slot_cells_T as SCT.

  assert (KD : exists Kd, slot_cells kd vo vr = slot_cells Kd vo vr /\
          ((Kd = VL /\ kd <> VM1 /\ stv = 16 * sz /\ 0 <= am_maplen am) \/ (Kd = VM1 /\ kd = VM1 /\ stv = am_maplen am * 4096 - 16 /\ 0 < am_maplen am))).
  { destruct kd_cases as [[Kk KF]|[[Kk [KF ?]]|[Kk [_ KF]]]].
    - exists VL. assert (NK : kd <> VM1) by (rewrite Kk; discriminate). split; [apply SCT; exact NK|]. left. pose proof Hmaplen. split; [reflexivity|]. split; [exact NK|]. split; [apply ST; exact NK| lia].
    - exists VL. assert (NK : kd <> VM1) by (rewrite Kk; discriminate). split; [apply SCT; exact NK|]. left. split; [reflexivity|]. split; [exact NK|]. split; [apply ST; exact NK| lia].
    - exists VM1. split; [rewrite Kk; reflexivity|]. right. split; [reflexivity|]. split; [exact Kk|]. split; [apply SM; exact Kk| exact KF]. }
  clear SM ST SCT.
  destruct KD as (Kd & SCE & [[EKd [Kk [STV KF]]]|[EKd [Kk [STV KF]]]]); subst Kd;
  destruct vo_cases as [[Ko OF]|[Ko OF]];
  destruct vr_cases as [[Kr RF']|[[Kr RF']|[[Kr RF']|[Kr RF']]]];
  (assert (AR : arith_facts (_ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _)) by exact (conj R (conj HO (conj OF (conj RF' (conj STV (conj PI (conj KF RD))))))));
  decide_cond (off =? 0); decide_cond (0 <? rsv); decide_cond (5 <=? rsv); decide_cond (5 <? rsv);
  cbn [app]; intros Hc.
  -
      destruct Hc as [<-|[<-|[]]];
        [ v3slot 0%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[]]]];
        [ v3slot 0%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[]]]]];
        [ v3slot 0%nat | v3slot 3%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        [ v3slot 0%nat | v3slot 4%nat | v3slot 3%nat | v3slot 1%nat | v3slot 2%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        [ v3slot 4%nat | v3slot 3%nat | v3slot 2%nat | v3slot 0%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        [ v3slot 5%nat | v3slot 4%nat | v3slot 3%nat | v3slot 0%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
        [ v3slot 6%nat | v3slot 5%nat | v3slot 4%nat | v3slot 0%nat | v3slot 3%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
        [ v3slot 7%nat | v3slot 6%nat | v3slot 5%nat | v3slot 0%nat | v3slot 4%nat | v3slot 3%nat | v3slot 1%nat | v3slot 2%nat ].
  -
      destruct Hc as [<-|[<-|[]]];
        [ v3slot 0%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[]]]];
        [ v3slot 0%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[]]]]];
        [ v3slot 0%nat | v3slot 3%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        [ v3slot 0%nat | v3slot 4%nat | v3slot 3%nat | v3slot 1%nat | v3slot 2%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        [ v3slot 4%nat | v3slot 3%nat | v3slot 2%nat | v3slot 0%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        [ v3slot 5%nat | v3slot 4%nat | v3slot 3%nat | v3slot 0%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
        [ v3slot 6%nat | v3slot 5%nat | v3slot 4%nat | v3slot 0%nat | v3slot 3%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
        [ v3slot 7%nat | v3slot 6%nat | v3slot 5%nat | v3slot 0%nat | v3slot 4%nat | v3slot 3%nat | v3slot 1%nat | v3slot 2%nat ].
Qed.

End ReabH.
