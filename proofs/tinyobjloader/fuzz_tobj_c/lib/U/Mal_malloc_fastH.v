(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "add"; "sub"; "le"; "div"; "pow"; "modulo"; "lt"; "of_nat"; "leb"; "eqb"; "ltb"; "opp"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SLit"; "SVar"; "cell"; "soff"; "SMd"; "rw"; "sv"; "c_val"; "smatch"; "sobj"; "c_off"; "c_width"; "eval"; "ob_base"; "ob_cells"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "option"; "pair"; "list"; "nat"; "true"; "Some"; "app"; "prod"; "None"; "length"; "nil"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "toS"; "zsupported"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI"; "zl1"; "zr1"; "kd"; "idx"; "off"; "stv"; "zz"; "zSt"; "sz"; "avail"; "zE"; "zG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LMem"; "MCell"; "VZ"; "le_byte"; "frame_ptr"; "loc_addr"; "mc_w"; "META_avail"; "hdr_byte3"; "hdr_off16"; "mc_loc"; "mc_val"; "sval_num"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "VM1"; "vkind"; "E_sll"; "E_strideT"; "E_stride"; "E_strideM"; "C0"; "MR_P"; "VL"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "M_MUL"; "ALU_OR"; "ALU_SLL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "padd"; "am_maplen"; "slot_start"; "nth_slot"; "sptr"; "ss_hdr"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFastPost"; "mf_idx"; "mf_frame"; "f_newcells"; "mf_ptr"; "loop_case"; "mf_hdr"; "mf_reserved"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "wz"; "C_U"; "byteview_of"; "malloc_stack"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD"; "rsv"; "vo"; "vr"; "@Corelib.Init.Peano"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc_fastH.ReabH"; "AND155"; "AND157"; "@Stdlib.Lists.List"; "In"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sv_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "slot_end"; "reserved_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastG"; "m'"; "slot_cells"; "AVAIL_T"; "oMeta"; "oSlot"; "@Corelib.Lists.ListDef"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "Pre_malloc"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MInv"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs.RP"; "LF"].
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
  FreeQuickModel Zones ImageUpd FpLaws MallocFastPost.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fast_enum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Section ReabH.

Variables (s : astate) (L : layout) (n : Z) (g : sptr) (am : ameta).
Variable rho : valuation.
Variables (b3 b16 : Z).
Hypothesis HW : WF s.
Hypothesis HC : ltac2:(tb__ "0|0|
S69Vs;Vn;Vg;Vam;A4").
Hypothesis HLok : layout_ok L s.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S4S64Q40S18Vrho;PcA2A2Vn;A3").
Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hb16 : 0 <= b16 < 65536.
Hypothesis Hhdr : ltac2:(tb__ "0|1|
S4S4S0S24S2bS4S4A2M0A1S61S5fVam;S65Vam;A1A2A1S29G0S25S4S4R2R1A4A2A3S1S0S4Vb3;R3A3S0S4Vb16;R2A3A2F_;Fh16;Fh3;").
Local Abbreviation idx := (@U.Mal_malloc__G2.Mal_malloc_fastI.idx am).
Local Abbreviation stv := (@U.Mal_malloc__G2.Mal_malloc_fastI.stv am).
Local Abbreviation sz := (@U.Mal_malloc__G2.Mal_malloc_fastI.sz am).
Local Abbreviation zG := (@U.Mal_malloc__G2.Mal_malloc_fastI.zG L g).
Local Abbreviation zSt := (@U.Mal_malloc__G2.Mal_malloc_fastI.zSt L am).
Local Abbreviation zE := (@U.Mal_malloc__G2.Mal_malloc_fastI.zE L am).
Local Abbreviation avail := (@U.Mal_malloc__G2.Mal_malloc_fastI.avail am).
Local Notation "§1§ h__" := (h__ s n am b3 b16) (at level 10, h__ global).
Local Abbreviation off := (§1§ U.Mal_malloc__G2.Mal_malloc_fastI.off).
Local Abbreviation zz := (@U.Mal_malloc__G2.Mal_malloc_fastI.zz s b3 b16).
Local Abbreviation kd := (@U.Mal_malloc__G2.Mal_malloc_fastI.kd am).
Local Notation "§2§ h__" := (h__ s n g am HW HC) (at level 10, h__ global).
Local Abbreviation Hmaplen := (§2§ U.Mal_malloc__G2.Mal_malloc_fastI.Hmaplen).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S8dS70S8eVs;VL;A2Vrd0;Vwok0;Vvm;A5").
Local Abbreviation Hoff := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hoff s n g am b3 b16 HW HC Hb3 Hb16).
Local Abbreviation off_model := (@U.Mal_malloc__G2.Mal_malloc_fastI.off_model s n am b3 b16 Hb3 Hb16 Hhdr).
Local Notation "§3§ h__" := (h__ s L n g am rho b3 b16) (at level 10, h__ global).
Local Abbreviation rho1 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.rho1).
Local Abbreviation zr1 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.zr1).
Local Abbreviation zl1 := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.zl1).
Local Abbreviation Hmaplen_small := (@U.Mal_malloc__G2.Mal_malloc_fastI.Hmaplen_small s L n g am b3 b16 HW HC Hb3 Hb16 rd0 wok0 vm HMI).
Local Notation "§4§ h__" := (h__ s L n g am b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation R_all := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.R_all).
Local Abbreviation ze_var := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_var).
Local Abbreviation ze_lit := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_lit).
Local Abbreviation ze_alu := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_alu).
Local Abbreviation ze_aluw := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_aluw).
Local Abbreviation ze_mul := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_mul).
Local Abbreviation ze_ext := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_ext).
Local Abbreviation ze_lbytes := (§3§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_lbytes).
Local Notation "§5§ h__" := (h__ s L n g am rho b3 b16 HW HC HP12 Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze12 := (§5§ U.Mal_malloc__G2.Mal_malloc_fastI.ze12).
Local Notation "§6§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation ze157 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze157).
Local Abbreviation ze158 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze158).
Local Abbreviation ze_strideT := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_strideT).
Local Abbreviation ze_stride := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_stride).
Local Abbreviation first_eq := (§2§ U.Mal_malloc__G2.Mal_malloc_fastI.first_eq).
Local Abbreviation pow_idx_range := (§4§ U.Mal_malloc__G2.Mal_malloc_fastI.pow_idx_range).
Local Abbreviation ze_sxavail := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_sxavail).
Local Abbreviation ze_lowbit := (§6§ U.Mal_malloc__G2.Mal_malloc_fastI.ze_lowbit).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S8Z1000S64Q40S18Vrho;PaA2A2M0A2S0S4SbG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S8S30Z40S64Q40S18Vrho;PfA2A2A2M0S11S72A1A2S8S11SaZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S8S73VL;A1S6S64Q40M0S18Vrho;PaA2A2S30Z40S64G0S18Vrho;PfA2A2A2A2A2").
Variable m0 : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S62Q40A1S24S62Q8A1A1F_;Vrd0;S6cS4cVm0;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S62Q40A1S22F_;Vwok0;S6dS4cVm0;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm0_sct : ltac2:(tb__ "0|1|
S4S1S8Z0R1A2ScR1Z60A2A2S0S24S62Q8A1M0A1Vm0;S63Q40S6Z108ecR2A2A2A1S2cG0A1A3F_;Fkk;").
Hypothesis Hm0_ctz : ltac2:(tb__ "0|1|
S4S1S8Z0R1A2ScR1Z20A2A2S0S24S62Q8A1M0A1Vm0;S63Q40S6Z108ccR2A2A2A1S2cG0A1A3F_;Fkk;").
Hypothesis Hm3 : ltac2:(tb__ "0|2|
S0S24S62Q8M0A1M1A1S6cS4cVm0;S63Q40S7S39VL;Vam;A2Z3A2A2A3S29G1S63G0Vb3;A2A2A3").
Hypothesis Hm16 : ltac2:(tb__ "0|3|
S27S77R1U2M0A2S0S24S62Q8M1A1M2A1S6cS4cVm0;S63Q40S6S7S39VL;Vam;A2Z2A2SdR2A1A2A2A3S29G2S63G1S42Vb16;G0R2A3A2A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S71S6cS4cVm0;A2S6dS4cVm0;A2A2").
Local Abbreviation soff_of_ev := (@U.Mal_malloc__G2.Mal_malloc_fastI.soff_of_ev s L n g am rho b3 b16 Hb3 Hb16 m0).
Local Abbreviation Zones := (@U.Mal_malloc__G2.Mal_malloc_fastI.Zones s L n g am rho b3 b16 HW HC HLok Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp Hsp_high).
Variable ok : world -> Prop.
Variable K : ltac2:(tb__ "0|0|
S26S79A1S7aOF_;F_;").
Hypothesis HK : ltac2:(tb__ "0|0|
S8aS4cVok;VK;A3").
Variable mW : word -> option byte.
Let rhoW : valuation := rho1 mW.
Local Abbreviation Zv12 := (§5§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv12).
Local Abbreviation Zv142 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv142).
Local Abbreviation Zv143 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv143).
Local Abbreviation Zv149 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv149).
Local Abbreviation Zv150 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv150).
Local Abbreviation Zv151 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv151).
Local Abbreviation Zv152 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv152).
Local Abbreviation Zv153 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv153).
Local Abbreviation Zv154 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv154).
Local Abbreviation Zv155 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv155).
Local Abbreviation Zv156 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv156).
Local Abbreviation Zv157 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv157).
Local Abbreviation Zv158 := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.Zv158).
Local Abbreviation ZE_S := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_S).
Local Abbreviation ZE_strideT := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_strideT).
Local Notation "§7§ h__" := (h__ s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp) (at level 10, h__ global).
Local Abbreviation ZE_and155 := (§7§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_and155).
Local Abbreviation ZE_strideM := (§6§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_strideM).
Local Abbreviation ZE_sll := (§7§ U.Mal_malloc__G2.Mal_malloc_fastC.ZE_sll).
Local Notation "§8§ h__" := (h__ rho b3 b16 Hb3 Hb16) (at level 10, h__ global).
Local Abbreviation land_255 := (§8§ U.Mal_malloc__G2.Mal_malloc_fastC.land_255).
Local Abbreviation land_31' := (§8§ U.Mal_malloc__G2.Mal_malloc_fastC.land_31').
Local Abbreviation rsv := (§1§ U.Mal_malloc__G3.Mal_malloc_fastD.rsv).
Local Abbreviation vo := (§1§ U.Mal_malloc__G3.Mal_malloc_fastD.vo).
Local Abbreviation vr := (§1§ U.Mal_malloc__G3.Mal_malloc_fastD.vr).
Local Abbreviation ze_sll := (§7§ U.Mal_malloc__G3.Mal_malloc_fastD.ze_sll).
Local Notation "§9§ h__" := (h__ s n g am rho b3 b16 HW HC Hb3 Hb16 Hsp) (at level 10, h__ global).
Local Abbreviation kd_cases := (§9§ U.Mal_malloc__G3.Mal_malloc_fastD.kd_cases).
Local Abbreviation vo_cases := (@U.Mal_malloc__G3.Mal_malloc_fastD.vo_cases s n g am rho b3 b16 HW HC Hb3 Hb16).
Local Abbreviation vr_cases := (§7§ U.Mal_malloc__G3.Mal_malloc_fastD.vr_cases).
Local Abbreviation stv_VM1 := (§9§ U.Mal_malloc__G3.Mal_malloc_fastD.stv_VM1).
Local Abbreviation stv_T := (§9§ U.Mal_malloc__G3.Mal_malloc_fastD.stv_T).
Variables (tr : list event) (md : Model) (ms' : machine_state) (rhoF : valuation).
Hypothesis EmW : mW = rm rho.
Hypothesis Em0 : m0 = rm rho.
Hypothesis Evm : vm = m_vmmaps md.
Hypothesis Hsm : ltac2:(tb__ "0|0|
S1bS4cVrho;S8cS8bA1S25S26S79A1S7bVtr;S7cVms;Vmd;A2A4A4").
Hypothesis Hsm0 : ltac2:(tb__ "0|0|
S1bS4cVrhoW;S53S54S34Vam;A1A2S25S26S79A1S7bVtr;S7cVms;Vmd;A2A4A4").
Hypothesis HagF : agrees rhoW rhoF.
Hypothesis HsmF : ltac2:(tb__ "0|0|
S1bS4cVrhoF;S8fS34Vam;A1S75Vs;Vn;Vam;Vb3;Vb16;A5S76Vs;Vn;Vam;Vb3;Vb16;A5A3S25S26S79A1S7bVtr;S7cVms';Vmd;A2A4A4").
Local Abbreviation oMeta := (@U.Mal_malloc__G3.Mal_malloc_fastG.oMeta).
Local Abbreviation oSlot := (§1§ U.Mal_malloc__G3.Mal_malloc_fastG.oSlot).
Local Abbreviation NL := (§1§ U.Mal_malloc__G3.Mal_malloc_fastG.NL).
Local Notation "§10§ h__" := (h__ s n am rho b3 b16 ms' rhoF) (at level 10, h__ global).
Local Abbreviation m' := (§10§ U.Mal_malloc__G3.Mal_malloc_fastG.m').
Local Notation "§11§ h__" := (h__ s L n g am rho b3 b16 mW rhoF HagF) (at level 10, h__ global).
Local Abbreviation evF := (§11§ U.Mal_malloc__G3.Mal_malloc_fastG.evF).
Local Abbreviation rhoW_m0 := (@U.Mal_malloc__G3.Mal_malloc_fastG.rhoW_m0 s L n g am rho b3 b16 m0 mW EmW Em0).
Local Abbreviation HromF := (@U.Mal_malloc__G3.Mal_malloc_fastG.HromF s n am b3 b16 tr md ms' rhoF HsmF).
Local Abbreviation m'_in := (§10§ U.Mal_malloc__G3.Mal_malloc_fastG.m'_in).
Local Notation "§12§ h__" := (h__ s n am rho b3 b16 Hb3 Hb16 Hsp Hdepth tr md ms' rhoF HsmF) (at level 10, h__ global).
Local Abbreviation HoSlotF := (§12§ U.Mal_malloc__G3.Mal_malloc_fastG.HoSlotF).
Local Abbreviation HoMetaF := (§12§ U.Mal_malloc__G3.Mal_malloc_fastG.HoMetaF).
Local Abbreviation soffFW := (§11§ U.Mal_malloc__G3.Mal_malloc_fastG.soffFW).
Local Abbreviation baseF_151 := (@U.Mal_malloc__G3.Mal_malloc_fastG.baseF_151 s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI mW rhoF HagF).
Local Abbreviation baseF_p0 := (@U.Mal_malloc__G3.Mal_malloc_fastG.baseF_p0 s L n g am rho b3 b16 HW HC Hb3 Hb16 Hhdr rd0 wok0 vm HMI Hsp mW rhoF HagF).
Local Abbreviation soffF_lit := (@U.Mal_malloc__G3.Mal_malloc_fastG.soffF_lit rho b3 b16 Hb3 Hb16 rhoF).

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
  rewrite ?Zv12, ?Zv142, ?Zv143, ?Zv149, ?Zv150, ?Zv151, ?Zv152, ?Zv153, ?Zv154, ?Zv155, ?Zv156, ?Zv157, ?Zv158;
  flat_mods; zlits;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by (clear; lia);
  rewrite ?land_255, ?land_31'.

Lemma loc_padd : ltac2:(tb__ "0|0|
S60S4S0S4S44VL;S3fS5cR2R1A2A1A2S6S6eVL;R2A2R1A2A3Fd;Fp;").
Proof using Hb16 Hb3 rho. intros [r o] d. unfold addr_of, loc_addr, padd. lia. Qed.
Lemma A_g : ltac2:(tb__ "0|0|
S0S4S6eVL;Vg;A2S3dVL;Vg;A2A3"). Proof using . reflexivity. Qed.
Lemma A_st : ltac2:(tb__ "0|0|
S0S4S6eVL;S5eVam;S65Vam;A1A2A2S39VL;Vam;A2A3"). Proof using . reflexivity. Qed.
Lemma A_e : ltac2:(tb__ "0|0|
S0S4S6eVL;S81Vam;S65Vam;A1A2A2S3cVL;Vam;A2A3"). Proof using . reflexivity. Qed.
Lemma A_p : ltac2:(tb__ "0|0|
S0S4S6eVL;S68Vs;Vn;Vam;S38Vs;Vb3;Vb16;A3A4A2S6S39VL;Vam;A2S5Z10S36Vs;Vn;Vam;Vb3;Vb16;A5A2A2A3").
Proof using Hb16 Hb3 Hhdr rho. unfold mf_ptr. rewrite <- (loc_padd (slot_start am (mf_idx am))). unfold addr_of. rewrite <- off_model. unfold UNIT. reflexivity. Qed.
Lemma A_fp : ltac2:(tb__ "0|0|
S0S4S6eVL;S43Vam;S65Vam;A1S66Vs;Vn;Vam;S38Vs;Vb3;Vb16;A3A4A3A2S6S39VL;Vam;A2S5Z10S36Vs;Vn;Vam;Vb3;Vb16;A5A2A2A3").
Proof using Hb16 Hb3 Hhdr rho. unfold frame_ptr, mf_frame. cbn [fr_off]. rewrite <- (loc_padd (slot_start am (mf_idx am))). unfold addr_of. rewrite <- off_model. unfold UNIT. reflexivity. Qed.
Lemma rsv_eq1 : ltac2:(tb__ "0|0|
S0S4S6bVs;Vn;Vam;S38Vs;Vb3;Vb16;A3A4S74Vs;Vn;Vam;Vb3;Vb16;A5A3").
Proof using Hb16 Hb3 Hhdr rho. unfold mf_reserved, U.Mal_malloc__G3.Mal_malloc_fastD.rsv. rewrite <- off_model. change (mf_stride am) with stv. unfold IB, UNIT. lia. Qed.
Lemma rsv_eq2 : ltac2:(tb__ "0|0|
S0S4S82Vam;S66Vs;Vn;Vam;S38Vs;Vb3;Vb16;A3A4A2S74Vs;Vn;Vam;Vb3;Vb16;A5A3").
Proof using Hb16 Hb3 Hhdr rho. unfold reserved_of, mf_frame, U.Mal_malloc__G3.Mal_malloc_fastD.rsv. cbn [fr_off fr_n]. rewrite <- off_model. change (stride_of am) with stv. unfold IB, UNIT. lia. Qed.
Lemma hdr3_eq : ltac2:(tb__ "0|2|
S0S4S47Vam;S65Vam;A1S66Vs;Vn;Vam;S38Vs;Vb3;Vb16;A3A4A3S6S35Vam;A1S5Z20S22S4L_;SeZ5M0S74Vs;Vn;Vam;Vb3;Vb16;A5M1A2G0G1X22x2A2A2A3").
Proof using Hb16 Hb3 Hhdr rho.
  unfold hdr_byte3, rsv_code, mf_frame. cbn [fr_kind fr_off fr_n]. rewrite <- off_model.
  change (stride_of am) with stv. change (mf_idx am) with idx. unfold U.Mal_malloc__G3.Mal_malloc_fastD.rsv, IB, UNIT.
  replace (stv - 4 - 16 * off - n) with (stv - 16 * off - n - 4) by lia. reflexivity.
Qed.
Lemma hoff16_eq : ltac2:(tb__ "0|0|
S0S4S48Vam;S65Vam;A1S66Vs;Vn;Vam;S38Vs;Vb3;Vb16;A3A4A3S6S9S5S37Vam;A1S35Vam;A1A2Z10A2S36Vs;Vn;Vam;Vb3;Vb16;A5A2A3").
Proof using Hb16 Hb3 Hhdr. unfold hdr_off16, mf_frame. cbn [fr_off]. rewrite <- off_model. reflexivity. Qed.
Lemma mf_hdr_eq : ltac2:(tb__ "0|5|
S0S2bS4S4A2M0S6aVs;Vn;Vam;S38Vs;Vb3;Vb16;A3A4S22G0L_;SfS36Vs;Vn;Vam;Vb3;Vb16;A5M1Z0A2S25S4S4S6S35Vam;A1M2S5S22S4L_;SeZ5M3S74Vs;Vn;Vam;Vb3;Vb16;A5M4A2G3G4X22x2Z20A2A2S9S5S37Vam;A1G2A2Z10A2A4S25S4S4Ze0G1A4X22x2A3").
Proof using Hb16 Hb3 Hhdr rho. unfold mf_hdr, mf_rsv. rewrite rsv_eq1, <- off_model. reflexivity. Qed.

Lemma newcells_eq : ltac2:(tb__ "0|1a|
S0S26S3eA1M0S67Vs;Vn;Vg;Vam;S38Vs;Vb3;Vb16;A3M1A5S23S3eS40S3fS5cVg;S46A2A1U4M2S41S7S3bVam;A1SaZ2S35Vam;A1M3A2A2A1A3S2aS3eS2bS4S4A2M4G0Lp;S22G4L_;SfS36Vs;Vn;Vam;Vb3;Vb16;A5M5Z0M6A2M7S25S4S4S6G3S5S22S4L_;SeZ5M8S74Vs;Vn;Vam;Vb3;Vb16;A5M9A2MaG8G9X22x2MbZ20McA2A2S9S5S37Vam;A1G3A2Z10A2MdA4S25S4S4Ze0G5A4X22x2S4S4S23S3eS40S3fS5cS5eVam;S65Vam;A1MeA2MfN3M10A2A1U1M11S41R2A1A3S23S3eS40S3fS5cGfN2M12A2A1U2M13S41R1A1A3S2eS3eA1M14A3A3Lh16;Lh3;X2bx1S2aS3eS22G0L_;M15G7G14S23S3eS40S3fS5cS68Vs;Vn;Vam;G1A4M16N4M17A2A1G11S41G6A1M18A3S23S3eS40S3fS5cG16G10A2A1G11S41S6G3S5GcGbA2A2A1A3S23S3eS40S3fS5cG16G12A2A1G13S41S6GdG5A2A1A3G14A3A3A3X22x2S2aS3eG15S10G6G9A2S23S3eS40S3fS5cS43Vam;GeS66Vs;Vn;Vam;G1A4A3Vn;A2A1G11G18A3G14A3G14X22x2S2aS3eG15GaS23S3eS40S3fS5cS81Vam;GeA2M19G17A2A1G2S41G9A1A3G14A3G14X22x2G15S10G8G9A2S23S3eS40S3fS5cG19N5A2A1G11G18A3G14A3G14X22x2A3A3A3A3A3A3").
Proof using HC HW Hb16 Hb3 Hhdr rho.
  unfold f_newcells, f_Cavail, f_hdrcells, f_frcells, f_footcells, f_off, f_fr, f_idx.
  rewrite mf_hdr_eq, hdr3_eq, hoff16_eq. unfold frame_footer_cells. cbn [fr_kind mf_frame fr_n]. rewrite rsv_eq2.
  rewrite <- off_model. change (mf_first am) with (lowbit avail). rewrite first_eq. change (am_avail am) with avail. reflexivity.
Qed.

Lemma le_byte_congr : ltac2:(tb__ "0|1|
S4S4S27S27S0S4SbR4SaZ2S5Z8SdR2A1A2A2M0A2SbR3G0A2A3S0S4S42R5R3R2A3S42R4R3R2A3A3F_;Fk;Fw;Fy;Fx;").
Proof using . intros x y w k E. unfold le_byte. rewrite E. reflexivity. Qed.

Lemma In_nth_eq : ltac2:(tb__ "0|0|
S26S15A1S27S15S15S0S15S89S15R3R4R2A4R1A3S77R4S2dS15R5A2A2S7fS15R3R6A3F_;F_;Fc;Fd;Fi;Fl;").
Proof using . intros l i d c <- Hi. apply nth_In. exact Hi. Qed.

Lemma soffF_ev : ltac2:(tb__ "0|0|
S19S4S0S22S80S83R2A2S28A3S0S22S31R3A1S28A3S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8R4A3R3A3S1S8Z0R4A2ScR4SaZ2Z3fA2A2A2S0S4S16VrhoF;R6A2R5A3F_;F_;F_;F_;Fz;Fe;").
Proof using Em0 EmW HagF Hb16 Hb3. intros e z Hv Hs Hz Hr. rewrite (soffFW e Hv). rewrite rhoW_m0. exact (soff_of_ev e z Hs Hz Hr). Qed.

Lemma availT_val : ltac2:(tb__ "0|2|
S0S4SbS2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S86A3SaZ2M0Z20A2M1A2SbS7S3bVam;A1SaG0S35Vam;A1A2A2G1A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr.
  change AVAIL_T with (SAluW ALU_SUB (SExt true 32 (v 152)) E_lowbit).
  rewrite ze_aluw, ze_sxavail, ze_lowbit. cbn [zalu]. pose proof R_all as R. pose proof pow_idx_range as P.
  rewrite (sx32_mod32 avail) by lia. rewrite (sx32_mod32 (2 ^ idx)) by lia. rewrite sx32_mod32 by mlia. mlia.
Qed.

Lemma V3_cell : ltac2:(tb__ "0|5|
S1cS15S4S4S27S3S0S1cR5S88Vs;Vn;Vam;Vb3;Vb16;A5A3S0S1cR5S87A3A2S7fS15R5S21R6A1A3S0S4S1eR6A1SdR3A1A3S1S77U0R4A2S78R4U8A2A2S0S4S6S64Q40S1fVrhoF;S20R9A1A2A2S16VrhoF;S1dR8A1A2A2R7A3S0S22S80S83S1aR9A1A2S28A3S0S22S31S1aRaA1A1S28A3S0S4SbS2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S1aRbA1A3SaZ2S5Z8SdR8A1A2A2M0A2SbR9G0A2A3S27S77R1RaA2S1S0S22S6dS4cS84Vs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8M1S6fS6RdSdR2A1A2A1M2A3S28A3S0S24S62Q8M3A1M4A1S6cS4cG1G2A3S29G4S63G3S42RcRbR2A3A2A2A3A2F_;Fj;F_;F_;F_;F_;F_;F_;F_;F_;Fw;FV;FA;Fc;Fo;").
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
S4S8Z1S36Vs;Vn;Vam;Vb3;Vb16;A5M0A2S1ScN10R2A2S8R2Z0A2A2S0S4S16VrhoF;S12S56S4fS13R3A1A3A2S6S5Z10G0A2R3A2A3F_;F_;Fk;").
Proof using Em0 EmW HC HMI HW HagF Hb16 Hb3 Hhdr Hsp.
  intros k Ho Hk. apply soffF_ev; [reflexivity|reflexivity| |pose proof Hoff; lia].
  rewrite ze_alu, ze_sll, ze_lit. zfin. mlia.
Qed.
Lemma a_12 : ltac2:(tb__ "0|0|
S0S4S16VrhoF;S14PcA1A2Vn;A3").
Proof using Em0 EmW HC HMI HP12 HW HagF Hb16 Hb3 Hhdr Hsp. apply soffF_ev; [reflexivity|reflexivity| exact ze12 |pose proof R_all; lia]. Qed.
Lemma a_12sll : ltac2:(tb__ "0|0|
S0S4S16VrhoF;S12S56S14PcA1S4fA3A2S6Vn;S5Z10S36Vs;Vn;Vam;Vb3;Vb16;A5A2A2A3").
Proof using Em0 EmW HC HMI HP12 HW HagF Hb16 Hb3 Hhdr Hsp.
  apply soffF_ev; [reflexivity|reflexivity| |pose proof R_all; pose proof Hoff; lia].
  rewrite ze_alu, ze_sll. change (SVar 12) with (v 12). rewrite ze12. zfin. mlia.
Qed.
Lemma a_T : ltac2:(tb__ "0|0|
S4S2S0S4eS34Vam;A1S4dA3A1S1S8N10R2A2S8R2Z0A2A2S0S4S16VrhoF;S12S56S50S13R3A1A3A2S6S5Z10S3aVam;A1A2R3A2A3F_;F_;Fk;").
Proof using Em0 EmW HC HMI HW HagF Hb16 Hb3 Hhdr Hsp.
  intros k Hk Hr. apply soffF_ev; [reflexivity|reflexivity| |pose proof R_all; lia].
  rewrite ze_alu, ze_strideT, ze_lit. zfin. mlia.
Qed.
Lemma a_M : ltac2:(tb__ "0|0|
S4S0S4eS34Vam;A1S4dA3S1S8N20R2A2S8R2Z0A2A2S0S4S16VrhoF;S12S56S7dS13R3A1A3A2S6S5S5dVam;A1Z1000A2R3A2A3F_;F_;Fk;").
Proof using Em0 EmW HC HMI HW HagF Hb16 Hb3 Hhdr Hsp.
  intros k Hk Hr. pose proof kd_cases as KC. rewrite Hk in KC. destruct KC as [[? _]|[[? _]|[_ [_ KF]]]]; try discriminate.
  apply soffF_ev; [reflexivity|reflexivity| |pose proof R_all; pose proof Hmaplen_small; lia].
  unfold AND155. rewrite ze_alu, ZE_and155, ze_lit by lia. zfin. pose proof Hmaplen_small. mlia.
Qed.

Lemma v_and157 : ltac2:(tb__ "0|0|
S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S7eA3S35Vam;A1A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. unfold AND157. rewrite ze_alu, ze_var, ze_lit. zfin. rewrite Zv157. rewrite land_31'. mlia. Qed.
Lemma v_or160 : ltac2:(tb__ "0|1|
S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S12S5aS13Za0M0A1S7eA3A3S6G0S35Vam;A1A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. rewrite ze_alu, v_and157, ze_lit. zfin. rewrite (Z.mod_small idx) by lia. apply lor_low5; mlia. Qed.
Lemma v_orX : ltac2:(tb__ "0|2|
S19S4S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8M0S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8M1R2A3R1A3S1S8Z0R2A2ScR2SaZ2Z14A2A2A2S0S4S2fG0G1S12S5aS12S5bR4S13Z5A1A3S7eA3A3S6S5R3Z20A2S35Vam;A1A2A3F_;F_;Fx;Fe;").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  intros e x He Hx. rewrite ze_alu, (ze_alu ALU_SLL), He, v_and157, ze_lit. zfin.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. rewrite !Z.mod_small by lia. apply lor_low5; mlia.
Qed.
Lemma v_xT0 : ltac2:(tb__ "0|0|
S2S0S4eS34Vam;A1S4dA3A1S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S12S56S12S58S50S14PcA1A3S13N4A1A3A3S7S7S5Z10S3aVam;A1A2Vn;A2Z4A2A3F_;").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr Hsp. intros Hk. rewrite !ze_alu, ze_strideT, ze_lit. change (SVar 12) with (v 12). rewrite ze12. zfin. pose proof (stv_T Hk). mlia. Qed.
Lemma v_xT1 : ltac2:(tb__ "0|1|
S2S0S4eS34Vam;A1S4dA3A1S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S12S56S12S58S12S58S50S4fA3S14PcA1A3S13N4A1A3A3S7S7S7S5Z10M0S3aVam;A1A2S5G0S36Vs;Vn;Vam;Vb3;Vb16;A5A2A2Vn;A2Z4A2A3F_;").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr Hsp. intros Hk. rewrite !ze_alu, ze_strideT, ze_sll, ze_lit. change (SVar 12) with (v 12). rewrite ze12. zfin. pose proof (stv_T Hk). mlia. Qed.
Lemma v_xM0 : ltac2:(tb__ "0|0|
S0S4eS34Vam;A1S4dA3S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S12S56S12S58S7dS14PcA1A3S13N14A1A3A3S7S7S5S5dVam;A1Z1000A2Vn;A2Z14A2A3F_;").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr Hsp.
  intros Hk. pose proof kd_cases as KC. rewrite Hk in KC. destruct KC as [[? _]|[[? _]|[_ [_ KF]]]]; try discriminate.
  unfold AND155. rewrite ze_alu, (ze_alu ALU_SUB), ZE_and155, ze_lit by lia. change (SVar 12) with (v 12). rewrite ze12. zfin. pose proof (stv_VM1 Hk). pose proof Hmaplen_small. mlia.
Qed.
Lemma v_xM1 : ltac2:(tb__ "0|0|
S0S4eS34Vam;A1S4dA3S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S12S56S12S58S12S58S7dS4fA3S14PcA1A3S13N14A1A3A3S7S7S7S5S5dVam;A1Z1000A2S5Z10S36Vs;Vn;Vam;Vb3;Vb16;A5A2A2Vn;A2Z14A2A3F_;").
Proof using HC HMI HP12 HW Hb16 Hb3 Hhdr Hsp.
  intros Hk. pose proof kd_cases as KC. rewrite Hk in KC. destruct KC as [[? _]|[[? _]|[_ [_ KF]]]]; try discriminate.
  unfold AND155. rewrite ze_alu, (ze_alu ALU_SUB), (ze_alu ALU_SUB), ZE_and155, ze_sll, ze_lit by lia. change (SVar 12) with (v 12). rewrite ze12. zfin. pose proof (stv_VM1 Hk). pose proof Hmaplen_small. mlia.
Qed.
Lemma v_h16 : ltac2:(tb__ "0|0|
S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S12S57S17S59S51S34Vam;A1A1S14P9dA1A3S13Z4A1A3A3S9S5S37Vam;A1S35Vam;A1A2Z10A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr. rewrite ze_alu, ze_mul, ze_stride, ze_lit. change (SVar 157) with (v 157). rewrite ze157. zfin. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. mlia. Qed.
Lemma v_f16 : ltac2:(tb__ "0|0|
S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S12S57S12S56S4fS17S59S51S34Vam;A1A1S14P9dA1A3A3S13Z4A1A3A3S6S36Vs;Vn;Vam;Vb3;Vb16;A5S9S5S37Vam;A1S35Vam;A1A2Z10A2A2A3").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. rewrite !ze_alu, ze_mul, ze_sll, ze_stride, ze_lit. change (SVar 157) with (v 157). rewrite ze157. zfin. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. mlia. Qed.
Lemma v_158 : ltac2:(tb__ "0|0|
S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S14P9eA1A3S36Vs;Vn;Vam;Vb3;Vb16;A5A3"). Proof using HC HMI HW Hb16 Hb3 Hhdr. exact ze158. Qed.
Lemma v_litv : ltac2:(tb__ "0|0|
S4S1S8Z0R1A2ScR1SaZ2Z40A2A2A2S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S13R2A1A3R2A3F_;Fz;"). Proof using . intros z Hz. rewrite ze_lit. apply Z.mod_small. exact Hz. Qed.

Lemma E_stride_T : ltac2:(tb__ "0|1|
S2S0S4eS34Vam;A1M0S4dA3A1S0S19S51G0A1S50A3F_;").
Proof using HC HW Hb16 Hb3 Hsp. intros Hk. destruct kd_cases as [[-> _]|[[-> _]|[E _]]]; [reflexivity|reflexivity|exfalso; exact (Hk E)]. Qed.
Lemma E_stride_M : ltac2:(tb__ "0|1|
S0S4eS34Vam;A1M0S4dA3S0S19S51G0A1S52A3F_;").
Proof using . intros ->. reflexivity. Qed.
Lemma v_h16T : ltac2:(tb__ "0|0|
S2S0S4eS34Vam;A1S4dA3A1S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S12S57S17S59S50S14P9dA1A3S13Z4A1A3A3S9S5S37Vam;A1S35Vam;A1A2Z10A2A3F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. intros Hk. rewrite <- (E_stride_T Hk). apply v_h16. Qed.
Lemma v_h16M : ltac2:(tb__ "0|0|
S0S4eS34Vam;A1S4dA3S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S12S57S17S59S52S14P9dA1A3S13Z4A1A3A3S9S5S37Vam;A1S35Vam;A1A2Z10A2A3F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr. intros Hk. rewrite <- (E_stride_M Hk). apply v_h16. Qed.
Lemma v_f16T : ltac2:(tb__ "0|0|
S2S0S4eS34Vam;A1S4dA3A1S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S12S57S12S56S4fS17S59S50S14P9dA1A3A3S13Z4A1A3A3S6S36Vs;Vn;Vam;Vb3;Vb16;A5S9S5S37Vam;A1S35Vam;A1A2Z10A2A2A3F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. intros Hk. rewrite <- (E_stride_T Hk). apply v_f16. Qed.
Lemma v_f16M : ltac2:(tb__ "0|0|
S0S4eS34Vam;A1S4dA3S0S4S2fS33Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S32Vs;VL;Vn;Vg;Vam;Vrho;Vb3;Vb16;A8S12S57S12S56S4fS17S59S52S14P9dA1A3A3S13Z4A1A3A3S6S36Vs;Vn;Vam;Vb3;Vb16;A5S9S5S37Vam;A1S35Vam;A1A2Z10A2A2A3F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp. intros Hk. rewrite <- (E_stride_M Hk). apply v_f16. Qed.

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
    | unfold U.Mal_malloc__G3.Mal_malloc_fastG.oSlot; cbn [ob_cells]; rewrite SCE, Ko, Kr; apply (nth_error_In _ i); vm_compute; reflexivity
    | reflexivity
    | clear; cbn; lia
    | unfold U.Mal_malloc__G3.Mal_malloc_fastG.oSlot; cbn [ob_base c_off]; rewrite baseF_p0; addr_soff; lean; lia
    | reflexivity | reflexivity
    | cbn [c_val]; let m := eval vm_compute in (2 ^ (8 * Z.of_nat w)) in change (2 ^ (8 * Z.of_nat w)) with m;
      val_rw; lean; mlia ]
  end.

Ltac v3meta :=
  cbn [mc_w mc_loc mc_val sval_num]; model_addr;
  lazymatch goal with
  | |- forall j, (j < ?w)%nat -> _ /\ _ = Some (Z_to_bv 8 (le_byte ?V _ _)) =>
    apply (V3_cell oMeta (mkCell (SLit 24) 4 AVAIL_T) _ V w);
    [ right; reflexivity
    | unfold U.Mal_malloc__G3.Mal_malloc_fastG.oMeta; cbn [ob_cells]; left; reflexivity
    | reflexivity
    | clear; cbn; lia
    | unfold U.Mal_malloc__G3.Mal_malloc_fastG.oMeta; cbn [ob_base c_off]; rewrite baseF_151, soffF_lit by (clear; lia); unfold META_avail; clear; lia
    | reflexivity | reflexivity
    | cbn [c_val]; change (8 * Z.of_nat 4) with 32; exact availT_val ]
  end.

Lemma rsv_def : ltac2:(tb__ "0|0|
S0S4S74Vs;Vn;Vam;Vb3;Vb16;A5S7S7S7S37Vam;A1S5Z10S36Vs;Vn;Vam;Vb3;Vb16;A5A2A2Vn;A2Z4A2A3"). Proof using . reflexivity. Qed.

Lemma slot_cells_T : ltac2:(tb__ "0|3|
S2S0S4eS34Vam;A1M0S4dA3A1S0S26S15A1S85G0S75Vs;Vn;Vam;Vb3;Vb16;A5M1S76Vs;Vn;Vam;Vb3;Vb16;A5M2A3S85S55G1G2A3A3F_;").
Proof using HC HMI HW Hb16 Hb3 Hhdr Hsp.
  intros Hk. destruct kd_cases as [[-> _]|[[-> _]|[E _]]]; [reflexivity| |exfalso; exact (Hk E)].
  destruct vo_cases as [[-> _]|[-> _]]; destruct vr_cases as [[-> _]|[[-> _]|[[-> _]|[-> _]]]]; reflexivity.
Qed.

Ltac decide_cond b :=
  first [ replace b with true by (symmetry; lean; first [apply (proj2 (Z.eqb_eq _ _)) | apply (proj2 (Z.ltb_lt _ _)) | apply (proj2 (Z.leb_le _ _))]; lia)
        | replace b with false by (symmetry; lean; first [apply (proj2 (Z.eqb_neq _ _)) | apply (proj2 (Z.ltb_ge _ _)) | apply (proj2 (Z.leb_gt _ _))]; lia) ].

Theorem V3 : ltac2:(tb__ "0|4|
S3eS7fS3eR1S67Vs;Vn;Vg;Vam;S38Vs;Vb3;Vb16;A3A5A3S27S77R1S45R3A1A2S1S0S22S6dS4cS84Vs;Vn;Vam;Vrho;Vb3;Vb16;Vms';VrhoF;A8M0S6fS6S44VL;S49R4A1A2SdR2A1A2A1M1A3S28A3S0S24S62Q8M2A1M3A1S6cS4cG0G1A3S29G3S63G2S42S4bVL;S4aR4A1A2S45R4A1R2A3A2A2A3A2F_;Fj;F_;Fc;").
Proof using Em0 EmW HC HMI HP12 HW HagF Hb16 Hb3 Hdepth Hhdr HsmF Hsp.
  intros c Hc. rewrite newcells_eq in Hc. revert Hc.
  pose proof R_all as R. pose proof Hoff as HO. pose proof pow_idx_range as PI. pose proof rsv_def as RD.
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
      destruct Hc as [<-|[<-|[<-|[]]]];
        [ v3meta | v3slot 0%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[]]]]];
        [ v3meta | v3slot 0%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        [ v3meta | v3slot 0%nat | v3slot 3%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        [ v3meta | v3slot 0%nat | v3slot 4%nat | v3slot 3%nat | v3slot 1%nat | v3slot 2%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        [ v3meta | v3slot 4%nat | v3slot 3%nat | v3slot 2%nat | v3slot 0%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
        [ v3meta | v3slot 5%nat | v3slot 4%nat | v3slot 3%nat | v3slot 0%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
        [ v3meta | v3slot 6%nat | v3slot 5%nat | v3slot 4%nat | v3slot 0%nat | v3slot 3%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
        [ v3meta | v3slot 7%nat | v3slot 6%nat | v3slot 5%nat | v3slot 0%nat | v3slot 4%nat | v3slot 3%nat | v3slot 1%nat | v3slot 2%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[]]]];
        [ v3meta | v3slot 0%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[]]]]];
        [ v3meta | v3slot 0%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        [ v3meta | v3slot 0%nat | v3slot 3%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        [ v3meta | v3slot 0%nat | v3slot 4%nat | v3slot 3%nat | v3slot 1%nat | v3slot 2%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        [ v3meta | v3slot 4%nat | v3slot 3%nat | v3slot 2%nat | v3slot 0%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
        [ v3meta | v3slot 5%nat | v3slot 4%nat | v3slot 3%nat | v3slot 0%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
        [ v3meta | v3slot 6%nat | v3slot 5%nat | v3slot 4%nat | v3slot 0%nat | v3slot 3%nat | v3slot 2%nat | v3slot 1%nat ].
  -
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
        [ v3meta | v3slot 7%nat | v3slot 6%nat | v3slot 5%nat | v3slot 0%nat | v3slot 4%nat | v3slot 3%nat | v3slot 1%nat | v3slot 2%nat ].
Qed.

End ReabH.
