(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "True"; "False"; "@Corelib.Init.Datatypes"; "cons"; "Some"; "pair"; "list"; "option"; "bool"; "app"; "prod"; "true"; "nil"; "None"; "fst"; "snd"; "false"; "nat"; "andb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "MFree"; "st_free_meta_head"; "st_init_done"; "brkst"; "mupdate"; "padd"; "sptr_eqb"; "st_area_head"; "st_area_tail"; "st_areas"; "st_avail_meta"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_avail_meta_count"; "st_brk"; "st_meta_alloc_shift"; "st_mmap_counter"; "st_seq"; "st_active"; "st_bounces"; "st_metas"; "st_regions"; "st_unmap_seq"; "st_usage"; "PGSZ"; "SP"; "astate"; "region"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "cell"; "SLit"; "eval"; "mkCell"; "SVar"; "sv"; "obj_range"; "obj_holds"; "sprop"; "rm"; "rw"; "reg_sv"; "smatch"; "soff"; "sstate"; "DUnknown"; "c_width"; "mkObj"; "FcsrFrm0"; "c_off"; "c_val"; "ob_base"; "ob_cells"; "odefault"; "valuation"; "agree_below"; "enc_bytes"; "fcsr_match"; "freg_sv"; "fregs_match"; "holds"; "mkVal"; "ob_dflt"; "obj_wf"; "outside_all"; "pairwise_disjoint"; "regs_match"; "resv_match"; "rl"; "sfcsr"; "ss_fcsr"; "ss_fregs"; "ss_next"; "ss_objs"; "ss_pc"; "ss_resv"; "tfact"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "to_nat"; "of_nat"; "modulo"; "pow"; "eqb"; "leb"; "ltb"; "mul"; "sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "callee_saved"; "pre_reg"; "pre_fregs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs"; "v"; "AM_P"; "O_stk"; "AE_head3"; "AM_NEXT"; "ne_facts"; "ptr_facts"; "O_auxvp"; "O_brk"; "O_errno"; "O_got"; "O_guard"; "O_m"; "O_nprev"; "O_pgsz"; "O_pnext"; "O_sec"; "Pre_am"; "zero_tail"; "O_ctxB"; "Posts_am_P"; "ctx_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I"; "zA"; "rho1"; "hlinks"; "optrZ"; "D0"; "sp0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta_H3.InstX.Head3"; "sH"; "CHG_H"; "UNCH_H"; "mF"; "LF_H"; "rho'"; "touched"; "stkF_cells"; "rw'"; "xb"; "xp'"; "C_hd'"; "N_H3"; "O_mF"; "xa"; "xp"; "O_nF"; "O_pF"; "R_H3"; "SC13"; "ctxB_F"; "xm"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LCtx"; "MCell"; "MT"; "VZ"; "image"; "sval"; "ctx_cells"; "loc_addr"; "optr"; "LMem"; "VP"; "keys"; "meta_slot_cells"; "CTX_free_meta_head"; "CTX_seq"; "Inv"; "cell_holds"; "footprint"; "loc"; "user_blocks"; "CTX_SIZE"; "CTX_active"; "CTX_avail_meta"; "CTX_avail_meta_area_count"; "CTX_avail_meta_areas"; "CTX_avail_meta_count"; "CTX_brk"; "CTX_init_done"; "CTX_meta_alloc_shift"; "CTX_meta_area_head"; "CTX_meta_area_tail"; "CTX_mmap_counter"; "CTX_secret"; "VSec"; "alloc_owned"; "ly_ctx"; "mc_loc"; "mc_w"; "sval_num"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "In"; "forallb"; "hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "topL"; "blocks"; "holds";
"mc_auxv"; "mc_chk_guard"; "mc_errno"; "mc_tp"; "vm_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "canary_kept"; "maps_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "mkMA"; "MA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "L_am_ok"; "Pre_am"; "JL_am_ok"; "J_am_pre"; "Posts_am"; "AM_D"; "meta_obj0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "add"; "le"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "agree_vals"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric"; "meets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsFuel"; "leaf"; "lf_state"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost"; "am_spec_post"; "s_H23"; "s_H23a"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_DEPTH"; "V_RES"; "mem_kept"; "ok_sideK"; "stack_win"; "top_high"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit"; "fully_covered"; "m'"; "obj_lits_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundR SymFrame SymSummary SymCall SymEntail SymHeap Glue3 ExampleMemcpy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import WalkLink ReabKit ObjBytes GapGeneric MallocLaws
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfArith MallocWfInv MallocWfFrame MallocWfRings MallocWfRepr MallocWfMeta MallocWfGeom MallocWfSurgery MallocLayout MallocFooter
  MallocIface MallocIfaceI Contract ContractI ContractAM Glue ReprGlue ZEval ZBits WalkArith FpLaws Zones2 AllocMetaPost AllocMetaImage AllocMetaGrow ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import XLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac lia := slia.
Local Ltac nia := snia.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
SbbVX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S106Sd9VX;VR;VU;Se9Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§1§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation HV := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HV).
Local Abbreviation HLG := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HLG).
Local Abbreviation Hctx := (§1§ U.Mal_ameta__G1.Mal_ameta_I.Hctx).
Local Abbreviation HB := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HB).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation zA := (@U.Mal_ameta__G1.Mal_ameta_I.zA L).
Local Abbreviation optrZ := (@U.Mal_ameta__G1.Mal_ameta_I.optrZ L).
Local Notation "§2§ h__" := (h__ s L) (at level 10, h__ global).
Local Abbreviation secZ := (§2§ U.Mal_ameta__G1.Mal_ameta_I.secZ).
Local Abbreviation initZ := (@U.Mal_ameta__G1.Mal_ameta_I.initZ s).
Local Abbreviation avmZ := (§2§ U.Mal_ameta__G1.Mal_ameta_I.avmZ).
Local Abbreviation areasZ := (§2§ U.Mal_ameta__G1.Mal_ameta_I.areasZ).
Local Abbreviation brkZ := (§2§ U.Mal_ameta__G1.Mal_ameta_I.brkZ).
Local Abbreviation hlinks := (@U.Mal_ameta__G1.Mal_ameta_I.hlinks s).
Local Abbreviation n2Z := (§2§ U.Mal_ameta__G1.Mal_ameta_I.n2Z).
Local Abbreviation ppZ := (§2§ U.Mal_ameta__G1.Mal_ameta_I.ppZ).
Local Notation "§3§ h__" := (h__ s L rho gd evb avb) (at level 10, h__ global).
Local Abbreviation rho1 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.rho1).
Local Notation "§4§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§4§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Notation "§5§ h__" := (h__ s L X R U HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation key_R := (§5§ U.Mal_ameta__G1.Mal_ameta_I.key_R).
Local Abbreviation ev173 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev175 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev175).
Local Abbreviation ev176 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev176).
Local Abbreviation ev177 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev177).
Local Abbreviation ev178 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev178).
Local Abbreviation ev179 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev179).
Local Abbreviation ev180 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev180).
Local Abbreviation ev181 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev181).
Local Abbreviation ev183 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev183).
Local Abbreviation ev184 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev184).
Local Abbreviation ev185 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev185).
Local Abbreviation ev186 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Local Abbreviation ev187 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev187).
Local Abbreviation ev188 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev188).
Local Abbreviation ev189 := (§4§ U.Mal_ameta__G1.Mal_ameta_I.ev189).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S3Sd3Q40A1SeSd3Q8A1A1F_;Vrd0;Se3S74VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S3Sd3Q40A1SfF_;Vwok0;Se4S74VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
SddSdaVrd0;Sd3Q40A1S12L_;A2SdfSd9A1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S18S102R1U4A2S3SeSd3Q8M0A1M1A1Se3S74VmW;Sd4Q40S69Se0Sd9A1S6cR2A1A2A2A3SbG1SeeG1R2Vevb;Sd4G0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S18S102R1U8A2S3SeSd3Q8M0A1M1A1Se3S74VmW;Sd4Q40S69SdeSd9A1S6cR2A1A2A2A3SbG1SeeG1R2Vavb;Sd4G0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
SdaSe3S74VmW;A2Se4S74VmW;A2A2").
Local Abbreviation HMI0 := (@U.Mal_ameta__G1.Mal_ameta_I.HMI0 s L X R U rd0 wok0 vm HMI mW Erd Ewok).
Local Notation "§6§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S43Vrho;P18A2Sd4G0Se1Sd9A1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation hold_errno := (@U.Mal_ameta__G1.Mal_ameta_I.hold_errno s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hev_rd Htp).
Local Notation "§7§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW) (at level 10, h__ global).
Local Abbreviation B_ctx := (§7§ U.Mal_ameta__G1.Mal_ameta_I.B_ctx).
Local Abbreviation hold_sec := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_sec).
Local Abbreviation hold_brk := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_brk).
Local Abbreviation hold_ctxB := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_ctxB).
Local Abbreviation key_slot_cells_image := (@U.Mal_ameta__G1.Mal_ameta_I.key_slot_cells_image s X R U HI).
Local Abbreviation slot_obj := (@U.Mal_ameta__G1.Mal_ameta_I.slot_obj).
Local Abbreviation hold_slot := (§6§ U.Mal_ameta__G1.Mal_ameta_I.hold_slot).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Local Abbreviation rng_stk := (§7§ U.Mal_ameta__G1.Mal_ameta_I.rng_stk).
Local Abbreviation rng_lit := (§7§ U.Mal_ameta__G1.Mal_ameta_I.rng_lit).
Variables (tr : list event) (md : Model).
Hypothesis EmW : mW = rm rho.
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S45S74Vrho;Sf4Se5A1ScSdSebA1Sf0Vtr;Sf1Vms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S119Se9Vs;VL;A2Vrho;A2").
Local Notation "§8§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop) (at level 10, h__ global).
Local Abbreviation sm_pre1 := (§8§ U.Mal_ameta__G1.Mal_ameta_I.sm_pre1).
Local Abbreviation stk_facts := (§8§ U.Mal_ameta__G1.Mal_ameta_I.stk_facts).
Local Abbreviation pw := (@U.Mal_ameta__G1.Mal_ameta_I.pw).
Local Abbreviation pairwise_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.pairwise_of_ranges).
Local Abbreviation vs_stack_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.vs_stack_of_ranges).
Local Notation "§9§ h__" := (h__ s L rho gd evb avb mW) (at level 10, h__ global).
Local Abbreviation holds1 := (§9§ U.Mal_ameta__G1.Mal_ameta_I.holds1).
Local Abbreviation zr1_var := (§3§ U.Mal_ameta__G1.Mal_ameta_I.zr1_var).
Local Abbreviation rw1_v := (§9§ U.Mal_ameta__G1.Mal_ameta_I.rw1_v).
Local Abbreviation ctx_facts_hold := (@U.Mal_ameta__G1.Mal_ameta_I.ctx_facts_hold s L rho gd evb avb Hgd Hev Hav mW Htp).
Local Abbreviation map_region_where := (§5§ U.Mal_ameta__G1.Mal_ameta_I.map_region_where).

Section Head3.
  Variables mH nH pH ppH n2H : sptr.
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S3SeS1aA1S1dVs;A1SbS1aVmH;A2A3").
  Hypothesis Hnm : nH <> mH.
  Hypothesis Hpm : pH <> mH.
  Hypothesis Hpn : pH <> nH.
  Hypothesis HmH : ltac2:(tb__ "0|0|
S3SeS1bA1SaeVs;VmH;A2SbS1bS1cSbS1aVpH;A2SbS1aVnH;A2A2A2A3").
  Hypothesis HnH : ltac2:(tb__ "0|0|
S3SeS1bA1SaeVs;VnH;A2SbS1bS1cSbS1aVmH;A2SbS1aVn2H;A2A2A2A3").
  Hypothesis HpH : ltac2:(tb__ "0|0|
S3SeS1bA1SaeVs;VpH;A2SbS1bS1cSbS1aVppH;A2SbS1aVmH;A2A2A2A3").
  Hypothesis Hinit : st_init_done s = true.

  Lemma mH_key : In mH (keys s).
  Proof using HmH. unfold keys. apply (mlookup_In_keys _ _ _ HmH). Qed.
  Lemma mH_R : ltac2:(tb__ "0|3|
S4S68Z1000S8fVL;VmH;A2M0A2S4S68S69G0Z28A2M1SdbVL;A1A2S4S3S0S6dG0Z8A2Z0A3S4S5S68G1Z10000A2S68Z5b000G0A2A2S5S68S69Z5a3d0M2Z3a0A2G0A2S68G1G2A2A2A2A2A2A2").
  Proof using HI HMI Hav Hev Hgd HmH. exact (key_R mH mH_key). Qed.
  Lemma E178 : ltac2:(tb__ "0|0|
S3S0S92VL;S1dVs;A1A2S8fVL;VmH;A2A3"). Proof using Hhd. rewrite Hhd. reflexivity. Qed.
  Lemma Ehl : ltac2:(tb__ "0|1|
S3S11SeS1aA1M0G0A2S91Vs;A1ScG0G0SbS1aVpH;A2SbS1aVnH;A2A4A3"). Proof using Hhd HmH. unfold hlinks. rewrite Hhd, HmH. reflexivity. Qed.
  Lemma ev178' m : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S3bS90Vs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7S79Pb2A1A2Sd4G0S8fVL;VmH;A2A2A3"). Proof using Hav Hev Hgd Hhd. rewrite ev178, E178. reflexivity. Qed.
  Lemma nH_key : In nH (keys s).
  Proof using HnH. unfold keys. apply (mlookup_In_keys _ _ _ HnH). Qed.
  Lemma Hmn : mH <> nH. Proof using Hnm. intros E. exact (Hnm (eq_sym E)). Qed.
  Lemma Hmp : mH <> pH. Proof using Hpm. intros E. exact (Hpm (eq_sym E)). Qed.
  Lemma Hnp : nH <> pH. Proof using Hpn. intros E. exact (Hpn (eq_sym E)). Qed.
  Lemma pH_key : In pH (keys s).
  Proof using HpH. unfold keys. apply (mlookup_In_keys _ _ _ HpH). Qed.
  Lemma pH_R : ltac2:(tb__ "0|3|
S4S68Z1000S8fVL;VpH;A2M0A2S4S68S69G0Z28A2M1SdbVL;A1A2S4S3S0S6dG0Z8A2Z0A3S4S5S68G1Z10000A2S68Z5b000G0A2A2S5S68S69Z5a3d0M2Z3a0A2G0A2S68G1G2A2A2A2A2A2A2").
  Proof using HI HMI Hav Hev Hgd HpH. exact (key_R pH pH_key). Qed.
  Lemma ev180' m : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S3bS90Vs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7S79Pb4A1A2Sd4G0S8fVL;VpH;A2A2A3"). Proof using Hav Hev Hgd Hhd HmH. rewrite ev180, Ehl. reflexivity. Qed.
  Lemma En2 : n2Z = zA n2H. Proof using Hhd HmH HnH. unfold n2Z. rewrite Ehl. cbn [snd]. rewrite HnH. reflexivity. Qed.
  Lemma Epp : ppZ = zA ppH. Proof using Hhd HmH HpH. unfold ppZ. rewrite Ehl. cbn [fst]. rewrite HpH. reflexivity. Qed.
  Lemma ev188' m : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S3bS90Vs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7S79PbcA1A2Sd4G0S8fVL;Vn2H;A2A2A3"). Proof using Hav Hev Hgd Hhd HmH HnH. rewrite ev188, En2. reflexivity. Qed.
  Lemma ev189' m : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S3bS90Vs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7S79PbdA1A2Sd4G0S8fVL;VppH;A2A2A3"). Proof using Hav Hev Hgd Hhd HmH HpH. rewrite ev189, Epp. reflexivity. Qed.
  Lemma mp_apart : ltac2:(tb__ "0|3|
S5S68S69S8fVL;VmH;A2M0Z28M1A2S8fVL;VpH;A2M2A2S68S69G2G1A2G0A2A2").
  Proof using HI HMI Hav Hev Hgd HmH HpH Hpm. pose proof (meta_ranges_disjoint X R U s L HI HL mH pH mH_key pH_key Hmp) as M. unfold zA, META_SIZE in *. lia. Qed.
  Lemma np_apart : ltac2:(tb__ "0|3|
S5S68S69S8fVL;VnH;A2M0Z28M1A2S8fVL;VpH;A2M2A2S68S69G2G1A2G0A2A2").
  Proof using HI HMI Hav Hev Hgd HnH HpH Hpn. pose proof (meta_ranges_disjoint X R U s L HI HL nH pH nH_key pH_key Hnp) as M. unfold zA, META_SIZE in *. lia. Qed.
  Lemma nH_R : ltac2:(tb__ "0|3|
S4S68Z1000S8fVL;VnH;A2M0A2S4S68S69G0Z28A2M1SdbVL;A1A2S4S3S0S6dG0Z8A2Z0A3S4S5S68G1Z10000A2S68Z5b000G0A2A2S5S68S69Z5a3d0M2Z3a0A2G0A2S68G1G2A2A2A2A2A2A2").
  Proof using HI HMI Hav Hev Hgd HnH. exact (key_R nH nH_key). Qed.
  Lemma ev179' m : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S3bS90Vs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7S79Pb3A1A2Sd4G0S8fVL;VnH;A2A2A3"). Proof using Hav Hev Hgd Hhd HmH. rewrite ev179, Ehl. reflexivity. Qed.
  Lemma mn_apart : ltac2:(tb__ "0|3|
S5S68S69S8fVL;VmH;A2M0Z28M1A2S8fVL;VnH;A2M2A2S68S69G2G1A2G0A2A2").
  Proof using HI HMI Hav Hev Hgd HmH HnH Hnm. pose proof (meta_ranges_disjoint X R U s L HI HL mH nH mH_key nH_key Hmn) as M. unfold zA, META_SIZE in *. lia. Qed.

  Definition N_H3 : list sobj := ltac2:(tb__ "0|0|
SaS38S83S7aA1SaS38S84SaS38S80S7aA1SaS38S87S7aA1SaS38S82SaS38S89S7aS79PafA1Z1A3SaS38S8cS7aS79Pb2A1S79Pb0A1S79Pb5A1S79Pb7A1S79Pb8A1S79Pb9A1S79PbaA1S79Pb1A1A9SaS38S81S7aS79PbbA1A2SaS38S85S79Pb4A1S79Pb3A1A2SaS38S86SaS38S88S13S38A1A3A3A3A3A3A3A3A3A3A3A3").
  Definition R_H3 (q n p : Z) : list (Z * Z) := ltac2:(tb__ "0|3|
SaS11S0S0A2M0ScS0S0Z28d50Z28d58A4SaG0ScS0S0Z5a338Z5a340A4SaG0ScS0S0Z5a360Z5a368A4SaG0ScS0S0Z5a388Z5a390A4SaG0ScS0S0Z3a02cZ3a030A4SaG0ScS0S0Z5a3d0Z5a3dcA4SaG0ScS0S0Z5a3e0Z5a420A4SaG0ScS0S0Z5a768Z5a770A4SaG0ScS0S0S69Vq;Z0M1A2S69Vq;Z28M2A2A4SaG0ScS0S0S69Vn;G1A2S69Vn;G2A2A4SaG0ScS0S0S69Vp;G1A2S69Vp;G2A2A4S13G0A1A3A3A3A3A3A3A3A3A3A3A3").

  Lemma N_H3_ranges : ltac2:(tb__ "0|1|
S3SdS11S0S0A2M0A1SefS38G0S3fS90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1Sa1A4Sa7S8fVL;VmH;A2S8fVL;VnH;A2S8fVL;VpH;A2A3A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH HnH HpH Htp.
    pose proof mH_R as (Q1 & Q2 & _). pose proof nH_R as (N1 & N2 & _). pose proof pH_R as (P1 & P2 & _).
    cbn [map N_H3 R_H3]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxB, O_brk, O_m, O_nprev, O_pnext. cbn [am_got am_libc am_ctx AM_P].
    rewrite !(rng_lit (SLit 167248) _ _ _ _ 167248) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369496) _ _ _ _ 369496) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369608) _ _ _ _ 369608) by (try lia; cbn [eval]; apply u64; lia).
    rewrite (rng_lit (v 173) _ _ _ _ 0x5a338) by (try lia; rewrite ev173; apply u64; cbn; lia).
    rewrite (rng_lit (SVar 24) _ _ _ _ 0x3a0d0) by (try lia; rewrite ev_tp; apply u64; cbn; lia).
    rewrite (rng_lit (v 178) _ _ _ _ (zA mH)) by (try lia; rewrite ev178'; apply u64; top_ranges; lia).
    rewrite (rng_lit (v 179) _ _ _ _ (zA nH)) by (try lia; rewrite ev179'; apply u64; top_ranges; lia).
    rewrite (rng_lit (v 180) _ _ _ _ (zA pH)) by (try lia; rewrite ev180'; apply u64; top_ranges; lia).
    unfold R_H3. reflexivity.
  Qed.

  Lemma hold_m : ltac2:(tb__ "0|0|
S40S74S90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sf2Vms;VmW;A2S85S79Pb4A1S79Pb3A1A2A4").
  Proof using Erd Ewok HI HMI Hav Hev Hgd Hhd HmH Hrom.
    pose proof mH_R as (Q1 & Q2 & _).
    change (O_m (v 180) (v 179)) with (slot_obj (v 178) (v 180) (v 179)).
    apply (hold_slot (v 178) (v 180) (v 179) mH (Some (MFree (Some pH) (Some nH)))).
    - intros c Hc. apply (key_slot_cells_image mH c mH_key). rewrite HmH. exact Hc.
    - exact I.
    - rewrite ev178'. apply u64. top_ranges. lia.
    - cbn [fst links_of]. apply ev180'.
    - cbn [snd links_of]. apply ev179'.
    - lia.
    - top_ranges. lia.
  Qed.
  Lemma hold_n : ltac2:(tb__ "0|0|
S40S74S90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sf2Vms;VmW;A2S86A4").
  Proof using Erd Ewok HI HMI Hav Hev Hgd Hhd HmH HnH Hrom.
    pose proof nH_R as (N1 & N2 & _).
    change O_nprev with (slot_obj (v 179) (v 178) (v 188)).
    apply (hold_slot (v 179) (v 178) (v 188) nH (Some (MFree (Some mH) (Some n2H)))).
    - intros c Hc. apply (key_slot_cells_image nH c nH_key). rewrite HnH. exact Hc.
    - exact I.
    - rewrite ev179'. apply u64. top_ranges. lia.
    - cbn [fst links_of]. apply ev178'.
    - cbn [snd links_of]. apply ev188'.
    - lia.
    - top_ranges. lia.
  Qed.
  Lemma hold_p : ltac2:(tb__ "0|0|
S40S74S90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sf2Vms;VmW;A2S88A4").
  Proof using Erd Ewok HI HMI Hav Hev Hgd Hhd HmH HpH Hrom.
    pose proof pH_R as (N1 & N2 & _).
    change O_pnext with (slot_obj (v 180) (v 189) (v 178)).
    apply (hold_slot (v 180) (v 189) (v 178) pH (Some (MFree (Some ppH) (Some mH)))).
    - intros c Hc. apply (key_slot_cells_image pH c pH_key). rewrite HpH. exact Hc.
    - exact I.
    - rewrite ev180'. apply u64. top_ranges. lia.
    - cbn [fst links_of]. apply ev189'.
    - cbn [snd links_of]. apply ev178'.
    - lia.
    - top_ranges. lia.
  Qed.

  Lemma N_H3_hold : ltac2:(tb__ "0|0|
SedS38S40S74S90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sf2Vms;VmW;A2A3Sa1A3").
  Proof using Erd Ewok HI HMI Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH HnH HpH Hrom Htp.
    unfold N_H3. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
    constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
    constructor; [apply hold_errno|]. constructor; [exact HS|].
    constructor; [apply hold_ctxB; [apply ev178 | apply ev176 | apply ev181 | apply ev183 | apply ev184 | apply ev185 | apply ev186 | apply ev177]|].
    constructor; [apply hold_brk|]. constructor; [apply hold_m|]. constructor; [apply hold_n|]. constructor; [apply hold_p|]. constructor.
  Qed.

  Lemma E179 : ltac2:(tb__ "0|1|
S3S0S92VL;S16SeS1aA1M0G0S91Vs;A1A3A2S8fVL;VnH;A2A3"). Proof using Hhd HmH. rewrite Ehl. reflexivity. Qed.
  Lemma E180 : ltac2:(tb__ "0|1|
S3S0S92VL;S15SeS1aA1M0G0S91Vs;A1A3A2S8fVL;VpH;A2A3"). Proof using Hhd HmH. rewrite Ehl. reflexivity. Qed.
  Lemma H3_facts_hold : ltac2:(tb__ "0|4|
SedS41S57S90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S10S41S10S41S7fPb2M0Z3M1A2S10S41S7fPb3M2G1A2S10S41S7fPb4M3G1A2S10S41S7eG0G2A2S10S41S7eG0G3A2S7eG2G3A2A3A3A3A3A3S8eA3A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH HnH Hnm HpH Hpm Hpn Htp.
    pose proof mH_R as (Q1 & Q2 & Q3 & _). top_ranges. pose proof nH_R as (N1 & N2 & N3 & _). top_ranges.
    pose proof pH_R as (P1 & P2 & P3 & _). top_ranges.
    pose proof mn_apart as MN. pose proof mp_apart as MP. pose proof np_apart as NP.
    apply Forall_app. split; [|apply ctx_facts_hold].
    unfold ptr_facts, ne_facts. cbn [app].
    constructor. { cbn [SymState.holds]. rewrite (rw1_v 178 _ eq_refl), E178. split; [lia|]. rewrite Z_to_bv_unsigned.
                   change (bv_wrap 64 (zA mH)) with (zA mH mod 2 ^ 64). zlit. Z.to_euclidean_division_equations; lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 178 _ eq_refl), E178. zlit. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 178 _ eq_refl), E178. zlit. lia. }
    constructor. { cbn [SymState.holds]. rewrite (rw1_v 179 _ eq_refl), E179. split; [lia|]. rewrite Z_to_bv_unsigned.
                   change (bv_wrap 64 (zA nH)) with (zA nH mod 2 ^ 64). zlit. Z.to_euclidean_division_equations; lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 179 _ eq_refl), E179. zlit. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 179 _ eq_refl), E179. zlit. lia. }
    constructor. { cbn [SymState.holds]. rewrite (rw1_v 180 _ eq_refl), E180. split; [lia|]. rewrite Z_to_bv_unsigned.
                   change (bv_wrap 64 (zA pH)) with (zA pH mod 2 ^ 64). zlit. Z.to_euclidean_division_equations; lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 180 _ eq_refl), E180. zlit. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval v]. rewrite (zr1_var 180 _ eq_refl), E180. zlit. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval zcond v]. rewrite (zr1_var 178 _ eq_refl), (zr1_var 179 _ eq_refl), E178, E179. zlit. rewrite Z.eqb_eq. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval zcond v]. rewrite (zr1_var 178 _ eq_refl), (zr1_var 179 _ eq_refl), E178, E179. zlit. rewrite Z.eqb_eq. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval zcond v]. rewrite (zr1_var 178 _ eq_refl), (zr1_var 180 _ eq_refl), E178, E180. zlit. rewrite Z.eqb_eq. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval zcond v]. rewrite (zr1_var 178 _ eq_refl), (zr1_var 180 _ eq_refl), E178, E180. zlit. rewrite Z.eqb_eq. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval zcond v]. rewrite (zr1_var 179 _ eq_refl), (zr1_var 180 _ eq_refl), E179, E180. zlit. rewrite Z.eqb_eq. lia. }
    constructor. { apply holds1; [reflexivity|]. cbn [zholds zeval zcond v]. rewrite (zr1_var 179 _ eq_refl), (zr1_var 180 _ eq_refl), E179, E180. zlit. rewrite Z.eqb_eq. lia. }
    constructor.
  Qed.

  Theorem entry_H3 : ltac2:(tb__ "0|0|
S45S74S90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S8aS74S7aS7cA3ScSdSebA1Sf0Vtr;Sf1Vms;Vmd;A2A4A4").
  Proof using EmW Erd Ewok HI HMI Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH HnH Hnm HpH Hpm Hpn Hrom Hsm_pre Htop Htp.
    pose proof stk_facts as (S1 & S2 & S3 & S4). pose proof mH_R as (Q1 & Q2 & Q3 & Q4 & Q5). top_ranges.
    pose proof nH_R as (N1 & N2 & N3 & N4 & N5). top_ranges. pose proof mn_apart as MN.
    pose proof pH_R as (P1 & P2 & P3 & P4 & P5). top_ranges. pose proof mp_apart as MP. pose proof np_apart as NP.
    pose proof (smatch_extend_objs segsU (rho1 mW) (ContractAM.Pre_am IEC_U) tr ms md N_H3 AM_NEXT sm_pre1) as E1.
    cbn zeta in E1.
    assert (SM1 : smatch segsU (rho1 mW)
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_H3) (ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT (ss_lenient (ContractAM.Pre_am IEC_U)))
      (tr, mkCfg ms md)).
    { apply E1.
      - vm_compute. reflexivity.
      - change (rm (rho1 mW)) with mW. apply N_H3_hold.
      - apply (vs_stack_of_ranges (rho1 mW) (stack_win ContractAM.AM_D) N_H3 (R_H3 (zA mH) (zA nH) (zA pH)) N_H3_ranges).
        change (stack_win ContractAM.AM_D) with (O_stk []). rewrite rng_stk.
        unfold R_H3. repeat (apply Forall_cons; [unfold SymState.ranges_disjoint; cbn [fst snd]; lia|]). apply Forall_nil.
      - apply (pairwise_of_ranges (rho1 mW) N_H3 (R_H3 (zA mH) (zA nH) (zA pH)) N_H3_ranges).
        cbn [pw R_H3]. repeat match goal with |- _ /\ _ => split | |- True => exact I | |- Forall _ _ => first [apply Forall_nil | apply Forall_cons] | |- SymState.ranges_disjoint _ _ => unfold SymState.ranges_disjoint; cbn [fst snd]; lia end. }
    pose proof (smatch_set_objs_facts_next segsU (rho1 mW) _ (tr, mkCfg ms md) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_H3)
                  ((ptr_facts 178 3 ++ ptr_facts 179 3 ++ ptr_facts 180 3 ++ ne_facts 178 179 ++ ne_facts 178 180 ++ ne_facts 179 180) ++ ctx_facts) AM_NEXT false SM1) as E2.
    cbn [cfg_ms snd] in E2.
    match goal with |- smatch _ _ ?S _ => change S with
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_H3)
            (((ptr_facts 178 3 ++ ptr_facts 179 3 ++ ptr_facts 180 3 ++ ne_facts 178 179 ++ ne_facts 178 180 ++ ne_facts 179 180) ++ ctx_facts) ++ ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT false) end.
    apply E2.
    - destruct SM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _). exact HM.
    - apply H3_facts_hold.
    - vm_compute. reflexivity.
  Qed.

  Definition ctxB_F : sobj := ltac2:(tb__ "0|2|
S4aS3aZ5a3c8A1S3aZ18A1M0S3aZ58A1SaS39S3cG0Z8M1S79Pb3A1A3SaS39S3cS3aZ20A1G1S79Pb0A1A3SaS39S3cS3aZ28A1G1S79Pb5A1A3SaS39S3cS3aZ30A1G1S79Pb7A1A3SaS39S3cS3aZ38A1G1S79Pb8A1A3SaS39S3cS3aZ40A1G1S79Pb9A1A3SaS39S3cS3aZ48A1G1S79PbaA1A3SaS39S3cS3aZ50A1G1S79Pb1A1A3S13S39A1A3A3A3A3A3A3A3A3S48A5").

  Definition O_mF : sobj := O_m (SLit 0) (SLit 0).

  Definition O_nF : sobj := ltac2:(tb__ "0|2|
S4aS79Pb3A1S3aZ0A1M0S3aZ28A1S10S39SaS39S3cG0Z8M1S79Pb4A1A3SaS39S3cS3aG1A1G1S79PbcA1A3S13S39A1A3A3S8bA3S48A5").

  Definition O_pF : sobj := ltac2:(tb__ "0|2|
S4aS79Pb4A1S3aZ0A1M0S3aZ28A1S10S39SaS39S3cS3aZ8M1A1G1S79Pb3A1A3SaS39S3cG0G1S79PbdA1A3S13S39A1A3A3S8bA3S48A5").
  Definition stkF_cells : list cell := ltac2:(tb__ "0|1|
SaS39S3cS3aN38A1Z8M0S79PaeA1A3SaS39S3cS3aN30A1G0S3dP28A1A3SaS39S3cS3aN28A1G0S3dP27A1A3SaS39S3cS3aN20A1G0S3dP26A1A3SaS39S3cS3aN18A1G0S3dP1dA1A3SaS39S3cS3aN10A1G0S3dP1cA1A3SaS39S3cS3aN8A1G0S3dPbA1A3S13S39A1A3A3A3A3A3A3A3").
  Definition UNCH_H : list sobj := ltac2:(tb__ "0|0|
SaS38S83S7aA1SaS38S84SaS38S80S7aA1SaS38S87S7aA1SaS38S82S13S38A1A3A3A3A3A3").
  Definition CHG_H : list sobj := ltac2:(tb__ "0|0|
SaS38S89S7aS79PafA1Z1A3SaS38Sa9SaS38S81S7aS79PbbA1A2SaS38Sa2SaS38Sa5SaS38Sa6S13S38A1A3A3A3A3A3A3").
  Definition LF_H : sstate := ltac2:(tb__ "0|0|
S10fSd8S10eS110S8aS74S7aS7cA3S10dA2S8dS7cA1A3A1").

  Lemma LF_H_objs : ltac2:(tb__ "0|0|
S3SdS38A1S64S99A1SaS38S7bS9cA1S10S38S97S96A3A3A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma LF_H_misc : ltac2:(tb__ "0|0|
S4S3S0S65S99A1Z20ec8A3S4S3S1S63S99A1S7dA3S4S3SdS3eA1S62S99A1S78A3S4S3S60S61S99A1S4bA3S4S3SeS3eA1S66S99A1S14S3eA1A3S3S3eS44S99ZaA2S79Pb2A1A3A2A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma LF_H_cs : ltac2:(tb__ "0|0|
S0S4S68Z1R1A2S68R1Z1fA2A2S3SfS76S6bR2A1A1S12A3S3S3eS44S99R3A2S77S6bR3A1A1A3F_;F_;Fz;").
  Proof using Hav Hev Hgd.
    intros z Hz Hcs.
    pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv LF_H z) (pre_reg (Z.to_nat z)))%bool 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
    cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX. apply sv_eqb_sound in XX. exact XX.
  Qed.

  Variables (msF : machine_state) (rhoF : valuation).
  Hypothesis HagF : ltac2:(tb__ "0|0|
S52S7dS90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoF;A3").
  Hypothesis HsmF : ltac2:(tb__ "0|0|
S45S74VrhoF;S99ScSdSebA1Sf0Vtr;Sf1VmsF;Vmd;A2A4A4").

  Lemma HromF : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
  Lemma HroF : ro_clear segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.
  Lemma HOF : ltac2:(tb__ "0|0|
SedS38S40S74VrhoF;VmsF;A3SaS38S7bS9cA1S10S38S97S96A3A3A3").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
    rewrite LF_H_objs in Hall. exact Hall.
  Qed.
  Lemma HpdF : ltac2:(tb__ "0|0|
S5cVrhoF;SaS38S7bS9cA1S10S38S97S96A3A3A2").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _). cbn [fst snd cfg_ms] in Hpd.
    rewrite LF_H_objs in Hpd. exact Hpd.
  Qed.
  Lemma HfrF : ltac2:(tb__ "0|0|
Sd3Q40A1S5bVrhoF;SaS38S7bS9cA1S10S38S97S96A3A3R1A3S3SeSd3Q8A1A1S108VmsF;R2A2S42VrhoF;R2A2A3F_;Fa;").
  Proof using HsmF.
    pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
    rewrite LF_H_objs in Hfr. exact Hfr.
  Qed.
  Lemma rmF a : ltac2:(tb__ "0|0|
S3SeSd3Q8A1A1S42VrhoF;Va;A2VmW;Va;A1A3"). Proof using HagF. destruct HagF as (_ & _ & M). rewrite <- M. reflexivity. Qed.

  Lemma F_pc : ms_pc msF = Z_to_bv 64 0x20ec8.
  Proof using HsmF. pose proof HsmF as (_ & Hpc & _). destruct LF_H_misc as (Mpc & _). rewrite Mpc in Hpc. exact Hpc. Qed.
  Lemma F_pend : ms_svc_pending msF = None. Proof using HsmF. exact (proj1 (proj2 (proj2 HsmF))). Qed.
  Lemma F_halt : model_idle md. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 HsmF)))). Qed.
  Lemma F_regs : ltac2:(tb__ "0|0|
S5dVrhoF;S99VmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & Hr & _). exact Hr. Qed.
  Lemma F_fregs : ltac2:(tb__ "0|0|
S56VrhoF;S99VmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & Hf & _). exact Hf. Qed.
  Lemma F_a0 : reg_sv LF_H 10 = v 178. Proof using . destruct LF_H_misc as (_ & _ & _ & _ & _ & Ma0). exact Ma0. Qed.
  Lemma F_fr : ss_fregs LF_H = pre_fregs. Proof using . destruct LF_H_misc as (_ & _ & Mfr & _). exact Mfr. Qed.
  Lemma F_fcsr : ltac2:(tb__ "0|0|
S54VrhoF;S4bVmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & Hc & _). destruct LF_H_misc as (_ & _ & _ & Mfc & _). rewrite Mfc in Hc. exact Hc. Qed.
  Lemma F_resv : ltac2:(tb__ "0|0|
S5eVrhoF;S14S3eA1VmsF;A3").
  Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _). destruct LF_H_misc as (_ & _ & _ & _ & Mrs & _). rewrite Mrs in Hv. exact Hv. Qed.

  Definition mF : word -> option byte := ltac2:(tb__ "0|0|
S11bVrhoF;VmsF;S97S96A4").

  Lemma KU_entry : ltac2:(tb__ "0|0|
SedS38S40S74S90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sf2Vms;VmW;A2A3S97A3").
  Proof using Erd Ewok HMI Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom Htp.
    unfold UNCH_H. constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|].
    constructor; [apply hold_pgsz|]. constructor; [apply hold_errno|]. constructor.
  Qed.
  Lemma KU_leaf : ltac2:(tb__ "0|0|
SedS38S40S74VrhoF;VmsF;A3S97A3").
  Proof using HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [H _]. exact H. Qed.
  Lemma KC_leaf : ltac2:(tb__ "0|0|
SedS38S40S74VrhoF;VmsF;A3S96A3").
  Proof using HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [_ H]. exact H. Qed.
  Lemma Kvars : ltac2:(tb__ "0|0|
S3SfSd7S38S5aS7dA1S10S38S97S96A3A3S12A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Kcov : ltac2:(tb__ "0|0|
S3SfSd7S38S11aS97A3S12A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Klits : ltac2:(tb__ "0|0|
S3SfSd7S38S11cS10S38S97S96A3A3S12A3"). Proof using . vm_compute. reflexivity. Qed.
  Lemma Kdunk : ltac2:(tb__ "0|1|
S3SfSd7S38S38S50SfLx;S59R1A1S12S17S17S1S17Ll;M0G0S0S3eSdS11S0S0A2A1SdS67A1S17Ltmpl;Lflds;Lcnt;Lesz;X50x6Lo;S10S38S97S96A3A3S12A3"). Proof using . reflexivity. Qed.

  Lemma KIT_unch : ltac2:(tb__ "0|2|
S38S0Sd6S38R2S97A3S4S68S15S0S0S3fVrhoF;R3A2M0A3R2A2S6aR2S16S0S0G0A3A2A2S4S3SeSd3Q8A1A1Se3S74S98Sd4Q40R3A2M1A3Se3S74VmW;G1A3A3S3SfSe4S74S98G1A3Se4S74VmW;G1A3A3A2F_;F_;Fx;Fo;").
  Proof using Erd Ewok HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom HsmF Htp. exact (ReabKit.unch_same segsU (rho1 mW) rhoF ms msF mW Hrom HromF UNCH_H CHG_H KU_entry KU_leaf AM_NEXT HagF Kvars Kcov Klits Kdunk). Qed.
  Lemma KIT_chgb : ltac2:(tb__ "0|3|
S38S0Sd6S38R2S96A3S4S68S15S0S0S3fVrhoF;R3A2M0A3R2A2S6aR2S16S0S0G0A3A2A2S4S3SfSe4S74S98Sd4Q40M1R3A2A3S12A3S7Sd3Q8A1M2G2S3SeG2A1Se3S74S98Sd4G1R4A2A3SbG2R1A2A3Lb;A2A2F_;F_;Fx;Fo;").
  Proof using HsmF. exact (ReabKit.chg_byte segsU rhoF msF HromF UNCH_H CHG_H KC_leaf Kdunk). Qed.
  Lemma KIT_chgc : ltac2:(tb__ "0|4|
S38S39S18Sd6S38R3S96A3Sd6S39R3S4fR4A1A3S102R3S6bS49R4A1A1A2S3SeSd3Q8M0A1M1A1Se3S74S98Sd4Q40M2S69S69Sd5G2S3bS90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7M3S4eR6A1A2A2S46G3S4cR5A1A2A2S6cR4A1A2A2A3SbG1SeeG1R4S53S6bS49R5A1A1S3bVrhoF;S4dR5A1A2A2Sd4G0Z0A2A4A2A3F_;F_;F_;Fj;Fc;Fo;").
  Proof using HagF HsmF. exact (ReabKit.chg_cell segsU (rho1 mW) rhoF msF HromF UNCH_H CHG_H KC_leaf AM_NEXT HagF Kvars). Qed.

  Definition xm : mslot := ltac2:(tb__ "0|0|
S1cSbS1aVpH;A2SbS1aVnH;A2A2").
  Definition xp : mslot := ltac2:(tb__ "0|0|
S1cSbS1aVppH;A2SbS1aVmH;A2A2").
  Definition xp' : mslot := ltac2:(tb__ "0|0|
S1cSbS1aVppH;A2SbS1aVnH;A2A2").
  Definition xa : mslot := ltac2:(tb__ "0|0|
S1cSbS1aVmH;A2SbS1aVn2H;A2A2").
  Definition xb : mslot := ltac2:(tb__ "0|0|
S1cSbS1aVpH;A2SbS1aVn2H;A2A2").
  Definition sH : astate := ltac2:(tb__ "0|0|
S112Vs;VmH;SaaVpH;VnH;Sa4Sa3A7").
  Lemma Hxa : ltac2:(tb__ "0|0|
S3SeS1bA1SaeS113Vs;VpH;VnH;Sa4A4VnH;A2SbS1bSa3A2A3").
  Proof using HnH Hpn. unfold s_H23a. rewrite MT_upd_other by exact Hnp. unfold s0. rewrite MT_set_init_done. exact HnH. Qed.
  Lemma SPEC : ltac2:(tb__ "0|0|
S111VX;VR;VU;Vs;ScSeS1aA1S36SbS1aVmH;A2S95A4A5").
  Proof using HI Hhd HmH HnH Hnm HpH Hpm Hpn. exact (am_spec_of_yields X R U s HI [] _ (yields_H23 s mH Hhd xm HmH pH nH eq_refl Hnm Hpm xp HpH xa Hxa)). Qed.
  Lemma HI' : ltac2:(tb__ "0|0|
SbbSaS1aVmH;VX;A3VR;VU;S95A4"). Proof using HI Hhd HmH HnH Hnm HpH Hpm Hpn. exact (proj1 SPEC). Qed.
  Lemma sH_fields : ltac2:(tb__ "0|3|
S4S3SdS1aA1S25S95A1S25Vs;A1A3S4S3SdS37A1S31S95A1S31Vs;A1A3S4S3S1fS2aS95A1S2aVs;A1A3S4S3SfS1eS95A1S12A3S4S3SeS1aA1M0S1dS95A1SbS1aVnH;A2A3S4S3S1aS26S95A1S26Vs;A1A3S4S3S0S29S95A1S29Vs;A1A3S4S3S0S27S95A1S27Vs;A1A3S4S3S0S2bS95A1S2bVs;A1A3S4S3G0S23S95A1S23Vs;A1A3S4S3G0S24S95A1S24Vs;A1A3S4S3S1aS28S95A1S28Vs;A1A3S4S3SdG0A1S2eS95A1S2eVs;A1A3S4S3SdS0A1M1S33S95A1S33Vs;A1A3S4S3G1S32S95A1S32Vs;A1A3S4S3G1S2fS95A1S2fVs;A1A3S4S3S0S2dS95A1S2dVs;A1A3S4S3S0S2cS95A1S2cVs;A1A3S3SdS11S1aS1bA2A1S30S95A1S20S20S20S30Vs;A1VpH;S9fA3VnH;S9eA3VmH;S1cS14S1aA1M2G2A2A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using . unfold sH, s_H23, s_H23b, s_H23a, s0. repeat split; reflexivity. Qed.
  Lemma MT_sH q : ltac2:(tb__ "0|3|
S3SeS1bA1M0SaeS95Vq;A2SfG0L_;M1S22Vq;VmH;A2SbS1bS1cS14S1aA1M2G2A2A2G1S22Vq;VnH;A2SbS1bS9eA2G1S22Vq;VpH;A2SbS1bS9fA2SaeVs;Vq;A2Xfx2Xfx2Xfx2A3").
  Proof using .
    unfold sH, s_H23, s_H23b, s_H23a. destruct (sptr_eqb q mH) eqn:E.
    - apply sptr_eqb_eq in E. subst q. apply MT_upd_same.
    - apply sptr_eqb_neq in E. rewrite MT_upd_other by exact E. rewrite MT_set_free_meta_head.
      destruct (sptr_eqb q nH) eqn:E2.
      + apply sptr_eqb_eq in E2. subst q. rewrite MT_upd_same. reflexivity.
      + apply sptr_eqb_neq in E2. rewrite MT_upd_other by exact E2.
        destruct (sptr_eqb q pH) eqn:E3.
        * apply sptr_eqb_eq in E3. subst q. rewrite MT_upd_same. reflexivity.
        * apply sptr_eqb_neq in E3. rewrite MT_upd_other by exact E3. unfold s0. rewrite MT_set_init_done. reflexivity.
  Qed.
  Lemma HXr' : ltac2:(tb__ "0|0|
S11dSaS1aVmH;VX;A3S95A2").
  Proof using HXr HnH HpH.
    intros q [<-|Hq]; rewrite MT_sH.
    - right. rewrite sptr_eqb_refl. reflexivity.
    - destruct (sptr_eqb q mH) eqn:E; [right; reflexivity|].
      destruct (sptr_eqb q nH) eqn:E2.
      { exfalso. apply sptr_eqb_eq in E2. subst q. destruct (HXr nH Hq) as [H|H]; rewrite HnH in H; discriminate. }
      destruct (sptr_eqb q pH) eqn:E3; [|exact (HXr q Hq)].
      exfalso. apply sptr_eqb_eq in E3. subst q. destruct (HXr pH Hq) as [H|H]; rewrite HpH in H; discriminate.
  Qed.
  Lemma mH_key' : In mH (keys sH). Proof using HI Hhd HmH HnH Hnm HpH Hpm Hpn. exact (proj1 (proj2 (proj2 SPEC))). Qed.
  Lemma D_fp : ltac2:(tb__ "0|0|
S3SdS11SbeS0A2A1SbdS95A1SbdVs;A1A3"). Proof using . reflexivity. Qed.
  Lemma keys_sH : ltac2:(tb__ "0|0|
S3SdS1aA1Sb7S95A1Sb7Vs;A1A3").
  Proof using HmH HnH HpH.
    assert (K0 : keys (s0 s) = keys s) by reflexivity.
    assert (Ka : keys (s_H23a s pH nH xp) = keys s) by (unfold s_H23a; rewrite keys_upd_In by (rewrite K0; exact pH_key); exact K0).
    assert (Kb : keys (s_H23b s pH nH xp xa) = keys s) by (unfold s_H23b; rewrite keys_upd_In by (rewrite Ka; exact nH_key); exact Ka).
    assert (Kt : keys (set_free_meta_head (Some nH) (s_H23b s pH nH xp xa)) = keys s) by (rewrite <- Kb; reflexivity).
    unfold sH, s_H23. rewrite keys_upd_In by (rewrite Kt; exact mH_key). exact Kt.
  Qed.
  Lemma nH_key' : In nH (keys sH).
  Proof using HmH HnH HpH. rewrite keys_sH. exact nH_key. Qed.
  Lemma pH_key' : In pH (keys sH).
  Proof using HmH HnH HpH. rewrite keys_sH. exact pH_key. Qed.
  Lemma D_ub : ltac2:(tb__ "0|0|
S3SdS11S1aS0A2A1SbfS95A1SbfVs;A1A3").
  Proof using HmH HnH Hnm HpH Hpm Hpn.
    unfold sH, s_H23. rewrite uf_user_blocks; [| rewrite MT_set_free_meta_head; unfold s_H23b; rewrite MT_upd_other by exact Hmn; unfold s_H23a; rewrite MT_upd_other by exact Hmp; unfold s0; rewrite MT_set_init_done, HmH; exact I | exact I].
    rewrite (co_user_blocks (s_H23b s pH nH xp xa) (set_free_meta_head (Some nH) (s_H23b s pH nH xp xa)) eq_refl).
    unfold s_H23b. rewrite uf_user_blocks; [| rewrite Hxa; exact I | exact I].
    unfold s_H23a. rewrite uf_user_blocks; [| unfold s0; rewrite MT_set_init_done, HpH; exact I | exact I].
    reflexivity.
  Qed.
  Lemma HL' : layout_ok L sH.
  Proof using HMI. exact HL. Qed.
  Lemma Hbounded' : bounded sH.
  Proof using HMI. pose proof HB as (B1 & B2 & B3). split; [|split]; [intros sc; exact (B1 sc) | exact B2 | exact B3]. Qed.
  Lemma Hvm' : ltac2:(tb__ "0|0|
Se2VL;S95Vvm;A3").
  Proof using HMI. exact HV. Qed.

  Definition C_hd' : mcell := ltac2:(tb__ "0|0|
SadSacSb9A1U8Sb4SbS1aVnH;A2A1A3").

  Lemma ctx_cells_sH c : ltac2:(tb__ "0|0|
Sd6SabVc;Sb2S95A1A3S5Sd6SabVc;Sb2Vs;A1A3S3SabVc;Sa0A3A2F_;").
  Proof using Hinit.
    assert (E : ctx_cells sH = firstn 3 (ctx_cells s) ++ [C_hd'] ++ skipn 4 (ctx_cells s)).
    { unfold sH, s_H23, s_H23b, s_H23a, s0. unfold ctx_cells. cbn -[Z.add Z.mul Z.sub Z.of_nat seq map padd META_SIZE]. rewrite Hinit. reflexivity. }
    rewrite E. intros H. apply in_app_iff in H as [H|H]; [left; rewrite <- (firstn_skipn 3 (ctx_cells s)); apply in_app_iff; left; exact H|].
    apply in_app_iff in H as [H|H].
    - destruct H as [<-|[]]; auto.
    - left. rewrite <- (firstn_skipn 4 (ctx_cells s)). apply in_app_iff. right. exact H.
  Qed.

  Lemma image_sH c : ltac2:(tb__ "0|1|
Sd6SabVc;S10SabSb0S95A1SfaS95A1A3A3S5Sd6SabVc;S10SabSb0Vs;A1SfaVs;A1A3A3S5S3SabVc;Sa0A3S5Sd6SabVc;Sb8VmH;SbS1bS1cS14S1aA1M0G0A2A2A2A3S5Sd6SabVc;Sb8VnH;SbS1bS9eA2A2A3Sd6SabVc;Sb8VpH;SbS1bS9fA2A2A3A2A2A2A2F_;").
  Proof using Hinit HmH HnH Hnm HpH Hpm Hpn.
    set (ta := s_H23a s pH nH xp). set (tb := s_H23b s pH nH xp xa).
    set (t := set_free_meta_head (Some nH) tb).
    assert (Et : sH = upd_meta mH (MFree None None) t) by reflexivity.
    assert (Etb : tb = upd_meta nH xb ta) by reflexivity.
    assert (Eta : ta = upd_meta pH xp' (s0 s)) by reflexivity.
    assert (MTt : MT t mH = Some xm).
    { unfold t. rewrite MT_set_free_meta_head. rewrite Etb. rewrite MT_upd_other by exact Hmn. rewrite Eta. rewrite MT_upd_other by exact Hmp.
      unfold s0. rewrite MT_set_init_done. exact HmH. }
    assert (MTta : MT ta nH = Some xa) by exact Hxa.
    assert (MT0 : MT (s0 s) pH = Some xp) by (unfold s0; rewrite MT_set_init_done; exact HpH).
    intros H. apply in_app_iff in H as [H|H].
    - rewrite Et in H. destruct (uf_image_In t mH (MFree None None) ltac:(rewrite MTt; exact I) I c H) as [Ht|Hq]; [|right; right; left; exact Hq].
      destruct (co_image_In tb t eq_refl eq_refl c Ht) as [Hb|Hc].
      + rewrite Etb in Hb. destruct (uf_image_In ta nH xb ltac:(rewrite MTta; exact I) I c Hb) as [Ha|Hq]; [|right; right; right; left; exact Hq].
        rewrite Eta in Ha. destruct (uf_image_In (s0 s) pH xp' ltac:(rewrite MT0; exact I) I c Ha) as [H0|Hq]; [|right; right; right; right; exact Hq].
        destruct (co_image_In s (s0 s) eq_refl eq_refl c H0) as [Hs|Hc0]; [left; apply in_app_iff; left; exact Hs|].
        assert (Ec0 : ctx_cells (s0 s) = ctx_cells s) by (unfold s0, ctx_cells; cbn -[Z.add Z.mul Z.sub Z.of_nat seq map padd META_SIZE]; rewrite Hinit; reflexivity).
        rewrite Ec0 in Hc0. left. apply in_app_iff. left. unfold image. apply in_app_iff. left. exact Hc0.
      + change (ctx_cells t) with (ctx_cells sH) in Hc.
        destruct (ctx_cells_sH c Hc) as [Hs|E]; [|right; left; exact E]. left. apply in_app_iff. left. unfold image. apply in_app_iff. left. exact Hs.
    - left. apply in_app_iff. right. rewrite Et in H. rewrite (uf_footers t mH (MFree None None) ltac:(rewrite MTt; exact I) I) in H.
      rewrite (co_footers tb t eq_refl) in H. rewrite Etb, (uf_footers ta nH xb ltac:(rewrite MTta; exact I) I) in H.
      rewrite Eta, (uf_footers (s0 s) pH xp' ltac:(rewrite MT0; exact I) I) in H. rewrite (co_footers s (s0 s) eq_refl) in H. exact H.
  Qed.

  Definition SC13 (u : astate) : list mcell := ltac2:(tb__ "0|9|
SaSabSadSacSccA1U8M0SfSb1L_;M1S1eVu;A1M2ScdSafZ0M3A1M4Xfx2A3SaSabSadSacSc7A1U4M5SafSfS0L_;G2Z1G3Xfx2A1A3SaSabSadSacScbA1G5SafS2cVu;A1A1A3SaSabSadSacSb9A1G0Sb4S1dVu;A1A1A3SaSabSadSacSc2A1G0SdS1aA1M6Sb1Lx;S25Vu;A1M7G4S1aG6Sb6S26Vu;A1A1Ll;Ls0;Xdx2A3SaSabSadSacSc5A1G0SafS29Vu;A1A1A3SaSabSadSacSc3A1G0SafS27Vu;A1M8A1A3SaSabSadSacSc8A1G0SafS2bVu;A1A1A3SaSabSadSacSc9A1G0Sb4S23Vu;A1A1A3SaSabSadSacScaA1G0Sb4S24Vu;A1A1A3SaSabSadSacSc4A1G0G1S19G6SfLx;G7S12S1aG6S17Ll;Ls0;Xdx2S6fG8G3A2A2G4Sb6S28Vu;A1A1Xfx2A3SaSabSadSacSbaA1U1SafS2dVu;A1A1A3SaSabSadSacSc6A1G0S1fSb1Lx;S2aVu;A1G4SafN1A1S18S0Sb6S35R2S72S34R1A2A2A1Lp;Lr;X1fx3A3S13SabA1A3A3A3A3A3A3A3A3A3A3A3A3A3").

  Lemma ctx_cells_SC13 u c o : ltac2:(tb__ "0|0|
Sd6SabVc;Sb2Vu;A1A3S3SbeSd0Vc;A1SacVo;A1A3S5S6aVo;Sc1A2S68SbaVo;A2A2Sd6SabVc;Sa8Vu;A1A3F_;F_;F_;").
  Proof using Hav Hev Hgd.
    intros Hin Hloc Ho. unfold ctx_cells in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [exact Hin|]. exfalso.
    unfold CTX_active, CTX_seq, CTX_usage, CTX_unmap_seq, CTX_bounces in *.
    apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
      apply in_map_iff in H1 as (k & E & Hk); subst c; apply in_seq in Hk; cbn [mc_loc] in Hloc; injection Hloc as Hloc; lia.
  Qed.

  Lemma ctx_cell_w8 u c : ltac2:(tb__ "0|0|
Sd6SabVc;Sb2Vu;A1A3S103Sd1Vc;A1U8A2F_;").
  Proof using Hav Hev Hgd.
    intros Hin. unfold ctx_cells in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    { cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn; lia. }
    apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
      apply in_map_iff in H1 as (k & E & Hk); subst c; cbn; lia.
  Qed.

  Definition touched (x : Z) : Prop := ltac2:(tb__ "0|4|
S5S4S68Z5a3d0Vx;A2S6aVx;Z5a3dcA2A2S5S4S68Z5a3e0Vx;A2S6aVx;Z5a420A2A2S5S4S68Z5a768Vx;A2S6aVx;Z5a770A2A2S5S4S68S8fVL;VmH;A2M0Vx;A2S6aVx;S69G0Z28M1A2A2A2S5S4S68S8fVL;VnH;A2M2Vx;A2S6aVx;S69G2G1A2A2A2S4S68S8fVL;VpH;A2M3Vx;A2S6aVx;S69G3G1A2A2A2A2A2A2A2A2").
  Lemma touched_dec x : ltac2:(tb__ "0|1|
S107S9bVx;A1M0S6G0A1A2").
  Proof using . unfold touched. repeat (apply or_dec); apply range_dec. Qed.

  Lemma evF_lit z : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S3bVrhoF;S3aVz;A1A2Sd4G0Vz;A2A3"). Proof using . reflexivity. Qed.
  Lemma evF_v j : ltac2:(tb__ "0|1|
SfbVj;P12cA2S3Sd3Q40A1S3bVrhoF;S79Vj;A1M0A2S3bS90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7G0A2A3F_;").
  Proof using HagF. intros Hj. symmetry. apply (eval_agree AM_NEXT); [exact HagF|]. cbn. unfold AM_NEXT. apply Pos.ltb_lt. exact Hj. Qed.
  Lemma CHG_ranges : ltac2:(tb__ "0|5|
S3SdS11S0S0A2M0A1SefS38G0S3fVrhoF;A1S96A4SaG0ScS0S0Z5a3d0Z5a3dcA4SaG0ScS0S0Z5a3e0Z5a420A4SaG0ScS0S0Z5a768Z5a770A4SaG0ScS0S0S8fVL;VmH;A2M1S69G1Z28M2A2A4SaG0ScS0S0S8fVL;VnH;A2M3S69G3G2A2A4SaG0ScS0S0S8fVL;VpH;A2M4S69G4G2A2A4S13G0A1A3A3A3A3A3A3A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH HnH HpH.
    pose proof mH_R as (Q1 & Q2 & _). top_ranges. pose proof nH_R as (N1 & N2 & _). top_ranges.
    pose proof pH_R as (P1 & P2 & _). top_ranges.
    cbn [map CHG_H]. unfold O_sec, ctxB_F, O_brk, O_mF, O_m, O_nF, O_pF. cbn [am_ctx AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia.
    rewrite (evF_v 178), (evF_v 179), (evF_v 180) by reflexivity. rewrite ev178', ev179', ev180', !u64 by lia. repeat f_equal; lia.
  Qed.
  Lemma UNCH_rangesF : ltac2:(tb__ "0|1|
S3SdS11S0S0A2M0A1SefS38G0S3fVrhoF;A1S97A4SaG0ScS0S0Z28d50Z28d58A4SaG0ScS0S0Z5a338Z5a340A4SaG0ScS0S0Z5a360Z5a368A4SaG0ScS0S0Z5a388Z5a390A4SaG0ScS0S0Z3a02cZ3a030A4S13G0A1A3A3A3A3A3A3").
  Proof using HagF Hav Hev Hgd Htp.
    cbn [map UNCH_H]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno. cbn [am_got am_libc AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia.
    rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (v 173) HagF eq_refl), ev173.
    rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (SVar 24) HagF eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
  Qed.

  Lemma in_ranges_cases x : ltac2:(tb__ "0|1|
S4S68Z0Vx;A2S6aVx;S6eZ2Z40A2A2A2S10cVrhoF;S10S38S97S96A3Sd4Q40Vx;A2A3S5S7S38S38S4Sd6S38R1S97A3S4S68S15S0S0S3fVrhoF;R1A2M0A3Vx;A2S6aVx;S16S0S0G0A3A2A2A2Lo;A2S9bVx;A1A2F_;F_;").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH HnH HpH.
    intros Hx (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho]; [left; exists o; auto|right].
    pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite CHG_ranges in M. unfold touched.
    destruct M as [E|[E|[E|[E|[E|[E|[]]]]]]]; rewrite <- E in RR; cbn [fst snd] in RR; lia.
  Qed.

  Lemma touched_in x : ltac2:(tb__ "0|1|
S9bVx;A1S7S38S38S4Sd6S38R1S96A3S4S68S15S0S0S3fVrhoF;R1A2M0A3Vx;A2S6aVx;S16S0S0G0A3A2A2A2Lo;A2F_;").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH HnH HpH.
    intros T. unfold touched in T.
    assert (M : forall r, In r [(369616, 369628); (369632, 369696); (370536, 370544); (zA mH, zA mH + 40); (zA nH, zA nH + 40); (zA pH, zA pH + 40)] -> exists o, In o CHG_H /\ obj_range rhoF o = r).
    { intros r Hr. rewrite <- CHG_ranges in Hr. apply in_map_iff in Hr as (o & E & Ho). exists o. auto. }
    destruct T as [T|[T|[T|[T|[T|T]]]]].
    - destruct (M (369616, 369628) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (369632, 369696) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (370536, 370544) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (zA mH, zA mH + 40) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (zA nH, zA nH + 40) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
    - destruct (M (zA pH, zA pH + 40) ltac:(cbn; tauto)) as (o & Ho & E). exists o. rewrite E. cbn. auto.
  Qed.

  Let bv1 : byteview := ltac2:(tb__ "0|0|
SdaSe3S74S98A2Se4S74S98A2A2").
  Let rv1 : byteview := ltac2:(tb__ "0|0|
SdaSe3S74S98A2Sd3Q40A1S12L_;A2").
  Let rv0 : byteview := ltac2:(tb__ "0|0|
SdaSe3S74VmW;A2Sd3Q40A1S12L_;A2").

  Theorem V1 : ltac2:(tb__ "0|1|
S0S4S68Z0R1A2S6aR1S6eZ2Z40A2A2A2S6S9bR2A1A1S4S3SeS0A1M0Vbv1;R3A1Vbv0;R3A1A3S3G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
  Proof using Erd Ewok HI HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd HmH HnH HpH Hrom HsmF Htp.
    intros x Hx NT.
    assert (EQ : Glue.rd_of segsU mF (Z_to_bv 64 x) = Glue.rd_of segsU mW (Z_to_bv 64 x) /\ Glue.wok_of segsU mF (Z_to_bv 64 x) = Glue.wok_of segsU mW (Z_to_bv 64 x)).
    { destruct (in_ranges_dec rhoF (UNCH_H ++ CHG_H) (Z_to_bv 64 x)) as [IN|OUT].
      - destruct (in_ranges_cases x Hx IN) as [(o & Ho & RR)|T]; [exact (KIT_unch o x Ho RR) | exfalso; exact (NT T)].
      - unfold mF. unfold Glue.rd_of, Glue.wok_of. rewrite (ReabKit.kit_out rhoF msF UNCH_H CHG_H _ OUT), rmF. auto. }
    destruct EQ as [E1 E2]. unfold bv1, bv0, rv1, rv0, byteview_of. rewrite E1, E2. auto.
  Qed.

  Theorem VM : ltac2:(tb__ "0|0|
S0S4S68Z0R1A2S6aR1S6eZ2Z40A2A2A2S9bR2A1SceVL;S95R3A3S6S3SeS0A1Vbv1;R4A1S14S0A1A3A1F_;F_;F_;Fx;").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH HnH HpH HsmF.
    intros x Hx T _. destruct (touched_in x T) as (o & Ho & RR). destruct (KIT_chgb o x Ho RR) as [W [b Hb]].
    unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [andb]. rewrite W, Hb. discriminate.
  Qed.

  Lemma leaf_cell (oF : sobj) (cF : cell) (lc : loc) (w : nat) (val : sval) (z : Z) : ltac2:(tb__ "0|5|
Sd6S38VoF;S96A3Sd6S39VcF;S4fVoF;A1A3S3S0S49VcF;A1S6cVw;A1M0A3S103Vw;U8A2Sb1OLval;Vval;S0S8Lz0;S1aS8Lp;S0S9Lz0;S8Xb1x4S3S0Sd2VL;Vval;A2Vz;A3S3S0S69Sd5Q40M1S3bS90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7M2S4eVoF;A1A2A2S46G2S4cVcF;A1A2A2Sb3VL;Vlc;A2M3A3S4S68S15S0S0S3fVrhoF;VoF;A2M4A3G3A2S68S69G3G0A2S16S0S0G4A3A2A2S3Sd3G1A1S3bVrhoF;S4dVcF;A1A2Sd4G1Vz;A2A3SbcVL;Vbv1;SadVlc;Vw;Vval;A3A3F_;F_;F_;F_;F_;F_;F_;F_;F_;").
  Proof using HagF Hav Hev Hgd HsmF.
    intros HoF HcF Hw Hw8 Hval Hz Haddr Hrng Hevl. subst z.
    unfold MallocInv.cell_holds. cbn [mc_loc mc_val mc_w].
    assert (BYTE : forall k, (k < w)%nat -> bv1 (loc_addr L lc + Z.of_nat k) = Some (le_byte (sval_num L val) w k)).
    { intros k Hk.
      pose proof (KIT_chgc oF cF k HoF HcF ltac:(rewrite Hw, Nat2Z.id; exact Hk)) as RD. rewrite Haddr, Hw, Nat2Z.id, Hevl in RD.
      rewrite nth_enc_bytes in RD by assumption.
      destruct (KIT_chgb oF (loc_addr L lc + Z.of_nat k) HoF ltac:(lia)) as [W _].
      unfold bv1, byteview_of.
      assert (R64 : 0 <= loc_addr L lc + Z.of_nat k < 2 ^ 64).
      { pose proof (proj1 (Forall_forall _ _) KC_leaf oF HoF) as ((R0 & R1 & _) & _). unfold obj_range, obj_lo_of, obj_hi_of in Hrng, R0, R1. cbn [fst snd] in Hrng. lia. }
      replace ((0 <=? loc_addr L lc + Z.of_nat k) && (loc_addr L lc + Z.of_nat k <? 2 ^ 64))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. rewrite W, RD. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
      change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia. }
    destruct val; try (exact BYTE); destruct Hval.
  Qed.

  Lemma Hctx' : ly_ctx L = 369616. Proof using HMI. exact Hctx. Qed.
  Lemma B_m : ltac2:(tb__ "0|0|
S3S0Sd5Q40S3bS90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S79Pb2A1A2A2S8fVL;VmH;A2A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH. pose proof mH_R as (Q1 & Q2 & _). top_ranges. rewrite ev178'. apply u64. lia. Qed.
  Lemma addr_m d : ltac2:(tb__ "0|0|
S3S0Sb3VL;Sb5S21VmH;Vd;A2A1A2S69S8fVL;VmH;A2Vd;A2A3").
  Proof using Hav Hev Hgd Hhd HmH HnH Hnm HpH Hpm. unfold zA, addr_of, loc_addr. destruct mH; cbn [padd]. lia. Qed.
  Lemma B_n : ltac2:(tb__ "0|0|
S3S0Sd5Q40S3bS90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S79Pb3A1A2A2S8fVL;VnH;A2A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH HnH. pose proof nH_R as (Q1 & Q2 & _). top_ranges. rewrite ev179'. apply u64. lia. Qed.
  Lemma addr_n d : ltac2:(tb__ "0|0|
S3S0Sb3VL;Sb5S21VnH;Vd;A2A1A2S69S8fVL;VnH;A2Vd;A2A3").
  Proof using Hav Hev Hgd HmH HnH Hnm Hpn. unfold zA, addr_of, loc_addr. destruct nH; cbn [padd]. lia. Qed.
  Lemma evF179 : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S3bVrhoF;S79Pb3A1A2Sd4G0S8fVL;VnH;A2A2A3").
  Proof using HagF Hav Hev Hgd Hhd HmH. rewrite (evF_v 179) by reflexivity. apply ev179'. Qed.
  Lemma B_p : ltac2:(tb__ "0|0|
S3S0Sd5Q40S3bS90Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S79Pb4A1A2A2S8fVL;VpH;A2A3").
  Proof using HI HMI Hav Hev Hgd Hhd HmH HpH. pose proof pH_R as (Q1 & Q2 & _). top_ranges. rewrite ev180'. apply u64. lia. Qed.
  Lemma addr_p d : ltac2:(tb__ "0|0|
S3S0Sb3VL;Sb5S21VpH;Vd;A2A1A2S69S8fVL;VpH;A2Vd;A2A3").
  Proof using Hav Hev Hgd HmH HpH Hpm Hpn. unfold zA, addr_of, loc_addr. destruct pH; cbn [padd]. lia. Qed.
  Lemma evF180 : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S3bVrhoF;S79Pb4A1A2Sd4G0S8fVL;VpH;A2A2A3").
  Proof using HagF Hav Hev Hgd Hhd HmH. rewrite (evF_v 180) by reflexivity. apply ev180'. Qed.
  Lemma evF188 : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S3bVrhoF;S79PbcA1A2Sd4G0S8fVL;Vn2H;A2A2A3").
  Proof using HagF Hav Hev Hgd Hhd HmH HnH. rewrite (evF_v 188) by reflexivity. apply ev188'. Qed.
  Lemma evF189 : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S3bVrhoF;S79PbdA1A2Sd4G0S8fVL;VppH;A2A2A3").
  Proof using HagF Hav Hev Hgd Hhd HmH HpH. rewrite (evF_v 189) by reflexivity. apply ev189'. Qed.

  Theorem VIN : ltac2:(tb__ "0|0|
SabSd6SabR1S10SabSb0S95A1SfaS95A1A3A3S105VL;S9bR2A3SbcVL;Vbv1;R3A3F_;F_;Fc;").
  Proof using HI HMI HXr HagF Hav Hev Hgd Hhd Hinit HmH HnH Hnm HpH Hpm Hpn HsmF.
    intros c Hc (k & Hk & T). pose proof Hctx' as HCX.
    destruct sH_fields as (Fa & Fr & Fb & Fi & Fh & Fav & Fcn & Fac & Fsh & Fah & Fat & Far & _).
    pose proof (f_equal (fun l => nth 0 l (0, 0)) CHG_ranges) as CRsec. pose proof (f_equal (fun l => nth 1 l (0, 0)) CHG_ranges) as CRctx.
    pose proof (f_equal (fun l => nth 2 l (0, 0)) CHG_ranges) as CRbrk. pose proof (f_equal (fun l => nth 3 l (0, 0)) CHG_ranges) as CRm.
    pose proof (f_equal (fun l => nth 4 l (0, 0)) CHG_ranges) as CRn. pose proof (f_equal (fun l => nth 5 l (0, 0)) CHG_ranges) as CRp.
    cbn [nth map CHG_H] in CRsec, CRctx, CRbrk, CRm, CRn, CRp.
    assert (CASE : ((369616 <= loc_addr L (mc_loc c) + Z.of_nat k < 369628) \/ (369632 <= loc_addr L (mc_loc c) + Z.of_nat k < 369696)
                    \/ (370536 <= loc_addr L (mc_loc c) + Z.of_nat k < 370544))
                   \/ (zA mH <= loc_addr L (mc_loc c) + Z.of_nat k < zA mH + 40)
                   \/ (zA nH <= loc_addr L (mc_loc c) + Z.of_nat k < zA nH + 40)
                   \/ (zA pH <= loc_addr L (mc_loc c) + Z.of_nat k < zA pH + 40)) by (unfold touched in T; tauto).
    clear T. destruct CASE as [T|[T|[T|T]]].
    4:{
    pose proof (meta_zone (mH :: X) R U sH L HI' HXr' HL' pH c pH_key' Hc ltac:(exists k; split; [exact Hk | unfold META_SIZE; exact T])) as Hm.
    rewrite MT_sH in Hm. replace (sptr_eqb pH mH) with false in Hm by (symmetry; apply sptr_eqb_neq; exact Hpm).
    replace (sptr_eqb pH nH) with false in Hm by (symmetry; apply sptr_eqb_neq; exact Hpn). rewrite sptr_eqb_refl in Hm.
    cbn [meta_slot_cells optr xp'] in Hm.
    unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hm.
    destruct Hm as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst c.
    - apply (leaf_cell O_pF (mkCell (SLit 0) 8 (v 189)) (LMem (padd pH 0)) 8 (VP ppH) (zA ppH)); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_pF c_off]; rewrite B_p, soff_lit_small by lia; rewrite addr_p; lia | rewrite CRp; cbn [fst snd]; rewrite addr_p; lia | cbn [c_val]; exact evF189 ].
    - apply (leaf_cell O_pF (mkCell (SLit 8) 8 (v 179)) (LMem (padd pH 8)) 8 (VP nH) (zA nH)); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_pF c_off]; rewrite B_p, soff_lit_small by lia; rewrite addr_p; lia | rewrite CRp; cbn [fst snd]; rewrite addr_p; lia | cbn [c_val]; exact evF179 ].
    - apply (leaf_cell O_pF (mkCell (SLit 16) 8 (SLit 0)) (LMem (padd pH 16)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_pF c_off]; rewrite B_p, soff_lit_small by lia; rewrite addr_p; lia | rewrite CRp; cbn [fst snd]; rewrite addr_p; lia ].
    - apply (leaf_cell O_pF (mkCell (SLit 24) 4 (SLit 0)) (LMem (padd pH 24)) 4 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_pF c_off]; rewrite B_p, soff_lit_small by lia; rewrite addr_p; lia | rewrite CRp; cbn [fst snd]; rewrite addr_p; lia ].
    - apply (leaf_cell O_pF (mkCell (SLit 28) 4 (SLit 0)) (LMem (padd pH 28)) 4 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_pF c_off]; rewrite B_p, soff_lit_small by lia; rewrite addr_p; lia | rewrite CRp; cbn [fst snd]; rewrite addr_p; lia ].
    - apply (leaf_cell O_pF (mkCell (SLit 32) 8 (SLit 0)) (LMem (padd pH 32)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_pF c_off]; rewrite B_p, soff_lit_small by lia; rewrite addr_p; lia | rewrite CRp; cbn [fst snd]; rewrite addr_p; lia ]. }
    3:{
    pose proof (meta_zone (mH :: X) R U sH L HI' HXr' HL' nH c nH_key' Hc ltac:(exists k; split; [exact Hk | unfold META_SIZE; exact T])) as Hm.
    rewrite MT_sH in Hm. replace (sptr_eqb nH mH) with false in Hm by (symmetry; apply sptr_eqb_neq; exact Hnm). rewrite sptr_eqb_refl in Hm.
    cbn [meta_slot_cells optr xb] in Hm.
    unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hm.
    destruct Hm as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst c.
    - apply (leaf_cell O_nF (mkCell (SLit 0) 8 (v 180)) (LMem (padd nH 0)) 8 (VP pH) (zA pH)); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia | cbn [c_val]; exact evF180 ].
    - apply (leaf_cell O_nF (mkCell (SLit 8) 8 (v 188)) (LMem (padd nH 8)) 8 (VP n2H) (zA n2H)); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia | cbn [c_val]; exact evF188 ].
    - apply (leaf_cell O_nF (mkCell (SLit 16) 8 (SLit 0)) (LMem (padd nH 16)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia ].
    - apply (leaf_cell O_nF (mkCell (SLit 24) 4 (SLit 0)) (LMem (padd nH 24)) 4 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia ].
    - apply (leaf_cell O_nF (mkCell (SLit 28) 4 (SLit 0)) (LMem (padd nH 28)) 4 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia ].
    - apply (leaf_cell O_nF (mkCell (SLit 32) 8 (SLit 0)) (LMem (padd nH 32)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_nF c_off]; rewrite B_n, soff_lit_small by lia; rewrite addr_n; lia | rewrite CRn; cbn [fst snd]; rewrite addr_n; lia ]. }
    2:{
    pose proof (meta_zone (mH :: X) R U sH L HI' HXr' HL' mH c mH_key' Hc ltac:(exists k; split; [exact Hk | unfold META_SIZE; exact T])) as Hm.
    rewrite MT_sH, sptr_eqb_refl in Hm. cbn [meta_slot_cells optr] in Hm.
    unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hm.
    destruct Hm as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst c.
    - apply (leaf_cell O_mF (mkCell (SLit 0) 8 (SLit 0)) (LMem (padd mH 0)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ].
    - apply (leaf_cell O_mF (mkCell (SLit 8) 8 (SLit 0)) (LMem (padd mH 8)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ].
    - apply (leaf_cell O_mF (mkCell (SLit 16) 8 (SLit 0)) (LMem (padd mH 16)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ].
    - apply (leaf_cell O_mF (mkCell (SLit 24) 4 (SLit 0)) (LMem (padd mH 24)) 4 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ].
    - apply (leaf_cell O_mF (mkCell (SLit 28) 4 (SLit 0)) (LMem (padd mH 28)) 4 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ].
    - apply (leaf_cell O_mF (mkCell (SLit 32) 8 (SLit 0)) (LMem (padd mH 32)) 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia;
        [ cbn [ob_base O_mF O_m c_off]; rewrite B_m, soff_lit_small by lia; rewrite addr_m; lia | rewrite CRm; cbn [fst snd]; rewrite addr_m; lia ]. }
    assert (Z3 : exists off n, (0 <= off /\ off + n <= CTX_SIZE) /\ cmeets L c (ly_ctx L + off) n /\
              ((off = 0 /\ n = 12) \/ (off = 16 /\ n = 64) \/ (off = 920 /\ n = 8))).
    { destruct T as [T|[T|T]].
      - exists 0, 12. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | lia]|]. left; auto.
      - exists 16, 64. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | lia]|]. right; left; auto.
      - exists 920, 8. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | lia]|]. right; right; auto. }
    destruct Z3 as (off & n & [Ho1 Ho2] & CM & ZONE).
    destruct (ctx_zone (mH :: X) R U sH L HI' HXr' HL' c off n Hc Ho1 Ho2 CM) as [Hcc (o & Eloc & O1 & O2)].
    pose proof (ctx_cell_w8 sH c Hcc) as W8.
    assert (Ho : o < CTX_active \/ CTX_seq <= o) by (unfold CTX_active, CTX_seq; destruct ZONE as [[-> ->]|[[-> ->]|[-> ->]]]; lia).
    pose proof (ctx_cells_SC13 sH c o Hcc Eloc Ho) as H13.
    unfold SC13 in H13. rewrite Fi, Fh, Fav, Fcn, Fac, Fsh, Fah, Fat, Far, Fa, Fb in H13.
    unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count,
      CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in H13.
    destruct H13 as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn [mc_loc mc_w] in Eloc, O1, O2; injection Eloc as Eo; subst o;
      try (exfalso; clear - O1 O2 ZONE; lia); clear T ZONE O1 O2 CM Ho Ho1 Ho2 W8 Hcc Hc.
    {   apply (leaf_cell (O_sec AM_P (v 175) 1) (mkCell (SLit 8) 8 (v 175)) (LCtx 0) 8 VSec (ly_sec L)); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRsec; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; rewrite ev175; unfold secZ; rewrite Hinit; reflexivity ]. }
    {   apply (leaf_cell (O_sec AM_P (v 175) 1) (mkCell (SLit 16) 4 (SLit 1)) (LCtx 8) 4 (VZ 1) 1); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRsec; cbn [fst snd loc_addr]; rewrite HCX; lia ]. }
    {   apply (leaf_cell ctxB_F (mkCell (SLit 24) 8 (v 179)) (LCtx 16) 8 (optr (Some nH)) (zA nH)); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; exact evF179 ]. }
    {
      apply (leaf_cell ctxB_F (mkCell (SLit 32) 8 (v 176)) (LCtx 24) 8 _ avmZ); try reflexivity; try (cbn; tauto); try lia;
      [ destruct (st_areas s); exact I
      | unfold avmZ; destruct (st_areas s); reflexivity
      | cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev176 ]. }
    {
      apply (leaf_cell ctxB_F (mkCell (SLit 40) 8 (v 181)) (LCtx 32) 8 (VZ (st_avail_meta_count s)) (st_avail_meta_count s)); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev181 ]. }
    {   apply (leaf_cell ctxB_F (mkCell (SLit 48) 8 (v 183)) (LCtx 40) 8 (VZ (st_avail_meta_area_count s)) (st_avail_meta_area_count s)); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev183 ]. }
    {   apply (leaf_cell ctxB_F (mkCell (SLit 56) 8 (v 184)) (LCtx 48) 8 (VZ (st_meta_alloc_shift s)) (st_meta_alloc_shift s)); try reflexivity; try (cbn; tauto); try lia;
      [ cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev184 ]. }
    {   apply (leaf_cell ctxB_F (mkCell (SLit 64) 8 (v 185)) (LCtx 56) 8 (optr (st_area_head s)) (optrZ (st_area_head s))); try reflexivity; try (cbn; tauto); try lia;
      [ destruct (st_area_head s); exact I
      | destruct (st_area_head s); reflexivity
      | cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev185 ]. }
    {   apply (leaf_cell ctxB_F (mkCell (SLit 72) 8 (v 186)) (LCtx 64) 8 (optr (st_area_tail s)) (optrZ (st_area_tail s))); try reflexivity; try (cbn; tauto); try lia;
      [ destruct (st_area_tail s); exact I
      | destruct (st_area_tail s); reflexivity
      | cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev186 ]. }
    {
      apply (leaf_cell ctxB_F (mkCell (SLit 80) 8 (v 177)) (LCtx 72) 8 _ areasZ); try reflexivity; try (cbn; tauto); try lia;
      [ destruct (match st_areas s with [] => true | _ :: _ => false end && (st_avail_meta_area_count s =? 0)); exact I
      | unfold areasZ; destruct (match st_areas s with [] => true | _ :: _ => false end && (st_avail_meta_area_count s =? 0)); reflexivity
      | cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRctx; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev177 ]. }
    {   apply (leaf_cell (O_brk AM_P (v 187)) (mkCell (SLit 928) 8 (v 187)) (LCtx 920) 8 _ brkZ); try reflexivity; try (cbn; tauto); try lia;
      [ destruct (st_brk s); exact I
      | unfold brkZ; destruct (st_brk s); reflexivity
      | cbn [ob_base O_sec O_brk ctxB_F am_ctx AM_P c_off loc_addr]; rewrite B_ctx, soff_lit_small by lia; rewrite HCX; lia
      | rewrite CRbrk; cbn [fst snd loc_addr]; rewrite HCX; lia
      | cbn [c_val]; rewrite evF_v by reflexivity; apply ev187 ]. }
  Qed.

  Theorem OLD : ltac2:(tb__ "0|0|
SabSd6SabR1S10SabSb0S95A1SfaS95A1A3A3S6S105VL;S9bR2A3A1Sd6SabR3S10SabSb0Vs;A1SfaVs;A1A3A3F_;F_;Fc;").
  Proof using HMI Hav Hev Hgd Hhd Hinit HmH HnH Hnm HpH Hpm Hpn.
    intros c Hc NM. pose proof Hctx' as HCX. destruct (image_sH c Hc) as [H|[->|[Hm|Hn]]]; [exact H| | |]; exfalso; apply NM.
    - exists 0%nat. split; [cbn; lia|]. cbn [mc_loc loc_addr C_hd']. rewrite HCX. unfold touched, CTX_free_meta_head. lia.
    - cbn [meta_slot_cells optr] in Hm. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hm.
      destruct Hm as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst c; exists 0%nat; (split; [cbn; lia|]); cbn [mc_loc]; rewrite addr_m; unfold touched; lia.
    - destruct Hn as [Hn|Hp].
      + cbn [meta_slot_cells optr xb] in Hn. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hn.
        destruct Hn as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst c; exists 0%nat; (split; [cbn; lia|]); cbn [mc_loc]; rewrite addr_n; unfold touched; lia.
      + cbn [meta_slot_cells optr xp'] in Hp. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hp.
        destruct Hp as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst c; exists 0%nat; (split; [cbn; lia|]); cbn [mc_loc]; rewrite addr_p; unfold touched; lia.
  Qed.

  Theorem minvI' : ltac2:(tb__ "0|0|
S106Sd9SaS1aVmH;VX;A3VR;VU;Se9S95VL;A2Se3S74S98A2Se4S74S98A2Vvm;A8").
  Proof using Erd Ewok HI HMI HXr HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH HnH Hnm HpH Hpm Hpn Hrom HsmF Htp bv0 rv0.
    unfold MInvI. pose proof Hctx' as HCX. pose proof mH_R as (Q1 & Q2 & Q3 & Q4 & Q5).
    refine (minv_postG C_U (Inv X R U) (Inv (mH :: X) R U) s sH L (Glue.rd_of segsU mW) (Glue.rd_of segsU mF) (Glue.wok_of segsU mW) (Glue.wok_of segsU mF) vm
              HMI0 HI' Hbounded' HL' D_fp D_ub Hvm' touched touched_dec V1 VIN VM OLD _ _ _ statics_in_image_U _ _ _).
    - intros c Hc. exact (cell_spanI (mH :: X) R U sH L HI' HXr' HL' c Hc).
    - intros x Hx. exact (owned_spanI sH L HL' x Hx).
    - intros c Hc. exact (cell_w_posI sH c Hc).
    - intros x T Himg. cbn [mc_img_lo mc_img_hi C_U] in Himg. unfold touched in T. cbn [mc_ctx C_U]. unfold CTX_SIZE.
      pose proof nH_R as (_ & _ & _ & N4 & _). pose proof pH_R as (_ & _ & _ & P4 & _). clear - T Himg Q4 N4 P4. lia.
    - intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
      unfold CTX_SIZE in Hx. clear - Hx. lia.
    - intros Hf. exfalso. destruct sH_fields as (_ & _ & _ & Fi & _). rewrite Fi in Hf. discriminate.
  Qed.

  Definition rw' (j : positive) : word := ltac2:(tb__ "0|2|
SfSd3Q40A1L_;S19S70Z64M0S2Vj;A1M1A2S71G1Z84A2A2S3bVrhoF;S44S99S73G1G0A2A2A2S43Vrho;Vj;A2Xfx2").
  Definition rho' : valuation := ltac2:(tb__ "0|0|
S58S9dS5fVrhoF;A1S98A3").

  Lemma rw'_low j : ltac2:(tb__ "0|0|
SfbVj;P64A2S3Sd3Q40A1S9dVj;A1S43Vrho;Vj;A2A3F_;").
  Proof using Hav Hev Hgd.
    intros Hj. unfold rw'. replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). reflexivity.
  Qed.
  Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
S101S75Vrho;S9aA3").
  Proof using HagF Hav Hev Hgd.
    split; [intros j Hj; cbn [rw rho']; symmetry; apply rw'_low; exact Hj|].
    intros l. cbn [rl rho']. destruct HagF as (_ & HL2 & _). rewrite <- (HL2 l). reflexivity.
  Qed.
  Lemma rwF_low j : ltac2:(tb__ "0|0|
SfbVj;PaaA2S3Sd3Q40A1S43VrhoF;Vj;A2S43Vrho;Vj;A2A3F_;").
  Proof using HagF Hav Hev Hgd.
    intros Hj. destruct HagF as (A & _ & _). rewrite <- (A j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj.
  Qed.

  Lemma pre_reg_cs z : ltac2:(tb__ "0|1|
S4S68Z1Vz;A2S68Vz;Z1fA2A2S3SfS76S6bVz;A1M0A1S12A3S7S1S1S4S3S3eS77G0A1S3dR1A1A3SfbR1P64A2A2Lvv;A2F_;F_;").
  Proof using Hav Hev Hgd.
    intros Hr Hcs.
    pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || match pre_reg (Z.to_nat z) with SVar vv => (vv <? 100)%positive | _ => false end)%bool 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
    cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX.
    destruct (pre_reg (Z.to_nat z)) as [|vv| | | | | |]; try discriminate. apply Pos.ltb_lt in XX. exists vv. auto.
  Qed.
  Lemma reg_sv_ok z : ltac2:(tb__ "0|1|
S4S68Z1Vz;A2S68Vz;Z1fA2A2S3S3eS44Sf3Se5A1Vz;A2SfS3eL_;S76S6bVz;A1M0A1S77G0A1S3dSfcP64SfeG0A1A2A1Xfx2A3F_;").
  Proof using Hav Hev Hgd.
    intros Hz.
    pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_am_ok IEC_U) z)
                   (if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
    apply sv_eqb_sound in H. exact H.
  Qed.
  Lemma freg_sv_ok z : ltac2:(tb__ "0|2|
S4S68Z0M0Vz;A2S68Vz;Z1fA2A2S7S1S1S4S3S3eS55Sf3Se5A1Vz;A2S3dR1A1M1A3S4S3S3eSeeS3eS6bVz;A1S78S3aG0A1A4G1A3S4SfdP3cR1A2SfbR1P64A2A2A2A2Lvv;A2F_;").
  Proof using Hav Hev Hgd.
    intros Hz.
    pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
    unfold freg_sv. change (ss_fregs (L_am_ok IEC_U)) with pre_fregs.
    destruct (nth (Z.to_nat z) pre_fregs (SLit 0)); try discriminate. apply andb_prop in XX as [X1 X2].
    apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. eexists. split; [reflexivity|]. split; [reflexivity|]. lia.
  Qed.

  Lemma rng_m_F : ltac2:(tb__ "0|1|
S3S11S0S0A2S3fVrhoF;Sa2A2ScS0S0S8fVL;VmH;A2M0S69G0Z28A2A4A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH HnH HpH. pose proof (f_equal (fun l => nth 3 l (0, 0)) CHG_ranges) as CRm. cbn [nth map CHG_H] in CRm. exact CRm. Qed.

  Lemma E110 : ltac2:(tb__ "0|1|
S3Sd3Q40M0A1S9dP6eA1Sd4G0S8fVL;VmH;A2A2A3").
  Proof using HagF Hav Hev Hgd Hhd.
    unfold rw'. change ((100 <=? Z.pos 110) && (Z.pos 110 <? 132))%bool with true. change (Z.pos 110 - 100) with 10.
    rewrite F_a0. rewrite (evF_v 178) by reflexivity. apply ev178'.
  Qed.
  Lemma U110 : ltac2:(tb__ "0|0|
S3S0Sd5Q40S9dP6eA1A2S8fVL;VmH;A2A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH. pose proof mH_R as (Q1 & Q2 & _). top_ranges. rewrite E110. apply u64. lia. Qed.

  Lemma EBs : ltac2:(tb__ "0|1|
S3Sd3Q40A1S3bS9aS3dPaA1M0A2S3bVrhoF;G0A2A3").
  Proof using HagF Hav Hev Hgd. cbn [eval rho' rw]. rewrite rw'_low by lia. symmetry. apply rwF_low. lia. Qed.
  Lemma ELs : ltac2:(tb__ "0|0|
S3S0S46S9aS3dS114A1A2S46VrhoF;S3dPfA1A2A3").
  Proof using HagF Hav Hev Hgd. unfold soff, V_DEPTH. cbn [eval rho' rw]. rewrite rw'_low by lia. rewrite (rwF_low 15) by lia. reflexivity. Qed.
  Lemma EQbs : ltac2:(tb__ "0|0|
S3Sd3Q40A1S3bS9aS3dS115A1A2S3bVrhoF;S79Pb2A1A2A3").
  Proof using HagF Hav Hev Hgd Hhd. unfold V_RES. cbn [eval rho' rw]. rewrite E110. rewrite (evF_v 178) by reflexivity. rewrite ev178'. reflexivity. Qed.
  Lemma RSF : ltac2:(tb__ "0|1|
S3S11S0S0A2S3fVrhoF;S7bS9cA1A2ScS0S0S69S94Vrho;A1M0S93Vrho;A1A2G0A4A3").
  Proof using HagF Hav Hev Hgd.
    rewrite (ReabKit.range_ag (rho1 mW) rhoF [O_stk stkF_cells] [] AM_NEXT HagF ltac:(vm_compute; reflexivity) (O_stk stkF_cells) ltac:(left; reflexivity)).
    apply rng_stk.
  Qed.
  Lemma RS' : ltac2:(tb__ "0|1|
S3S11S0S0A2S3fS9aS118Sf8A1A2ScS0S0S69S94Vrho;A1M0S93Vrho;A1A2G0A4A3").
  Proof using HagF Hav Hev Hgd.
    rewrite <- RSF. unfold obj_range, obj_lo_of, obj_hi_of, stack_win, O_stk. cbn [ob_base ob_lo ob_hi]. rewrite EBs, ELs. reflexivity.
  Qed.
  Lemma RQ' : ltac2:(tb__ "0|1|
S3S11S0S0A2S3fS9aSf9A2ScS0S0S8fVL;VmH;A2M0S69G0Z28A2A4A3").
  Proof using HI HMI HagF Hav Hev Hgd Hhd HmH.
    unfold obj_range, obj_lo_of, obj_hi_of, meta_obj0. cbn [ob_base ob_lo ob_hi]. rewrite EQbs. unfold META_SIZE. rewrite !soff_lit_small by lia.
    rewrite (evF_v 178) by reflexivity. pose proof mH_R as (Q1 & Q2 & _).
    top_ranges. rewrite ev178', u64 by lia. f_equal. lia.
  Qed.

  Theorem smatch_ok : ltac2:(tb__ "0|0|
S45S74S9aSf3Se5A1ScSdSebA1Sf0Vtr;Sf1VmsF;Vmd;A2A4A4").
  Proof using EmW HI HMI HagF Hav Hev Hgd Hhd HmH HsmF Hsm_pre Htop.
    pose proof mH_R as (Q1 & Q2 & Q3 & _). top_ranges.
    pose proof stk_facts as (S1 & S2 & S3 & S4). top_ranges.
    unfold smatch. cbn [fst snd cfg_ms cfg_model].
    split; [vm_compute; reflexivity|].
    split; [exact F_pc|].
    split; [exact F_pend|]. split; [exact F_halt|]. split; [exact HromF|]. split; [exact HroF|].
    split.
    {   intros r Hr0. rewrite (F_regs r Hr0).
      assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
      rewrite reg_sv_ok by lia.
      destruct (callee_saved (Z.to_nat (bv_unsigned r))) eqn:CS.
      - destruct (pre_reg_cs (bv_unsigned r) ltac:(lia) CS) as (vv & E & Hv100).
        rewrite (LF_H_cs (bv_unsigned r) ltac:(lia) CS), E.
        cbn [eval rho' rw]. rewrite rw'_low by exact Hv100. first [apply rwF_low | symmetry; apply rwF_low]; lia.
      - cbn [eval rho' rw]. unfold rw'.
        replace ((100 <=? Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r)))) && (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) <? 132))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        replace (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) - 100) with (bv_unsigned r) by lia.
        reflexivity. }
    split.
    {   intros r. rewrite (F_fregs r).
      assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
      destruct (freg_sv_ok (bv_unsigned r) ltac:(lia)) as (vv & E1 & E2 & Hvv). rewrite E1.
      unfold freg_sv. rewrite F_fr, E2.
      cbn [eval rho' rw]. rewrite rw'_low by lia. first [apply rwF_low | symmetry; apply rwF_low]; lia. }
    split; [exact F_fcsr|].
    split; [exact F_resv|].
    split.
    {
      assert (HOS : obj_holds segsU rhoF msF (O_stk stkF_cells)) by (apply (proj1 (Forall_forall _ _) HOF); left; reflexivity).
      assert (HOQ : obj_holds segsU rhoF msF O_mF) by (apply (proj1 (Forall_forall _ _) HOF); right; apply in_app_iff; right; cbn; tauto).
      split; [|split].
      - constructor; [|constructor; [|constructor]].
        + apply obj_holds_drop_cells in HOS.
          destruct HOS as (B1 & B2 & B3 & B4 & B5). unfold stack_win, obj_holds, obj_lo_of, obj_hi_of in *.
          cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
          rewrite EBs, ELs. split; [exact B1|]. split; [exact B2|]. split; [constructor|]. split; [|exact I].
          intros z Hz Hnc. apply B4; [exact Hz|]. intros C. inversion C.
        +
          assert (EB2 : bv_unsigned (eval rhoF (ob_base O_mF)) = bv_unsigned (eval rho' (ob_base meta_obj0))) by (cbn [ob_base O_mF O_m meta_obj0]; rewrite <- EQbs; reflexivity).
          apply (obj_holds_transfer segsU rhoF rho' msF O_mF meta_obj0 AM_NEXT HromF); [vm_compute; reflexivity | | | reflexivity | | left; split; reflexivity | exact HOQ].
          * unfold obj_lo_of. rewrite EB2. cbn [ob_lo O_mF O_m meta_obj0]. rewrite !soffL by reflexivity. reflexivity.
          * unfold obj_hi_of. rewrite EB2. cbn [ob_hi O_mF O_m meta_obj0]. unfold META_SIZE. rewrite !soffL by reflexivity. reflexivity.
          * intros c2 Hc2. exists c2. split; [exact Hc2|].
            unfold cell_abs. rewrite EB2. clear - Hc2.
            unfold meta_obj0, meta_cells0, zero_tail in Hc2. cbn [ob_cells app] in Hc2.
            destruct Hc2 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [c_off c_val c_width eval]; rewrite !soffL by reflexivity; reflexivity.
      - cbn [pairwise_disjoint]. split; [constructor; [|constructor]|split; [constructor|exact I]].
        rewrite RS', RQ'. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
      - intros a Ha. cbn [rm rho'].
        destruct (in_ranges_dec rhoF (UNCH_H ++ CHG_H) a) as [IN|OUT].
        + unfold mF. rewrite (ReabKit.kit_in _ _ _ _ _ IN). reflexivity.
        + unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply HfrF.
          apply Forall_cons_iff in Ha as [HaS _]. cbn zeta in HaS. rewrite RS' in HaS.
          constructor; [cbn zeta; rewrite RSF; exact HaS|].
          apply Forall_app. split.
          -- apply Forall_forall. intros o Ho. cbn zeta. intros RR. apply OUT. exists o. split; [apply in_app_iff; left; exact Ho | exact RR].
          -- apply Forall_forall. intros o Ho. cbn zeta. intros RR. apply OUT. exists o. split; [apply in_app_iff; right; exact Ho | exact RR]. }

    unfold L_am_ok. cbn [ss_facts].
    assert (AGR : forall f, sprop_below NF f = true -> SymState.holds rho f -> SymState.holds rho' f).
    { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho rho' f agree_vals_rho' Hb) Hh). }
    pose proof Hsm_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF0). cbn [ss_facts ContractAM.Pre_am] in HF0.
    unfold F_meta_facts. cbn [app].
    pose proof U110 as U110.
    assert (AR : 0 <= 3 /\ (zA mH =? 0) = false /\ 4096 <= zA mH /\ (zA mH + 40) mod 2 ^ 64 <= 0x7fffff800000
                 /\ 0 <= zA mH < 2 ^ 64 /\ 0 <= 0 < 2 ^ 64 /\ 0 <= 4096 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= 0x7fffff800000 < 2 ^ 64).
    { clear - Q1 Q2 Q3. top_ranges. rewrite Z.eqb_neq. rewrite Z.mod_small by lia. lia. }
    destruct AR as (AR0 & ARnz & AR1 & AR2 & ARq & ARz & AR4k & AR40 & ARc).
    constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. split; [exact AR0|]. rewrite U110. change (2 ^ 3) with 8. exact Q3. }
    constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. unfold branch_taken, bv_eqb. rewrite U110. rewrite (u64 _ ARz).
                   rewrite ARnz. intros X0; discriminate. }
    constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. rewrite U110. rewrite (u64 _ AR4k). exact AR1. }
    constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
                   rewrite U110. top_ranges. unfold META_SIZE. rewrite (u64 _ AR40), (u64 _ ARc). exact AR2. }
    repeat (constructor; [apply AGR; [reflexivity|]; apply (proj1 (Forall_forall _ _) HF0); cbn; tauto|]). constructor.
  Qed.

  Lemma block_vs_ctx b n a : ltac2:(tb__ "0|1|
Sd6S11S0S0A2ScS0S0Vb;Vn;A4SdcVL;Vs;A2A3S4S68Vb;Va;A2S6aVa;S69Vb;Vn;A2A2A2S6S4S68ScfVL;A1M0Va;A2S6aVa;S69G0Sc0A2A2A2A1F_;F_;").
  Proof using HI HMI HXr Hav Hev Hgd.
    intros Hin Ha Hc. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    destruct (user_block_in_group X R U s L HI HXr (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    cbn [fst snd] in B1, B2, B3, B4.
    destruct (group_range X R U s L HI HL C_U vm g am Hu HV HLG) as (G1 & G2 & G3 & G4).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Sp. assert (0 <= stride_of am * i) by nia.
    unfold UNIT, IB in *. lia.
  Qed.
  Lemma block_vs_meta b n a q : ltac2:(tb__ "0|1|
Sd6S11S0S0A2ScS0S0Vb;Vn;A4SdcVL;Vs;A2A3S4S68Vb;Va;A2S6aVa;S69Vb;Vn;A2A2A2Sd6S1aVq;Sb7Vs;A1A3S6S4S68S8fVL;Vq;A2M0Va;A2S6aVa;S69G0Z28A2A2A2A1F_;F_;F_;").
  Proof using HI HMI HXr Hav Hev Hgd.
    intros Hin Ha Hq Hc. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    destruct (user_block_in_group X R U s L HI HXr (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    cbn [fst snd] in B1, B2, B3, B4.
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Sp. assert (0 <= stride_of am * i) by nia.
    pose proof (meta_vs_group X R U s L HI HL q g am (a - addr_of L (am_mem am)) Hq Hu ltac:(unfold UNIT, IB in *; lia)) as M.
    unfold zA, META_SIZE, UNIT, IB in *. lia.
  Qed.

  Theorem kept : ltac2:(tb__ "0|0|
S116S74Sd9Se9Vs;VL;A2Se9S95VL;A2S42Vrho;A1S98A6").
  Proof using EmW HI HMI HXr HagF Hav Hev Hgd Hhd HmH HnH HpH Htp.
    intros a Ha CA _ NE NS. pose proof Hctx' as HCX. pose proof mH_R as (Q1 & Q2 & Q3 & Q4 & Q5).
    destruct (in_ranges_dec rhoF (UNCH_H ++ CHG_H) (Z_to_bv 64 a)) as [IN|OUT].
    2:{ unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). rewrite rmF, EmW. reflexivity. }
    exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia.
    assert (RNG : In (obj_range rhoF o) [(167248, 167256); (369464, 369472); (369504, 369512); (369544, 369552); (237612, 237616)]
                  \/ In (obj_range rhoF o) [(369616, 369628); (369632, 369696); (370536, 370544); (zA mH, zA mH + 40); (zA nH, zA nH + 40); (zA pH, zA pH + 40)]).
    { apply in_app_iff in Ho as [Ho|Ho]; [left; rewrite <- UNCH_rangesF | right; rewrite <- CHG_ranges]; apply in_map; exact Ho. }
    unfold alloc_static, errno_range, mc_errno in NS, NE. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_tp C_U] in NS, NE.
    assert (NCTX : ~ (369616 <= a < 369616 + CTX_SIZE)).
    { intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(_ & H & _)]].
      - top_ranges. unfold CTX_SIZE in Hc. lia.
      - apply (block_vs_ctx b n a); [exact Hin | exact Hr | rewrite HCX; exact Hc].
      - apply H. cbn [mc_ctx C_U]. exact Hc. }
    assert (NM : ~ (zA mH <= a < zA mH + 40)).
    { intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(Hw & _)]].
      - clear - H Hc Q2. cbn [ma_L] in H. top_ranges. lia.
      - exact (block_vs_meta b n a mH Hin Hr mH_key Hc).
      - apply wseg_in_image_U in Hw. rewrite u64 in Hw by lia. cbn [mc_img_lo mc_img_hi C_U] in Hw. clear - Hw Hc Q4. lia. }
    assert (NN : ~ (zA nH <= a < zA nH + 40)).
    { pose proof nH_R as (N1 & N2 & N3 & N4 & N5).
      intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(Hw & _)]].
      - clear - H Hc N2. cbn [ma_L] in H. top_ranges. lia.
      - exact (block_vs_meta b n a nH Hin Hr nH_key Hc).
      - apply wseg_in_image_U in Hw. rewrite u64 in Hw by lia. cbn [mc_img_lo mc_img_hi C_U] in Hw. clear - Hw Hc N4. lia. }
    assert (NP' : ~ (zA pH <= a < zA pH + 40)).
    { pose proof pH_R as (N1 & N2 & N3 & N4 & N5).
      intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(Hw & _)]].
      - clear - H Hc N2. cbn [ma_L] in H. top_ranges. lia.
      - exact (block_vs_meta b n a pH Hin Hr pH_key Hc).
      - apply wseg_in_image_U in Hw. rewrite u64 in Hw by lia. cbn [mc_img_lo mc_img_hi C_U] in Hw. clear - Hw Hc N4. lia. }
    unfold CTX_SIZE in NCTX. clear - RNG RR NS NE NCTX NM NN NP'.
    destruct RNG as [M|M]; repeat (destruct M as [M|M]; [rewrite <- M in RR; cbn [fst snd] in RR; lia|]); destruct M.
  Qed.

  Theorem maps_keptA : ltac2:(tb__ "0|0|
Se7Se9Vs;VL;A2S42Vrho;A1S98A3").
  Proof using EmW HI HMI HagF Hav Hev Hgd Hhd HmH HnH HpH Htp.
    intros k rg Hk Hkd Hl x Hx. cbn [ma_s ma_L] in *. rewrite <- EmW.
    destruct (map_region_where k rg x Hk Hkd Hl Hx) as (R64 & NI & NA & NK). cbn [mc_img_lo mc_img_hi C_U] in NI. pose proof (NK mH mH_key) as NK_mH. pose proof (NK nH nH_key) as NK_nH. pose proof (NK pH pH_key) as NK_pH.
    destruct (in_ranges_dec rhoF (UNCH_H ++ CHG_H) (Z_to_bv 64 x)) as [IN|OUT].
    2:{ unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply rmF. }
    exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia.
    pose proof (in_map (obj_range rhoF) _ _ Ho) as RNG. rewrite map_app, UNCH_rangesF, CHG_ranges in RNG. cbn [app In] in RNG.
    clear - RNG RR NI NK_mH NK_nH NK_pH.
    repeat (destruct RNG as [E|RNG]; [rewrite <- E in RR; cbn [fst snd] in RR; unfold META_SIZE in *; lia|]). destruct RNG.
  Qed.
  Theorem canaryA : ltac2:(tb__ "0|0|
Se6S74Sd9S42Vrho;A1S98A4").
  Proof using EmW Erd Ewok HMI HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hrom HsmF Htp.
    intros x Hx. rewrite <- EmW, !rdG. cbn [mc_chk_guard_got mc_chk_guard C_U] in Hx.
    pose proof (f_equal (fun l => nth 0 l (0, 0)) UNCH_rangesF) as R0. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCH_H] in R0, R1.
    destruct Hx as [Hx|Hx].
    - refine (proj1 (KIT_unch (O_got AM_P) x _ _)); [left; reflexivity | rewrite R0; cbn [fst snd]; lia].
    - refine (proj1 (KIT_unch O_guard x _ _)); [right; left; reflexivity | rewrite R1; cbn [fst snd]; lia].
  Qed.

  Variable Kc : ltac2:(tb__ "0|0|
SdSebA1SecOF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : vm = m_vmmaps md.

  Theorem post_ok_in posts : ltac2:(tb__ "0|0|
Sd6S11S47S100A2ScS47S100Sf3Se5A1Sf5S74Sd9VX;VR;VU;Se9Vs;VL;A2VKc;A7A4Vposts;A3SffS74S75Vrho;Vposts;ScSdSebA1Sf0Vtr;Sf1VmsF;Vmd;A2A4A5F_;").
  Proof using EmW Erd Evm Ewok HI HKc HMI HXr HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH HnH Hnm HpH Hpm Hpn Hrom HsmF Hsm_pre Htop Htp bv0 bv1 rv0 rv1.
    intros HINP.
    destruct SPEC as (HI2 & Hmemb & Hkey & Hraw & Hfr & Hux & Hub).
    exists (L_am_ok IEC_U), (JL_am_ok segsU C_U X R U (mkMA s L) Kc), rho'.
    split; [exact HINP|]. split; [exact agree_vals_rho'|]. split; [exact smatch_ok|].
    cbn [w_tr w_cfg fst snd cfg_model].
    exists (mkMA sH L), mH. cbn [ma_s ma_L].
    split; [cbn [rw rho']; symmetry; exact U110|].
    split; [unfold MInvIR; cbn [rm rho']; rewrite <- Evm; exact minvI'|].
    split.
    {
      destruct sH_fields as (Fa & Fr & Fb & Fi & Fh & Fav & Fc & Fac & Fsh & Fah & Fat & Far & Fact & Fus & Fun & Fbo & Fsq & Fmc & Fmt).
      split; [exact HXr'|]. split; [exact Fi|]. split; [exact Hfr|].
      split; [repeat split; assumption|]. split; [exact Hux|]. split; [exact Hub|].
      split; [|apply layout_extends_refl].
      intros q Hq. cbn [ma_s] in Hq |- *. rewrite keys_sH. exact Hq. }
    split; [exact Hmemb|]. split; [exact Hkey|]. split; [exact kept|]. split; [exact maps_keptA|]. split; [exact canaryA|].
    split; [eexists; exact (yields_H23 s mH Hhd xm HmH pH nH eq_refl Hnm Hpm xp HpH xa Hxa) | exact HKc].
  Qed.
  Theorem post_ok : ltac2:(tb__ "0|0|
SffS74S75Vrho;Sf7S74Sd9Se5VX;VR;VU;Se9Vs;VL;A2VKc;A8ScSdSebA1Sf0Vtr;Sf1VmsF;Vmd;A2A4A5").
  Proof using EmW Erd Evm Ewok HI HKc HMI HXr HagF Hav Hav_rd Hev Hev_rd Hgd Hgd_rd Hhd Hinit HmH HnH Hnm HpH Hpm Hpn Hrom HsmF Hsm_pre Htop Htp bv0 bv1 rv0 rv1. apply post_ok_in. right; left; reflexivity. Qed.
End Head3.

End InstX.

Theorem am_H3_sound : ltac2:(tb__ "0|2|
S10bOF_;SdS1aA1SeS11S1aS0A2A1S0S0F_;SeaSdSebA1SecOF_;F_;S51S117S74R7R2A3S1aS1aS1aS1aS1aS3SeS1aA1S1dSe8R9A1A1SbS1aR5A2A3S6S3S1aR5R6A3A1S6S3S1aR5R7A3A1S6S3S1aR6R7A3A1S3SeS1bA1M0SaeSe8RdA1R9A2SbS1bS1cSbS1aR7A2SbS1aR8A2M1A2A2A3S3G0SaeSe8ReA1R9A2SbS1bS1cSbS1aRaA2SbS1aR6A2A2A2A3S3G0SaeSe8RfA1R9A2SbS1bS1cG1SbS1aRbA2A2A2A3S3SfS1eSe8R10A1A1S12A3S10aS74R15S104S74Sf6S74Sd9R14R13R12R11R10A7Sf4Se5A1RfA4SffS74S75RfSf7S74Sd9Se5R14R13R12R11R10A8A4A4F_;F_;F_;F_;F_;F_;F_;F_;Fn2;Fpp;Fp;Fn;Fm;F_;Frho;FKc;FA;FU;FR;FX;Fok;").
Proof.
  intros ok X R U [s L] Kc rho HOK m nn p pp n2 Hhd Hnm Hpm Hpn HmH HnH HpH Hinit. cbn [ma_s ma_L] in *.
  intros n HQ [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_H3 s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn p pp n2 Hhd Hnm Hpm Hpn HmH HnH HpH Hinit) as ENTRY.

  pose proof (alloc_meta_run_P AE_head3 ok (Kexact tr md) (rho1 s L rho gd evb avb mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN.
  apply (RUN n).
  -
    intros [tr' [msF md']] (Lf & rhoF & HinL & HagF & HsmF & HK). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
    cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
    destruct (Posts_am_P_shape AE_head3) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LF_H) by (unfold LF_H; rewrite EP; reflexivity). rewrite ELF in HsmF.
    apply HQ.
    exact (post_ok s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn p pp n2 Hhd Hnm Hpm Hpn HmH HnH HpH Hinit msF rhoF HagF HsmF Kc HKc eq_refl).
  -
    split; [exact ENTRY | split; reflexivity].
Qed.

Theorem am_H3_ex : ltac2:(tb__ "0|3|
SdS1aA1SeS11S1aS0A2A1S0S0F_;SeaSdSebA1SecOF_;F_;S51SdS11S47S100A2M0A1Sd6G0ScS47S100Sf3Se5A1Sf5S74Sd9R7R6R5R4R3A7A4R1A3S1aS1aS1aS1aS1aS3SeS1aA1S1dSe8RaA1A1SbS1aR5A2A3S6S3S1aR5R6A3A1S6S3S1aR5R7A3A1S6S3S1aR6R7A3A1S3SeS1bA1M1SaeSe8ReA1R9A2SbS1bS1cSbS1aR7A2SbS1aR8A2M2A2A2A3S3G1SaeSe8RfA1R9A2SbS1bS1cSbS1aRaA2SbS1aR6A2A2A2A3S3G1SaeSe8R10A1R9A2SbS1bS1cG2SbS1aRbA2A2A2A3S3SfS1eSe8R11A1A1S12A3S109S74S104S74Sf6S74Sd9R15R14R13R12R11A7Sf4Se5A1R10A4SffS74S75R10RfA4A3F_;F_;F_;F_;F_;F_;F_;F_;Fn2;Fpp;Fp;Fn;Fm;F_;Fposts;Frho;FKc;FA;FU;FR;FX;").
Proof.
  intros X R U [s L] Kc rho posts HINP m nn p pp n2 Hhd Hnm Hpm Hpn HmH HnH HpH Hinit. cbn [ma_s ma_L] in *.
  intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_H3 s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn p pp n2 Hhd Hnm Hpm Hpn HmH HnH HpH Hinit) as ENTRY.

  destruct (alloc_meta_run_ex_P AE_head3 (Kexact tr md) (rho1 s L rho gd evb avb mW) (tr, mkCfg ms md) (conj ENTRY (conj eq_refl eq_refl)))
    as ([tr' [msF md']] & STEPS & Lf & rhoF & HinL & HagF & HsmF & HK).
  exists (tr', mkCfg msF md'). split; [exact STEPS|].
  cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
  cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmF.
  destruct (Posts_am_P_shape AE_head3) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
  assert (ELF : lf_state L0 = LF_H) by (unfold LF_H; rewrite EP; reflexivity). rewrite ELF in HsmF.
  exact (post_ok_in s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop m nn p pp n2 Hhd Hnm Hpm Hpn HmH HnH HpH Hinit msF rhoF HagF HsmF Kc HKc eq_refl posts HINP).
Qed.
