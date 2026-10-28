(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "True"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "sub"; "pow"; "to_nat"; "eqb"; "leb"; "ltb"; "opp"; "mul"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "callee_saved"; "pre_reg"; "pre_fregs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "sv"; "eval"; "cell"; "obj_range"; "rd"; "rw"; "mkCell"; "valuation"; "sstate"; "rm"; "mkObj"; "obj_holds"; "odefault"; "DUnknown"; "SVar"; "smatch"; "ss_objs"; "sv_eqb"; "reg_sv"; "ob_dflt"; "sfcsr"; "SAlu"; "SAluW"; "agree_below"; "ob_base"; "ob_hi"; "ob_lo"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_resv"; "tfact"; "FcsrFrm0"; "SExt"; "c_off"; "c_val"; "c_width"; "enc_bytes"; "mkVal"; "obj_wf"; "rl"; "sv_below"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "bool"; "list"; "option"; "cons"; "pair"; "true"; "Some"; "nat"; "andb"; "false"; "prod"; "None"; "nil"; "fst"; "snd"; "orb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "addr_of"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2.Reabstract"; "NL"; "m'"; "stkL"; "rho'"; "rw'"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "wview"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "wok_of"; "rd_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "frame_ptr"; "le_byte"; "layout"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "L_free"; "J_free_preT"; "Pre_freeI"; "alloc_static"; "JL_free"; "ok_sideK"; "mem_kept_owned"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick"; "N_all"; "zG"; "O_grp"; "rvv"; "zMem"; "zP"; "kv"; "D0"; "S1"; "n"; "sp0"; "zA"; "O_hdr"; "O_meta"; "rw1_changed"; "zEnd"; "zl1"; "zr1"; "InstH"; "O_area"; "O_ctx"; "O_libc"; "O_lock"; "O_sctab"; "O_stk"; "covers_lit"; "in_G_after_block"; "lit_of"; "rho1"; "rsv"; "rw1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "NFM"; "gm_mem_sv"; "@Corelib.Lists.ListDef"; "Forall"; "skipn"; "nth"; "seq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_absorb"; "in_ranges_dec"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "agree_vals"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "ameta"; "frame"; "fr_n"; "am_freed"; "AREA_HDR"; "METAS_PER_AREA"; "META_SIZE"; "am_mem"; "astate"; "padd"; "poff"; "rg_len"; "st_areas"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsCut"; "RsSymJump"; "lf_state"; "set_objs"; "sym_run"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "ma_s"; "MInv"; "mkMA"; "@Stdlib.Lists.List"; "In"; "hd"; "tl"; "forallb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost"; "quick_case"; "free_quick_post";
"@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2"; "LeafP"; "O_hdr'"; "O_meta'"; "in_windows"; "NEWFREED"; "leaf_okb"; "win_byte"; "leaf_objs_okb"; "quick_post_ok"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "add"; "eqb"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "stableJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "cell_eqb"; "@Corelib.Init.Peano"; "le"; "lt"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "drvN"; "JLd_free"; "vm_room"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "sx32"; "zsupported"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast"; "Posts_free_fast_P"; "ff_kind"; "ff_rsv"; "FF_P"; "Pre_free_fast"; "ff_objs_rsv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2.Gap"; "win_byte"; "in_windows"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quickE.TopE"; "J_free_drvST"; "J_free_drvT"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "list_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS"; "JLdS_free"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel"; "frame_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_free_quick2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Section Gap.
Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame) (a : sptr) (k : Z).
Variables (m0 m' : word -> option byte) (vm : VmMaps).

Definition win_byte (x : Z) : option Z := ltac2:(tb__ "0|4|
S7dVL;Vam;Vi;Vfr;A4S0S79VL;Vg;A2S0S4aS4cS0A1L_;M0S10SdR2Z3A2Vx;A2S50S0ZffA2G0S10SdR2Z2M1A2Vx;A2S50S0Z0A2M2G0S10SdR2Z1A2Vx;A2G2G0S52S11SaR1Z1cA2M3Vx;A2S12Vx;SaR1Z20A2A2A2S50S0S6cSaSa8Vam;A1SeG1Vi;A2A2U4SfSdVx;G3A2A1A3A2S55S0A1X4ax2X4ax2X4ax2X4ax2Tzg;Tzp;").

Definition in_windows (x : Z) : Prop := ltac2:(tb__ "0|4|
S7dVL;Vam;Vi;Vfr;A4S0S7cVL;Vam;A2S0S79VL;Vg;A2S0S83VL;Va;A2S0S87VL;Vam;Vi;A3S0S81Vfr;A1S0S6S4SbSdR6Z4M0A2Vx;A2ScVx;R6A2A2S6S4SbR5Vx;A2ScVx;SaR5Z8M1A2A2A2S6S4SbSaR4Z10A2Vx;A2ScVx;SaR4Z28A2A2A2S6S4SbR3Vx;A2ScVx;SaR3G1A2A2A2S6S4SbZ5a3d0M2Vx;A2ScVx;SaG2G1A2A2A2S6S4SbZ5a3c8M3Vx;A2ScVx;SaG3G0A2A2A2S4SbSaR6R1A2Vx;A2ScVx;SaR2Z1A2A2A2A2A2A2A2A2A2Tnn;Tze;Tza;Tzg;Tzm;Tzp;").

Definition quick_post_ok : Prop := ltac2:(tb__ "0|e|
SbcS5aSbdVs;VL;A2M0S6aS16Vm0;A2S69S16Vm0;A2Vvm;A5Sf2Vs;Vg;Vam;Vi;Vfr;A5Sc2Vs;S6bVam;Vi;Vfr;A3Vg;Vam;Vi;Vfr;A6S4SbeSa4Va;Sb1Vs;A1A3S4S4SbZ0M1Vk;A2ScVk;SaaA2A2S3Sa4Vg;SaeVa;SaSa9S14SabVk;A2A2A2A3A2A2S0S4SbG1R1A2ScR1SeZ2Z40A2A2A2S5S4SbS7dVL;Vam;Vi;Vfr;A4M2R2A2ScR2SaG2S81Vfr;A1A2M3A2A2A1S3S4cS0A1M4SebR3A1S55S0A1A3S4S3S4cS47Q8M5A1M6A1M7S6aS16Vm';S49Q40M8R4A2M9A3S6aS16Vm0;G9A3A3S3S4aS69S16Vm';G9A3S69S16Vm0;G9A3A3A2F_;F_;F_;Fx;S0S4SbG2R1A2ScR1G3A2A2S4S3S4aS69S16Vm';S49G8R2A2A3S4fA3S7G6G6S3G7S6aS16Vm';S49G8R3A2MaA3MbS50G6R1A2A3Lb;A2A2F_;Fx;S0S0S3G4SebR2A1S50S0R1A2A3S4S3S4aS69S16Vm';GaA3S4fA3S3G7GbS50G6S49G5R2A2A2A3A2F_;Fb;Fx;S47G8A1S5S4SbG2S48G8R1A2McA2ScGcG3A2A2A1S5SecS48G8R2A2A1A1S5S72S5aS48G8R3A2A2A1S3G7Vm';R4A1Vm0;R4A1A3F_;F_;F_;Fw;S4SbcS5aSbdSc3Vs;Vg;Vam;Vi;A4VL;A2MdS6aS16Vm';A2S69S16Vm';A2Vvm;A5S75S5aG0GdVm0;Vm';A5A2F_;F_;F_;F_;F_;F_;F_;F_;").
End Gap.

Definition quick_post_stmt : Prop := ltac2:(tb__ "0|1|
SadS6dSa4Sa5S0Sa6Sa4S0S47Q40A1S4cS47Q8A1A1F_;M0G0S67SceRbRaR9R8R7R6R5R4R3R2R1AbFvm;Fm';Fm0;Fk;Fa;Ffr;Fi;Fam;Fg;FL;Fs;").

Definition LeafP (k : ff_kind) (r : ff_rsv) : sstate := ltac2:(tb__ "0|0|
Sb6SbfSb2Sb3S80Sb4A2Se5Vk;Vr;A2A3A1").

Lemma Posts_single : ltac2:(tb__ "0|0|
Se6Se7S3S4bSb2A1Se5R2R1A2S4dSb2Sb3Sc6R2R1A2Sb5A2S56Sb2A1A3A3Fr;Fk;").
Proof.
  intros k r. pose proof (Posts_free_fast_P_shape k r) as H. unfold LeafP.
  destruct (Posts_free_fast_P k r) as [|L [|L' t]]; cbn in H; try discriminate.
  cbn [hd]. destruct L as [st rs]. cbn in H |- *. injection H as _ ->. reflexivity.
Qed.

Definition leaf_okb (Lf : sstate) : bool := ltac2:(tb__ "0|2|
S52S52S52S52S52S10S3aVLf;A1Z20738A2Sf0S1dS2eS39VLf;A1S1aA4A2S31S4aLx;S38VLf;A1S4fS1dS53Lv;X31x2A2S4cS1dA1S4aLx;S3bVLf;A1S1dS53Ls;S4fX4cx2A2Sc1S51S51S4aS4aL_;S18R1A1S2eS2fVLf;S15R1A1A2S19R1A1A2S4fX4ax2Lr;S9dU1U1fA2A3A2S4bS1bA1M0S4aLx;S2dVLf;A1S53S1bG0S52S52S52S2eS35R2A1S2bPaA1A2S2eS37R2A1S97P8bA1A2A2S2eS36R2A1S1cZ0A1A2A2S29S4aLx;S30R2A1S4fS53S53S1S53Ll;M1G1S0S1dS4bS54S0S0A2A1S4bS3cA1S53Ltmpl;Lflds;Lcnt;Lesz;X29x6A2Lnl;Lstk;X4bx2A2").

Lemma leaf_ok : ltac2:(tb__ "0|0|
Se6Se7S3S4aScbSc6R2R1A2A1S4fA3Fr;Fk;").
Proof. intros [|] [| | |]; vm_compute; reflexivity. Qed.

Definition NEWFREED : sv := ltac2:(tb__ "0|0|
S33Sd9S3eS4fQ20S2bP86A1A3S33SdbS1cZ1A1S32SdaS2bP82A1S1cZ1fA1A3A3A3").

Definition is_new_cell (t : nat) (c : cell) : bool := ltac2:(tb__ "0|0|
S51S4aLt;Vt;S59Sd5Vc;S23S1cN3A1Z1S1cZffffffffffffffffA1A3A2Sd5Vc;S23S1cN2A1Z2S1cZ0A1A3A2A2S51S51S4aLn;R1S53S51S51S4aLn0;R1Sd5Vc;S23S1cZ1cA1Z4ScaA3A2S51S53Ln1;X51x2Ln0;X51x2Ln;X51x2").

Fixpoint leaf_objs_okb (t : nat) (pre leaf : list sobj) : bool :=
  match pre, leaf with
  | [], [] => true
  | op :: pre', ol :: leaf' =>
      sv_eqb (ob_base op) (ob_base ol) && sv_eqb (ob_lo op) (ob_lo ol) && sv_eqb (ob_hi op) (ob_hi ol)
      && odefault_eqb (ob_dflt op) (ob_dflt ol)
      && forallb (fun c => existsb (cell_eqb c) (ob_cells op) || is_new_cell t c)%bool (ob_cells ol)
      && obj_coveredb ol
      && forallb (fun c => match lit_of (c_off c) with Some _ => (0 <? c_width c) && (c_width c <=? 8) | None => false end)%bool (ob_cells ol)
      && leaf_objs_okb (S t) pre' leaf'
  | _, _ => false
  end.

Lemma leaf_objs_ok : ltac2:(tb__ "0|0|
Sa5Sa6S3S4aScdU0S78R2R1A2Sc0S1bS2dSc6S7eR2A1S7bR2R1A2A2A1A2A3S4fA3Ffr;Fam;").
Proof.
  intros am fr. unfold N_all, kv, rvv.
  destruct (am_maplen am =? 0), (rsv am fr =? 0); [| destruct (rsv am fr <? 5); [|destruct (rsv am fr =? 5)] | | destruct (rsv am fr <? 5); [|destruct (rsv am fr =? 5)]]; vm_compute; reflexivity.
Qed.

Definition O_hdr' : sobj := ltac2:(tb__ "0|3|
S27S97PcA1S1cN4A1M0S1cZ0A1M1S4dS1fS23S1cN2A1Z2G1A3S4dS1fS23S1cN3A1Z1M2S1cZffffffffffffffffA1A3S4dS1fS23G0G2G1A3S56S1fA1A3A3A3S2aA5").
Definition O_meta' : sobj := ltac2:(tb__ "0|3|
S27S97P84A1S1cZ10A1M0S1cZ28A1S4dS1fS23S1cZ1cA1Z4M1ScaA3S4dS1fS23G0Z8M2S32Sd9S99S1cN10A1A3A3S4dS1fS23S1cZ18A1G1S97P85A1A3S4dS1fS23S1cZ20A1G2S97P87A1A3S56S1fA1A3A3A3A3S2aA5").

Lemma NL_shape : ltac2:(tb__ "0|0|
Sa5Sa6S3S4bS1bA1Sc0S1bS2dSc6S7eR2A1S7bR2R1A2A2A1A2S4dS1bSc7S4dS1bS7aS4dS1bSc8S9bS1bU3S78R2R1A2A3A3A3A3A3Ffr;Fam;").
Proof.
  intros am fr. unfold N_all, kv, rvv.
  destruct (am_maplen am =? 0), (rsv am fr =? 0); [| destruct (rsv am fr <? 5); [|destruct (rsv am fr =? 5)] | | destruct (rsv am fr <? 5); [|destruct (rsv am fr =? 5)]]; vm_compute; reflexivity.
Qed.

Lemma lit_obj_bytes_eq : ltac2:(tb__ "0|8|
S4bSefA1S24S64S24S64S1dS0S0S4bS1fA1S0S28RaR9R8S27R5S1cR4A1M0S1cR3A1R2S2aA5A4S28RbR8R7S27R6S1cR5A1G0R3S2aA5A4S3S47Q40M1A1M2S1eRbR7A2S1eR9R7A2A3S9aS1fS1fS3G2S1eRdS40R1A1M3A2S1eRbG3A2A3Lc;R5A3S9aS1fS1fS3S4aS4cS0A1S4aLx;S93S3fR1A1A1S0S52S12Z0S41R2A1M4A2S11G4Z8A2A2Lz;S53X4cx2S4fA3Lc;R6A3SbS13SeZ2Z3eA2M5A1R9A2SbR9G5A2S4SbRbR8A2ScR8RaA2A2S3S4aS91RaR9A2S4fA3S4S3S4cS47Q8A1M6A1M7S21R11S49G1SaS48G1S1eR12ReA2A2RaA2A2A2S21RfS49G1SaS48G1S1eR10ReA2A2RaA2A2A2A3S7G6G6S3G7S21R12S49G1SaS48G1S1eR13RfA2A2RbA2A2A2S50G6R1A2A3Lbyte;A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Foff;Fcs;Fhi;Flo;Fbase;FmsB;FrhoB;FmsA;FrhoA;Fsegs;").
Proof.
  intros segs rhoA msA rhoB msB base lo hi cs off HA HB Eb Ev Hlit Hlo Hhi Hoff Hcov.
  unfold covers_lit in Hcov. apply existsb_exists in Hcov as (c & Hc & Hcc).
  pose proof (proj1 (Forall_forall _ _) Hlit c Hc) as L1. pose proof (proj1 (Forall_forall _ _) Ev c Hc) as V1.
  destruct c as [co cw cv]. cbn [c_off c_width c_val lit_of] in *.
  destruct co as [o| | | | | | |]; try discriminate.
  apply andb_prop in Hcc as [O1 O2]. apply Z.leb_le in O1. apply Z.ltb_lt in O2.
  apply andb_prop in L1 as [W1 W2]. apply Z.ltb_lt in W1. apply Z.leb_le in W2.
  destruct HA as (RA & _ & CA & _). destruct HB as (RB & _ & CB & _).
  unfold obj_lo_of, obj_hi_of in RA, RB. cbn [ob_base ob_lo ob_hi ob_cells] in *.
  rewrite !soff_lit_small in RA, RB by lia.
  pose proof (proj1 (Forall_forall _ _) CA _ Hc) as CHA. pose proof (proj1 (Forall_forall _ _) CB _ Hc) as CHB.
  unfold obj_lo_of, obj_hi_of in CHA, CHB. cbn [ob_lo ob_hi] in CHA, CHB. rewrite !soff_lit_small in CHA, CHB by lia.
  pose proof CHA as (A1 & A2 & _). pose proof CHB as (B1 & B2 & _). cbn [c_off c_width c_val] in A1, A2, B1, B2.
  rewrite !soff_lit_small in A1, A2, B1, B2 by lia.
  pose proof (cell_holds_bytes rhoA base lo hi msA o cw cv CHA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (Z.to_nat (off - o)) ltac:(lia)) as XA.
  pose proof (cell_holds_bytes rhoB base lo hi msB o cw cv CHB ltac:(lia) ltac:(rewrite <- Eb; lia) ltac:(rewrite <- Eb; lia) ltac:(lia) (Z.to_nat (off - o)) ltac:(lia)) as XB.
  rewrite Z2Nat.id in XA, XB by lia.
  replace (bv_unsigned (eval rhoA base) + o + (off - o)) with (bv_unsigned (eval rhoA base) + off) in XA by lia.
  replace (bv_unsigned (eval rhoB base) + o + (off - o)) with (bv_unsigned (eval rhoB base) + off) in XB by lia.
  rewrite XA, XB, V1. split; [reflexivity|]. eexists; reflexivity.
Qed.

Lemma le_byte_mod32 : ltac2:(tb__ "0|1|
S0S51Sd7R1U4M0A2S3S0S6cSe3R3A1G0R2A3S6cR3G0R2A3A3F_;Fj;Fz;").
Proof.
  intros z j Hj. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  unfold sx32. rewrite <- Znumtheory.Zmod_div_mod; [|lia|lia|exists (2 ^ 32); reflexivity].
  rewrite toS_mod_back by lia. reflexivity.
Qed.

Section Reabstract.
Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame).
Variables (rho : valuation) (tr : list event) (ms : machine_state) (md : Model).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S2cS16Vrho;S80S4eS4bS65A1Sc4Vtr;Sc5Vms;Vmd;A2A4A4").
Hypothesis HMI0 : ltac2:(tb__ "0|1|
SbcS5aSbdVs;VL;A2S76S16S26Vrho;A1M0A2S77S16G0A2S68Vmd;A1A5").
Hypothesis HQ : ltac2:(tb__ "0|0|
Sc2Vs;S6bVam;Vi;Vfr;A3Vg;Vam;Vi;Vfr;A6").
Hypothesis HP12 : ltac2:(tb__ "0|0|
S3S0S5bVL;S6bVam;Vi;Vfr;A3A2S48Q40S22Vrho;PcA2A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S3S0Sa7Vfr;A1S48Q40S22Vrho;PdA2A2A3").
Variable m1 : word -> option byte.
Let zp : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S5bVL;S6bVam;Vi;Vfr;A3A2").
Let nn := fr_n fr.
Hypothesis Hout : ltac2:(tb__ "0|2|
S47Q40M0A1S5S4SbVzp;S48G0R1A2M1A2ScG1SaVzp;Vnn;A2A2A2A1S3S4cS47Q8A1A1Vm1;R2A1S26Vrho;R2A2A3F_;Fw;").
Hypothesis Hin : ltac2:(tb__ "0|2|
S47Q40M0A1S4SbVzp;S48G0R1A2M1A2ScG1SaVzp;Vnn;A2A2A2S3S4cS47Q8A1A1Vm1;R2A1S62Vms;R2A2A3F_;Fw;").
Let rhoP : ltac2:(tb__ "0|0|
S24") := ltac2:(tb__ "0|0|
S94VL;Vg;Vam;Vi;Vfr;Vrho;Vm1;A7").
Variable IH : ltac2:(tb__ "0|0|
S8aVs;VL;Vg;Vam;Vi;Vfr;Vrho;Vm1;A8").
Hypothesis Hblk : ltac2:(tb__ "0|3|
S0S4SbVzp;R1A2ScR1SaVzp;Vnn;A2A2A2S4S5S3S4cS47Q8A1M0A1M1S63S16S62Vms;A1S49Q40M2R2A2A3S55G0A1A3A1S7G0G0S3G1S21Vms;S49G2R3A2A2S50G0R1A2A3Lb;A2A2F_;Fx;").
Hypothesis HsmP : ltac2:(tb__ "0|0|
S2cS16VrhoP;Se9Se8S7eVam;A1S7bVam;Vfr;A2A3S4eS4bS65A1Sc4Vtr;Sc5Vms;Vmd;A2A4A4").
Let Lf : ltac2:(tb__ "0|0|
S25") := ltac2:(tb__ "0|0|
Sc6S7eVam;A1S7bVam;Vfr;A2A2").
Variables (rho2 : valuation) (ms' : machine_state).
Hypothesis Hag2 : ltac2:(tb__ "0|0|
S34S98VrhoP;Vrho2;A3").
Hypothesis HsmL : ltac2:(tb__ "0|0|
S2cS16Vrho2;VLf;S4eS4bS65A1Sc4Vtr;Sc5Vms';Vmd;A2A4A4").

Definition NL : list sobj := tl (ss_objs Lf).
Definition stkL : sobj := ltac2:(tb__ "0|0|
SbfS1bS90S2dVLf;A1A3").
Definition m' : word -> option byte := ltac2:(tb__ "0|2|
S47Q40A1Sd8S9eVrho2;S5dR1A3M0S5G0A1M1A2S4cS47Q8A1A1L_;Sa0Vrho2;S5dR1A3G0S62Vms';R2A2L_;G1Vm1;R2A1L_;Xd8x2La;").
Definition rw' (j : positive) : word := ltac2:(tb__ "0|4|
S4aS47Q40A1L_;M0S52S11Z64M1S2Vj;A1M2A2S12G2Z84A2A2S1eVrho2;S2fVLf;SdG2G1A2A2A2G0Sd1Vj;PdM3A2S22Vrho;G3A2S22Vrho2;Vj;A2X4ax2X4ax2").
Definition rho' : valuation := ltac2:(tb__ "0|0|
S43S61S45Vrho;A1S5eA3").

Lemma Lf_ok : ltac2:(tb__ "0|0|
S3S4aScbVLf;A1S4fA3"). Proof using am fr. apply leaf_ok. Qed.

Lemma Lf_objs : ltac2:(tb__ "0|0|
S3S4bS1bA1S2dVLf;A1S4dS1bS5fS5dA3A3").
Proof using .
  pose proof Lf_ok as H. unfold leaf_okb in H. unfold stkL, NL.
  destruct (ss_objs Lf) as [|o t]; [|reflexivity].
  repeat (apply andb_prop in H; destruct H as [H ?]). discriminate.
Qed.

Lemma rw2_low : ltac2:(tb__ "0|0|
S1ScfR1Pc8A2S3S47Q40A1S22Vrho2;R2A2S96VL;Vg;Vam;Vi;Vfr;Vrho;R2A7A3F_;Fj;").
Proof using Hag2. intros j Hj. destruct Hag2 as (A & _ & _). symmetry. exact (A j Hj). Qed.

Lemma rw2_unchanged : ltac2:(tb__ "0|0|
S1ScfR1Pc8A2S3S4aS86R2A1S53A3S3S47Q40A1S22Vrho2;R3A2S22Vrho;R3A2A3F_;F_;Fj;").
Proof using Hag2. intros j Hj Hc. rewrite rw2_low by exact Hj. apply rw1_other. exact Hc. Qed.

Lemma rm2 : ltac2:(tb__ "0|0|
S47Q40A1S3S4cS47Q8A1A1S26Vrho2;R1A2Vm1;R1A1A3Fa;").
Proof using Hag2. intros a. destruct Hag2 as (_ & _ & C). symmetry. exact (C a). Qed.

Lemma rw1_changed_low : ltac2:(tb__ "0|0|
S1ScfR1P64A2S5S3S1R2PdA3A1S3S4aS86R3A1S53A3F_;F_;Fj;").
Proof using nn zp.
  intros j Hj H13. unfold rw1_changed.
  repeat (rewrite (proj2 (Pos.eqb_neq j _)) by lia). reflexivity.
Qed.

Lemma rw'_low : ltac2:(tb__ "0|0|
S1ScfR1P64A2S3S47Q40A1S61R2A1S22Vrho;R2A2A3F_;Fj;").
Proof using Hag2 zp.
  intros j Hj. unfold rw'.
  replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
  destruct (Pos.eqb_spec j 13) as [->|H13]; [reflexivity|].
  apply rw2_unchanged; [lia|]. apply rw1_changed_low; assumption.
Qed.

Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
Sa3S17Vrho;S60A3").
Proof using Hag2 zp. split; [|reflexivity]. intros j Hj. cbn [rw rho']. symmetry. apply rw'_low. exact Hj. Qed.

Lemma pre_reg_callee : ltac2:(tb__ "0|0|
S51S4Sd6U1R1A2Sd6R1U1fA2A2S3S4aS18R2A1S4fA3S7S1S1S4S3S1dS19R4A1S2bR1A1A3S4ScfR1P64A2S5S3S1R1PdA3A1A2A2Lvv;A2F_;F_;Fr;").
Proof using nn zp.
  intros r Hr Hc.
  assert (X : forallb (fun r => negb (callee_saved r) || match pre_reg r with SVar vv => (vv <? 100)%positive && negb (Pos.eqb vv 13) | _ => false end)%bool (seq 1 31) = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) X r ltac:(apply in_seq; lia)) as Y. cbn beta in Y. rewrite Hc in Y. cbn [negb orb] in Y.
  destruct (pre_reg r); try discriminate. apply andb_prop in Y as [Y1 Y2]. apply Pos.ltb_lt in Y1.
  eexists. split; [reflexivity|]. split; [exact Y1|]. intros E. subst. discriminate.
Qed.

Lemma reg_sv_Lfree : ltac2:(tb__ "0|1|
S0S4SbZ1R1A2SbR1Z1fA2A2S3S1dS2fS6fS6eA1R2A2S4aS1dL_;S18SfR2A1M0A1S19G0A1S2bSd0P64Sd2G0A1A2A1X4ax2A3F_;Fz;").
Proof using nn zp.
  intros z Hz.
  pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_free EC_U) z)
                 (if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
  apply sv_eqb_sound in H. exact H.
Qed.

Lemma Lf_callee : ltac2:(tb__ "0|0|
S0S4SbZ1R1A2SbR1Z1fA2A2S3S4aS18SfR2A1A1S4fA3S3S1dS2fVLf;R3A2S19SfR3A1A1A3F_;F_;Fz;").
Proof using nn zp.
  intros z Hz Hc. pose proof Lf_ok as H. unfold leaf_okb in H.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  match goal with [ Hf : forallb _ (seq 1 31) = true |- _ ] =>
    pose proof (proj1 (forallb_forall _ _) Hf (Z.to_nat z) ltac:(apply in_seq; lia)) as X end.
  cbn beta in X. rewrite Hc in X. rewrite Z2Nat.id in X by lia. apply sv_eqb_sound in X. exact X.
Qed.

Lemma Lf_parts : ltac2:(tb__ "0|0|
S4S3S0S3aVLf;A1Z20738A3S4S3S4bS1dA1S39VLf;A1S1aA3S4S3S31S38VLf;A1S3dA3S4S3S4cS1dA1S3bVLf;A1S55S1dA1A3S4S3S1dS35S5fA1S2bPaA1A3S4S3S1dS37S5fA1S97P8bA1A3S4S3S1dS36S5fA1S1cZ0A1A3S3S29S30S5fA1S2aA3A2A2A2A2A2A2A2").
Proof using .
  pose proof Lf_ok as H. unfold leaf_okb in H. rewrite Lf_objs in H.
  apply andb_prop in H as [H Ho]. apply andb_prop in H as [H Hcs]. apply andb_prop in H as [H Hrv].
  apply andb_prop in H as [H Hfc]. apply andb_prop in H as [Hpc Hfr].
  apply andb_prop in Ho as [Ho Hd]. apply andb_prop in Ho as [Ho Hhi]. apply andb_prop in Ho as [Hb Hlo].
  apply Z.eqb_eq in Hpc.
  split; [exact Hpc|].
  split; [apply (list_eqb_sound sv_eqb); [apply sv_eqb_sound | exact Hfr]|].
  split; [destruct (ss_fcsr Lf); [reflexivity|discriminate]|].
  split; [destruct (ss_resv Lf); [discriminate|reflexivity]|].
  split; [apply sv_eqb_sound; exact Hb|].
  split; [apply sv_eqb_sound; exact Hlo|].
  split; [apply sv_eqb_sound; exact Hhi|].
  destruct (ob_dflt stkL); try discriminate. reflexivity.
Qed.

Lemma HsmA : ltac2:(tb__ "0|0|
S2cS16S9fVrho2;S5dVms';A3Sb7VLf;S4dS1bS5fS56S1bA1A3A2S4eS4bS65A1Sc4Vtr;Sc5Vms';Vmd;A2A4A4").
Proof using HsmL. apply (smatch_frame_in segsU rho2 Lf [stkL] NL tr ms' md Lf_objs HsmL). Qed.

Lemma m'_absorb : ltac2:(tb__ "0|0|
S47Q40A1S3S4cS47Q8A1A1S26S9fVrho2;S5dVms';A3R1A2S5eR1A1A3Fa;").
Proof using Hag2. intros a. unfold rho_absorb, m'. cbn [rm]. destruct (in_ranges_dec rho2 NL a); [reflexivity|apply rm2]. Qed.

Theorem smatch_Lfree : ltac2:(tb__ "0|0|
S2cS16S60S6fS6eA1S4eS4bS65A1Sc4Vtr;Sc5Vms';Vmd;A2A4A4").
Proof using Hag2 Hsm HsmL zp.
  pose proof Lf_parts as (Ppc & Pf & Pc & Pv & Pb & Plo & Phi & Pd).
  pose proof HsmL as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  pose proof HsmA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HallA & _ & HfrA) & _).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [vm_compute; reflexivity|].
  split; [rewrite Hpc, Ppc; reflexivity|].
  split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split.
  {   intros r Hr0. rewrite (Hr r Hr0).
    assert (U : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    rewrite reg_sv_Lfree by lia.
    destruct (callee_saved (Z.to_nat (bv_unsigned r))) eqn:C.
    - rewrite (Lf_callee (bv_unsigned r) ltac:(lia) C).
      destruct (pre_reg_callee (Z.to_nat (bv_unsigned r)) ltac:(lia) C) as (vv & E & Hv100 & Hv13). rewrite E.
      cbn [eval rho' rw]. unfold rw'.
      replace ((100 <=? Z.pos vv) && (Z.pos vv <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      rewrite (proj2 (Pos.eqb_neq vv 13)) by exact Hv13. reflexivity.
    - cbn [eval rho' rw]. unfold rw'.
      replace ((100 <=? Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r)))) && (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) <? 132))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      f_equal. f_equal. lia. }
  split.
  {   intros r. rewrite (Hf r). unfold freg_sv. rewrite Pf. change (ss_fregs (L_free EC_U)) with pre_fregs.
    assert (U : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    assert (E : exists vv, nth (Z.to_nat (bv_unsigned r)) pre_fregs (SLit 0) = SVar vv /\ (60 <= vv < 100)%positive).
    { pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
                  ltac:(vm_compute; reflexivity) (bv_unsigned r) ltac:(lia)) as X. cbn beta in X.
      destruct (nth (Z.to_nat (bv_unsigned r)) pre_fregs (SLit 0)); try discriminate. apply andb_prop in X as [X1 X2].
      eexists. split; [reflexivity|]. apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. lia. }
    destruct E as (vv & E & Hvv). rewrite E. cbn [eval rho' rw]. rewrite rw'_low by lia.
    apply rw2_unchanged; [lia|]. apply rw1_changed_low; lia. }
  split; [rewrite Pc in Hc; exact Hc|].
  split; [unfold resv_match in *; rewrite Pv in Hv; exact Hv|].
  split.
  {
    assert (RS : obj_range rho' (stack_win free_stack) = obj_range (rho_absorb rho2 NL ms') stkL).
    { unfold obj_range, obj_lo_of, obj_hi_of, stack_win. rewrite Pb, Plo, Phi. cbn [ob_base ob_lo ob_hi].
      rewrite eval_absorb, !soff_absorb. cbn [eval rho' rw]. unfold soff. cbn [eval rho' rw v].
      rewrite (rw'_low 10) by lia. unfold V_DEPTH. rewrite (rw'_low 15) by lia.
      rewrite (rw2_unchanged 10) by (try lia; reflexivity). rewrite (rw2_low 139) by lia.
      unfold rw1. cbn [Pos.eqb]. reflexivity. }
    split; [|split].
    - constructor; [|constructor].
      pose proof (proj1 (Forall_forall _ _) HallA stkL ltac:(left; reflexivity)) as HO.
      destruct stkL as [sb slo shi scs sd]. cbn [ob_base ob_lo ob_hi ob_dflt] in Pb, Plo, Phi, Pd. subst sb slo shi sd.
      apply obj_holds_drop_cells in HO.

      destruct HO as (B1 & B2 & B3 & B4 & B5). unfold stack_win, obj_holds, obj_lo_of, obj_hi_of in *.
      cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
      assert (EB : eval rho' (SVar 10) = eval (rho_absorb rho2 NL ms') (SVar 10)).
      { rewrite eval_absorb. cbn [eval rho' rw]. rewrite (rw'_low 10) by lia. symmetry. apply rw2_unchanged; [lia|reflexivity]. }
      assert (EL : soff rho' (SVar V_DEPTH) = soff (rho_absorb rho2 NL ms') (v 139)).
      { rewrite soff_absorb. unfold soff. cbn [eval rho' rw v]. unfold V_DEPTH. rewrite (rw'_low 15) by lia. rewrite (rw2_low 139) by lia. unfold rw1. cbn [Pos.eqb]. reflexivity. }
      assert (EH : soff rho' (SLit 0) = soff (rho_absorb rho2 NL ms') (SLit 0)) by (rewrite !soff_lit_small by lia; reflexivity).
      rewrite EB, EL, EH. split; [exact B1|]. split; [exact B2|]. split; [constructor|]. split; [|exact I].
      intros off Hoff Hnc. apply B4; [exact Hoff|]. intros C. inversion C.
    - cbn. split; [constructor|exact I].
    - intros a Ha. rewrite <- m'_absorb. apply HfrA.
      unfold outside_all in *. constructor; [|constructor]. rewrite <- RS. inversion Ha; subst. assumption. }

  apply Forall_forall. intros f Hf0.
  apply (proj1 (holds_agree_vals NF rho rho' f agree_vals_rho' ltac:(revert Hf0; generalize f; apply (proj1 (forallb_forall _ _)); vm_compute; reflexivity))).
  pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF1). exact (proj1 (Forall_forall _ _) HF1 f Hf0).
Qed.

Let zp_ : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S7dVL;Vam;Vi;Vfr;A4").
Let n_ := n fr.

Lemma zp_eq : ltac2:(tb__ "0|0|
S4S3S0Vzp;Vzp_;A3S3S0Vnn;Vn_;A3A2").
Proof using L am fr i. split; reflexivity. Qed.

Lemma ev2 : ltac2:(tb__ "0|0|
S1dS3S4aS46S98R1A2S4fA3S3S47Q40A1S1eVrho2;R2A2S1eVrhoP;R2A2A3F_;Fe;").
Proof using Hag2. intros e He. symmetry. apply (eval_agree NFM rhoP rho2 e Hag2 He). Qed.

Lemma ms_m1 : ltac2:(tb__ "0|1|
S47Q40M0A1ScS48G0R1A2SaS82Vrho;A1S7fVrho;A1A2A2S3S4cS47Q8A1A1S62Vms;R2A2Vm1;R2A1A3F_;Fw;").
Proof using HMI0 HP12 HP13 HQ Hin Hout Hsm n_ zp_.
  intros w Hw.
  destruct (Z_le_dec zp (bv_unsigned w)) as [H1|H1]; [destruct (Z_lt_dec (bv_unsigned w) (zp + nn)) as [H2|H2]|].
  - symmetry. apply Hin. lia.
  - rewrite Hout by lia.
    destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr. apply Hfr.
    cbn [ss_objs S1]. constructor; [|constructor; [|constructor]].
    + unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi eval fst snd].
      unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. unfold V_DEPTH, sp0, D0 in *. lia.
    + rewrite (I_block_range s L g am i fr rho md HMI0 HQ HP12 HP13). cbn [fst snd]. unfold zp, nn in *. lia.
  - rewrite Hout by lia.
    destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr. apply Hfr.
    cbn [ss_objs S1]. constructor; [|constructor; [|constructor]].
    + unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi eval fst snd].
      unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. unfold V_DEPTH, sp0, D0 in *. lia.
    + rewrite (I_block_range s L g am i fr rho md HMI0 HQ HP12 HP13). cbn [fst snd]. unfold zp, nn in *. lia.
Qed.

Let a0 := ih_a _ _ _ _ _ _ _ _ IH.
Let k0 := ih_k _ _ _ _ _ _ _ _ IH.
Let rgm0 := ih_rgm _ _ _ _ _ _ _ _ IH.

Lemma RZ : ltac2:(tb__ "0|c|
S7dVL;Vam;Vi;Vfr;A4S0S7cVL;Vam;A2S0S79VL;Vg;A2S0S83VL;Va0;A2S0S87VL;Vam;Vi;A3S0S4SbZ0M0S81Vfr;A1M1A2S4SbG0S95Vam;Vfr;A2M2A2S4SbZ1000M3R4A2S4SbSaR4Z10M4A2R5A2S4S3S0SaSaR5G1A2G2A2R1A3S4SbSaR1Z4A2M5S5cVL;A1M6A2S4ScG6SeZ2Z2fA2A2S4SbG3R2A2S4SbSaR2G3A2M7G6A2S4S3S0R3SaSaR2Z18A2S14Z28Vk0;A2A2A3S4S4SbG0Vk0;A2ScVk0;Z65A2A2S4S6SbG7SdR4SafSacVam;A1A1A2M8A2SbSaG8Sb0Vrgm0;A1A2M9R2A2A2S4SbG8R4A2S4SbG5G9A2S4S6SbG9Z10000MaA2SbZ5b000MbG8A2A2S4S6SbG7GaA2SbGbR2A2A2S4SbG6SaS82Vrho;A1S7fVrho;A1A2A2SbSaGbG4A2G6A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Tze;Tza;Tzg;Tzm;Tzp;").
Proof using HMI0 HQ IH.
  destruct IH as [a k rgm FFx Lok Har Hmp P12 Hrg HzA0 Hsp0 Hdp Hm1e HEg HEa Hrom0 Hsh]. cbn in a0, k0, rgm0. subst a0 k0 rgm0.
  pose proof (R_all s L g am i fr a k FFx HQ Har Hmp rgm Hrg HzA0) as R.
  pose proof (Zones s L g am i fr a k rho FFx HQ Lok Har Hmp rgm Hrg HzA0 Hsp0 Hdp (m_vmmaps md) (I_MI s L rho md HMI0) HEg HEa Hsh) as ZZ. cbn zeta in ZZ.
  cbn zeta. unfold sti, stl in R. repeat match goal with |- _ /\ _ => split end; try lia.
Qed.

Lemma objsP : ltac2:(tb__ "0|0|
S9aS1bS28S16VrhoP;Vms;A3S78Vam;Vfr;A2A3").
Proof using HsmP.
  pose proof HsmP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
  unfold Pre_free_fast in Hall. cbn [ss_objs] in Hall. rewrite ff_objs_eq in Hall. apply Forall_app in Hall as [_ H]. exact H.
Qed.

Lemma objsL : ltac2:(tb__ "0|0|
S9aS1bS28S16Vrho2;Vms';A3S5dA3").
Proof using HsmL.
  pose proof HsmL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
  rewrite Lf_objs in Hall. inversion Hall; assumption.
Qed.

Lemma NL_def : ltac2:(tb__ "0|0|
S3S4bS1bA1S5dS4dS1bSc7S4dS1bS7aS4dS1bSc8S9bS1bU3S78Vam;Vfr;A2A3A3A3A3A3").
Proof using . unfold NL, Lf. apply NL_shape. Qed.

Lemma N_all_def : ltac2:(tb__ "0|1|
S3S4bS1bA1S78Vam;Vfr;A2M0S4dS1bS84S4dS1bS7aS4dS1bS85S9bS1bU3G0A3A3A3A3A3").
Proof using . reflexivity. Qed.

Lemma evP : ltac2:(tb__ "0|0|
S1dS3S4aSe4R1A1S4fA3S3S0S48Q40S1eVrhoP;R2A2A2Se2S89VL;Vg;Vam;Vi;Vfr;Vrho;A6S88VL;Vg;Vam;Vi;Vfr;Vrho;A6R2A3A3F_;Fe;").
Proof using m1. intros e He. unfold rhoP. apply ev1u. exact He. Qed.

Lemma HromP0 : rom_ok segsU ms. Proof using HsmP. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmP))))). Qed.
Lemma HromL : rom_ok segsU ms'. Proof using HsmL. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmL))))). Qed.
Lemma HroL : ro_clear segsU ms'. Proof using HsmL. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmL)))))). Qed.

Ltac openIH := destruct IH as [a k rgm FFx Lok Har Hmp P12 Hrg HzA0 Hsp0 Hdp Hm1e HEg HEa Hrom0 Hsh]; cbn [ih_a ih_k ih_rgm] in *.

Lemma W_rng : ltac2:(tb__ "0|d|
S4S3S54S0S0A2M0S20VrhoP;S84A2S4eS0S0SaVzp_;N4A2SaVzp_;Z0M1A2A4A3S4S3G0S20VrhoP;S7aA2S4eS0S0SaSaS7cVL;Vam;A2Z10M2A2M3N10A2SaG3N8A2A4A3S4S3G0S20VrhoP;S85A2S4eS0S0SaS79VL;Vg;A2M4G2A2SaG4Z28A2A4A3S4S3G0S20VrhoP;S8bA2S4eS0S0SaS83VL;Va0;A2M5G1A2SaG5Z8M6A2A4A3S4S9aS1bS1bS92VL;Vam;Vi;Vfr;S20VrhoP;R1A2M7A5Lo;SeaS7bVam;Vfr;A2A1A3S4S9aS1bS1bS4SbS58S0S0G7A3M8S5cVL;A1A2SbS57S0S0G7A3G8A2A2Lo;S78Vam;Vfr;A2A3S4S3G0S20VrhoP;S8cA2S4eS0S0SaZ5a3d0M9G1A2SaG9G6A2A4A3S4S3G0S20VrhoP;S8dA2S4eS0S0SaZ5a35bMaG1A2SaGaZ1A2A4A3S4S3G0S20VrhoP;S8eA2S4eS0S0SaZ5a3c8MbG1A2SaGbZ4A2A4A3S3G0S20VrhoP;S8fA2S4eS0S0SaZ108ecMcG1A2SaGcZ60A2A4A3A2A2A2A2A2A2A2A2A2").
Proof using HMI0 HQ IH.
  unfold rhoP, a0. openIH.
  split; [exact (rng_hdr s L g am i fr a k rho FFx HQ Har Hmp P12 rgm Hrg HzA0 m1)|].
  split; [exact (rng_grp s L g am i fr a k rho FFx HQ Har Hmp P12 rgm Hrg HzA0 m1)|].
  split; [exact (rng_meta s L g am i fr a k rho FFx HQ Har Hmp rgm Hrg HzA0 m1)|].
  split; [exact (rng_area s L g am i fr a k rho FFx HQ Har Hmp rgm Hrg HzA0 m1)|].
  split; [exact (proj1 (rng_rsv s L g am i fr a k rho FFx HQ Har Hmp P12 rgm Hrg HzA0 Hsp0 m1))|].
  split; [exact (N_all_low s L g am i fr a k rho FFx HQ Lok Har Hmp P12 rgm Hrg HzA0 Hsp0 Hdp (m_vmmaps md) (I_MI s L rho md HMI0) m1 HEg HEa Hsh)|].
  split; [apply rng_ctx|]. split; [apply rng_libc|]. split; [apply rng_lock|]. apply rng_sctab.
Qed.

Lemma W_ze : ltac2:(tb__ "0|1|
S1dS6S4S3S1dR1S97PcA1A3S3S0Se2S89VL;Vg;Vam;Vi;Vfr;Vrho;A6S88VL;Vg;Vam;Vi;Vfr;Vrho;A6R1A3M0Vzp_;A3A2S6S4S3S1dR1S97P84A1A3S3S0G0S79VL;Vg;A2A3A2S4S3S1dR1S99A3S3S0G0SaS7cVL;Vam;A2Z10A2A3A2A2A2S8F_;Fe;").
Proof using . intros; exact I. Qed.

Lemma b12 : ltac2:(tb__ "0|2|
S4S3S0S48Q40M0S1eVrho2;S97PcA1M1A2A2Vzp_;A3S3S0S48G0S1eVrhoP;G1A2A2Vzp_;A3A2").
Proof using HQ Hag2 IH. openIH. rewrite ev2 by reflexivity. rewrite evP by reflexivity. rewrite (ze12 s L g am i fr a k rho FFx HQ Har Hmp P12 rgm Hrg HzA0). auto. Qed.
Lemma b132 : ltac2:(tb__ "0|3|
S4S3S0S48Q40M0S1eVrho2;S97P84A1M1A2A2S79VL;Vg;A2M2A3S3S0S48G0S1eVrhoP;G1A2A2G2A3A2").
Proof using HQ Hag2 IH. openIH. rewrite ev2 by reflexivity. rewrite evP by reflexivity. rewrite (ze132 s L g am i fr a k rho FFx HQ Har Hmp rgm Hrg HzA0). auto. Qed.
Lemma bmem : ltac2:(tb__ "0|2|
S4S3S0S48Q40M0S1eVrho2;S99A2A2SaS7cVL;Vam;A2Z10A2M1A3S3S0S48G0S1eVrhoP;S99A2A2G1A3A2").
Proof using HQ Hag2 IH. openIH. rewrite ev2 by reflexivity. rewrite evP by reflexivity. rewrite (ze_mem s L g am i fr a k rho FFx HQ Har Hmp P12 rgm Hrg HzA0). auto. Qed.

Lemma cell_byte : ltac2:(tb__ "0|7|
S24S64S1dS0S0S4bS1fA1S29S0S0S1dS51S28S16RbRaS27R9S1cR8A1S1cR7A1R6R5A5A4SbeS1fS23S1cR5A1R4R3A3R7A3S4SbS13SeZ2Z3eA2M0A1M1RaA2SbRaG0A2A2M2G2S4SbG1R8A2SbR8G0A2A2SbZ0M3R8A2Sd7R7SfR9A1A2S3S4cS47Q8M4A1M5A1S21R11S49Q40M6SaSaS48G6S1eR12R10A2A2RbA2S15R8A1A2A2A2S50G5S9cG5R8S42SfRaA1S1eR12R9A2A2S49G4G3A2A4A2A3F_;F_;F_;F_;F_;F_;F_;Fj;Fval;Fk;Foff;Fd;Fcs;Fhi;Flo;Fbase;FmsX;FrhoX;").
Proof using k0 n_ nn zp zp_.
  intros rhoX msX base lo hi cs d off k val j (Hb & _ & Hc & _) Hcin Hlo Hhi Hoff Hk Hj.
  unfold obj_lo_of, obj_hi_of in Hb, Hc. cbn [ob_base ob_lo ob_hi ob_cells] in Hb, Hc. rewrite !soff_lit_small in Hb, Hc by lia.
  pose proof (proj1 (Forall_forall _ _) Hc _ Hcin) as CH.
  pose proof CH as (C1 & C2 & _). cbn [c_off c_width] in C1, C2. rewrite soff_lit_small in C1, C2 by lia.
  apply (cell_holds_bytes rhoX base lo hi msX off k val CH); lia.
Qed.

Lemma obj_wview : ltac2:(tb__ "0|5|
S24S64S1dS0S0S4bS1fA1S0S28S16R7R6S27R5S1cR4A1S1cR3A1R2S2aA5A4S4SbS13SeZ2Z3eA2M0A1R5A2SbR5G0A2A2M1G1S4SbSaS48Q40M2S1eRaR8A2A2M3R7A2R4A2ScR4SaG3R6A2A2A2S5S3S4cS47Q8A1M4A1S63S16S62RaA1S49G2R5A2A3S55G4A1A3A1F_;F_;F_;F_;Fx;Fcs;Fhi;Flo;Fbase;FmsX;FrhoX;").
Proof using k0 n_ nn zp zp_.
  intros rhoX msX base lo hi cs x (Hb & Hw & _) Hlo Hhi Hx.
  unfold obj_lo_of, obj_hi_of in Hb, Hw. cbn [ob_base ob_lo ob_hi ob_dflt] in Hb, Hw. rewrite !soff_lit_small in Hb, Hw by lia.
  specialize (Hw (x - bv_unsigned (eval rhoX base)) ltac:(lia) eq_refl).
  replace (bv_unsigned (eval rhoX base) + (x - bv_unsigned (eval rhoX base))) with x in Hw by lia. exact Hw.
Qed.

Lemma wok_of_mem : ltac2:(tb__ "0|3|
S47Q40A1M0S4cS47Q8A1A1M1F_;M2G2G0S3G1R3R1A1R2R1A1A3S3S4aS69S16R4R2A3S69S16R3R2A3A3F_;Fw;Fmm;Fm;").
Proof using . intros m mm w E. unfold Glue.wok_of. rewrite E. reflexivity. Qed.

Lemma Hag2s : ltac2:(tb__ "0|0|
S34S98Vrho2;VrhoP;A3").
Proof using Hag2. destruct Hag2 as (A & B & C). split; [|split]; intros; symmetry; auto. Qed.

Lemma NL_wf : ltac2:(tb__ "0|0|
S9aS1bS1bS3S4aS44S98R1A2S4fA3Lo;S5dA3").
Proof using HsmL.
  pose proof (smatch_swf segsU _ _ _ HsmL) as W. apply swf_objs in W. rewrite Lf_objs in W.
  cbn [forallb] in W. apply andb_prop in W as [_ W].
  replace (ss_next Lf) with NFM in W.
  2:{ unfold Lf, LeafP, kv, rvv. destruct (am_maplen am =? 0), (rsv am fr =? 0); [| destruct (rsv am fr <? 5); [|destruct (rsv am fr =? 5)] | | destruct (rsv am fr <? 5); [|destruct (rsv am fr =? 5)]]; vm_compute; reflexivity. }
  apply Forall_forall. exact (proj1 (forallb_forall _ _) W).
Qed.

Lemma objsL' : ltac2:(tb__ "0|0|
S9aS1bS28S16VrhoP;Vms';A3S5dA3").
Proof using Hag2 HsmL.
  apply Forall_forall. intros o Ho. apply (obj_holds_agree segsU NFM rho2 rhoP ms' o Hag2s).
  - exact (proj1 (Forall_forall _ _) NL_wf o Ho).
  - exact (proj1 (Forall_forall _ _) objsL o Ho).
Qed.

Lemma in_ranges_P : ltac2:(tb__ "0|0|
S47Q40A1S9S9eVrho2;S5dR1A3S9eVrhoP;S5dR1A3A2Fw;").
Proof using Hag2 HsmL.
  intros w. unfold in_ranges. split; intros (o & Ho & R); exists o; split; [exact Ho| |exact Ho|];
    [rewrite <- (obj_range_agree NFM rhoP rho2 o Hag2) | rewrite (obj_range_agree NFM rhoP rho2 o Hag2)]; try exact R;
    exact (proj1 (Forall_forall _ _) NL_wf o Ho).
Qed.

Lemma rngP_lit : ltac2:(tb__ "0|2|
S1dS0S0S4bS1fA1S29S0S4SbS13SeZ2Z3eA2M0A1R5A2SbR5G0A2A2M1G1S3S0S48Q40S1eVrhoP;R8A2A2R3A3S3S54S0S0A2S20VrhoP;S27R9S1cR8A1S1cR7A1R6R5A5A2S4eS0S0SaR4R8A2SaR4R7A2A4A3F_;F_;F_;Fb;Fd;Fcs;Fhi;Flo;Fbase;").
Proof using L am fr g i m1 rho. intros. unfold rhoP. apply rng_lit; assumption. Qed.

Lemma rng_hdr' : ltac2:(tb__ "0|0|
S3S54S0S0A2S20VrhoP;Sc7A2S4eS0S0SaVzp_;N4A2SaVzp_;Z0A2A4A3").
Proof using HQ Hag2 k0 n_ nn zp. apply rngP_lit; try lia. apply b12. Qed.
Lemma rng_meta' : ltac2:(tb__ "0|1|
S3S54S0S0A2S20VrhoP;Sc8A2S4eS0S0SaS79VL;Vg;A2M0Z10A2SaG0Z28A2A4A3").
Proof using HQ Hag2 k0 n_ nn zp zp_. apply rngP_lit; try lia. apply b132. Qed.

Lemma N_all_zone : ltac2:(tb__ "0|3|
S1bSbeS1bR1S78Vam;Vfr;A2A3S20VrhoP;R2A2S54S0S0A2S4SbS58S0S0R1A3M0S5cVL;A1A2S4SbS57S0S0R1A3G0A2S4S0S4SbS57S0S0R2A3R1A2ScR1S58S0S0R2A3A2A2M1S5S4SbVzp_;R2A2ScR2SaVzp_;Vn_;A2A2A2A1F_;Fx;S0G1S6Sc9VL;Vg;Vam;Vi;Vfr;Va0;R2A7S6S72S5aR2A2S4SbZ108ecM2R2A2ScR2SaG2Z60A2A2A2A2A2F_;Fx;A2A2A2Tr;F_;Fo;").
Proof using HMI0 HQ k0 rgm0.
  intros o Ho. pose proof RZ as R. cbn zeta in R. pose proof W_rng as (Rh & Rg & Rm & Ra & GR & LOW & Rc & Rl & Rk & Rs).
  pose proof (proj1 (Forall_forall _ _) LOW o Ho) as [L1 L2]. split; [exact L1|]. split; [exact L2|].
  unfold N_all, N_common in Ho. cbn [app] in Ho.
  unfold in_windows, alloc_static. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_replaced C_U]. unfold zp_, n_ in *.
  destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|Ho]]]]]]];
    rewrite ?Rh, ?Rg, ?Rm, ?Ra, ?Rc, ?Rl, ?Rk; cbn [fst snd]; try (split; intros x Hx; lia).
  apply in_app_iff in Ho. destruct Ho as [Ho|[<-|[]]].
  - pose proof (proj1 (Forall_forall _ _) GR o Ho) as G. unfold in_G_after_block in G. split; intros x Hx; lia.
  - rewrite Rs. cbn [fst snd]. split; intros x Hx; lia.
Qed.

Lemma rest_bytes : ltac2:(tb__ "0|a|
S1bSbeS1bR1S4dS1bS7aS9bS1bU3S78Vam;Vfr;A2A3A3A3S29OLx;S30R2A1S0S4SbS57S0S0S20VrhoP;R3A2M0A3R1A2ScR1S58S0S0G0A3A2A2S4S3S4cS47Q8A1M1A1M2S21Vms';S49Q40M3R2A2M4A2S21Vms;G4A2A3S4S7G1G1S3G2S21Vms';S49G3R3A2A2S50G1R1A2A3Lb;A2S4S5S3G2S63S16S62Vms';A1G4A3S55G1A1M5A3A1S5S3G2S63S16S62Vms;A1G4A3G5A3A1A2A2A2M6F_;Fx;M7G7G7S1S0S4SbS57S0S0S20VrhoP;R4A2M8A3R1A2ScR1S58S0S0G8A3A2A2G6F_;Fx;Ll;S1S8Ll;S0S1dS4bS54S0S0A2A1S4bS3cA1S0S4SbS57S0S0S20VrhoP;R7A2M9A3R1A2ScR1S58S0S0G9A3A2A2G6F_;Fx;Ltmpl;Lflds;Lcnt;Lesz;X29x6F_;Fo;").
Proof using Hag2 HsmL HsmP k0 zp zp_.
  intros o Ho.
  pose proof (proj1 (forallb_forall _ _) (N_rest_covered am fr) o Ho) as C. cbn beta in C.
  assert (HoL : In o NL) by (rewrite NL_def; cbn; destruct Ho as [<-|Ho]; [tauto|]; right; right; right; exact Ho).
  assert (HoP : In o (N_all am fr)) by (rewrite N_all_def; cbn; destruct Ho as [<-|Ho]; [tauto|]; right; right; right; exact Ho).
  pose proof (proj1 (Forall_forall _ _) objsL' o HoL) as OL. pose proof (proj1 (Forall_forall _ _) objsP o HoP) as OP.
  destruct o as [ob olo ohi ocs od]. cbn [ob_dflt ob_lo ob_hi ob_cells] in *.
  destruct od; try exact I; try discriminate.
  apply andb_prop in C as [Ccov Clit]. unfold obj_coveredb in Ccov. cbn [ob_dflt ob_lo ob_hi ob_cells] in Ccov.
  destruct olo as [lo| | | | | | |]; try discriminate. destruct ohi as [hi| | | | | | |]; try discriminate. cbn [lit_of] in Ccov.
  intros x Hx.
  pose proof OL as (RL & _). pose proof OP as (RP & _). unfold obj_lo_of, obj_hi_of in RL, RP. cbn [ob_base ob_lo ob_hi] in RL, RP.
  assert (Hlohi : - 2 ^ 62 <= lo <= 2 ^ 62 /\ - 2 ^ 62 <= hi <= 2 ^ 62).
  {
    assert (X : forallb (fun o => match lit_of (ob_lo o), lit_of (ob_hi o) with Some lo, Some hi => (- 100 <=? lo) && (hi <=? 100) && (lo <=? hi) | _, _ => true end)%bool
                  (O_grp :: skipn 3 (N_all am fr)) = true).
    { unfold N_all, N_common, rvv. destruct (rsv am fr =? 0); [|destruct (rsv am fr <? 5); [|destruct (rsv am fr =? 5)]]; vm_compute; reflexivity. }
    pose proof (proj1 (forallb_forall _ _) X _ Ho) as Y. cbn [ob_lo ob_hi lit_of] in Y.
    apply andb_prop in Y as [Y Y3]. apply andb_prop in Y as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.leb_le in Y2. lia. }
  unfold obj_range, obj_lo_of, obj_hi_of in Hx. cbn [ob_base ob_lo ob_hi fst snd] in Hx. rewrite !soff_lit_small in Hx, RL, RP by lia.
  assert (COV : covers_lit ocs (x - bv_unsigned (eval rhoP ob)) = true).
  { pose proof (proj1 (forallb_forall _ _) Ccov (Z.to_nat (x - bv_unsigned (eval rhoP ob) - lo)) ltac:(apply in_seq; lia)) as Y.
    cbn beta in Y. rewrite Z2Nat.id in Y by lia. replace (lo + (x - bv_unsigned (eval rhoP ob) - lo)) with (x - bv_unsigned (eval rhoP ob)) in Y by lia. exact Y. }
  destruct (lit_obj_bytes_eq segsU rhoP ms' rhoP ms ob lo hi ocs (x - bv_unsigned (eval rhoP ob)) OL OP eq_refl
              ltac:(apply Forall_forall; intros; reflexivity) ltac:(apply Forall_forall; exact (proj1 (forallb_forall _ _) Clit)) ltac:(lia) ltac:(lia) ltac:(lia) COV) as [E B].
  replace (bv_unsigned (eval rhoP ob) + (x - bv_unsigned (eval rhoP ob))) with x in E, B by lia.
  split; [exact E|]. split; [exact B|].
  split; [apply (obj_wview rhoP ms' ob lo hi ocs x OL); lia | apply (obj_wview rhoP ms ob lo hi ocs x OP); lia].
Qed.

Lemma hdr_bytes : ltac2:(tb__ "0|9|
S4S3S4cS47Q8M0A1M1A1M2S21Vms';S49Q40M3SdVzp_;Z4A2M4A2M5A2S50G1S49G0Z0A2A2M6A3S4S3G2S21Vms';S49G3SdVzp_;Z3A2A2A2S50G1S49G0ZffA2A2A3S4S3G2S21Vms';S49G3SdVzp_;Z2A2A2A2G6A3S4S3G2S21Vms';S49G3SdVzp_;Z1A2A2A2G6A3S4S3G2S21Vms;G5A2G6A3S0S4SbG4R1A2ScR1Vzp_;A2A2S4S5S3G2S63S16S62Vms';A1S49G3R2A2M7A3S55G1A1M8A3A1S5S3G2S63S16S62Vms;A1G7A3G8A3A1A2F_;Fx;A2A2A2A2A2").
Proof using HQ Hag2 HsmL HsmP k0 n_ nn zp.
  pose proof b12 as [B2 BP].
  assert (HL : obj_holds segsU rhoP ms' O_hdr') by (apply (proj1 (Forall_forall _ _) objsL'); rewrite NL_def; left; reflexivity).
  assert (HP : obj_holds segsU rhoP ms O_hdr) by (apply (proj1 (Forall_forall _ _) objsP); rewrite N_all_def; left; reflexivity).
  unfold O_hdr' in HL. unfold O_hdr in HP.
  pose proof (fun j => cell_byte rhoP ms' (v 12) (-4) 0 _ DUnknown (-2) 2 (SLit 0) j HL ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as C2.
  pose proof (cell_byte rhoP ms' (v 12) (-4) 0 _ DUnknown (-3) 1 (SLit 18446744073709551615) 0 HL ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as C3.
  pose proof (cell_byte rhoP ms' (v 12) (-4) 0 _ DUnknown (-4) 1 (SLit 0) 0 HL ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as C4.
  pose proof (cell_byte rhoP ms (v 12) (-4) 0 _ DUnknown (-4) 1 (SLit 0) 0 HP ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as P4.
  rewrite BP in C2, C3, C4, P4. cbn [Z.of_nat] in C3, C4, P4. rewrite Z.add_0_r in C3, C4, P4.
  replace (zp_ + -4) with (zp_ - 4) in C4, P4 by lia. replace (zp_ + -3) with (zp_ - 3) in C3 by lia.
  split; [rewrite C4; reflexivity|]. split; [rewrite C3; apply f_equal; apply bv_eq; vm_compute; reflexivity|].
  split; [specialize (C2 0%nat ltac:(cbn; lia)); cbn [Z.of_nat] in C2; rewrite Z.add_0_r in C2; replace (zp_ + -2) with (zp_ - 2) in C2 by lia; rewrite C2; reflexivity|].
  split; [specialize (C2 1%nat ltac:(cbn; lia)); replace (zp_ + -2 + Z.of_nat 1) with (zp_ - 1) in C2 by lia; rewrite C2; reflexivity|].
  split; [rewrite P4; reflexivity|].
  intros x Hx. split; [apply (obj_wview rhoP ms' (v 12) (-4) 0 _ x HL); lia | apply (obj_wview rhoP ms (v 12) (-4) 0 _ x HP); lia].
Qed.

Lemma meta_bytes : ltac2:(tb__ "0|9|
S0S4SbSaS79VL;Vg;A2M0Z10A2R1A2ScR1SaG0Z28A2A2A2S4S5S3S4cS47Q8M1A1M2A1M3S63S16S62Vms';A1S49Q40M4R2A2M5A3S55G2A1M6A3A1S4S5S3G3S63S16S62Vms;A1G5A3G6A3A1S4aOL_;S52S11SaG0Z1cA2M7R2A2S12R2SaG0Z20A2A2A2S3G3S21Vms';G5A2M8S50G2S49G1S6cSaSa8Vam;A1SeZ2Vi;A2A2U4SfSdR2G7A2A1A3A2A2A3S4S3G3G8S21Vms;G5A2A3S7G2G2S3G3S21Vms;S49G4R3A2A2S50G2R1A2A3Lb;A2A2X4ax2A2A2F_;Fx;").
Proof using HQ Hag2 HsmL HsmP k0 n_ nn zp zp_.
  intros x Hx. pose proof b132 as [B2 BP].
  assert (HL : obj_holds segsU rhoP ms' O_meta') by (apply (proj1 (Forall_forall _ _) objsL'); rewrite NL_def; right; right; left; reflexivity).
  assert (HP : obj_holds segsU rhoP ms O_meta) by (apply (proj1 (Forall_forall _ _) objsP); rewrite N_all_def; right; right; left; reflexivity).
  split; [apply (obj_wview rhoP ms' (v 132) 16 40 _ x HL); lia|]. split; [apply (obj_wview rhoP ms (v 132) 16 40 _ x HP); lia|].
  unfold O_meta' in HL. unfold O_meta in HP.
  destruct ((zG L g + 28 <=? x) && (x <? zG L g + 32))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    pose proof (cell_byte rhoP ms' (v 132) 16 40 _ DUnknown 28 4 NEWFREED (Z.to_nat (x - (zG L g + 28))) HL ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as C.
    rewrite BP, Z2Nat.id in C by lia. replace (zG L g + 28 + (x - (zG L g + 28))) with x in C by lia. rewrite C. f_equal.
    unfold rhoP. rewrite (ev1 L g am i fr rho m1) by reflexivity.
    openIH. change NEWFREED with (SAluW ALU_ADD (SExt true 32 (v 134)) ff_self).
    rewrite (ze_newfreed s L g am i fr a k rho FFx HQ Har Hmp rgm Hrg HzA0).
    change 4%nat with (Z.to_nat 4) at 1. rewrite nth_enc_bytes by lia. rewrite le_byte_mod32 by lia. reflexivity.
  - assert (OFF : (16 <= x - zG L g < 24) \/ (24 <= x - zG L g < 28) \/ (32 <= x - zG L g < 40)).
    { destruct (Z_lt_dec x (zG L g + 28)); [|]. 1: destruct (Z_lt_dec x (zG L g + 24)); [left; lia|right; left; lia].
      right; right. assert (~ (x < zG L g + 32)) by (intros C; assert (E' : ((zG L g + 28 <=? x) && (x <? zG L g + 32))%bool = true) by (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia); rewrite E' in E; discriminate). lia. }
    assert (GEN : forall off k val, In (mkCell (SLit off) k val) [mkCell (SLit 16) 8 (SAlu ALU_ADD gm_mem_sv (SLit (-16))); mkCell (SLit 24) 4 (v 133); mkCell (SLit 32) 8 (v 135)] ->
                  0 <= k -> off <= x - zG L g < off + k -> - 2 ^ 62 <= off <= 2 ^ 62 ->
                  rd ms' (Z_to_bv 64 x) = rd ms (Z_to_bv 64 x) /\ exists b, rd ms (Z_to_bv 64 x) = Some b).
    { intros off kk val Hcin Hk Hoff Hob.
      assert (InL : In (mkCell (SLit off) kk val) (ob_cells O_meta')) by (cbn; cbn in Hcin; tauto).
      assert (InP : In (mkCell (SLit off) kk val) (ob_cells O_meta)) by (cbn; cbn in Hcin; tauto).
      pose proof (cell_byte rhoP ms' (v 132) 16 40 _ DUnknown off kk val (Z.to_nat (x - zG L g - off)) HL InL ltac:(lia) ltac:(lia) Hob Hk ltac:(lia)) as CL.
      pose proof (cell_byte rhoP ms (v 132) 16 40 _ DUnknown off kk val (Z.to_nat (x - zG L g - off)) HP InP ltac:(lia) ltac:(lia) Hob Hk ltac:(lia)) as CP.
      rewrite BP, Z2Nat.id in CL, CP by lia. replace (zG L g + off + (x - zG L g - off)) with x in CL, CP by lia.
      rewrite CL, CP. split; [reflexivity|eexists; reflexivity]. }
    destruct OFF as [O|[O|O]].
    + apply (GEN 16 8 (SAlu ALU_ADD gm_mem_sv (SLit (-16)))); [cbn; tauto|lia|lia|lia].
    + apply (GEN 24 4 (v 133)); [cbn; tauto|lia|lia|lia].
    + apply (GEN 32 8 (v 135)); [cbn; tauto|lia|lia|lia].
Qed.

Lemma NL_cases : ltac2:(tb__ "0|3|
S47Q40M0A1S9eVrhoP;S5dR1A3S48G0R2A2S0S6S4SbSdVzp_;Z4A2R1A2ScR1Vzp_;A2A2S6S4SbSaS79VL;Vg;A2M1Z10A2R1A2ScR1SaG1Z28A2A2A2S7S1bS1bS4SbeS1bR1S4dS1bS7aS9bS1bU3S78Vam;Vfr;A2A3A3A3S4SbS57S0S0S20VrhoP;R1A2M2A3R2A2ScR2S58S0S0G2A3A2A2A2Lo;A2A2A2Tx;F_;Fw;").
Proof using HQ Hag2 k0 zp.
  intros w (o & Ho & R) x. rewrite NL_def in Ho.
  destruct Ho as [<-|[<-|[<-|Ho]]].
  - left. rewrite rng_hdr' in R. cbn [fst snd] in R. subst x. lia.
  - right; right. exists O_grp. split; [left; reflexivity|exact R].
  - right; left. rewrite rng_meta' in R. cbn [fst snd] in R. subst x. lia.
  - right; right. exists o. split; [right; exact Ho|exact R].
Qed.

Lemma In_rest_N_all : ltac2:(tb__ "0|1|
S1bSbeS1bR1S4dS1bS7aS9bS1bU3S78Vam;Vfr;A2M0A3A3A3SbeS1bR2G0A3F_;Fo;").
Proof using . intros o [<-|Ho]; rewrite N_all_def; [right; left; reflexivity | right; right; right; exact Ho]. Qed.

Lemma NL_zone : ltac2:(tb__ "0|2|
S47Q40M0A1S9eVrhoP;S5dR1A3S48G0R2A2S0S4ScR1SaS82Vrho;A1S7fVrho;A1A2A2S4S5S4SbVzp_;R1A2ScR1SaVzp_;Vn_;A2A2A2A1S6Sc9VL;Vg;Vam;Vi;Vfr;Va0;R1A7S6S72S5aR1A2S4SbZ108ecM1R1A2ScR1SaG1Z60A2A2A2A2A2A2A2Tx;F_;Fw;").
Proof using HMI0 HQ Hag2 k0 rgm0.
  intros w Hw x. pose proof RZ as RR. cbn zeta in RR.
  pose proof W_rng as (Rh & Rg & Rm & Ra & GR & LOW & Rc & Rl & Rk & Rs).
  destruct (NL_cases w Hw) as [X|[X|(o & Ho & R)]].
  - pose proof (N_all_zone O_hdr ltac:(rewrite N_all_def; left; reflexivity)) as Z1. cbn zeta in Z1. rewrite Rh in Z1. cbn [fst snd] in Z1.
    destruct Z1 as (Z1 & Z2 & Z3 & Z4). subst x. split; [lia|]. split; [apply Z3; lia | apply Z4; lia].
  - pose proof (N_all_zone O_meta ltac:(rewrite N_all_def; right; right; left; reflexivity)) as Z1. cbn zeta in Z1. rewrite Rm in Z1. cbn [fst snd] in Z1.
    destruct Z1 as (Z1 & Z2 & Z3 & Z4). subst x. split; [lia|]. split; [apply Z3; lia | apply Z4; lia].
  - pose proof (N_all_zone o (In_rest_N_all o Ho)) as Z1. cbn zeta in Z1.
    destruct Z1 as (Z1 & Z2 & Z3 & Z4). subst x. split; [lia|]. split; [apply Z3; lia | apply Z4; lia].
Qed.

Lemma m'_in : ltac2:(tb__ "0|0|
S47Q40A1S9eVrhoP;S5dR1A3S3S4cS47Q8A1A1S5eR2A1S62Vms';R2A2A3F_;Fw;").
Proof using Hag2 HsmL. intros w Hw. unfold m'. destruct (in_ranges_dec rho2 NL w) as [|N]; [reflexivity|]. exfalso. apply N. apply in_ranges_P. exact Hw. Qed.
Lemma m'_out : ltac2:(tb__ "0|0|
S47Q40A1S5S9eVrhoP;S5dR1A3A1S3S4cS47Q8A1A1S5eR2A1Vm1;R2A1A3F_;Fw;").
Proof using Hag2 HsmL. intros w Hw. unfold m'. destruct (in_ranges_dec rho2 NL w) as [Y|]; [|reflexivity]. exfalso. apply Hw. apply in_ranges_P. exact Y. Qed.

Lemma m0_on_NL : ltac2:(tb__ "0|0|
S47Q40A1S9eVrhoP;S5dR1A3S3S4cS47Q8A1A1S26Vrho;R2A2S62Vms;R2A2A3F_;Fw;").
Proof using HMI0 HP12 HP13 HQ Hag2 Hin Hout Hsm a0 k0 rgm0 zp_.
  intros w Hw. destruct (NL_zone w Hw) as (B & NB & _).
  rewrite (ms_m1 w B). symmetry. apply Hout. exact NB.
Qed.

Lemma sctab_ro : ltac2:(tb__ "0|6|
S47Q40M0A1S4SbZ108ecM1S48G0R1A2M2A2ScG2SaG1Z60A2A2A2S4S3S4cS47Q8A1M3A1M4S62Vms';R2A2S55G3A1M5A3S3G4S26Vrho;R2A2G5A3A2F_;Fw;").
Proof using HsmL k0 n_ nn zp zp_.
  intros w Hw. split.
  - apply HroL. rewrite <- (Z_to_bv_bv_unsigned 64 w).
    replace (bv_unsigned w) with (0x108ec + (bv_unsigned w - 0x108ec)) by lia. apply ro_sctab. lia.
  - openIH. rewrite <- (Z_to_bv_bv_unsigned 64 w).
    replace (bv_unsigned w) with (0x108ec + (bv_unsigned w - 0x108ec)) by lia. apply Hrom0. lia.
Qed.

Theorem views : ltac2:(tb__ "0|b|
S4S0S4SbZ0R1A2ScR1SeZ2Z40A2A2A2S5S4SbVzp_;R2A2ScR2SaVzp_;Vn_;A2M0A2A2A1S3S4cS0A1M1SccVL;Vg;Vam;Vi;Vfr;R3A6S55S0A1A3S4S3S4cS47Q8M2A1M3A1M4S6aS16S5eS49Q40M5R4A2M6A3S6aS16S26Vrho;A1M7G6A3A3S3S4aS69S16S5eG6A3S69S16G7G6A3A3A2F_;F_;F_;Fx;S4S0S4SbVzp_;R1A2ScR1G0A2A2S4S3S4aS69S16S5eS49G5R2A2A3S4fA3S7G3G3S3G4S6aS16S5eS49G5R3A2M8A3M9S50G3R1A2A3Lb;A2A2F_;Fx;S4S0S0S3G1SccVL;Vg;Vam;Vi;Vfr;R2A6S50S0R1A2A3S4S3S4aS69S16S5eG8A3S4fA3S3G4G9S50G3S49G2R2A2A2A3A2F_;Fb;Fx;S47G5A1S5S4SbVzp_;S48G5R1A2MaA2ScGaG0A2A2A1S5Sc9VL;Vg;Vam;Vi;Vfr;Va0;S48G5R2A2A7A1S5S72S5aS48G5R3A2A2A1S3G4S5eR4A1S26Vrho;R4A2A3F_;F_;F_;Fw;A2A2A2").
Proof using HMI0 HP12 HP13 HQ Hag2 Hblk Hin Hout Hsm HsmL HsmP k0 rgm0.
  pose proof RZ as RR. cbn zeta in RR.
  pose proof W_rng as (Rh & Rg & Rm & Ra & GR & LOW & Rc & Rl & Rk & Rs).
  pose proof hdr_bytes as (Hb4 & Hb3 & Hb2 & Hb1 & Hp4 & Hbw).
  assert (U : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x) by (intros; apply u64; lia).
  assert (INH : forall x, zp_ - 4 <= x < zp_ -> in_ranges rhoP NL (Z_to_bv 64 x)).
  { intros x Hx. exists O_hdr'. split; [rewrite NL_def; left; reflexivity|]. rewrite rng_hdr'. cbn [fst snd]. rewrite U by lia. lia. }
  assert (INM : forall x, zG L g + 16 <= x < zG L g + 40 -> in_ranges rhoP NL (Z_to_bv 64 x)).
  { intros x Hx. exists O_meta'. split; [rewrite NL_def; right; right; left; reflexivity|]. rewrite rng_meta'. cbn [fst snd]. rewrite U by lia. lia. }
  split; [|split; [|split]].
  -   intros x Hx NB Hwin. set (w := Z_to_bv 64 x).
    destruct (in_ranges_dec rhoP NL w) as [IN|OUT].
    + pose proof (m'_in w IN) as M1.
      assert (M0 : rm rho w = ms_mem ms w) by (apply m0_on_NL; exact IN).
      destruct (NL_cases w IN) as [X|[X|(o & Ho & R)]]; subst w; try (rewrite U in X by lia); try (rewrite U in R by lia).
      *
        assert (x = zp_ - 4) as ->.
        { unfold win_byte in Hwin. fold zp_ in Hwin.
          destruct (zp_ - 3 =? x) eqn:E3; [discriminate|]. destruct (zp_ - 2 =? x) eqn:E2; [discriminate|]. destruct (zp_ - 1 =? x) eqn:E1; [discriminate|].
          apply Z.eqb_neq in E3. apply Z.eqb_neq in E2. apply Z.eqb_neq in E1. lia. }
        destruct (Hbw (zp_ - 4) ltac:(lia)) as [W1 W2].
        rewrite (rd_of_eq_rd segsU ms' m' _ HromL M1), (rd_of_eq_rd segsU ms (rm rho) _ HromP0 M0).
        split; [rewrite Hb4, Hp4; reflexivity|].
        rewrite (wok_of_mem m' (ms_mem ms') _ M1), (wok_of_mem (rm rho) (ms_mem ms) _ M0).
        rewrite !wok_of_wview by assumption. reflexivity.
      *
        pose proof (meta_bytes x X) as (W1 & W2 & MB).
        replace ((zG L g + 28 <=? x) && (x <? zG L g + 32))%bool with false in MB.
        2:{ unfold win_byte in Hwin. destruct ((zG L g + 28 <=? x) && (x <? zG L g + 32))%bool eqn:E; [|reflexivity].
            destruct (zP L am i fr - 3 =? x); [discriminate|]. destruct (zP L am i fr - 2 =? x); [discriminate|]. destruct (zP L am i fr - 1 =? x); discriminate. }
        destruct MB as [E _].
        rewrite (rd_of_eq_rd segsU ms' m' _ HromL M1), (rd_of_eq_rd segsU ms (rm rho) _ HromP0 M0).
        split; [exact E|].
        rewrite (wok_of_mem m' (ms_mem ms') _ M1), (wok_of_mem (rm rho) (ms_mem ms) _ M0).
        rewrite !wok_of_wview by assumption. reflexivity.
      *
        pose proof (rest_bytes o Ho) as RB.
        destruct (ob_dflt o) eqn:Ed.
        all: try (destruct (RB x R) as (E & _ & W1 & W2);
                  rewrite (rd_of_eq_rd segsU ms' m' _ HromL M1), (rd_of_eq_rd segsU ms (rm rho) _ HromP0 M0);
                  split; [exact E|];
                  rewrite (wok_of_mem m' (ms_mem ms') _ M1), (wok_of_mem (rm rho) (ms_mem ms) _ M0);
                  rewrite !wok_of_wview by assumption; reflexivity).

        assert (HS : o = O_sctab).
        { assert (X : forallb (fun o' => match ob_dflt o' with DRom _ => list_eqb sv_eqb [ob_base o'] [SLit 0x108ec] && list_eqb sv_eqb [ob_lo o'; ob_hi o'] [SLit 0; SLit 96] && match ob_cells o' with [] => true | _ => false end | _ => true end)%bool (O_grp :: skipn 3 (N_all am fr)) = true).
          { unfold N_all, N_common, rvv. destruct (rsv am fr =? 0); [|destruct (rsv am fr <? 5); [|destruct (rsv am fr =? 5)]]; vm_compute; reflexivity. }
          pose proof (proj1 (forallb_forall _ _) X o Ho) as Y. cbn beta in Y. rewrite Ed in Y.
          destruct o as [ob olo ohi ocs od]. cbn [ob_dflt ob_base ob_lo ob_hi ob_cells] in *. subst od.
          apply andb_prop in Y as [Y Y3]. apply andb_prop in Y as [Y1 Y2].
          destruct ocs; [|discriminate].
          cbn [list_eqb] in Y1, Y2. apply andb_prop in Y1 as [Y1 _]. apply andb_prop in Y2 as [Y2 Y2']. apply andb_prop in Y2' as [Y2' _].
          apply sv_eqb_sound in Y1. apply sv_eqb_sound in Y2. apply sv_eqb_sound in Y2'. subst.
          unfold O_sctab. f_equal.

          assert (X2 : forallb (fun o' => match ob_dflt o' with DRom l' => Pos.eqb l' L_SIZECLASSES | _ => true end) (O_grp :: skipn 3 (N_all am fr)) = true).
          { unfold N_all, N_common, rvv. destruct (rsv am fr =? 0); [|destruct (rsv am fr <? 5); [|destruct (rsv am fr =? 5)]]; vm_compute; reflexivity. }
          pose proof (proj1 (forallb_forall _ _) X2 _ Ho) as Y. cbn beta in Y. cbn [ob_dflt] in Y. apply Pos.eqb_eq in Y. rewrite Y. reflexivity. }
        subst o. rewrite Rs in R. cbn [fst snd] in R.
        destruct (sctab_ro (Z_to_bv 64 x) ltac:(rewrite U by lia; lia)) as [N1 N2].
        unfold Glue.rd_of, Glue.wok_of. rewrite M1, N1, N2. split; reflexivity.
    + pose proof (m'_out w OUT) as M1. subst w.
      rewrite Hout in M1 by (rewrite U by lia; destruct zp_eq as [E1 E2]; rewrite E1, E2; exact NB).
      unfold Glue.rd_of, Glue.wok_of. rewrite M1. split; reflexivity.
  -   intros x Hx.
    assert (OUT : ~ in_ranges rhoP NL (Z_to_bv 64 x)).
    { intros IN. destruct (NL_zone _ IN) as (_ & NB & _). rewrite U in NB by lia. exact (NB Hx). }
    assert (M1 : m' (Z_to_bv 64 x) = ms_mem ms (Z_to_bv 64 x)).
    { rewrite (m'_out _ OUT). apply Hin. rewrite U by lia. destruct zp_eq as [E1 E2]; rewrite E1, E2; exact Hx. }
    rewrite (wok_of_mem m' (ms_mem ms) (Z_to_bv 64 x) M1).
    destruct (Hblk x ltac:(destruct zp_eq as [E1 E2]; rewrite E1, E2; exact Hx)) as [W [b Hb]].
    split; [apply wok_of_wview; exact W|].
    exists b. rewrite (rd_of_eq_rd segsU ms m' _ HromP0 M1). exact Hb.
  -   intros x b Hwin.
    unfold win_byte in Hwin. fold zp_ in Hwin.
    assert (CASES : (x = zp_ - 3 /\ b = 255) \/ (x = zp_ - 2 /\ b = 0) \/ (x = zp_ - 1 /\ b = 0)
                    \/ (zG L g + 28 <= x < zG L g + 32 /\ b = le_byte (am_freed am + 2 ^ i) 4 (Z.to_nat (x - (zG L g + 28))))).
    { destruct (zp_ - 3 =? x) eqn:E3; [apply Z.eqb_eq in E3; injection Hwin as <-; left; split; [lia|reflexivity]|].
      destruct (zp_ - 2 =? x) eqn:E2; [apply Z.eqb_eq in E2; injection Hwin as <-; right; left; split; [lia|reflexivity]|].
      destruct (zp_ - 1 =? x) eqn:E1; [apply Z.eqb_eq in E1; injection Hwin as <-; right; right; left; split; [lia|reflexivity]|].
      destruct ((zG L g + 28 <=? x) && (x <? zG L g + 32))%bool eqn:E; [|discriminate].
      apply andb_prop in E as [Ea Eb]. apply Z.leb_le in Ea. apply Z.ltb_lt in Eb. injection Hwin as <-.
      right; right; right. split; [lia|reflexivity]. }
    assert (IN : in_ranges rhoP NL (Z_to_bv 64 x)) by (destruct CASES as [[-> _]|[[-> _]|[[-> _]|[X _]]]]; [apply INH; lia|apply INH; lia|apply INH; lia|apply INM; lia]).
    rewrite (wok_of_mem m' (ms_mem ms') (Z_to_bv 64 x) (m'_in _ IN)).
    rewrite (rd_of_eq_rd segsU ms' m' _ HromL (m'_in _ IN)).
    destruct CASES as [[-> ->]|[[-> ->]|[[-> ->]|[X ->]]]].
    + destruct (Hbw (zp_ - 3) ltac:(lia)) as [W1 _]. split; [apply wok_of_wview; exact W1 | exact Hb3].
    + destruct (Hbw (zp_ - 2) ltac:(lia)) as [W1 _]. split; [apply wok_of_wview; exact W1 | exact Hb2].
    + destruct (Hbw (zp_ - 1) ltac:(lia)) as [W1 _]. split; [apply wok_of_wview; exact W1 | exact Hb1].
    + pose proof (meta_bytes x ltac:(lia)) as (W1 & W2 & MB).
      replace ((zG L g + 28 <=? x) && (x <? zG L g + 32))%bool with true in MB
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      split; [apply wok_of_wview; exact W1 | exact MB].
  -   intros w NB NW NS.
    destruct (in_ranges_dec rhoP NL w) as [IN|OUT].
    + destruct (NL_zone w IN) as (_ & _ & [X|[X|X]]); [exfalso; exact (NW X) | exfalso; exact (NS X) |].
      destruct (sctab_ro w X) as [N1 N2]. rewrite (m'_in w IN), N1, N2. reflexivity.
    + rewrite (m'_out w OUT). apply Hout. destruct zp_eq as [E1 E2]; rewrite E1, E2; exact NB.
Qed.

End Reabstract.

Lemma run_free_entry_P : ltac2:(tb__ "0|1|
S3S4cS4bSb2A1M0A1Sb8S16U2S4dS0Z20570S56S0A1A3S71S6eA1S4fA5S50G0S4dSb2Sb3S80Sb4A2S56Sb2A1A3A2A3").
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.

Lemma stableJ_free_pre : ltac2:(tb__ "0|0|
Sb9S4bS65A1S66OF_;F_;Sd4S17S70S16S5aR2R1A4A2FKc;FA;").
Proof.
  intros A Kc rho rho' tr md (Hrw & Hrl & Hrm) (HM & HB & HK & HT).
  unfold J_free_preT, MInvR in *.
  assert (Erm : rm rho' = rm rho).
  { apply FunctionalExtensionality.functional_extensionality. intros a. symmetry. apply Hrm. }
  rewrite Erm. rewrite <- (Hrw 12%positive) by (unfold NF; lia). rewrite <- (Hrw 13%positive) by (unfold NF; lia).
  split; [exact HM|]. split; [exact HB|]. split; [exact HK|]. unfold tp_ok, top_high in *.
  rewrite <- (Hrw 24%positive), <- (Hrw 10%positive), <- (Hrw V_DEPTH) by (unfold NF, V_DEPTH; lia). exact HT.
Qed.

Theorem quick_post_proof : quick_post_stmt.
Proof.
  intros s L g am i fr a k m0 m' vm HMI FFx HQ Har V1 V2 V3 V4.
  pose proof (minv_post C_U s L g am i fr a k (Glue.rd_of segsU m0) (Glue.rd_of segsU m') (Glue.wok_of segsU m0) (Glue.wok_of segsU m') vm
                HMI FFx HQ Har statics_in_image_U V1 V2 V3) as M.
  split; [exact M|].
  intros x Hx Hno Hno' Herr Hstat.
  apply (V4 (Z_to_bv 64 x)); rewrite (u64 x Hx).
  - intros Hb. apply Hno'. left. exact (block_owned' C_U s L g am i fr (Glue.rd_of segsU m0) (Glue.wok_of segsU m0) vm HMI FFx HQ x Hb).
  - intros Hw. apply Hno.
    pose proof (proj1 (proj2 (proj2 HMI))) as HC. cbn [ma_L] in HC.
    unfold in_windows in Hw.
    destruct Hw as [W|[W|[W|[W|[W|[W|W]]]]]].
    6: { right. cbn. exact W. }
    all: left; apply (windows_owned C_U s L g am i fr a k (Glue.rd_of segsU m0) (Glue.wok_of segsU m0) vm HMI FFx HQ Har x).
    + left. exact W.
    + right; left. exact W.
    + right; right; left. exact W.
    + right; right; right; left. exact W.
    + right; right; right; right; left. rewrite HC. cbn. exact W.
    + right; right; right; right; right. exact W.
  - exact Hstat.
Qed.

Section Top.
Let GAP : quick_post_stmt := quick_post_proof.

Theorem free_contract_quick : ltac2:(tb__ "0|2|
SdeOF_;Sb9S4bS65A1S66OF_;F_;S24Sa4Sa5S0Sa6S74S16R8R6A3Sc2SbbR8A1S6bR4R3R2A3R5R4R3R2A6S3S0S5bSbaR9A1S6bR5R4R3A3A2S48Q40M0S22R7PcA2A2A3S3S0Sa7R4A1S48G0S22R8PdA2A2A3SddS16RcSd3S16S70S16S5aRbRaA4S71S6eA1R9A4Sa2S16S17R9S4dS54S25Sa1A2M1S4eS25Sa1S6fS6eA1S73S16S5aRbRaA4A4S56G1A1A3A4A4F_;F_;F_;F_;Ffr;Fi;Fam;Fg;Frho;FKc;FA;Fok;").
Proof using .
  intros ok [s L] Kc rho g am i fr (HokF & HokP & Hvm) HQ HP12 HP13. cbn [ma_s ma_L] in HQ, HP12.

  eapply triple_seq.
  { apply triple1_triple.
    apply (sym_run_soundJ_strict segsU 2 [0x20570] (Pre_freeI EC_U) [mkLeaf S1 RsCut] ok (J_free_preT segsU C_U (mkMA s L) Kc) rho eq_refl run_free_entry_P).
    - intros rho0 tr ms md ms' (_ & _ & HK & _). exact (HokF tr ms md ms' HK).
    - apply stableJ_free_pre. }

  intros n Hg [tr [ms md]] (Lf & rhoE & HinL & Hag & Hsm' & HJ').
  destruct HinL as [<-|[]]. cbn [lf_state] in Hsm'. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJ'.
  destruct HJ' as (HMI & Hblk & HKc & Htp & Hini & Htop').
  pose proof Hag as (Hrw & Hrl & Hrm).
  assert (Erm : rm rhoE = rm rho).
  { apply FunctionalExtensionality.functional_extensionality. intros a. symmetry. apply Hrm. }
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive) by (symmetry; apply Hrw; vm_compute; reflexivity).
  assert (E13 : rw rhoE 13%positive = rw rho 13%positive) by (symmetry; apply Hrw; vm_compute; reflexivity).
  assert (HP12' : addr_of L (frame_ptr am i fr) = bv_unsigned (rw rhoE 12%positive)) by (rewrite E12; exact HP12).
  assert (HP13' : fr_n fr = bv_unsigned (rw rhoE 13%positive)) by (rewrite E13; exact HP13).
  unfold MInvR in HMI. cbn [ma_s ma_L] in HMI.
  destruct (free_quick_instantiate s L g am i fr rhoE tr ms md Hsm' HMI HQ HP12' HP13' Htop') as (m1 & IH & Hout & Hin & HBLK & HsmP).
  set (rhoP := rho1 L g am i fr rhoE m1) in HsmP.
  set (K := fun tr' md' => Kc tr' md' /\ tr' = tr /\ md' = md).
  assert (HokK : ok_frame segsU ok K).
  { intros tr0 ms0 md0 ms0' (HK & _ & _). exact (HokF tr0 ms0 md0 ms0' HK). }
  apply (free_fast_sum_P (kv am) (rvv am fr) ok K rhoP HokK n).
  2:{ split; [exact HsmP|]. cbn. unfold liftK, K. auto. }

  intros [tr' [ms' md']] (Lf2 & rho2 & Hin2 & Hag2 & Hsm2 & HK2).
  rewrite Posts_single in Hin2. destruct Hin2 as [<-|[]]. cbn [lf_state] in Hsm2.
  unfold liftK, K in HK2. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HK2. destruct HK2 as (HKc' & Etr & Emd). subst tr' md'.
  fold (LeafP (kv am) (rvv am fr)) in Hsm2.
  apply Hg.

  exists (L_free EC_U), (JL_free segsU C_U (mkMA s L) Kc), (rho' am fr rhoE m1 rho2 ms').
  split; [left; reflexivity|].
  split.
  { eapply agree_vals_trans; [apply agree_below_vals; exact Hag|].
    exact (agree_vals_rho' L g am i fr rhoE m1 rho2 ms' Hag2). }
  split.
  { exact (smatch_Lfree L g am i fr rhoE tr ms md Hsm' m1 rho2 ms' Hag2 Hsm2). }

  cbn [w_tr w_cfg cfg_model cfg_ms fst snd].
  destruct (views s L g am i fr rhoE tr ms md Hsm' HMI HQ HP12' HP13' m1 Hout Hin IH HBLK HsmP rho2 ms' Hag2 Hsm2) as (V1 & V2 & V3 & V4).
  pose proof IH as IH0.
  destruct IH as [a k rgm FFx Lok Har Hmp P12 Hrg HzA0 Hsp0 Hdp Hm1e HEg HEa Hrom0 Hsh]. cbn [ih_a] in V4.
  pose proof (GAP s L g am i fr a k (rm rhoE) (m' am fr m1 rho2 ms') (m_vmmaps md) HMI FFx HQ
                (conj (proj1 Har) (conj (proj1 (proj2 Har)) (proj1 (proj2 (proj2 Har))))) V1 V2 V3 V4) as [HMI' KEPT].
  pose proof (proj1 HMI) as HW. cbn [ma_s] in HW.
  pose proof (free_quick_yields s (frame_ptr am i fr) g am i fr HW HQ) as Hy.
  pose proof (frame_user_block s g am i fr (proj1 HQ) (proj1 (proj2 HQ))) as HUB.
  destruct (free_blocks s (frame_ptr am i fr) (fr_n fr) [] (free_quick_post s g am i) HW HUB Hy) as (l1 & l2 & E1 & E2).
  exists (mkMA (free_quick_post s g am i) L).
  exists (map (fun b : sptr * Z => (addr_of L (fst b), snd b)) l1), (map (fun b : sptr * Z => (addr_of L (fst b), snd b)) l2).
  split; [unfold MInvR; cbn [ma_s ma_L]; exact HMI'|].
  split; [unfold ma_blocks, blocks; cbn [ma_s ma_L]; rewrite E1, map_app; cbn [map fst snd]; rewrite HP12, HP13; reflexivity|].
  split; [unfold ma_blocks, blocks; cbn [ma_s ma_L]; rewrite E2, map_app; reflexivity|].
  split; [rewrite <- Erm; exact (mem_kept_weaken segsU C_U _ _ rhoE md (rho' am fr rhoE m1 rho2 ms') md _ _ client_addr_not_owned_U HMI ltac:(unfold MInvR; cbn [ma_s ma_L]; exact HMI') KEPT)|].
  split; [split; [intros Hi0; exact Hi0 | reflexivity]|].
  exact HKc'.
Qed.

End Top.
End Mal_free_quick2.

Module Mal_free_quickE.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Section TopE.
Let GAP : quick_post_stmt := quick_post_proof.

Theorem free_contract_quick_ex : ltac2:(tb__ "0|2|
Sb9S4bS65A1S66OF_;F_;S24Sa4Sa5S0Sa6Sc2SbbR7A1S6bR3R2R1A3R4R3R2R1A6S3S0S5bSbaR8A1S6bR4R3R2A3A2S48Q40M0S22R6PcA2A2A3S3S0Sa7R3A1S48G0S22R7PdA2A2A3SdcS16Sd3S16S70S16S5aRaR9A4S71S6eA1R8A4Sa2S16S17R8S4dS54S25Sa1A2M1S4eS25Sa1S6fS6eA1S73S16S5aRaR9A4A4S56G1A1A3A4A3F_;F_;F_;Ffr;Fi;Fam;Fg;Frho;FKc;FA;").
Proof using .
  intros [s L] Kc rho g am i fr HQ HP12 HP13. cbn [ma_s ma_L] in HQ, HP12.
  intros w0 Hw0.

  destruct (sym_run_completeJ segsU 2 [0x20570] (Pre_freeI EC_U) [mkLeaf S1 RsCut] (J_free_preT segsU C_U (mkMA s L) Kc) rho w0
              eq_refl (stableJ_free_pre (mkMA s L) Kc) run_free_entry_P Hw0) as (Lf & rhoE & [tr [ms md]] & HinL & Hsteps1 & Hag & Hsm' & HJ').
  destruct HinL as [<-|[]]. cbn [lf_state] in Hsm'. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJ'.
  destruct HJ' as (HMI & Hblk & HKc & Htp & Hini & Htop').
  pose proof Hag as (Hrw & Hrl & Hrm).
  assert (Erm : rm rhoE = rm rho).
  { apply FunctionalExtensionality.functional_extensionality. intros a. symmetry. apply Hrm. }
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive) by (symmetry; apply Hrw; vm_compute; reflexivity).
  assert (E13 : rw rhoE 13%positive = rw rho 13%positive) by (symmetry; apply Hrw; vm_compute; reflexivity).
  assert (HP12' : addr_of L (frame_ptr am i fr) = bv_unsigned (rw rhoE 12%positive)) by (rewrite E12; exact HP12).
  assert (HP13' : fr_n fr = bv_unsigned (rw rhoE 13%positive)) by (rewrite E13; exact HP13).
  unfold MInvR in HMI. cbn [ma_s ma_L] in HMI.

  destruct (free_quick_instantiate s L g am i fr rhoE tr ms md Hsm' HMI HQ HP12' HP13' Htop') as (m1 & IH & Hout & Hin & HBLK & HsmP).
  set (rhoP := rho1 L g am i fr rhoE m1) in HsmP.
  set (K := fun tr' md' => Kc tr' md' /\ tr' = tr /\ md' = md).
  assert (HSP0 : SymSoundR.SP segsU K (Pre_free_fast FF_P (kv am) (rvv am fr)) rhoP (tr, mkCfg ms md)).
  { split; [exact HsmP|]. cbn. unfold liftK, K. auto. }
  destruct (sym_run_complete segsU FF_FUEL (ff_cuts FF_P) (Pre_free_fast FF_P (kv am) (rvv am fr)) (Posts_free_fast_P (kv am) (rvv am fr)) K rhoP
              (tr, mkCfg ms md) eq_refl (run_free_fast_P (kv am) (rvv am fr)) HSP0) as (Lf2 & rho2 & [tr' [ms' md']] & Hin2 & Hsteps2 & Hag2 & Hsm2 & HK2).
  exists (tr', mkCfg ms' md'). split; [eapply wsteps_trans; [exact Hsteps1 | exact Hsteps2]|].
  rewrite Posts_single in Hin2. destruct Hin2 as [<-|[]]. cbn [lf_state] in Hsm2.
  unfold liftK, K in HK2. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HK2. destruct HK2 as (HKc' & Etr & Emd). subst tr' md'.
  fold (LeafP (kv am) (rvv am fr)) in Hsm2.
  change (ss_next (Pre_free_fast FF_P (kv am) (rvv am fr))) with NFM in Hag2.

  exists (L_free EC_U), (JL_free segsU C_U (mkMA s L) Kc), (rho' am fr rhoE m1 rho2 ms').
  split; [left; reflexivity|].
  split.
  { eapply agree_vals_trans; [apply agree_below_vals; exact Hag|].
    exact (agree_vals_rho' L g am i fr rhoE m1 rho2 ms' Hag2). }
  split.
  { exact (smatch_Lfree L g am i fr rhoE tr ms md Hsm' m1 rho2 ms' Hag2 Hsm2). }
  cbn [w_tr w_cfg cfg_model cfg_ms fst snd].
  destruct (views s L g am i fr rhoE tr ms md Hsm' HMI HQ HP12' HP13' m1 Hout Hin IH HBLK HsmP rho2 ms' Hag2 Hsm2) as (V1 & V2 & V3 & V4).
  pose proof IH as IH0.
  destruct IH as [a k rgm FFx Lok Har Hmp P12 Hrg HzA0 Hsp0 Hdp Hm1e HEg HEa Hrom0 Hsh]. cbn [ih_a] in V4.
  pose proof (GAP s L g am i fr a k (rm rhoE) (m' am fr m1 rho2 ms') (m_vmmaps md) HMI FFx HQ
                (conj (proj1 Har) (conj (proj1 (proj2 Har)) (proj1 (proj2 (proj2 Har))))) V1 V2 V3 V4) as [HMI' KEPT].
  pose proof (proj1 HMI) as HW. cbn [ma_s] in HW.
  pose proof (free_quick_yields s (frame_ptr am i fr) g am i fr HW HQ) as Hy.
  pose proof (frame_user_block s g am i fr (proj1 HQ) (proj1 (proj2 HQ))) as HUB.
  destruct (free_blocks s (frame_ptr am i fr) (fr_n fr) [] (free_quick_post s g am i) HW HUB Hy) as (l1 & l2 & E1 & E2).
  exists (mkMA (free_quick_post s g am i) L).
  exists (map (fun b : sptr * Z => (addr_of L (fst b), snd b)) l1), (map (fun b : sptr * Z => (addr_of L (fst b), snd b)) l2).
  split; [unfold MInvR; cbn [ma_s ma_L]; exact HMI'|].
  split; [unfold ma_blocks, blocks; cbn [ma_s ma_L]; rewrite E1, map_app; cbn [map fst snd]; rewrite HP12, HP13; reflexivity|].
  split; [unfold ma_blocks, blocks; cbn [ma_s ma_L]; rewrite E2, map_app; reflexivity|].
  split; [rewrite <- Erm; exact (mem_kept_weaken segsU C_U _ _ rhoE md (rho' am fr rhoE m1 rho2 ms') md _ _ client_addr_not_owned_U HMI ltac:(unfold MInvR; cbn [ma_s ma_L]; exact HMI') KEPT)|].
  split; [split; [intros Hi0; exact Hi0 | reflexivity]|].
  exact HKc'.
Qed.

Definition J_free_drvT (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|0|
S24S4bS65A1S66S4S70S16S5aVA;VKc;R3R2R1A7S4SdfS5aVk;VA;A3S4ScZ0Vk;A2Se1R1VX;A2A2A2A2Lmd;Ltr;Lrho;").

Lemma stableJ_free_drv : ltac2:(tb__ "0|0|
Sb9S0S0S4bS65A1S66OF_;F_;Sd4S17SeeR4R3R2R1A4A2FKc;FX;Fk;FA;").
Proof using .
  intros A k X Kc rho1 rho2 tr md Hag [HJ HD]. split; [exact (stableJ_free_pre A Kc rho1 rho2 tr md Hag HJ) | exact HD].
Qed.

Theorem free_drv_quick_ex : ltac2:(tb__ "0|2|
Sb9S0S0S4bS65A1S66OF_;F_;S24Sa4Sa5S0Sa6Sc2SbbR9A1S6bR3R2R1A3R4R3R2R1A6S3S0S5bSbaRaA1S6bR4R3R2A3A2S48Q40M0S22R6PcA2A2A3S3S0Sa7R3A1S48G0S22R7PdA2A2A3SdcS16Sd3S16SeeRcRbRaR9A4S71S6eA1R8A4Sa2S16S17R8S4dS54S25Sa1A2M1S4eS25Sa1S6fS6eA1Se0S16S5aRcSdRbZ1A2RaR9A6A4S56G1A1A3A4A3F_;F_;F_;Ffr;Fi;Fam;Fg;Frho;FKc;FX;Fk;FA;").
Proof using .
  intros [s L] k X Kc rho g am i fr HQ HP12 HP13. cbn [ma_s ma_L] in HQ, HP12.
  intros w0 Hw0.

  destruct (sym_run_completeJ segsU 2 [0x20570] (Pre_freeI EC_U) [mkLeaf S1 RsCut] (J_free_drvT (mkMA s L) k X Kc) rho w0
              eq_refl (stableJ_free_drv (mkMA s L) k X Kc) run_free_entry_P Hw0) as (Lf & rhoE & [tr [ms md]] & HinL & Hsteps1 & Hag & Hsm' & HJ').
  destruct HinL as [<-|[]]. cbn [lf_state] in Hsm'. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJ'.
  destruct HJ' as ((HMI & Hblk & HKc & Htp & Hini & Htop') & HdrvN & Hk & HVR).
  pose proof Hag as (Hrw & Hrl & Hrm).
  assert (Erm : rm rhoE = rm rho).
  { apply FunctionalExtensionality.functional_extensionality. intros a. symmetry. apply Hrm. }
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive) by (symmetry; apply Hrw; vm_compute; reflexivity).
  assert (E13 : rw rhoE 13%positive = rw rho 13%positive) by (symmetry; apply Hrw; vm_compute; reflexivity).
  assert (HP12' : addr_of L (frame_ptr am i fr) = bv_unsigned (rw rhoE 12%positive)) by (rewrite E12; exact HP12).
  assert (HP13' : fr_n fr = bv_unsigned (rw rhoE 13%positive)) by (rewrite E13; exact HP13).
  unfold MInvR in HMI. cbn [ma_s ma_L] in HMI.

  destruct (free_quick_instantiate s L g am i fr rhoE tr ms md Hsm' HMI HQ HP12' HP13' Htop') as (m1 & IH & Hout & Hin & HBLK & HsmP).
  set (rhoP := rho1 L g am i fr rhoE m1) in HsmP.
  set (K := fun tr' md' => Kc tr' md' /\ tr' = tr /\ md' = md).
  assert (HSP0 : SymSoundR.SP segsU K (Pre_free_fast FF_P (kv am) (rvv am fr)) rhoP (tr, mkCfg ms md)).
  { split; [exact HsmP|]. cbn. unfold liftK, K. auto. }
  destruct (sym_run_complete segsU FF_FUEL (ff_cuts FF_P) (Pre_free_fast FF_P (kv am) (rvv am fr)) (Posts_free_fast_P (kv am) (rvv am fr)) K rhoP
              (tr, mkCfg ms md) eq_refl (run_free_fast_P (kv am) (rvv am fr)) HSP0) as (Lf2 & rho2 & [tr' [ms' md']] & Hin2 & Hsteps2 & Hag2 & Hsm2 & HK2).
  exists (tr', mkCfg ms' md'). split; [eapply wsteps_trans; [exact Hsteps1 | exact Hsteps2]|].
  rewrite Posts_single in Hin2. destruct Hin2 as [<-|[]]. cbn [lf_state] in Hsm2.
  unfold liftK, K in HK2. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HK2. destruct HK2 as (HKc' & Etr & Emd). subst tr' md'.
  fold (LeafP (kv am) (rvv am fr)) in Hsm2.
  change (ss_next (Pre_free_fast FF_P (kv am) (rvv am fr))) with NFM in Hag2.

  exists (L_free EC_U), (JLd_free segsU C_U (mkMA s L) (k - 1) X Kc), (rho' am fr rhoE m1 rho2 ms').
  split; [left; reflexivity|].
  split.
  { eapply agree_vals_trans; [apply agree_below_vals; exact Hag|].
    exact (agree_vals_rho' L g am i fr rhoE m1 rho2 ms' Hag2). }
  split.
  { exact (smatch_Lfree L g am i fr rhoE tr ms md Hsm' m1 rho2 ms' Hag2 Hsm2). }
  cbn [w_tr w_cfg cfg_model cfg_ms fst snd].
  destruct (views s L g am i fr rhoE tr ms md Hsm' HMI HQ HP12' HP13' m1 Hout Hin IH HBLK HsmP rho2 ms' Hag2 Hsm2) as (V1 & V2 & V3 & V4).
  pose proof IH as IH0.
  destruct IH as [a kk rgm FFx Lok Har Hmp P12 Hrg HzA0 Hsp0 Hdp Hm1e HEg HEa Hrom0 Hsh]. cbn [ih_a] in V4.
  pose proof (GAP s L g am i fr a kk (rm rhoE) (m' am fr m1 rho2 ms') (m_vmmaps md) HMI FFx HQ
                (conj (proj1 Har) (conj (proj1 (proj2 Har)) (proj1 (proj2 (proj2 Har))))) V1 V2 V3 V4) as [HMI' KEPT].
  pose proof (proj1 HMI) as HW. cbn [ma_s] in HW.
  pose proof (free_quick_yields s (frame_ptr am i fr) g am i fr HW HQ) as Hy.
  pose proof (frame_user_block s g am i fr (proj1 HQ) (proj1 (proj2 HQ))) as HUB.
  destruct (free_blocks s (frame_ptr am i fr) (fr_n fr) [] (free_quick_post s g am i) HW HUB Hy) as (l1 & l2 & E1 & E2).
  exists (mkMA (free_quick_post s g am i) L).
  exists (map (fun b : sptr * Z => (addr_of L (fst b), snd b)) l1), (map (fun b : sptr * Z => (addr_of L (fst b), snd b)) l2).
  split; [unfold MInvR; cbn [ma_s ma_L]; exact HMI'|].
  split; [split; [exact Hini | reflexivity]|].
  split.
  { destruct HdrvN as (j & Hr & H0 & Hj). exists (Datatypes.S j). split; [| split; [lia | rewrite Nat2Z.inj_succ; lia]].
    apply (DR_free C_U j (mkMA s L) (addr_of L (frame_ptr am i fr)) [] _ Hr). right. exists (frame_ptr am i fr), (fr_n fr). cbn [ma_s ma_L].
    split; [exact HUB|]. split; [reflexivity|]. split; [exact Hy | apply layout_extends_refl]. }
  split; [exact HVR|].
  split; [unfold ma_blocks, blocks; cbn [ma_s ma_L]; rewrite E1, map_app; cbn [map fst snd]; rewrite HP12, HP13; reflexivity|].
  split; [unfold ma_blocks, blocks; cbn [ma_s ma_L]; rewrite E2, map_app; reflexivity|].
  split; [rewrite <- Erm; exact (mem_kept_weaken segsU C_U _ _ rhoE md (rho' am fr rhoE m1 rho2 ms') md _ _ client_addr_not_owned_U HMI ltac:(unfold MInvR; cbn [ma_s ma_L]; exact HMI') KEPT)|].
  exact HKc'.
Qed.

Definition J_free_drvST (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|0|
S24S4bS65A1S66S4S70S16S5aVA;VKc;R3R2R1A7S4SdfS5aVk;VA;A3S4ScZ0Vk;A2Sf3R1VX;A2A2A2A2Lmd;Ltr;Lrho;").

Lemma stableJ_free_drvS : ltac2:(tb__ "0|0|
Sb9S0S0S4bS65A1S66OF_;F_;Sd4S17SedR4R3R2R1A4A2FKc;FX;Fk;FA;").
Proof using .
  intros A k X Kc rho1 rho2 tr md Hag [HJ HD]. split; [exact (stableJ_free_pre A Kc rho1 rho2 tr md Hag HJ) | exact HD].
Qed.

Theorem free_drv_quick_S : ltac2:(tb__ "0|2|
SdeOF_;Sb9S0S0S4bS65A1S66OF_;F_;S24Sa4Sa5S0Sa6S74S16RaR6A3Sc2SbbRaA1S6bR4R3R2A3R5R4R3R2A6S3S0S5bSbaRbA1S6bR5R4R3A3A2S48Q40M0S22R7PcA2A2A3S3S0Sa7R4A1S48G0S22R8PdA2A2A3SddS16ReSd3S16SedRdRcRbRaA4S71S6eA1R9A4Sa2S16S17R9S4dS54S25Sa1A2M1S4eS25Sa1S6fS6eA1Sf1S16S5aRdSdRcZ1A2RbRaA6A4S56G1A1A3A4A4F_;F_;F_;F_;Ffr;Fi;Fam;Fg;Frho;FKc;FX;Fk;FA;Fok;").
Proof using .
  intros ok [s L] k X Kc rho g am i fr (HokF & HokP & Hvm) HQ HP12 HP13. cbn [ma_s ma_L] in HQ, HP12.

  eapply triple_seq.
  { apply triple1_triple.
    apply (sym_run_soundJ_strict segsU 2 [0x20570] (Pre_freeI EC_U) [mkLeaf S1 RsCut] ok (J_free_drvST (mkMA s L) k X Kc) rho eq_refl run_free_entry_P).
    - intros rho0 tr ms md ms' ((_ & _ & HK & _) & _). exact (HokF tr ms md ms' HK).
    - apply stableJ_free_drvS. }

  intros n Hg [tr [ms md]] (Lf & rhoE & HinL & Hag & Hsm' & HJ').
  destruct HinL as [<-|[]]. cbn [lf_state] in Hsm'. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJ'.
  destruct HJ' as ((HMI & Hblk & HKc & Htp & Hini & Htop') & HdrvN & Hk & HVR).
  pose proof Hag as (Hrw & Hrl & Hrm).
  assert (Erm : rm rhoE = rm rho).
  { apply FunctionalExtensionality.functional_extensionality. intros a. symmetry. apply Hrm. }
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive) by (symmetry; apply Hrw; vm_compute; reflexivity).
  assert (E13 : rw rhoE 13%positive = rw rho 13%positive) by (symmetry; apply Hrw; vm_compute; reflexivity).
  assert (HP12' : addr_of L (frame_ptr am i fr) = bv_unsigned (rw rhoE 12%positive)) by (rewrite E12; exact HP12).
  assert (HP13' : fr_n fr = bv_unsigned (rw rhoE 13%positive)) by (rewrite E13; exact HP13).
  unfold MInvR in HMI. cbn [ma_s ma_L] in HMI.
  destruct (free_quick_instantiate s L g am i fr rhoE tr ms md Hsm' HMI HQ HP12' HP13' Htop') as (m1 & IH & Hout & Hin & HBLK & HsmP).
  set (rhoP := rho1 L g am i fr rhoE m1) in HsmP.
  set (K := fun tr' md' => Kc tr' md' /\ tr' = tr /\ md' = md).
  assert (HokK : ok_frame segsU ok K).
  { intros tr0 ms0 md0 ms0' (HK & _ & _). exact (HokF tr0 ms0 md0 ms0' HK). }
  apply (free_fast_sum_P (kv am) (rvv am fr) ok K rhoP HokK n).
  2:{ split; [exact HsmP|]. cbn. unfold liftK, K. auto. }

  intros [tr' [ms' md']] (Lf2 & rho2 & Hin2 & Hag2 & Hsm2 & HK2).
  rewrite Posts_single in Hin2. destruct Hin2 as [<-|[]]. cbn [lf_state] in Hsm2.
  unfold liftK, K in HK2. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HK2. destruct HK2 as (HKc' & Etr & Emd). subst tr' md'.
  fold (LeafP (kv am) (rvv am fr)) in Hsm2.
  apply Hg.

  exists (L_free EC_U), (JLdS_free segsU C_U (mkMA s L) (k - 1) X Kc), (rho' am fr rhoE m1 rho2 ms').
  split; [left; reflexivity|].
  split.
  { eapply agree_vals_trans; [apply agree_below_vals; exact Hag|].
    exact (agree_vals_rho' L g am i fr rhoE m1 rho2 ms' Hag2). }
  split.
  { exact (smatch_Lfree L g am i fr rhoE tr ms md Hsm' m1 rho2 ms' Hag2 Hsm2). }
  cbn [w_tr w_cfg cfg_model cfg_ms fst snd].
  destruct (views s L g am i fr rhoE tr ms md Hsm' HMI HQ HP12' HP13' m1 Hout Hin IH HBLK HsmP rho2 ms' Hag2 Hsm2) as (V1 & V2 & V3 & V4).
  pose proof IH as IH0.
  destruct IH as [a kk rgm FFx Lok Har Hmp P12 Hrg HzA0 Hsp0 Hdp Hm1e HEg HEa Hrom0 Hsh]. cbn [ih_a] in V4.
  pose proof (GAP s L g am i fr a kk (rm rhoE) (m' am fr m1 rho2 ms') (m_vmmaps md) HMI FFx HQ
                (conj (proj1 Har) (conj (proj1 (proj2 Har)) (proj1 (proj2 (proj2 Har))))) V1 V2 V3 V4) as [HMI' KEPT].
  pose proof (proj1 HMI) as HW. cbn [ma_s] in HW.
  pose proof (free_quick_yields s (frame_ptr am i fr) g am i fr HW HQ) as Hy.
  pose proof (frame_user_block s g am i fr (proj1 HQ) (proj1 (proj2 HQ))) as HUB.
  destruct (free_blocks s (frame_ptr am i fr) (fr_n fr) [] (free_quick_post s g am i) HW HUB Hy) as (l1 & l2 & E1 & E2).
  exists (mkMA (free_quick_post s g am i) L).
  exists (map (fun b : sptr * Z => (addr_of L (fst b), snd b)) l1), (map (fun b : sptr * Z => (addr_of L (fst b), snd b)) l2).
  split; [unfold MInvR; cbn [ma_s ma_L]; exact HMI'|].
  split; [split; [exact Hini | reflexivity]|].
  split.
  { destruct HdrvN as (j & Hr & H0 & Hj). exists (Datatypes.S j). split; [| split; [lia | rewrite Nat2Z.inj_succ; lia]].
    apply (DR_free C_U j (mkMA s L) (addr_of L (frame_ptr am i fr)) [] _ Hr). right. exists (frame_ptr am i fr), (fr_n fr). cbn [ma_s ma_L].
    split; [exact HUB|]. split; [reflexivity|]. split; [exact Hy | apply layout_extends_refl]. }
  split; [exact HVR|].
  split; [unfold ma_blocks, blocks; cbn [ma_s ma_L]; rewrite E1, map_app; cbn [map fst snd]; rewrite HP12, HP13; reflexivity|].
  split; [unfold ma_blocks, blocks; cbn [ma_s ma_L]; rewrite E2, map_app; reflexivity|].
  split; [rewrite <- Erm; exact (mem_kept_weaken segsU C_U _ _ rhoE md (rho' am fr rhoE m1 rho2 ms') md _ _ client_addr_not_owned_U HMI ltac:(unfold MInvR; cbn [ma_s ma_L]; exact HMI') KEPT)|].
  exact HKc'.
Qed.
End TopE.
End Mal_free_quickE.
