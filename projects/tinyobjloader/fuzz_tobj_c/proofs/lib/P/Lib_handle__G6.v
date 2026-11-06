(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "SLit"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "true"; "list"; "Some"; "cons"; "nil"; "option"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs"; "NP"; "HF_P"; "pC"; "vr_site_checkE"; "pQ"; "A_fv2"; "A_mi2"; "A_mm2"; "A_sg2"; "E_fv2"; "E_mi2"; "E_mm2"; "E_sg2"; "E_tp"; "F_fv2"; "F_mi2"; "F_mm2"; "F_sg2"; "pP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes"; "z0"; "FUEL"; "VT"; "VL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "ejcut"; "norm_xu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G4.Lib_handle_l_nodes"; "cpsl"; "hl_nodes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs"; "tvL"; "tvP"; "AL_lc"; "AL_li"; "AP_pi"; "EP_pc"; "EP_pi"; "FL_lc"; "FL_li"; "FP_pi"; "L50"; "L60"; "L94"; "LP"; "LP0"; "PP"; "PP0"; "Pre_hl"; "pcf_site_check"; "tvL_pre"; "vr_site_checkG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G6.Lib_handle_f_s4"; "E2_fv2"; "E2_mi2"; "E2_mm2"; "E2_sg2"; "s_fv2"; "s_mi2"; "s_mm2"; "s_sg2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G6.Lib_handle_p_s1"; "E2_pi"; "s_pi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_f_glue"; "tp_site_check"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require Stdlib.Sorting.Permutation.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G4.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G5.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_handle_f_s4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation h := HF_P.

Definition E2_mi2 : sstate := vr_view (E_mi2 h).
Definition s_mi2 : wsub := vr_sub mi1 12 E2_mi2.
Lemma chk_mi2 : ltac2:(tb__ "0|1|
ScS5S11S42S46U1S14SfA1S1dSfA1S24Z7A1Z28M0S21Z26G0S24Z8A1AbS6A3").
Proof. cbv delta [vr_site_checkE]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
Lemma view_mi2 : ltac2:(tb__ "0|2|
ScSbS1A1S28S9S25S26U1M0S2N40M1A1A2SaS25A1A3G0G1S18SfA1A4S8S1S42A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Definition E2_fv2 : sstate := vr_view (E_fv2 h).
Definition s_fv2 : wsub := vr_sub fv1 4 E2_fv2.
Lemma chk_fv2 : ltac2:(tb__ "0|1|
ScS5S11S41S45U2S13SfA1S1cSfA1S24Z5A1Z28M0S21Z26G0S24Z6A1AbS6A3").
Proof. cbv delta [vr_site_checkE]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
Lemma view_fv2 : ltac2:(tb__ "0|2|
ScSbS1A1S28S9S25S26U1M0S2N40M1A1A2SaS25A1A3G0G1S17SfA1A4S8S1S41A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Definition E2_mm2 : sstate := vr_view (E_mm2 h).
Definition s_mm2 : wsub := vr_sub mm1 4 E2_mm2.
Lemma chk_mm2 : ltac2:(tb__ "0|1|
ScS5S11S43S47U3S15SfA1S1eSfA1S24Z3A1Z28M0S21Z26G0S24Z4A1AbS6A3").
Proof. cbv delta [vr_site_checkE]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
Lemma view_mm2 : ltac2:(tb__ "0|2|
ScSbS1A1S28S9S25S26U1M0S2N40M1A1A2SaS25A1A3G0G1S19SfA1A4S8S1S43A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Definition E2_sg2 : sstate := vr_view (E_sg2 h).
Definition s_sg2 : wsub := vr_sub sg1 4 E2_sg2.
Lemma chk_sg2 : ltac2:(tb__ "0|1|
ScS5S11S44S48U4S16SfA1S1fSfA1S24Z1A1Z28M0S21Z26G0S24Z2A1AbS6A3").
Proof. cbv delta [vr_site_checkE]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
Lemma view_sg2 : ltac2:(tb__ "0|2|
ScSbS1A1S28S9S25S26U1M0S2N40M1A1A2SaS25A1A3G0G1S1aSfA1A4S8S1S44A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
End Lib_handle_f_s4.

Module Lib_handle_f_s6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_f_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G4.Lib_handle_f_s6a OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G5.Lib_handle_f_s6b.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation h := HF_P.

Lemma chk_tp : ltac2:(tb__ "0|1|
ScS5S4bS1bSfA1Z32M0S21G0S21Z34S21A7S6A3").
Proof. exact (tp_site_split _ _ _ _ _ _ _ chk_tpA chk_tpB). Qed.
End Lib_handle_f_s6.

Module Lib_handle_l_c1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G4.Lib_handle_l_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma ec_Pre_hl : ltac2:(tb__ "0|1|
ScS5S27S29SeS22S2aSeS2bU0S3S4S1S7S4S0S0A2A1M0A2S4SdS0A2S3S1G0S3dS3fA4S3SdS0Z64S21A4A4A8S6A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_L50 : ltac2:(tb__ "0|1|
ScS5S27S29SeS22S2aSeS2bU1S3S4S1S7S4S0S0A2A1M0A2S4SdS0A2S3S1G0S36S2cA4S3SdS0Z5aS23S20Z2A2A4A4A8S6A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_L60 : ltac2:(tb__ "0|1|
ScS5S27S29SeS22S2aSeS2bU2S3S4S1S7S4S0S0A2A1M0A2S4SdS0A2S3S1G0S37S2cA4S3SdS0Z5aS23S12Z1A2A4A4A8S6A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_L94 : ltac2:(tb__ "0|1|
ScS5S27S29SeS22S2aSeS2bU3S3S4S1S7S4S0S0A2A1M0A2S4SdS0A2S3S1G0S38S2cA4S3SdS0Z5aS23S12Z0A2A4A4A8S6A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_LP0 : ltac2:(tb__ "0|1|
ScS5S27S29SeS22S2aSeS2bU4S3S4S1S7S4S0S0A2A1M0A2S4SdS0A2S3S1G0S3aS2cA4S3SdS0Z5aS23S10Z6A2A4A4A8S6A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_LP : ltac2:(tb__ "0|1|
ScS5S27S29SeS22S2aSeS2bU5S3S4S1S7S4S0S0A2A1M0A2S4SdS0A2S3S1G0S39S2cA4S3SdS0Z5aS23S10Z6A2A4A4A8S6A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_AL_li : ltac2:(tb__ "0|1|
ScS5S27S29SeS22S2aSeS2bU6S3S4S1S7S4S0S0A2A1M0A2S4SdS0A2S3S1G0S2fS2cA4S3SdS0Z5aS23S10Z4A2A4A4A8S6A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_FL_li : ltac2:(tb__ "0|1|
ScS5S27S29SeS22S2aSeS2bU7S3S4S1S7S4S0S0A2A1M0A2S4SdS0A2S3S1G0S34S2cA4S3SdS0Z55S21A4A4A8S6A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_AL_lc : ltac2:(tb__ "0|1|
ScS5S27S29SeS22S2aSeS2bU8S3S4S1S7S4S0S0A2A1M0A2S4SdS0A2S3S1G0S2eS2cA4S3SdS0Z46S21A4A4A8S6A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_FL_lc : ltac2:(tb__ "0|1|
ScS5S27S29SeS22S2aSeS2bU9S3S4S1S7S4S0S0A2A1M0A2S4SdS0A2S3S1G0S33S2cA4S3SdS0Z46S21A4A4A8S6A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_l_c1.

Module Lib_handle_p_s1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G5.Lib_handle_p_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition E2_pi : sstate := vr_view EP_pi.
Definition s_pi : wsub := vr_sub pi1 12 E2_pi.
Lemma chk_pi : ltac2:(tb__ "0|1|
ScS5S40S2dZ60S49S4aU0S30S35S23S10Z4A2Z5aM0S21Z55G0S23S10Z5A2AdS6A3").
Proof. cbv delta [vr_site_checkG]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
Lemma view_pi : ltac2:(tb__ "0|2|
ScSbS1A1S28S9S25S26U1M0S2N40M1A1A2SaS25A1A3G0G1S32A4S8S1S49A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Lemma chk_pc : ltac2:(tb__ "0|2|
ScS5S3eS2dN54S31S3cS3bZ5aM0S23S10Z6A2M1G0G1G0S23S10Z7A2AbS6A3").
Proof. cbv delta [pcf_site_check Epf1 pccont_checkG norm_pcf]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_site. Qed.
End Lib_handle_p_s1.
