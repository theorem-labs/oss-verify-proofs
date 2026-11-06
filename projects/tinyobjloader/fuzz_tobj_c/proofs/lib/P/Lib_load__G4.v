(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "list"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "SAlu"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "ANone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "NP"; "FUEL"; "cps"; "amL"; "tvL"; "VLp"; "z0"; "K_um"; "K_disp"; "pQ"; "pR"; "tv0"; "K_A4"; "K_dfl"; "K_loop"; "K_mm"; "K_skip"; "K_tok"; "K_us1"; "K_us2"; "Pre_lo"; "T_mnull"; "T_mok"; "pE"; "pW"; "tv_m"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "ejcutA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes"; "nodesE"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"].
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle_f.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_load_obj_c3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.
Lemma ec_K_disp118 : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U17S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S13Z76A1S0G0S9SfSeA4A4S0S8S5Z1f4S10Z35S11A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_dfl : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U18S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S18S0G0S9SfSeA4A4S0S8S5Z1f4S10Z35S11A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_um2 : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U19S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S12Z143c4Z2A2S0G0S9SfSeA4A4S0S8S5Z1f4S10Z33S11A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_um3 : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U1aS0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S12Z143d8Z3A2S0G0S9SfSeA4A4S0S8S5Z1f4S10Z32S11A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_um4 : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U1bS0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S12Z143ecZ4A2S0G0S9SfSeA4A4S0S8S5Z1f4S10Z31S11A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_um5 : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U1cS0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S12Z14400Z5A2S0G0S9SfSeA4A4S0S8S5Z1f4S10Z30S11A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_c3.

Module Lib_load_obj_c1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.
Lemma ec_Pre_lo : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U0S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S1fS0G0S9S16SaA4A4S0S8S5Z3e8S11A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_mnull : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U1S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S20S0G0S9S16SaA4A4S0S8S5Z3d4S11A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_mok : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U2S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S21S0G0S9S24SaA4A4S0S8S5Z3d4S11A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_A4 : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U3S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S17S0G0S9SfSeA4A4S0S8S5Z3b6S11A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_loop : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U4S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S19S0G0S9SfSeA4A4S0S8S5Z1f4S10Z3cS11A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_skip : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U5S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S1bS0G0S9SfSeA4A4S0S8S5Z1f4S10Z3aS15A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_tok : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U6S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S1cS0G0S9SfSeA4A4S0S8S5Z1f4S10Z38S7S29S22S14A3A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp102 : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U7S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S13Z66A1S0G0S9SfSeA4A4S0S8S5Z1f4S10Z35S11A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_disp103 : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U8S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S13Z67A1S0G0S9SfSeA4A4S0S8S5Z1f4S10Z35S11A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_c1.

Module Lib_load_obj_c5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.
Lemma ec_K_mm6 : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U22S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S1aZ1447cZ6A2S0G0S9SfSeA4A4S0S8S5Z1f4S10Z2fS11A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_us1 : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U23S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S1dS0G0S9SfSeA4A4S0S8S5Z1f4S10Z2eS15A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_K_us2 : ltac2:(tb__ "0|2|
S25S2S26S27SbScSdSbS28U24S0S1S6S1S3S1S5S5A2A1M0S9A2M1A2S1S8S5A2S0S6G1S1eS0G0S9SfSeA4A4S0S8S5Z1f4S10Z2dS7S29S23S14A3A2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_c5.
